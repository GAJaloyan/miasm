from miasm2.expression.expression import ExprInt, ExprLoc, ExprAff, ExprId
from miasm2.core.graph import DiGraph
from miasm2.core.locationdb import LocationDB
from miasm2.expression.simplifications import expr_simp_explicit
from miasm2.ir.symbexec import SymbolicExecutionEngine
from miasm2.ir.ir import IRBlock, AssignBlock
from miasm2.ir.translators import Translator
from miasm2.expression.expression_helper import possible_values
from miasm2.analysis.depgraph import DependencyNode, DependencyState, \
    DependencyResult, DependencyResultImplicit, FollowExpr, DependencyGraph
try:
    import z3
except ImportError:
    pass

class InfluenceState(DependencyState):

    """
    Store intermediate depnodes states during influencegraph analysis
    """

    def __init__(self, loc_key, pending, line_nb=None):
        super(self.__class__, self).__init__(loc_key, pending, line_nb)

    def __repr__(self): ##
        return "<State: %r (%r) (%r)>" % (self.loc_key,
                                          self.pending,
                                          self.links)

    def extend(self, loc_key): ##
        """Return a copy of itself, with itself in history
        @loc_key: LocKey instance for the new DependencyState's loc_key
        """
        new_state = self.__class__(loc_key, self.pending)
        new_state.links = set(self.links)
        new_state.history = self.history + [loc_key]
        return new_state

    def get_done_state(self): ##
        """Returns immutable object representing current state"""
        return (self.loc_key, frozenset(self.links))

    def as_graph(self):
        """Generates a Digraph of dependencies"""
        graph = DiGraph()
        for node_a, node_b in self.links:
            graph.add_edge(node_b, node_a) 
        return graph

    @property
    def graph(self): 
        """Returns a DiGraph instance representing the DependencyGraph"""
        return self.as_graph()

    def remove_pendings(self, nodes):
        """Remove resolved @nodes"""
        for node in nodes:
            del self.pending[node]

    def link_element(self, element, line_nb): 
        """Link element to its dependencies
        @element: the element to link
        @line_nb: the element's line
        """
        depnode = DependencyNode(self.loc_key, element, line_nb)
        if not self.pending.has_key(element):
            # Create start node
            self.links.add((depnode, None))
        else:
            # Link element to its known dependencies
            for node_son in self.pending[depnode]:
                self.links.add((depnode, node_son))

    def link_dependencies(self, element, line_nb, sources,
                          future_pending): 
        """Link unfollowed sources and create remaining pending elements.
        @element: the element to link
        @line_nb: the element's line
        @sources: the element's taint sources
        @future_pending: the future taint source
        """

        depnode = DependencyNode(self.loc_key, element, line_nb)

        # Update pending, add link to unfollowed nodes
        for source in sources:
            pendingfound = None
            for i in list(self.pending):
                if i.element == source.element:
                    pendingfound = i
                    
            lc = pendingfound.loc_key if pendingfound is not None else self.loc_key
            lnb = pendingfound.line_nb if pendingfound is not None else line_nb
            parent = DependencyNode(lc, source.element, lnb)
            self.links.add((depnode, parent))
            # Create future pending between the current element and the 
            # old dependecy
            future_pending.setdefault(depnode, set()).add(parent)

class InfluenceResult(InfluenceState,DependencyResult):
    """Container and methods for DependencyGraph results"""
    
    def __init__(self, ircfg, initial_state, state, inputs):
        self.initial_state = initial_state
        self.loc_key = state.loc_key
        self.history = state.history
        self.pending = state.pending
        self.line_nb = state.line_nb
        self.inputs = inputs
        self.links = state.links
        self._ircfg = ircfg
        
        # Init lazy elements
        self._graph = None
        self._has_loop = None

class InfluenceResultImplicit(InfluenceResult,DependencyResultImplicit):
    pass
    # def emul(self, ir_arch, ctx=None, step=False):
    #     # Init
    #     ctx_init = {}
    #     if ctx is not None:
    #         ctx_init.update(ctx)
    #     solver = z3.Solver()
    #     symb_exec = SymbolicExecutionEngine(ir_arch, ctx_init)            
    #     history = self.history
    #     history_size = len(history)
    #     translator = Translator.to_language("z3m")
    #     size = self._ircfg.IRDst.size
    #     mem = translator._mem.get_mem_array(size)
    #     for i in ctx:
    #         solver.add(translator.from_expr(i) == translator.from_expr(ctx[i]))
    #     solver.add(mem.default() == 0x1ff)

    #     print map(hex,map(ir_arch.loc_db.get_location_offset,history))
    #     for hist_nb, loc_key in enumerate(history, 1):
    #         taintedirdst = False
    #         if hist_nb == history_size and loc_key == self.initial_state.loc_key:
    #             line_nb = self.initial_state.line_nb
    #         else:
    #             line_nb = None
    #         irc = self.irblock_slice(self._ircfg.blocks[loc_key], line_nb)
    #         if irc.dst is not None:
    #             #the dst is tainted
    #             taintedirdst = True

    #         irb = self._ircfg.blocks[loc_key]
    #         # Emul the block and get back destination
    #         dst = symb_exec.eval_updt_irblock(irb, step=step)
    #         # import IPython
    #         # IPython.embed()
    #         # Add constraint
    #         if hist_nb < history_size:
    #             next_loc_key = history[hist_nb]
    #             expected = symb_exec.eval_expr(ExprLoc(next_loc_key, size))
    #             solver.add(self._gen_path_constraints(translator, dst, expected))
    #             if(solver.check() == False):
    #                 self._solver = solver
    #                 return None
    #             print dst, expected
    #             print solver.check(), solver.model()
    #             if taintedirdst:
    #                 print "tainteddirst branch"
    #                 #get all the memory values not undefined
    #                 solver.push()
    #                 index_list = set()
    #                 z3m_temp = translator.from_expr(ExprId("__z3m__tmp",64))
    #                 z3m_free = translator.from_expr(ExprId("__z3m__free",64))
    #                 mem_body = solver.model()[mem].body()
    #                 solver.add(z3.ForAll([z3m_free], mem[z3m_free] == z3.substitute_vars(mem_body,z3m_free))) 
    #                 solver.add(mem[z3m_temp]!=0x1ff)
    #                 while(solver.check() == z3.sat):
    #                     index = solver.model()[z3m_temp]
    #                     index_list.add(index)
    #                     solver.add(z3m_temp != index)
    #                 solver.pop()

                    
    #                 import IPython
    #                 IPython.embed()


    #         if hist_nb == history_size:
    #             #last basic block: 
    #             print "last basic block"
    #             import IPython
    #             IPython.embed()
    #     # Save the solver
    #     self._solver = solver
    #     # Return only inputs values (others could be wrongs)
    #     return {element: symb_exec.eval_expr(element)
    #             for element in self.inputs}

class InfluenceGraph(DependencyGraph):

    """Implementation of an influence graph, a forward dependency graph

    An influence graph contains DependencyNode as nodes. The oriented edges
    stand for an influence.
    The influence graph is made of the lines of a group of IRblock
    *explicitely* or *implicitely* involved in the equation of given element.
    """

    def _track_exprs(self, state, assignblk, line_nb):
        """Track pending expression in an assignblock"""
        future_pending = {}
        node_resolved = set()
        for dst, src in assignblk.iteritems():
            # Track IRDst in implicit mode only
            if dst == self._ircfg.IRDst and not self._implicit:
                continue
            # HERE comes the tainting policy: we considered anything read from a tainted is tainted, but the lvalue is not tainted if it is computed from a tainted value (ie dereferencing a tainted pointers for W is not taitned)

            # Get all the tainted sources
            sourcesall = self._follow_apply_cb(src)
            pendings = {e.element for e in state.pending.keys()}
            sources = {i for i in sourcesall if i.element in pendings}
            if dst in pendings:
                #overwritten tainted lhs: influence ends here
                for i in state.pending:
                    if i.element == dst:
                        node_resolved.add(i)                            
#            print assignblk,"\n", sourcesall,"\n"
            if len(sources) == 0:
                #the rhs has no taint
                continue
            assert dst not in node_resolved
            state.link_dependencies(dst, line_nb, sources, future_pending)

        # Update pending nodes
        state.remove_pendings(node_resolved)
        state.add_pendings(future_pending)

    def _compute_intrablock(self, state):
        """Follow influences tracked in @state in the current irbloc
        @state: instance of InfluenceState"""

        try:
            irb = self._ircfg.blocks[state.loc_key]
        except:
            import IPython
            IPython.embed()
        line_nb = 0 if state.line_nb is None else state.line_nb

        for cur_line_nb, assignblk in list(enumerate(irb[line_nb:])):
            self._track_exprs(state, assignblk, cur_line_nb)

    def get(self, loc_key, elements, line_nb, tails):
        """Compute the influences of @elements at line number @line_nb in
        the block named @loc_key in the current IRCFG, before the execution of
        this line. Influence check stop if one of @tails is reached
        @loc_key: LocKey instance
        @element: set of Expr instances
        @line_nb: int
        @tails: set of LocKey instances
        Return an iterator on DiGraph(DependencyNode)
        """
        # Init the algorithm
        inputs = {DependencyNode(loc_key,element,line_nb): set() for element in elements}
        initial_state = InfluenceState(loc_key, inputs, line_nb)
        todo = set([initial_state])
        done = set()
        dpResultcls = InfluenceResultImplicit if self._implicit else InfluenceResult

        while todo:
            state = todo.pop()
            self._compute_intrablock(state)
            done_state = state.get_done_state()
            if done_state in done:
                continue
            done.add(done_state)
            if (not state.pending or
                    state.loc_key in tails or
                    not self._ircfg.successors(state.loc_key)): 
                yield dpResultcls(self._ircfg, initial_state, state, elements)
                if not state.pending:
                    continue

            #            if self._implicit:
            # Force IRDst to be tracked, except in the input block
            #                state.pending[self._ircfg.IRDst] = set()

            # Propagate state to children
            if state.loc_key not in tails:
                for succ in self._ircfg.successors_iter(state.loc_key):
                    todo.add(state.extend(succ))
