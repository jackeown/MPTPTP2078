%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:24 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 170 expanded)
%              Number of clauses        :   36 (  63 expanded)
%              Number of leaves         :    9 (  36 expanded)
%              Depth                    :   20
%              Number of atoms          :  167 ( 547 expanded)
%              Number of equality atoms :   69 ( 206 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f42,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f54,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f55,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f54])).

fof(f56,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK3,sK4)
        | ~ r2_hidden(sK2,sK4)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(sK2,sK3),sK4) )
      & ( ( r2_hidden(sK3,sK4)
          & r2_hidden(sK2,sK4) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ( ~ r2_hidden(sK3,sK4)
      | ~ r2_hidden(sK2,sK4)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(sK2,sK3),sK4) )
    & ( ( r2_hidden(sK3,sK4)
        & r2_hidden(sK2,sK4) )
      | k1_xboole_0 = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f55,f56])).

fof(f94,plain,
    ( r2_hidden(sK2,sK4)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f50])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f95,plain,
    ( r2_hidden(sK3,sK4)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f18,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f83,f79])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f82,f79])).

fof(f96,plain,
    ( ~ r2_hidden(sK3,sK4)
    | ~ r2_hidden(sK2,sK4)
    | k1_xboole_0 != k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_445,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_4194,plain,
    ( ~ r1_tarski(X0,X1)
    | X2 = k4_xboole_0(X0,X1)
    | X2 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_445,c_10])).

cnf(c_36,negated_conjecture,
    ( r2_hidden(sK2,sK4)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_4213,plain,
    ( r2_hidden(sK2,sK4)
    | X0 != k4_xboole_0(k2_tarski(sK2,sK3),sK4)
    | X0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_445,c_36])).

cnf(c_444,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4475,plain,
    ( r2_hidden(sK2,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4213,c_444])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4769,plain,
    ( r1_tarski(k2_tarski(sK2,sK3),sK4)
    | r2_hidden(sK2,sK4) ),
    inference(resolution,[status(thm)],[c_4475,c_11])).

cnf(c_26,plain,
    ( ~ r1_tarski(k2_tarski(X0,X1),X2)
    | r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_8265,plain,
    ( r2_hidden(sK2,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4769,c_26])).

cnf(c_448,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_35,negated_conjecture,
    ( r2_hidden(sK3,sK4)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_5802,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(k2_tarski(sK2,sK3),sK4))
    | r2_hidden(X1,k1_xboole_0)
    | r2_hidden(sK3,sK4)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_448,c_35])).

cnf(c_1199,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK2,sK3),sK4)
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k2_tarski(X0,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1212,plain,
    ( k4_xboole_0(k2_tarski(X0,X0),X1) = k1_xboole_0
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5045,plain,
    ( k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0
    | k4_xboole_0(k2_tarski(sK3,sK3),sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1199,c_1212])).

cnf(c_1222,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5648,plain,
    ( k4_xboole_0(k2_tarski(sK3,sK3),sK4) = k1_xboole_0
    | r1_tarski(k2_tarski(sK2,sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5045,c_1222])).

cnf(c_25,plain,
    ( ~ r1_tarski(k2_tarski(X0,X1),X2)
    | r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1209,plain,
    ( r1_tarski(k2_tarski(X0,X1),X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6084,plain,
    ( k4_xboole_0(k2_tarski(sK3,sK3),sK4) = k1_xboole_0
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5648,c_1209])).

cnf(c_23,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k2_tarski(X0,X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1211,plain,
    ( k4_xboole_0(k2_tarski(X0,X0),X1) != k1_xboole_0
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6707,plain,
    ( r2_hidden(sK3,sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6084,c_1211])).

cnf(c_6708,plain,
    ( r2_hidden(sK3,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6707])).

cnf(c_6719,plain,
    ( r2_hidden(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5802,c_6708])).

cnf(c_34,negated_conjecture,
    ( ~ r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK3,sK4)
    | k1_xboole_0 != k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_6730,plain,
    ( ~ r2_hidden(sK2,sK4)
    | k1_xboole_0 != k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_6719,c_34])).

cnf(c_9538,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_8265,c_6730])).

cnf(c_12200,plain,
    ( ~ r1_tarski(k2_tarski(sK2,sK3),sK4)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4194,c_9538])).

cnf(c_12201,plain,
    ( ~ r1_tarski(k2_tarski(sK2,sK3),sK4) ),
    inference(equality_resolution_simp,[status(thm)],[c_12200])).

cnf(c_24,plain,
    ( r1_tarski(k2_tarski(X0,X1),X2)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_12462,plain,
    ( ~ r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_12201,c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12462,c_8265,c_6708])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:36:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.56/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.00  
% 3.56/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.56/1.00  
% 3.56/1.00  ------  iProver source info
% 3.56/1.00  
% 3.56/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.56/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.56/1.00  git: non_committed_changes: false
% 3.56/1.00  git: last_make_outside_of_git: false
% 3.56/1.00  
% 3.56/1.00  ------ 
% 3.56/1.00  ------ Parsing...
% 3.56/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.56/1.00  ------ Proving...
% 3.56/1.00  ------ Problem Properties 
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  clauses                                 37
% 3.56/1.00  conjectures                             3
% 3.56/1.00  EPR                                     4
% 3.56/1.00  Horn                                    30
% 3.56/1.00  unary                                   12
% 3.56/1.00  binary                                  19
% 3.56/1.00  lits                                    72
% 3.56/1.00  lits eq                                 24
% 3.56/1.00  fd_pure                                 0
% 3.56/1.00  fd_pseudo                               0
% 3.56/1.00  fd_cond                                 1
% 3.56/1.00  fd_pseudo_cond                          2
% 3.56/1.00  AC symbols                              0
% 3.56/1.00  
% 3.56/1.00  ------ Input Options Time Limit: Unbounded
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  ------ 
% 3.56/1.00  Current options:
% 3.56/1.00  ------ 
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  ------ Proving...
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  % SZS status Theorem for theBenchmark.p
% 3.56/1.00  
% 3.56/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.56/1.00  
% 3.56/1.00  fof(f8,axiom,(
% 3.56/1.00    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f47,plain,(
% 3.56/1.00    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 3.56/1.00    inference(nnf_transformation,[],[f8])).
% 3.56/1.00  
% 3.56/1.00  fof(f69,plain,(
% 3.56/1.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f47])).
% 3.56/1.00  
% 3.56/1.00  fof(f25,conjecture,(
% 3.56/1.00    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f26,negated_conjecture,(
% 3.56/1.00    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.56/1.00    inference(negated_conjecture,[],[f25])).
% 3.56/1.00  
% 3.56/1.00  fof(f42,plain,(
% 3.56/1.00    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.56/1.00    inference(ennf_transformation,[],[f26])).
% 3.56/1.00  
% 3.56/1.00  fof(f54,plain,(
% 3.56/1.00    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 3.56/1.00    inference(nnf_transformation,[],[f42])).
% 3.56/1.00  
% 3.56/1.00  fof(f55,plain,(
% 3.56/1.00    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 3.56/1.00    inference(flattening,[],[f54])).
% 3.56/1.00  
% 3.56/1.00  fof(f56,plain,(
% 3.56/1.00    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK3,sK4) | ~r2_hidden(sK2,sK4) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK2,sK3),sK4)) & ((r2_hidden(sK3,sK4) & r2_hidden(sK2,sK4)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK2,sK3),sK4)))),
% 3.56/1.00    introduced(choice_axiom,[])).
% 3.56/1.00  
% 3.56/1.00  fof(f57,plain,(
% 3.56/1.00    (~r2_hidden(sK3,sK4) | ~r2_hidden(sK2,sK4) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK2,sK3),sK4)) & ((r2_hidden(sK3,sK4) & r2_hidden(sK2,sK4)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK2,sK3),sK4))),
% 3.56/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f55,f56])).
% 3.56/1.00  
% 3.56/1.00  fof(f94,plain,(
% 3.56/1.00    r2_hidden(sK2,sK4) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 3.56/1.00    inference(cnf_transformation,[],[f57])).
% 3.56/1.00  
% 3.56/1.00  fof(f68,plain,(
% 3.56/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f47])).
% 3.56/1.00  
% 3.56/1.00  fof(f21,axiom,(
% 3.56/1.00    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f50,plain,(
% 3.56/1.00    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.56/1.00    inference(nnf_transformation,[],[f21])).
% 3.56/1.00  
% 3.56/1.00  fof(f51,plain,(
% 3.56/1.00    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.56/1.00    inference(flattening,[],[f50])).
% 3.56/1.00  
% 3.56/1.00  fof(f84,plain,(
% 3.56/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f51])).
% 3.56/1.00  
% 3.56/1.00  fof(f95,plain,(
% 3.56/1.00    r2_hidden(sK3,sK4) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 3.56/1.00    inference(cnf_transformation,[],[f57])).
% 3.56/1.00  
% 3.56/1.00  fof(f20,axiom,(
% 3.56/1.00    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f49,plain,(
% 3.56/1.00    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 3.56/1.00    inference(nnf_transformation,[],[f20])).
% 3.56/1.00  
% 3.56/1.00  fof(f83,plain,(
% 3.56/1.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f49])).
% 3.56/1.00  
% 3.56/1.00  fof(f18,axiom,(
% 3.56/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.56/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f79,plain,(
% 3.56/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f18])).
% 3.56/1.00  
% 3.56/1.00  fof(f102,plain,(
% 3.56/1.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.56/1.00    inference(definition_unfolding,[],[f83,f79])).
% 3.56/1.00  
% 3.56/1.00  fof(f85,plain,(
% 3.56/1.00    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f51])).
% 3.56/1.00  
% 3.56/1.00  fof(f82,plain,(
% 3.56/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f49])).
% 3.56/1.00  
% 3.56/1.00  fof(f103,plain,(
% 3.56/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X0),X1)) )),
% 3.56/1.00    inference(definition_unfolding,[],[f82,f79])).
% 3.56/1.00  
% 3.56/1.00  fof(f96,plain,(
% 3.56/1.00    ~r2_hidden(sK3,sK4) | ~r2_hidden(sK2,sK4) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 3.56/1.00    inference(cnf_transformation,[],[f57])).
% 3.56/1.00  
% 3.56/1.00  fof(f86,plain,(
% 3.56/1.00    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f51])).
% 3.56/1.00  
% 3.56/1.00  cnf(c_445,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_10,plain,
% 3.56/1.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.56/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_4194,plain,
% 3.56/1.00      ( ~ r1_tarski(X0,X1)
% 3.56/1.00      | X2 = k4_xboole_0(X0,X1)
% 3.56/1.00      | X2 != k1_xboole_0 ),
% 3.56/1.00      inference(resolution,[status(thm)],[c_445,c_10]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_36,negated_conjecture,
% 3.56/1.00      ( r2_hidden(sK2,sK4)
% 3.56/1.00      | k1_xboole_0 = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
% 3.56/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_4213,plain,
% 3.56/1.00      ( r2_hidden(sK2,sK4)
% 3.56/1.00      | X0 != k4_xboole_0(k2_tarski(sK2,sK3),sK4)
% 3.56/1.00      | X0 = k1_xboole_0 ),
% 3.56/1.00      inference(resolution,[status(thm)],[c_445,c_36]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_444,plain,( X0 = X0 ),theory(equality) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_4475,plain,
% 3.56/1.00      ( r2_hidden(sK2,sK4)
% 3.56/1.00      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0 ),
% 3.56/1.00      inference(resolution,[status(thm)],[c_4213,c_444]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_11,plain,
% 3.56/1.00      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.56/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_4769,plain,
% 3.56/1.00      ( r1_tarski(k2_tarski(sK2,sK3),sK4) | r2_hidden(sK2,sK4) ),
% 3.56/1.00      inference(resolution,[status(thm)],[c_4475,c_11]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_26,plain,
% 3.56/1.00      ( ~ r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2) ),
% 3.56/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_8265,plain,
% 3.56/1.00      ( r2_hidden(sK2,sK4) ),
% 3.56/1.00      inference(forward_subsumption_resolution,
% 3.56/1.00                [status(thm)],
% 3.56/1.00                [c_4769,c_26]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_448,plain,
% 3.56/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.56/1.00      theory(equality) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_35,negated_conjecture,
% 3.56/1.00      ( r2_hidden(sK3,sK4)
% 3.56/1.00      | k1_xboole_0 = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
% 3.56/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_5802,plain,
% 3.56/1.00      ( ~ r2_hidden(X0,k4_xboole_0(k2_tarski(sK2,sK3),sK4))
% 3.56/1.00      | r2_hidden(X1,k1_xboole_0)
% 3.56/1.00      | r2_hidden(sK3,sK4)
% 3.56/1.00      | X1 != X0 ),
% 3.56/1.00      inference(resolution,[status(thm)],[c_448,c_35]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_1199,plain,
% 3.56/1.00      ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK2,sK3),sK4)
% 3.56/1.00      | r2_hidden(sK3,sK4) = iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_22,plain,
% 3.56/1.00      ( ~ r2_hidden(X0,X1)
% 3.56/1.00      | k4_xboole_0(k2_tarski(X0,X0),X1) = k1_xboole_0 ),
% 3.56/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_1212,plain,
% 3.56/1.00      ( k4_xboole_0(k2_tarski(X0,X0),X1) = k1_xboole_0
% 3.56/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_5045,plain,
% 3.56/1.00      ( k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0
% 3.56/1.00      | k4_xboole_0(k2_tarski(sK3,sK3),sK4) = k1_xboole_0 ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_1199,c_1212]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_1222,plain,
% 3.56/1.00      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 3.56/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_5648,plain,
% 3.56/1.00      ( k4_xboole_0(k2_tarski(sK3,sK3),sK4) = k1_xboole_0
% 3.56/1.00      | r1_tarski(k2_tarski(sK2,sK3),sK4) = iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_5045,c_1222]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_25,plain,
% 3.56/1.00      ( ~ r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) ),
% 3.56/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_1209,plain,
% 3.56/1.00      ( r1_tarski(k2_tarski(X0,X1),X2) != iProver_top
% 3.56/1.00      | r2_hidden(X1,X2) = iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_6084,plain,
% 3.56/1.00      ( k4_xboole_0(k2_tarski(sK3,sK3),sK4) = k1_xboole_0
% 3.56/1.00      | r2_hidden(sK3,sK4) = iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_5648,c_1209]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_23,plain,
% 3.56/1.00      ( r2_hidden(X0,X1)
% 3.56/1.00      | k4_xboole_0(k2_tarski(X0,X0),X1) != k1_xboole_0 ),
% 3.56/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_1211,plain,
% 3.56/1.00      ( k4_xboole_0(k2_tarski(X0,X0),X1) != k1_xboole_0
% 3.56/1.00      | r2_hidden(X0,X1) = iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_6707,plain,
% 3.56/1.00      ( r2_hidden(sK3,sK4) = iProver_top ),
% 3.56/1.00      inference(forward_subsumption_resolution,
% 3.56/1.00                [status(thm)],
% 3.56/1.00                [c_6084,c_1211]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_6708,plain,
% 3.56/1.00      ( r2_hidden(sK3,sK4) ),
% 3.56/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6707]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_6719,plain,
% 3.56/1.00      ( r2_hidden(sK3,sK4) ),
% 3.56/1.00      inference(global_propositional_subsumption,
% 3.56/1.00                [status(thm)],
% 3.56/1.00                [c_5802,c_6708]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_34,negated_conjecture,
% 3.56/1.00      ( ~ r2_hidden(sK2,sK4)
% 3.56/1.00      | ~ r2_hidden(sK3,sK4)
% 3.56/1.00      | k1_xboole_0 != k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
% 3.56/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_6730,plain,
% 3.56/1.00      ( ~ r2_hidden(sK2,sK4)
% 3.56/1.00      | k1_xboole_0 != k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
% 3.56/1.00      inference(backward_subsumption_resolution,
% 3.56/1.00                [status(thm)],
% 3.56/1.00                [c_6719,c_34]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_9538,plain,
% 3.56/1.00      ( k1_xboole_0 != k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
% 3.56/1.00      inference(backward_subsumption_resolution,
% 3.56/1.00                [status(thm)],
% 3.56/1.00                [c_8265,c_6730]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_12200,plain,
% 3.56/1.00      ( ~ r1_tarski(k2_tarski(sK2,sK3),sK4)
% 3.56/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.56/1.00      inference(resolution,[status(thm)],[c_4194,c_9538]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_12201,plain,
% 3.56/1.00      ( ~ r1_tarski(k2_tarski(sK2,sK3),sK4) ),
% 3.56/1.00      inference(equality_resolution_simp,[status(thm)],[c_12200]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_24,plain,
% 3.56/1.00      ( r1_tarski(k2_tarski(X0,X1),X2)
% 3.56/1.00      | ~ r2_hidden(X0,X2)
% 3.56/1.00      | ~ r2_hidden(X1,X2) ),
% 3.56/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_12462,plain,
% 3.56/1.00      ( ~ r2_hidden(sK2,sK4) | ~ r2_hidden(sK3,sK4) ),
% 3.56/1.00      inference(resolution,[status(thm)],[c_12201,c_24]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(contradiction,plain,
% 3.56/1.00      ( $false ),
% 3.56/1.00      inference(minisat,[status(thm)],[c_12462,c_8265,c_6708]) ).
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.56/1.00  
% 3.56/1.00  ------                               Statistics
% 3.56/1.00  
% 3.56/1.00  ------ Selected
% 3.56/1.00  
% 3.56/1.00  total_time:                             0.395
% 3.56/1.00  
%------------------------------------------------------------------------------
