%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:25 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   67 (  98 expanded)
%              Number of clauses        :   21 (  25 expanded)
%              Number of leaves         :   18 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  113 ( 156 expanded)
%              Number of equality atoms :   39 (  66 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f22])).

fof(f40,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f29,f25])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f33,f43])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f32,f44])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f31,f45])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f46])).

fof(f53,plain,(
    r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),sK2) ),
    inference(definition_unfolding,[],[f40,f42,f47])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f28,f42])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f20])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f41,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_101,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_100,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_912,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_101,c_100])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_2439,plain,
    ( ~ r1_tarski(X0,X1)
    | X0 = k3_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_912,c_2])).

cnf(c_103,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_886,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_100,c_103])).

cnf(c_2656,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k3_xboole_0(X0,X1),X2) ),
    inference(resolution,[status(thm)],[c_2439,c_886])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_1096,plain,
    ( ~ r1_tarski(k3_xboole_0(X0,X1),X2)
    | r1_tarski(k3_xboole_0(X1,X0),X2) ),
    inference(resolution,[status(thm)],[c_886,c_0])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1219,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(X2,X0),X1) ),
    inference(resolution,[status(thm)],[c_1096,c_1])).

cnf(c_2884,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(resolution,[status(thm)],[c_2656,c_1219])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2900,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))
    | r1_tarski(X0,sK2) ),
    inference(resolution,[status(thm)],[c_2884,c_9])).

cnf(c_3,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3068,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(resolution,[status(thm)],[c_2900,c_3])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3084,plain,
    ( r2_hidden(sK0,sK2) ),
    inference(resolution,[status(thm)],[c_3068,c_7])).

cnf(c_8,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3084,c_8])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:10:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.67/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/0.98  
% 2.67/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.67/0.98  
% 2.67/0.98  ------  iProver source info
% 2.67/0.98  
% 2.67/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.67/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.67/0.98  git: non_committed_changes: false
% 2.67/0.98  git: last_make_outside_of_git: false
% 2.67/0.98  
% 2.67/0.98  ------ 
% 2.67/0.98  ------ Parsing...
% 2.67/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.67/0.98  
% 2.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.67/0.98  
% 2.67/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.67/0.98  
% 2.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.67/0.98  ------ Proving...
% 2.67/0.98  ------ Problem Properties 
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  clauses                                 10
% 2.67/0.98  conjectures                             2
% 2.67/0.98  EPR                                     1
% 2.67/0.98  Horn                                    10
% 2.67/0.98  unary                                   5
% 2.67/0.98  binary                                  4
% 2.67/0.98  lits                                    16
% 2.67/0.98  lits eq                                 3
% 2.67/0.98  fd_pure                                 0
% 2.67/0.98  fd_pseudo                               0
% 2.67/0.98  fd_cond                                 0
% 2.67/0.98  fd_pseudo_cond                          0
% 2.67/0.98  AC symbols                              0
% 2.67/0.98  
% 2.67/0.98  ------ Input Options Time Limit: Unbounded
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  ------ 
% 2.67/0.98  Current options:
% 2.67/0.98  ------ 
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  ------ Proving...
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  % SZS status Theorem for theBenchmark.p
% 2.67/0.98  
% 2.67/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.67/0.98  
% 2.67/0.98  fof(f4,axiom,(
% 2.67/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f18,plain,(
% 2.67/0.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.67/0.98    inference(ennf_transformation,[],[f4])).
% 2.67/0.98  
% 2.67/0.98  fof(f27,plain,(
% 2.67/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f18])).
% 2.67/0.98  
% 2.67/0.98  fof(f1,axiom,(
% 2.67/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f24,plain,(
% 2.67/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f1])).
% 2.67/0.98  
% 2.67/0.98  fof(f3,axiom,(
% 2.67/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f17,plain,(
% 2.67/0.98    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 2.67/0.98    inference(ennf_transformation,[],[f3])).
% 2.67/0.98  
% 2.67/0.98  fof(f26,plain,(
% 2.67/0.98    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f17])).
% 2.67/0.98  
% 2.67/0.98  fof(f15,conjecture,(
% 2.67/0.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f16,negated_conjecture,(
% 2.67/0.98    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 2.67/0.98    inference(negated_conjecture,[],[f15])).
% 2.67/0.98  
% 2.67/0.98  fof(f19,plain,(
% 2.67/0.98    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 2.67/0.98    inference(ennf_transformation,[],[f16])).
% 2.67/0.98  
% 2.67/0.98  fof(f22,plain,(
% 2.67/0.98    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 2.67/0.98    introduced(choice_axiom,[])).
% 2.67/0.98  
% 2.67/0.98  fof(f23,plain,(
% 2.67/0.98    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 2.67/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f22])).
% 2.67/0.98  
% 2.67/0.98  fof(f40,plain,(
% 2.67/0.98    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 2.67/0.98    inference(cnf_transformation,[],[f23])).
% 2.67/0.98  
% 2.67/0.98  fof(f6,axiom,(
% 2.67/0.98    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f29,plain,(
% 2.67/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f6])).
% 2.67/0.98  
% 2.67/0.98  fof(f2,axiom,(
% 2.67/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f25,plain,(
% 2.67/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.67/0.98    inference(cnf_transformation,[],[f2])).
% 2.67/0.98  
% 2.67/0.98  fof(f42,plain,(
% 2.67/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 2.67/0.98    inference(definition_unfolding,[],[f29,f25])).
% 2.67/0.98  
% 2.67/0.98  fof(f7,axiom,(
% 2.67/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f30,plain,(
% 2.67/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f7])).
% 2.67/0.98  
% 2.67/0.98  fof(f8,axiom,(
% 2.67/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f31,plain,(
% 2.67/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f8])).
% 2.67/0.98  
% 2.67/0.98  fof(f9,axiom,(
% 2.67/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f32,plain,(
% 2.67/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f9])).
% 2.67/0.98  
% 2.67/0.98  fof(f10,axiom,(
% 2.67/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f33,plain,(
% 2.67/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f10])).
% 2.67/0.98  
% 2.67/0.98  fof(f11,axiom,(
% 2.67/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f34,plain,(
% 2.67/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f11])).
% 2.67/0.98  
% 2.67/0.98  fof(f12,axiom,(
% 2.67/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f35,plain,(
% 2.67/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f12])).
% 2.67/0.98  
% 2.67/0.98  fof(f43,plain,(
% 2.67/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.67/0.98    inference(definition_unfolding,[],[f34,f35])).
% 2.67/0.98  
% 2.67/0.98  fof(f44,plain,(
% 2.67/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.67/0.98    inference(definition_unfolding,[],[f33,f43])).
% 2.67/0.98  
% 2.67/0.98  fof(f45,plain,(
% 2.67/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.67/0.98    inference(definition_unfolding,[],[f32,f44])).
% 2.67/0.98  
% 2.67/0.98  fof(f46,plain,(
% 2.67/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.67/0.98    inference(definition_unfolding,[],[f31,f45])).
% 2.67/0.98  
% 2.67/0.98  fof(f47,plain,(
% 2.67/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.67/0.98    inference(definition_unfolding,[],[f30,f46])).
% 2.67/0.98  
% 2.67/0.98  fof(f53,plain,(
% 2.67/0.98    r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),sK2)),
% 2.67/0.98    inference(definition_unfolding,[],[f40,f42,f47])).
% 2.67/0.98  
% 2.67/0.98  fof(f5,axiom,(
% 2.67/0.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f28,plain,(
% 2.67/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.67/0.98    inference(cnf_transformation,[],[f5])).
% 2.67/0.98  
% 2.67/0.98  fof(f48,plain,(
% 2.67/0.98    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 2.67/0.98    inference(definition_unfolding,[],[f28,f42])).
% 2.67/0.98  
% 2.67/0.98  fof(f14,axiom,(
% 2.67/0.98    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.67/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f20,plain,(
% 2.67/0.98    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.67/0.98    inference(nnf_transformation,[],[f14])).
% 2.67/0.98  
% 2.67/0.98  fof(f21,plain,(
% 2.67/0.98    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.67/0.98    inference(flattening,[],[f20])).
% 2.67/0.98  
% 2.67/0.98  fof(f37,plain,(
% 2.67/0.98    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f21])).
% 2.67/0.98  
% 2.67/0.98  fof(f52,plain,(
% 2.67/0.98    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 2.67/0.98    inference(definition_unfolding,[],[f37,f47])).
% 2.67/0.98  
% 2.67/0.98  fof(f41,plain,(
% 2.67/0.98    ~r2_hidden(sK0,sK2)),
% 2.67/0.98    inference(cnf_transformation,[],[f23])).
% 2.67/0.98  
% 2.67/0.98  cnf(c_101,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_100,plain,( X0 = X0 ),theory(equality) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_912,plain,
% 2.67/0.98      ( X0 != X1 | X1 = X0 ),
% 2.67/0.98      inference(resolution,[status(thm)],[c_101,c_100]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_2,plain,
% 2.67/0.98      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.67/0.98      inference(cnf_transformation,[],[f27]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_2439,plain,
% 2.67/0.98      ( ~ r1_tarski(X0,X1) | X0 = k3_xboole_0(X0,X1) ),
% 2.67/0.98      inference(resolution,[status(thm)],[c_912,c_2]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_103,plain,
% 2.67/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.67/0.98      theory(equality) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_886,plain,
% 2.67/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 2.67/0.98      inference(resolution,[status(thm)],[c_100,c_103]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_2656,plain,
% 2.67/0.98      ( ~ r1_tarski(X0,X1)
% 2.67/0.98      | r1_tarski(X0,X2)
% 2.67/0.98      | ~ r1_tarski(k3_xboole_0(X0,X1),X2) ),
% 2.67/0.98      inference(resolution,[status(thm)],[c_2439,c_886]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_0,plain,
% 2.67/0.98      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.67/0.98      inference(cnf_transformation,[],[f24]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_1096,plain,
% 2.67/0.98      ( ~ r1_tarski(k3_xboole_0(X0,X1),X2)
% 2.67/0.98      | r1_tarski(k3_xboole_0(X1,X0),X2) ),
% 2.67/0.98      inference(resolution,[status(thm)],[c_886,c_0]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_1,plain,
% 2.67/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X2),X1) ),
% 2.67/0.98      inference(cnf_transformation,[],[f26]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_1219,plain,
% 2.67/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X2,X0),X1) ),
% 2.67/0.98      inference(resolution,[status(thm)],[c_1096,c_1]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_2884,plain,
% 2.67/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 2.67/0.98      inference(resolution,[status(thm)],[c_2656,c_1219]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_9,negated_conjecture,
% 2.67/0.98      ( r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),sK2) ),
% 2.67/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_2900,plain,
% 2.67/0.98      ( ~ r1_tarski(X0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))
% 2.67/0.98      | r1_tarski(X0,sK2) ),
% 2.67/0.98      inference(resolution,[status(thm)],[c_2884,c_9]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_3,plain,
% 2.67/0.98      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
% 2.67/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_3068,plain,
% 2.67/0.98      ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
% 2.67/0.98      inference(resolution,[status(thm)],[c_2900,c_3]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_7,plain,
% 2.67/0.98      ( r2_hidden(X0,X1)
% 2.67/0.98      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) ),
% 2.67/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_3084,plain,
% 2.67/0.98      ( r2_hidden(sK0,sK2) ),
% 2.67/0.98      inference(resolution,[status(thm)],[c_3068,c_7]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(c_8,negated_conjecture,
% 2.67/0.98      ( ~ r2_hidden(sK0,sK2) ),
% 2.67/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.67/0.98  
% 2.67/0.98  cnf(contradiction,plain,
% 2.67/0.98      ( $false ),
% 2.67/0.98      inference(minisat,[status(thm)],[c_3084,c_8]) ).
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.67/0.98  
% 2.67/0.98  ------                               Statistics
% 2.67/0.98  
% 2.67/0.98  ------ Selected
% 2.67/0.98  
% 2.67/0.98  total_time:                             0.129
% 2.67/0.98  
%------------------------------------------------------------------------------
