%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:25 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 128 expanded)
%              Number of clauses        :   21 (  25 expanded)
%              Number of leaves         :   17 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  111 ( 186 expanded)
%              Number of equality atoms :   37 (  96 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21])).

fof(f38,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f44])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f31,f40])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f30,f41])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f29,f42])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f43])).

fof(f51,plain,(
    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f38,f45,f44])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f26,f45])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f19])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f35,f44])).

fof(f39,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_98,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_100,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_876,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_98,c_100])).

cnf(c_99,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_906,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_99,c_98])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1059,plain,
    ( ~ r1_tarski(X0,X1)
    | X0 = k3_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_906,c_2])).

cnf(c_1201,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k3_xboole_0(X0,X1),X2) ),
    inference(resolution,[status(thm)],[c_876,c_1059])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_1190,plain,
    ( ~ r1_tarski(k3_xboole_0(X0,X1),X2)
    | r1_tarski(k3_xboole_0(X1,X0),X2) ),
    inference(resolution,[status(thm)],[c_876,c_0])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_1211,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(X2,X0),X1) ),
    inference(resolution,[status(thm)],[c_1190,c_1])).

cnf(c_1519,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(resolution,[status(thm)],[c_1201,c_1211])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1534,plain,
    ( ~ r1_tarski(X0,k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)))
    | r1_tarski(X0,sK2) ),
    inference(resolution,[status(thm)],[c_1519,c_9])).

cnf(c_3,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1554,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(resolution,[status(thm)],[c_1534,c_3])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1687,plain,
    ( r2_hidden(sK0,sK2) ),
    inference(resolution,[status(thm)],[c_1554,c_7])).

cnf(c_8,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1687,c_8])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:48:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.52/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/0.98  
% 2.52/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.52/0.98  
% 2.52/0.98  ------  iProver source info
% 2.52/0.98  
% 2.52/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.52/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.52/0.98  git: non_committed_changes: false
% 2.52/0.98  git: last_make_outside_of_git: false
% 2.52/0.98  
% 2.52/0.98  ------ 
% 2.52/0.98  ------ Parsing...
% 2.52/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.52/0.98  
% 2.52/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.52/0.98  
% 2.52/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.52/0.98  
% 2.52/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.52/0.98  ------ Proving...
% 2.52/0.98  ------ Problem Properties 
% 2.52/0.98  
% 2.52/0.98  
% 2.52/0.98  clauses                                 10
% 2.52/0.98  conjectures                             2
% 2.52/0.98  EPR                                     1
% 2.52/0.98  Horn                                    10
% 2.52/0.98  unary                                   5
% 2.52/0.98  binary                                  4
% 2.52/0.98  lits                                    16
% 2.52/0.98  lits eq                                 3
% 2.52/0.98  fd_pure                                 0
% 2.52/0.98  fd_pseudo                               0
% 2.52/0.98  fd_cond                                 0
% 2.52/0.98  fd_pseudo_cond                          0
% 2.52/0.98  AC symbols                              0
% 2.52/0.98  
% 2.52/0.98  ------ Input Options Time Limit: Unbounded
% 2.52/0.98  
% 2.52/0.98  
% 2.52/0.98  ------ 
% 2.52/0.98  Current options:
% 2.52/0.98  ------ 
% 2.52/0.98  
% 2.52/0.98  
% 2.52/0.98  
% 2.52/0.98  
% 2.52/0.98  ------ Proving...
% 2.52/0.98  
% 2.52/0.98  
% 2.52/0.98  % SZS status Theorem for theBenchmark.p
% 2.52/0.98  
% 2.52/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.52/0.98  
% 2.52/0.98  fof(f3,axiom,(
% 2.52/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f17,plain,(
% 2.52/0.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.52/0.98    inference(ennf_transformation,[],[f3])).
% 2.52/0.98  
% 2.52/0.98  fof(f25,plain,(
% 2.52/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.52/0.98    inference(cnf_transformation,[],[f17])).
% 2.52/0.98  
% 2.52/0.98  fof(f1,axiom,(
% 2.52/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f23,plain,(
% 2.52/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.52/0.98    inference(cnf_transformation,[],[f1])).
% 2.52/0.98  
% 2.52/0.98  fof(f2,axiom,(
% 2.52/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f16,plain,(
% 2.52/0.98    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 2.52/0.98    inference(ennf_transformation,[],[f2])).
% 2.52/0.98  
% 2.52/0.98  fof(f24,plain,(
% 2.52/0.98    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 2.52/0.98    inference(cnf_transformation,[],[f16])).
% 2.52/0.98  
% 2.52/0.98  fof(f14,conjecture,(
% 2.52/0.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f15,negated_conjecture,(
% 2.52/0.98    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 2.52/0.98    inference(negated_conjecture,[],[f14])).
% 2.52/0.98  
% 2.52/0.98  fof(f18,plain,(
% 2.52/0.98    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 2.52/0.98    inference(ennf_transformation,[],[f15])).
% 2.52/0.98  
% 2.52/0.98  fof(f21,plain,(
% 2.52/0.98    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 2.52/0.98    introduced(choice_axiom,[])).
% 2.52/0.98  
% 2.52/0.98  fof(f22,plain,(
% 2.52/0.98    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 2.52/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21])).
% 2.52/0.98  
% 2.52/0.98  fof(f38,plain,(
% 2.52/0.98    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 2.52/0.98    inference(cnf_transformation,[],[f22])).
% 2.52/0.98  
% 2.52/0.98  fof(f12,axiom,(
% 2.52/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f34,plain,(
% 2.52/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.52/0.98    inference(cnf_transformation,[],[f12])).
% 2.52/0.98  
% 2.52/0.98  fof(f45,plain,(
% 2.52/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.52/0.98    inference(definition_unfolding,[],[f34,f44])).
% 2.52/0.98  
% 2.52/0.98  fof(f6,axiom,(
% 2.52/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f28,plain,(
% 2.52/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.52/0.98    inference(cnf_transformation,[],[f6])).
% 2.52/0.98  
% 2.52/0.98  fof(f7,axiom,(
% 2.52/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f29,plain,(
% 2.52/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.52/0.98    inference(cnf_transformation,[],[f7])).
% 2.52/0.98  
% 2.52/0.98  fof(f8,axiom,(
% 2.52/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f30,plain,(
% 2.52/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.52/0.98    inference(cnf_transformation,[],[f8])).
% 2.52/0.98  
% 2.52/0.98  fof(f9,axiom,(
% 2.52/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f31,plain,(
% 2.52/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.52/0.98    inference(cnf_transformation,[],[f9])).
% 2.52/0.98  
% 2.52/0.98  fof(f10,axiom,(
% 2.52/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f32,plain,(
% 2.52/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.52/0.98    inference(cnf_transformation,[],[f10])).
% 2.52/0.98  
% 2.52/0.98  fof(f11,axiom,(
% 2.52/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f33,plain,(
% 2.52/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.52/0.98    inference(cnf_transformation,[],[f11])).
% 2.52/0.98  
% 2.52/0.98  fof(f40,plain,(
% 2.52/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.52/0.98    inference(definition_unfolding,[],[f32,f33])).
% 2.52/0.98  
% 2.52/0.98  fof(f41,plain,(
% 2.52/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.52/0.98    inference(definition_unfolding,[],[f31,f40])).
% 2.52/0.98  
% 2.52/0.98  fof(f42,plain,(
% 2.52/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.52/0.98    inference(definition_unfolding,[],[f30,f41])).
% 2.52/0.98  
% 2.52/0.98  fof(f43,plain,(
% 2.52/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.52/0.98    inference(definition_unfolding,[],[f29,f42])).
% 2.52/0.98  
% 2.52/0.98  fof(f44,plain,(
% 2.52/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.52/0.98    inference(definition_unfolding,[],[f28,f43])).
% 2.52/0.98  
% 2.52/0.98  fof(f51,plain,(
% 2.52/0.98    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2)),
% 2.52/0.98    inference(definition_unfolding,[],[f38,f45,f44])).
% 2.52/0.98  
% 2.52/0.98  fof(f4,axiom,(
% 2.52/0.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f26,plain,(
% 2.52/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.52/0.98    inference(cnf_transformation,[],[f4])).
% 2.52/0.98  
% 2.52/0.98  fof(f46,plain,(
% 2.52/0.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.52/0.98    inference(definition_unfolding,[],[f26,f45])).
% 2.52/0.98  
% 2.52/0.98  fof(f13,axiom,(
% 2.52/0.98    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.98  
% 2.52/0.98  fof(f19,plain,(
% 2.52/0.98    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.52/0.98    inference(nnf_transformation,[],[f13])).
% 2.52/0.98  
% 2.52/0.98  fof(f20,plain,(
% 2.52/0.98    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.52/0.98    inference(flattening,[],[f19])).
% 2.52/0.98  
% 2.52/0.98  fof(f35,plain,(
% 2.52/0.98    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 2.52/0.98    inference(cnf_transformation,[],[f20])).
% 2.52/0.98  
% 2.52/0.98  fof(f50,plain,(
% 2.52/0.98    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 2.52/0.98    inference(definition_unfolding,[],[f35,f44])).
% 2.52/0.98  
% 2.52/0.98  fof(f39,plain,(
% 2.52/0.98    ~r2_hidden(sK0,sK2)),
% 2.52/0.98    inference(cnf_transformation,[],[f22])).
% 2.52/0.98  
% 2.52/0.98  cnf(c_98,plain,( X0 = X0 ),theory(equality) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_100,plain,
% 2.52/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.52/0.98      theory(equality) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_876,plain,
% 2.52/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 2.52/0.98      inference(resolution,[status(thm)],[c_98,c_100]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_99,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_906,plain,
% 2.52/0.98      ( X0 != X1 | X1 = X0 ),
% 2.52/0.98      inference(resolution,[status(thm)],[c_99,c_98]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_2,plain,
% 2.52/0.98      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.52/0.98      inference(cnf_transformation,[],[f25]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1059,plain,
% 2.52/0.98      ( ~ r1_tarski(X0,X1) | X0 = k3_xboole_0(X0,X1) ),
% 2.52/0.98      inference(resolution,[status(thm)],[c_906,c_2]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1201,plain,
% 2.52/0.98      ( ~ r1_tarski(X0,X1)
% 2.52/0.98      | r1_tarski(X0,X2)
% 2.52/0.98      | ~ r1_tarski(k3_xboole_0(X0,X1),X2) ),
% 2.52/0.98      inference(resolution,[status(thm)],[c_876,c_1059]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_0,plain,
% 2.52/0.98      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.52/0.98      inference(cnf_transformation,[],[f23]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1190,plain,
% 2.52/0.98      ( ~ r1_tarski(k3_xboole_0(X0,X1),X2)
% 2.52/0.98      | r1_tarski(k3_xboole_0(X1,X0),X2) ),
% 2.52/0.98      inference(resolution,[status(thm)],[c_876,c_0]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1,plain,
% 2.52/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X2),X1) ),
% 2.52/0.98      inference(cnf_transformation,[],[f24]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1211,plain,
% 2.52/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X2,X0),X1) ),
% 2.52/0.98      inference(resolution,[status(thm)],[c_1190,c_1]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1519,plain,
% 2.52/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 2.52/0.98      inference(resolution,[status(thm)],[c_1201,c_1211]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_9,negated_conjecture,
% 2.52/0.98      ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
% 2.52/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1534,plain,
% 2.52/0.98      ( ~ r1_tarski(X0,k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)))
% 2.52/0.98      | r1_tarski(X0,sK2) ),
% 2.52/0.98      inference(resolution,[status(thm)],[c_1519,c_9]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_3,plain,
% 2.52/0.98      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 2.52/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_1554,plain,
% 2.52/0.98      ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
% 2.52/0.98      inference(resolution,[status(thm)],[c_1534,c_3]) ).
% 2.52/0.98  
% 2.52/0.98  cnf(c_7,plain,
% 2.52/0.98      ( r2_hidden(X0,X1)
% 2.52/0.98      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) ),
% 2.52/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1687,plain,
% 2.52/0.99      ( r2_hidden(sK0,sK2) ),
% 2.52/0.99      inference(resolution,[status(thm)],[c_1554,c_7]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_8,negated_conjecture,
% 2.52/0.99      ( ~ r2_hidden(sK0,sK2) ),
% 2.52/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(contradiction,plain,
% 2.52/0.99      ( $false ),
% 2.52/0.99      inference(minisat,[status(thm)],[c_1687,c_8]) ).
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.52/0.99  
% 2.52/0.99  ------                               Statistics
% 2.52/0.99  
% 2.52/0.99  ------ Selected
% 2.52/0.99  
% 2.52/0.99  total_time:                             0.118
% 2.52/0.99  
%------------------------------------------------------------------------------
