%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:00 EST 2020

% Result     : Theorem 35.81s
% Output     : CNFRefutation 35.81s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 171 expanded)
%              Number of clauses        :   20 (  21 expanded)
%              Number of leaves         :   14 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  113 ( 223 expanded)
%              Number of equality atoms :   62 ( 166 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f83,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f67,f60])).

fof(f88,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f46,f83,f83])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f87,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k5_xboole_0(X0,k3_xboole_0(X0,X1))))) ),
    inference(definition_unfolding,[],[f56,f83,f60,f60])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f85,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f70,f84])).

fof(f86,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f69,f85])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) = k3_enumset1(X0,X0,X0,X0,X0)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f76,f60,f86,f86])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f42])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2)))) ) ),
    inference(definition_unfolding,[],[f79,f60,f86])).

fof(f115,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2)))) ),
    inference(equality_resolution,[],[f107])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f23])).

fof(f28,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK2)) != sK3
      & r2_hidden(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK2)) != sK3
    & r2_hidden(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f44])).

fof(f82,plain,(
    k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK2)) != sK3 ),
    inference(cnf_transformation,[],[f45])).

fof(f109,plain,(
    k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))))) != sK3 ),
    inference(definition_unfolding,[],[f82,f83,f60,f86,f86])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f83])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f74,f86])).

fof(f81,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1276,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_10234,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1276,c_0])).

cnf(c_23,plain,
    ( r2_hidden(X0,X1)
    | k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1065,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) = k3_enumset1(X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1062,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2899,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0))))) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_1065,c_1062])).

cnf(c_29,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))))) != sK3 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_88142,plain,
    ( k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != sK3 ),
    inference(superposition,[status(thm)],[c_2899,c_29])).

cnf(c_88575,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) != sK3 ),
    inference(superposition,[status(thm)],[c_10234,c_88142])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1402,plain,
    ( ~ r1_tarski(X0,sK3)
    | k5_xboole_0(X0,k5_xboole_0(sK3,k3_xboole_0(sK3,X0))) = sK3 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1828,plain,
    ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),sK3)
    | k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(X0,X0,X0,X0,X0)))) = sK3 ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_1831,plain,
    ( ~ r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)
    | k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = sK3 ),
    inference(instantiation,[status(thm)],[c_1828])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1167,plain,
    ( ~ r2_hidden(sK2,sK3)
    | r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_30,negated_conjecture,
    ( r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_88575,c_1831,c_1167,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 19:41:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 35.81/4.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.81/4.99  
% 35.81/4.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.81/4.99  
% 35.81/4.99  ------  iProver source info
% 35.81/4.99  
% 35.81/4.99  git: date: 2020-06-30 10:37:57 +0100
% 35.81/4.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.81/4.99  git: non_committed_changes: false
% 35.81/4.99  git: last_make_outside_of_git: false
% 35.81/4.99  
% 35.81/4.99  ------ 
% 35.81/4.99  ------ Parsing...
% 35.81/4.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.81/4.99  
% 35.81/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 35.81/4.99  
% 35.81/4.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.81/4.99  
% 35.81/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.81/4.99  ------ Proving...
% 35.81/4.99  ------ Problem Properties 
% 35.81/4.99  
% 35.81/4.99  
% 35.81/4.99  clauses                                 30
% 35.81/4.99  conjectures                             2
% 35.81/4.99  EPR                                     4
% 35.81/4.99  Horn                                    23
% 35.81/4.99  unary                                   12
% 35.81/4.99  binary                                  11
% 35.81/4.99  lits                                    56
% 35.81/4.99  lits eq                                 17
% 35.81/4.99  fd_pure                                 0
% 35.81/4.99  fd_pseudo                               0
% 35.81/4.99  fd_cond                                 0
% 35.81/4.99  fd_pseudo_cond                          5
% 35.81/4.99  AC symbols                              0
% 35.81/4.99  
% 35.81/4.99  ------ Input Options Time Limit: Unbounded
% 35.81/4.99  
% 35.81/4.99  
% 35.81/4.99  ------ 
% 35.81/4.99  Current options:
% 35.81/4.99  ------ 
% 35.81/4.99  
% 35.81/4.99  
% 35.81/4.99  
% 35.81/4.99  
% 35.81/4.99  ------ Proving...
% 35.81/4.99  
% 35.81/4.99  
% 35.81/4.99  % SZS status Theorem for theBenchmark.p
% 35.81/4.99  
% 35.81/4.99  % SZS output start CNFRefutation for theBenchmark.p
% 35.81/4.99  
% 35.81/4.99  fof(f1,axiom,(
% 35.81/4.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 35.81/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.81/4.99  
% 35.81/4.99  fof(f46,plain,(
% 35.81/4.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 35.81/4.99    inference(cnf_transformation,[],[f1])).
% 35.81/4.99  
% 35.81/4.99  fof(f13,axiom,(
% 35.81/4.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 35.81/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.81/4.99  
% 35.81/4.99  fof(f67,plain,(
% 35.81/4.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 35.81/4.99    inference(cnf_transformation,[],[f13])).
% 35.81/4.99  
% 35.81/4.99  fof(f6,axiom,(
% 35.81/4.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 35.81/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.81/4.99  
% 35.81/4.99  fof(f60,plain,(
% 35.81/4.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 35.81/4.99    inference(cnf_transformation,[],[f6])).
% 35.81/4.99  
% 35.81/4.99  fof(f83,plain,(
% 35.81/4.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 35.81/4.99    inference(definition_unfolding,[],[f67,f60])).
% 35.81/4.99  
% 35.81/4.99  fof(f88,plain,(
% 35.81/4.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 35.81/4.99    inference(definition_unfolding,[],[f46,f83,f83])).
% 35.81/4.99  
% 35.81/4.99  fof(f4,axiom,(
% 35.81/4.99    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 35.81/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.81/4.99  
% 35.81/4.99  fof(f56,plain,(
% 35.81/4.99    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 35.81/4.99    inference(cnf_transformation,[],[f4])).
% 35.81/4.99  
% 35.81/4.99  fof(f87,plain,(
% 35.81/4.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k5_xboole_0(X0,k3_xboole_0(X0,X1)))))) )),
% 35.81/4.99    inference(definition_unfolding,[],[f56,f83,f60,f60])).
% 35.81/4.99  
% 35.81/4.99  fof(f20,axiom,(
% 35.81/4.99    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <=> ~r2_hidden(X0,X1))),
% 35.81/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.81/4.99  
% 35.81/4.99  fof(f41,plain,(
% 35.81/4.99    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)))),
% 35.81/4.99    inference(nnf_transformation,[],[f20])).
% 35.81/4.99  
% 35.81/4.99  fof(f76,plain,(
% 35.81/4.99    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) )),
% 35.81/4.99    inference(cnf_transformation,[],[f41])).
% 35.81/4.99  
% 35.81/4.99  fof(f15,axiom,(
% 35.81/4.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 35.81/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.81/4.99  
% 35.81/4.99  fof(f69,plain,(
% 35.81/4.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 35.81/4.99    inference(cnf_transformation,[],[f15])).
% 35.81/4.99  
% 35.81/4.99  fof(f16,axiom,(
% 35.81/4.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 35.81/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.81/4.99  
% 35.81/4.99  fof(f70,plain,(
% 35.81/4.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 35.81/4.99    inference(cnf_transformation,[],[f16])).
% 35.81/4.99  
% 35.81/4.99  fof(f17,axiom,(
% 35.81/4.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 35.81/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.81/4.99  
% 35.81/4.99  fof(f71,plain,(
% 35.81/4.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 35.81/4.99    inference(cnf_transformation,[],[f17])).
% 35.81/4.99  
% 35.81/4.99  fof(f18,axiom,(
% 35.81/4.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 35.81/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.81/4.99  
% 35.81/4.99  fof(f72,plain,(
% 35.81/4.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 35.81/4.99    inference(cnf_transformation,[],[f18])).
% 35.81/4.99  
% 35.81/4.99  fof(f84,plain,(
% 35.81/4.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 35.81/4.99    inference(definition_unfolding,[],[f71,f72])).
% 35.81/4.99  
% 35.81/4.99  fof(f85,plain,(
% 35.81/4.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 35.81/4.99    inference(definition_unfolding,[],[f70,f84])).
% 35.81/4.99  
% 35.81/4.99  fof(f86,plain,(
% 35.81/4.99    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 35.81/4.99    inference(definition_unfolding,[],[f69,f85])).
% 35.81/4.99  
% 35.81/4.99  fof(f103,plain,(
% 35.81/4.99    ( ! [X0,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) = k3_enumset1(X0,X0,X0,X0,X0) | r2_hidden(X0,X1)) )),
% 35.81/4.99    inference(definition_unfolding,[],[f76,f60,f86,f86])).
% 35.81/4.99  
% 35.81/4.99  fof(f22,axiom,(
% 35.81/4.99    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 35.81/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.81/4.99  
% 35.81/4.99  fof(f42,plain,(
% 35.81/4.99    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 35.81/4.99    inference(nnf_transformation,[],[f22])).
% 35.81/4.99  
% 35.81/4.99  fof(f43,plain,(
% 35.81/4.99    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 35.81/4.99    inference(flattening,[],[f42])).
% 35.81/4.99  
% 35.81/4.99  fof(f79,plain,(
% 35.81/4.99    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 35.81/4.99    inference(cnf_transformation,[],[f43])).
% 35.81/4.99  
% 35.81/4.99  fof(f107,plain,(
% 35.81/4.99    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))))) )),
% 35.81/4.99    inference(definition_unfolding,[],[f79,f60,f86])).
% 35.81/4.99  
% 35.81/4.99  fof(f115,plain,(
% 35.81/4.99    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))))) )),
% 35.81/4.99    inference(equality_resolution,[],[f107])).
% 35.81/4.99  
% 35.81/4.99  fof(f23,conjecture,(
% 35.81/4.99    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 35.81/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.81/4.99  
% 35.81/4.99  fof(f24,negated_conjecture,(
% 35.81/4.99    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 35.81/4.99    inference(negated_conjecture,[],[f23])).
% 35.81/4.99  
% 35.81/4.99  fof(f28,plain,(
% 35.81/4.99    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 35.81/4.99    inference(ennf_transformation,[],[f24])).
% 35.81/4.99  
% 35.81/4.99  fof(f44,plain,(
% 35.81/4.99    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK2)) != sK3 & r2_hidden(sK2,sK3))),
% 35.81/4.99    introduced(choice_axiom,[])).
% 35.81/4.99  
% 35.81/4.99  fof(f45,plain,(
% 35.81/4.99    k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK2)) != sK3 & r2_hidden(sK2,sK3)),
% 35.81/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f44])).
% 35.81/4.99  
% 35.81/4.99  fof(f82,plain,(
% 35.81/4.99    k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK2)) != sK3),
% 35.81/4.99    inference(cnf_transformation,[],[f45])).
% 35.81/4.99  
% 35.81/4.99  fof(f109,plain,(
% 35.81/4.99    k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))))) != sK3),
% 35.81/4.99    inference(definition_unfolding,[],[f82,f83,f60,f86,f86])).
% 35.81/4.99  
% 35.81/4.99  fof(f7,axiom,(
% 35.81/4.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 35.81/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.81/4.99  
% 35.81/4.99  fof(f26,plain,(
% 35.81/4.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 35.81/4.99    inference(ennf_transformation,[],[f7])).
% 35.81/4.99  
% 35.81/4.99  fof(f61,plain,(
% 35.81/4.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 35.81/4.99    inference(cnf_transformation,[],[f26])).
% 35.81/4.99  
% 35.81/4.99  fof(f95,plain,(
% 35.81/4.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 | ~r1_tarski(X0,X1)) )),
% 35.81/4.99    inference(definition_unfolding,[],[f61,f83])).
% 35.81/4.99  
% 35.81/4.99  fof(f19,axiom,(
% 35.81/4.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 35.81/4.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.81/4.99  
% 35.81/4.99  fof(f40,plain,(
% 35.81/4.99    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 35.81/4.99    inference(nnf_transformation,[],[f19])).
% 35.81/4.99  
% 35.81/4.99  fof(f74,plain,(
% 35.81/4.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 35.81/4.99    inference(cnf_transformation,[],[f40])).
% 35.81/4.99  
% 35.81/4.99  fof(f101,plain,(
% 35.81/4.99    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 35.81/4.99    inference(definition_unfolding,[],[f74,f86])).
% 35.81/4.99  
% 35.81/4.99  fof(f81,plain,(
% 35.81/4.99    r2_hidden(sK2,sK3)),
% 35.81/4.99    inference(cnf_transformation,[],[f45])).
% 35.81/4.99  
% 35.81/4.99  cnf(c_1,plain,
% 35.81/4.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 35.81/4.99      inference(cnf_transformation,[],[f88]) ).
% 35.81/4.99  
% 35.81/4.99  cnf(c_0,plain,
% 35.81/4.99      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k5_xboole_0(X0,X1) ),
% 35.81/4.99      inference(cnf_transformation,[],[f87]) ).
% 35.81/4.99  
% 35.81/4.99  cnf(c_1276,plain,
% 35.81/4.99      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k5_xboole_0(X1,X0) ),
% 35.81/4.99      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 35.81/4.99  
% 35.81/4.99  cnf(c_10234,plain,
% 35.81/4.99      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 35.81/4.99      inference(superposition,[status(thm)],[c_1276,c_0]) ).
% 35.81/4.99  
% 35.81/4.99  cnf(c_23,plain,
% 35.81/4.99      ( r2_hidden(X0,X1)
% 35.81/4.99      | k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) = k3_enumset1(X0,X0,X0,X0,X0) ),
% 35.81/4.99      inference(cnf_transformation,[],[f103]) ).
% 35.81/4.99  
% 35.81/4.99  cnf(c_1065,plain,
% 35.81/4.99      ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) = k3_enumset1(X0,X0,X0,X0,X0)
% 35.81/4.99      | r2_hidden(X0,X1) = iProver_top ),
% 35.81/4.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 35.81/4.99  
% 35.81/4.99  cnf(c_27,plain,
% 35.81/4.99      ( ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)))) ),
% 35.81/4.99      inference(cnf_transformation,[],[f115]) ).
% 35.81/4.99  
% 35.81/4.99  cnf(c_1062,plain,
% 35.81/4.99      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)))) != iProver_top ),
% 35.81/4.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 35.81/4.99  
% 35.81/4.99  cnf(c_2899,plain,
% 35.81/4.99      ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0))))) = k3_enumset1(X0,X0,X0,X0,X0) ),
% 35.81/4.99      inference(superposition,[status(thm)],[c_1065,c_1062]) ).
% 35.81/4.99  
% 35.81/4.99  cnf(c_29,negated_conjecture,
% 35.81/4.99      ( k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))))) != sK3 ),
% 35.81/4.99      inference(cnf_transformation,[],[f109]) ).
% 35.81/4.99  
% 35.81/4.99  cnf(c_88142,plain,
% 35.81/4.99      ( k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) != sK3 ),
% 35.81/4.99      inference(superposition,[status(thm)],[c_2899,c_29]) ).
% 35.81/4.99  
% 35.81/4.99  cnf(c_88575,plain,
% 35.81/4.99      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) != sK3 ),
% 35.81/4.99      inference(superposition,[status(thm)],[c_10234,c_88142]) ).
% 35.81/4.99  
% 35.81/4.99  cnf(c_14,plain,
% 35.81/4.99      ( ~ r1_tarski(X0,X1)
% 35.81/4.99      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ),
% 35.81/4.99      inference(cnf_transformation,[],[f95]) ).
% 35.81/4.99  
% 35.81/4.99  cnf(c_1402,plain,
% 35.81/4.99      ( ~ r1_tarski(X0,sK3)
% 35.81/4.99      | k5_xboole_0(X0,k5_xboole_0(sK3,k3_xboole_0(sK3,X0))) = sK3 ),
% 35.81/4.99      inference(instantiation,[status(thm)],[c_14]) ).
% 35.81/4.99  
% 35.81/4.99  cnf(c_1828,plain,
% 35.81/4.99      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),sK3)
% 35.81/4.99      | k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(X0,X0,X0,X0,X0)))) = sK3 ),
% 35.81/4.99      inference(instantiation,[status(thm)],[c_1402]) ).
% 35.81/4.99  
% 35.81/4.99  cnf(c_1831,plain,
% 35.81/4.99      ( ~ r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)
% 35.81/4.99      | k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = sK3 ),
% 35.81/4.99      inference(instantiation,[status(thm)],[c_1828]) ).
% 35.81/4.99  
% 35.81/4.99  cnf(c_21,plain,
% 35.81/4.99      ( ~ r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 35.81/4.99      inference(cnf_transformation,[],[f101]) ).
% 35.81/4.99  
% 35.81/4.99  cnf(c_1167,plain,
% 35.81/4.99      ( ~ r2_hidden(sK2,sK3)
% 35.81/4.99      | r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3) ),
% 35.81/4.99      inference(instantiation,[status(thm)],[c_21]) ).
% 35.81/4.99  
% 35.81/4.99  cnf(c_30,negated_conjecture,
% 35.81/4.99      ( r2_hidden(sK2,sK3) ),
% 35.81/4.99      inference(cnf_transformation,[],[f81]) ).
% 35.81/4.99  
% 35.81/4.99  cnf(contradiction,plain,
% 35.81/4.99      ( $false ),
% 35.81/4.99      inference(minisat,[status(thm)],[c_88575,c_1831,c_1167,c_30]) ).
% 35.81/4.99  
% 35.81/4.99  
% 35.81/4.99  % SZS output end CNFRefutation for theBenchmark.p
% 35.81/4.99  
% 35.81/4.99  ------                               Statistics
% 35.81/4.99  
% 35.81/4.99  ------ Selected
% 35.81/4.99  
% 35.81/4.99  total_time:                             4.27
% 35.81/4.99  
%------------------------------------------------------------------------------
