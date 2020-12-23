%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:14 EST 2020

% Result     : Theorem 6.55s
% Output     : CNFRefutation 6.55s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 406 expanded)
%              Number of clauses        :   32 (  53 expanded)
%              Number of leaves         :   16 ( 125 expanded)
%              Depth                    :   14
%              Number of atoms          :  117 ( 475 expanded)
%              Number of equality atoms :   75 ( 402 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f29,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f42,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK3),sK4) != sK4
      & r2_hidden(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( k2_xboole_0(k1_tarski(sK3),sK4) != sK4
    & r2_hidden(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f42])).

fof(f74,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f76])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f67,f77])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f72,f79])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f73,f77])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f82,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f63,f78,f78,f60])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f81,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f61,f78])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f80,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f44,f78,f78])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f83,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f64,f60,f60,f78])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f66,f78])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f75,plain,(
    k2_xboole_0(k1_tarski(sK3),sK4) != sK4 ),
    inference(cnf_transformation,[],[f43])).

fof(f88,plain,(
    k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) != sK4 ),
    inference(definition_unfolding,[],[f75,f78,f79])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1045,plain,
    ( r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1047,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1049,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2230,plain,
    ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k3_enumset1(X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1047,c_1049])).

cnf(c_27160,plain,
    ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_1045,c_2230])).

cnf(c_18,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_28624,plain,
    ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(superposition,[status(thm)],[c_27160,c_18])).

cnf(c_16,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_0,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1464,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_16])).

cnf(c_19,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1973,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_1464,c_19])).

cnf(c_21,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1048,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1286,plain,
    ( k3_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_1048,c_1049])).

cnf(c_1976,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1464,c_1286])).

cnf(c_1987,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1973,c_1976])).

cnf(c_15,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1050,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1285,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1050,c_1049])).

cnf(c_1989,plain,
    ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1987,c_1285])).

cnf(c_1979,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1464,c_18])).

cnf(c_1980,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1979,c_1464])).

cnf(c_2092,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1285,c_1980])).

cnf(c_2224,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1989,c_2092])).

cnf(c_28626,plain,
    ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = sK4 ),
    inference(demodulation,[status(thm)],[c_28624,c_16,c_2224])).

cnf(c_24,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) != sK4 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1456,plain,
    ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) != sK4 ),
    inference(demodulation,[status(thm)],[c_0,c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28626,c_1456])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 6.55/1.54  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.55/1.54  
% 6.55/1.54  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.55/1.54  
% 6.55/1.54  ------  iProver source info
% 6.55/1.54  
% 6.55/1.54  git: date: 2020-06-30 10:37:57 +0100
% 6.55/1.54  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.55/1.54  git: non_committed_changes: false
% 6.55/1.54  git: last_make_outside_of_git: false
% 6.55/1.54  
% 6.55/1.54  ------ 
% 6.55/1.54  
% 6.55/1.54  ------ Input Options
% 6.55/1.54  
% 6.55/1.54  --out_options                           all
% 6.55/1.54  --tptp_safe_out                         true
% 6.55/1.54  --problem_path                          ""
% 6.55/1.54  --include_path                          ""
% 6.55/1.54  --clausifier                            res/vclausify_rel
% 6.55/1.54  --clausifier_options                    --mode clausify
% 6.55/1.54  --stdin                                 false
% 6.55/1.54  --stats_out                             all
% 6.55/1.54  
% 6.55/1.54  ------ General Options
% 6.55/1.54  
% 6.55/1.54  --fof                                   false
% 6.55/1.54  --time_out_real                         305.
% 6.55/1.54  --time_out_virtual                      -1.
% 6.55/1.54  --symbol_type_check                     false
% 6.55/1.54  --clausify_out                          false
% 6.55/1.54  --sig_cnt_out                           false
% 6.55/1.54  --trig_cnt_out                          false
% 6.55/1.54  --trig_cnt_out_tolerance                1.
% 6.55/1.54  --trig_cnt_out_sk_spl                   false
% 6.55/1.54  --abstr_cl_out                          false
% 6.55/1.54  
% 6.55/1.54  ------ Global Options
% 6.55/1.54  
% 6.55/1.54  --schedule                              default
% 6.55/1.54  --add_important_lit                     false
% 6.55/1.54  --prop_solver_per_cl                    1000
% 6.55/1.54  --min_unsat_core                        false
% 6.55/1.54  --soft_assumptions                      false
% 6.55/1.54  --soft_lemma_size                       3
% 6.55/1.54  --prop_impl_unit_size                   0
% 6.55/1.54  --prop_impl_unit                        []
% 6.55/1.54  --share_sel_clauses                     true
% 6.55/1.54  --reset_solvers                         false
% 6.55/1.54  --bc_imp_inh                            [conj_cone]
% 6.55/1.54  --conj_cone_tolerance                   3.
% 6.55/1.54  --extra_neg_conj                        none
% 6.55/1.54  --large_theory_mode                     true
% 6.55/1.54  --prolific_symb_bound                   200
% 6.55/1.54  --lt_threshold                          2000
% 6.55/1.54  --clause_weak_htbl                      true
% 6.55/1.54  --gc_record_bc_elim                     false
% 6.55/1.54  
% 6.55/1.54  ------ Preprocessing Options
% 6.55/1.54  
% 6.55/1.54  --preprocessing_flag                    true
% 6.55/1.54  --time_out_prep_mult                    0.1
% 6.55/1.54  --splitting_mode                        input
% 6.55/1.54  --splitting_grd                         true
% 6.55/1.54  --splitting_cvd                         false
% 6.55/1.54  --splitting_cvd_svl                     false
% 6.55/1.54  --splitting_nvd                         32
% 6.55/1.54  --sub_typing                            true
% 6.55/1.54  --prep_gs_sim                           true
% 6.55/1.54  --prep_unflatten                        true
% 6.55/1.54  --prep_res_sim                          true
% 6.55/1.54  --prep_upred                            true
% 6.55/1.54  --prep_sem_filter                       exhaustive
% 6.55/1.54  --prep_sem_filter_out                   false
% 6.55/1.54  --pred_elim                             true
% 6.55/1.54  --res_sim_input                         true
% 6.55/1.54  --eq_ax_congr_red                       true
% 6.55/1.54  --pure_diseq_elim                       true
% 6.55/1.54  --brand_transform                       false
% 6.55/1.54  --non_eq_to_eq                          false
% 6.55/1.54  --prep_def_merge                        true
% 6.55/1.54  --prep_def_merge_prop_impl              false
% 6.55/1.54  --prep_def_merge_mbd                    true
% 6.55/1.54  --prep_def_merge_tr_red                 false
% 6.55/1.54  --prep_def_merge_tr_cl                  false
% 6.55/1.54  --smt_preprocessing                     true
% 6.55/1.54  --smt_ac_axioms                         fast
% 6.55/1.54  --preprocessed_out                      false
% 6.55/1.54  --preprocessed_stats                    false
% 6.55/1.54  
% 6.55/1.54  ------ Abstraction refinement Options
% 6.55/1.54  
% 6.55/1.54  --abstr_ref                             []
% 6.55/1.54  --abstr_ref_prep                        false
% 6.55/1.54  --abstr_ref_until_sat                   false
% 6.55/1.54  --abstr_ref_sig_restrict                funpre
% 6.55/1.54  --abstr_ref_af_restrict_to_split_sk     false
% 6.55/1.54  --abstr_ref_under                       []
% 6.55/1.54  
% 6.55/1.54  ------ SAT Options
% 6.55/1.54  
% 6.55/1.54  --sat_mode                              false
% 6.55/1.54  --sat_fm_restart_options                ""
% 6.55/1.54  --sat_gr_def                            false
% 6.55/1.54  --sat_epr_types                         true
% 6.55/1.54  --sat_non_cyclic_types                  false
% 6.55/1.54  --sat_finite_models                     false
% 6.55/1.54  --sat_fm_lemmas                         false
% 6.55/1.54  --sat_fm_prep                           false
% 6.55/1.54  --sat_fm_uc_incr                        true
% 6.55/1.54  --sat_out_model                         small
% 6.55/1.54  --sat_out_clauses                       false
% 6.55/1.54  
% 6.55/1.54  ------ QBF Options
% 6.55/1.54  
% 6.55/1.54  --qbf_mode                              false
% 6.55/1.54  --qbf_elim_univ                         false
% 6.55/1.54  --qbf_dom_inst                          none
% 6.55/1.54  --qbf_dom_pre_inst                      false
% 6.55/1.54  --qbf_sk_in                             false
% 6.55/1.54  --qbf_pred_elim                         true
% 6.55/1.54  --qbf_split                             512
% 6.55/1.54  
% 6.55/1.54  ------ BMC1 Options
% 6.55/1.54  
% 6.55/1.54  --bmc1_incremental                      false
% 6.55/1.54  --bmc1_axioms                           reachable_all
% 6.55/1.54  --bmc1_min_bound                        0
% 6.55/1.54  --bmc1_max_bound                        -1
% 6.55/1.54  --bmc1_max_bound_default                -1
% 6.55/1.54  --bmc1_symbol_reachability              true
% 6.55/1.54  --bmc1_property_lemmas                  false
% 6.55/1.54  --bmc1_k_induction                      false
% 6.55/1.54  --bmc1_non_equiv_states                 false
% 6.55/1.54  --bmc1_deadlock                         false
% 6.55/1.54  --bmc1_ucm                              false
% 6.55/1.54  --bmc1_add_unsat_core                   none
% 6.55/1.54  --bmc1_unsat_core_children              false
% 6.55/1.54  --bmc1_unsat_core_extrapolate_axioms    false
% 6.55/1.54  --bmc1_out_stat                         full
% 6.55/1.54  --bmc1_ground_init                      false
% 6.55/1.54  --bmc1_pre_inst_next_state              false
% 6.55/1.54  --bmc1_pre_inst_state                   false
% 6.55/1.54  --bmc1_pre_inst_reach_state             false
% 6.55/1.54  --bmc1_out_unsat_core                   false
% 6.55/1.54  --bmc1_aig_witness_out                  false
% 6.55/1.54  --bmc1_verbose                          false
% 6.55/1.54  --bmc1_dump_clauses_tptp                false
% 6.55/1.54  --bmc1_dump_unsat_core_tptp             false
% 6.55/1.54  --bmc1_dump_file                        -
% 6.55/1.54  --bmc1_ucm_expand_uc_limit              128
% 6.55/1.54  --bmc1_ucm_n_expand_iterations          6
% 6.55/1.54  --bmc1_ucm_extend_mode                  1
% 6.55/1.54  --bmc1_ucm_init_mode                    2
% 6.55/1.54  --bmc1_ucm_cone_mode                    none
% 6.55/1.54  --bmc1_ucm_reduced_relation_type        0
% 6.55/1.54  --bmc1_ucm_relax_model                  4
% 6.55/1.54  --bmc1_ucm_full_tr_after_sat            true
% 6.55/1.54  --bmc1_ucm_expand_neg_assumptions       false
% 6.55/1.54  --bmc1_ucm_layered_model                none
% 6.55/1.54  --bmc1_ucm_max_lemma_size               10
% 6.55/1.54  
% 6.55/1.54  ------ AIG Options
% 6.55/1.54  
% 6.55/1.54  --aig_mode                              false
% 6.55/1.54  
% 6.55/1.54  ------ Instantiation Options
% 6.55/1.54  
% 6.55/1.54  --instantiation_flag                    true
% 6.55/1.54  --inst_sos_flag                         false
% 6.55/1.54  --inst_sos_phase                        true
% 6.55/1.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.55/1.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.55/1.54  --inst_lit_sel_side                     num_symb
% 6.55/1.54  --inst_solver_per_active                1400
% 6.55/1.54  --inst_solver_calls_frac                1.
% 6.55/1.54  --inst_passive_queue_type               priority_queues
% 6.55/1.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.55/1.54  --inst_passive_queues_freq              [25;2]
% 6.55/1.54  --inst_dismatching                      true
% 6.55/1.54  --inst_eager_unprocessed_to_passive     true
% 6.55/1.54  --inst_prop_sim_given                   true
% 6.55/1.54  --inst_prop_sim_new                     false
% 6.55/1.54  --inst_subs_new                         false
% 6.55/1.54  --inst_eq_res_simp                      false
% 6.55/1.54  --inst_subs_given                       false
% 6.55/1.54  --inst_orphan_elimination               true
% 6.55/1.54  --inst_learning_loop_flag               true
% 6.55/1.54  --inst_learning_start                   3000
% 6.55/1.54  --inst_learning_factor                  2
% 6.55/1.54  --inst_start_prop_sim_after_learn       3
% 6.55/1.54  --inst_sel_renew                        solver
% 6.55/1.54  --inst_lit_activity_flag                true
% 6.55/1.54  --inst_restr_to_given                   false
% 6.55/1.54  --inst_activity_threshold               500
% 6.55/1.54  --inst_out_proof                        true
% 6.55/1.54  
% 6.55/1.54  ------ Resolution Options
% 6.55/1.54  
% 6.55/1.54  --resolution_flag                       true
% 6.55/1.54  --res_lit_sel                           adaptive
% 6.55/1.54  --res_lit_sel_side                      none
% 6.55/1.54  --res_ordering                          kbo
% 6.55/1.54  --res_to_prop_solver                    active
% 6.55/1.54  --res_prop_simpl_new                    false
% 6.55/1.54  --res_prop_simpl_given                  true
% 6.55/1.54  --res_passive_queue_type                priority_queues
% 6.55/1.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.55/1.54  --res_passive_queues_freq               [15;5]
% 6.55/1.54  --res_forward_subs                      full
% 6.55/1.54  --res_backward_subs                     full
% 6.55/1.54  --res_forward_subs_resolution           true
% 6.55/1.54  --res_backward_subs_resolution          true
% 6.55/1.54  --res_orphan_elimination                true
% 6.55/1.54  --res_time_limit                        2.
% 6.55/1.54  --res_out_proof                         true
% 6.55/1.54  
% 6.55/1.54  ------ Superposition Options
% 6.55/1.54  
% 6.55/1.54  --superposition_flag                    true
% 6.55/1.54  --sup_passive_queue_type                priority_queues
% 6.55/1.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.55/1.54  --sup_passive_queues_freq               [8;1;4]
% 6.55/1.54  --demod_completeness_check              fast
% 6.55/1.54  --demod_use_ground                      true
% 6.55/1.54  --sup_to_prop_solver                    passive
% 6.55/1.54  --sup_prop_simpl_new                    true
% 6.55/1.54  --sup_prop_simpl_given                  true
% 6.55/1.54  --sup_fun_splitting                     false
% 6.55/1.54  --sup_smt_interval                      50000
% 6.55/1.54  
% 6.55/1.54  ------ Superposition Simplification Setup
% 6.55/1.54  
% 6.55/1.54  --sup_indices_passive                   []
% 6.55/1.54  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.55/1.54  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.55/1.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.55/1.54  --sup_full_triv                         [TrivRules;PropSubs]
% 6.55/1.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.55/1.54  --sup_full_bw                           [BwDemod]
% 6.55/1.54  --sup_immed_triv                        [TrivRules]
% 6.55/1.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.55/1.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.55/1.54  --sup_immed_bw_main                     []
% 6.55/1.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.55/1.54  --sup_input_triv                        [Unflattening;TrivRules]
% 6.55/1.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.55/1.54  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.55/1.54  
% 6.55/1.54  ------ Combination Options
% 6.55/1.54  
% 6.55/1.54  --comb_res_mult                         3
% 6.55/1.54  --comb_sup_mult                         2
% 6.55/1.54  --comb_inst_mult                        10
% 6.55/1.54  
% 6.55/1.54  ------ Debug Options
% 6.55/1.54  
% 6.55/1.54  --dbg_backtrace                         false
% 6.55/1.54  --dbg_dump_prop_clauses                 false
% 6.55/1.54  --dbg_dump_prop_clauses_file            -
% 6.55/1.54  --dbg_out_stat                          false
% 6.55/1.54  ------ Parsing...
% 6.55/1.54  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.55/1.54  
% 6.55/1.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.55/1.54  
% 6.55/1.54  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.55/1.54  
% 6.55/1.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.55/1.54  ------ Proving...
% 6.55/1.54  ------ Problem Properties 
% 6.55/1.54  
% 6.55/1.54  
% 6.55/1.54  clauses                                 25
% 6.55/1.54  conjectures                             2
% 6.55/1.54  EPR                                     5
% 6.55/1.54  Horn                                    18
% 6.55/1.54  unary                                   9
% 6.55/1.54  binary                                  9
% 6.55/1.54  lits                                    48
% 6.55/1.54  lits eq                                 8
% 6.55/1.54  fd_pure                                 0
% 6.55/1.54  fd_pseudo                               0
% 6.55/1.54  fd_cond                                 0
% 6.55/1.54  fd_pseudo_cond                          1
% 6.55/1.54  AC symbols                              0
% 6.55/1.54  
% 6.55/1.54  ------ Schedule dynamic 5 is on 
% 6.55/1.54  
% 6.55/1.54  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.55/1.54  
% 6.55/1.54  
% 6.55/1.54  ------ 
% 6.55/1.54  Current options:
% 6.55/1.54  ------ 
% 6.55/1.54  
% 6.55/1.54  ------ Input Options
% 6.55/1.54  
% 6.55/1.54  --out_options                           all
% 6.55/1.54  --tptp_safe_out                         true
% 6.55/1.54  --problem_path                          ""
% 6.55/1.54  --include_path                          ""
% 6.55/1.54  --clausifier                            res/vclausify_rel
% 6.55/1.54  --clausifier_options                    --mode clausify
% 6.55/1.54  --stdin                                 false
% 6.55/1.54  --stats_out                             all
% 6.55/1.54  
% 6.55/1.54  ------ General Options
% 6.55/1.54  
% 6.55/1.54  --fof                                   false
% 6.55/1.54  --time_out_real                         305.
% 6.55/1.54  --time_out_virtual                      -1.
% 6.55/1.54  --symbol_type_check                     false
% 6.55/1.54  --clausify_out                          false
% 6.55/1.54  --sig_cnt_out                           false
% 6.55/1.54  --trig_cnt_out                          false
% 6.55/1.54  --trig_cnt_out_tolerance                1.
% 6.55/1.54  --trig_cnt_out_sk_spl                   false
% 6.55/1.54  --abstr_cl_out                          false
% 6.55/1.54  
% 6.55/1.54  ------ Global Options
% 6.55/1.54  
% 6.55/1.54  --schedule                              default
% 6.55/1.54  --add_important_lit                     false
% 6.55/1.54  --prop_solver_per_cl                    1000
% 6.55/1.54  --min_unsat_core                        false
% 6.55/1.54  --soft_assumptions                      false
% 6.55/1.54  --soft_lemma_size                       3
% 6.55/1.54  --prop_impl_unit_size                   0
% 6.55/1.54  --prop_impl_unit                        []
% 6.55/1.54  --share_sel_clauses                     true
% 6.55/1.54  --reset_solvers                         false
% 6.55/1.54  --bc_imp_inh                            [conj_cone]
% 6.55/1.54  --conj_cone_tolerance                   3.
% 6.55/1.54  --extra_neg_conj                        none
% 6.55/1.54  --large_theory_mode                     true
% 6.55/1.54  --prolific_symb_bound                   200
% 6.55/1.54  --lt_threshold                          2000
% 6.55/1.54  --clause_weak_htbl                      true
% 6.55/1.54  --gc_record_bc_elim                     false
% 6.55/1.54  
% 6.55/1.54  ------ Preprocessing Options
% 6.55/1.54  
% 6.55/1.54  --preprocessing_flag                    true
% 6.55/1.54  --time_out_prep_mult                    0.1
% 6.55/1.54  --splitting_mode                        input
% 6.55/1.54  --splitting_grd                         true
% 6.55/1.54  --splitting_cvd                         false
% 6.55/1.54  --splitting_cvd_svl                     false
% 6.55/1.54  --splitting_nvd                         32
% 6.55/1.54  --sub_typing                            true
% 6.55/1.54  --prep_gs_sim                           true
% 6.55/1.54  --prep_unflatten                        true
% 6.55/1.54  --prep_res_sim                          true
% 6.55/1.54  --prep_upred                            true
% 6.55/1.54  --prep_sem_filter                       exhaustive
% 6.55/1.54  --prep_sem_filter_out                   false
% 6.55/1.54  --pred_elim                             true
% 6.55/1.54  --res_sim_input                         true
% 6.55/1.54  --eq_ax_congr_red                       true
% 6.55/1.54  --pure_diseq_elim                       true
% 6.55/1.54  --brand_transform                       false
% 6.55/1.54  --non_eq_to_eq                          false
% 6.55/1.54  --prep_def_merge                        true
% 6.55/1.54  --prep_def_merge_prop_impl              false
% 6.55/1.54  --prep_def_merge_mbd                    true
% 6.55/1.54  --prep_def_merge_tr_red                 false
% 6.55/1.54  --prep_def_merge_tr_cl                  false
% 6.55/1.54  --smt_preprocessing                     true
% 6.55/1.54  --smt_ac_axioms                         fast
% 6.55/1.54  --preprocessed_out                      false
% 6.55/1.54  --preprocessed_stats                    false
% 6.55/1.54  
% 6.55/1.54  ------ Abstraction refinement Options
% 6.55/1.54  
% 6.55/1.54  --abstr_ref                             []
% 6.55/1.54  --abstr_ref_prep                        false
% 6.55/1.54  --abstr_ref_until_sat                   false
% 6.55/1.54  --abstr_ref_sig_restrict                funpre
% 6.55/1.54  --abstr_ref_af_restrict_to_split_sk     false
% 6.55/1.54  --abstr_ref_under                       []
% 6.55/1.54  
% 6.55/1.54  ------ SAT Options
% 6.55/1.54  
% 6.55/1.54  --sat_mode                              false
% 6.55/1.54  --sat_fm_restart_options                ""
% 6.55/1.54  --sat_gr_def                            false
% 6.55/1.54  --sat_epr_types                         true
% 6.55/1.54  --sat_non_cyclic_types                  false
% 6.55/1.54  --sat_finite_models                     false
% 6.55/1.54  --sat_fm_lemmas                         false
% 6.55/1.54  --sat_fm_prep                           false
% 6.55/1.54  --sat_fm_uc_incr                        true
% 6.55/1.54  --sat_out_model                         small
% 6.55/1.54  --sat_out_clauses                       false
% 6.55/1.54  
% 6.55/1.54  ------ QBF Options
% 6.55/1.54  
% 6.55/1.54  --qbf_mode                              false
% 6.55/1.54  --qbf_elim_univ                         false
% 6.55/1.54  --qbf_dom_inst                          none
% 6.55/1.54  --qbf_dom_pre_inst                      false
% 6.55/1.54  --qbf_sk_in                             false
% 6.55/1.54  --qbf_pred_elim                         true
% 6.55/1.54  --qbf_split                             512
% 6.55/1.54  
% 6.55/1.54  ------ BMC1 Options
% 6.55/1.54  
% 6.55/1.54  --bmc1_incremental                      false
% 6.55/1.54  --bmc1_axioms                           reachable_all
% 6.55/1.54  --bmc1_min_bound                        0
% 6.55/1.54  --bmc1_max_bound                        -1
% 6.55/1.54  --bmc1_max_bound_default                -1
% 6.55/1.54  --bmc1_symbol_reachability              true
% 6.55/1.54  --bmc1_property_lemmas                  false
% 6.55/1.54  --bmc1_k_induction                      false
% 6.55/1.54  --bmc1_non_equiv_states                 false
% 6.55/1.54  --bmc1_deadlock                         false
% 6.55/1.54  --bmc1_ucm                              false
% 6.55/1.54  --bmc1_add_unsat_core                   none
% 6.55/1.54  --bmc1_unsat_core_children              false
% 6.55/1.54  --bmc1_unsat_core_extrapolate_axioms    false
% 6.55/1.54  --bmc1_out_stat                         full
% 6.55/1.54  --bmc1_ground_init                      false
% 6.55/1.54  --bmc1_pre_inst_next_state              false
% 6.55/1.54  --bmc1_pre_inst_state                   false
% 6.55/1.54  --bmc1_pre_inst_reach_state             false
% 6.55/1.54  --bmc1_out_unsat_core                   false
% 6.55/1.54  --bmc1_aig_witness_out                  false
% 6.55/1.54  --bmc1_verbose                          false
% 6.55/1.54  --bmc1_dump_clauses_tptp                false
% 6.55/1.54  --bmc1_dump_unsat_core_tptp             false
% 6.55/1.54  --bmc1_dump_file                        -
% 6.55/1.54  --bmc1_ucm_expand_uc_limit              128
% 6.55/1.54  --bmc1_ucm_n_expand_iterations          6
% 6.55/1.54  --bmc1_ucm_extend_mode                  1
% 6.55/1.54  --bmc1_ucm_init_mode                    2
% 6.55/1.54  --bmc1_ucm_cone_mode                    none
% 6.55/1.54  --bmc1_ucm_reduced_relation_type        0
% 6.55/1.54  --bmc1_ucm_relax_model                  4
% 6.55/1.54  --bmc1_ucm_full_tr_after_sat            true
% 6.55/1.54  --bmc1_ucm_expand_neg_assumptions       false
% 6.55/1.54  --bmc1_ucm_layered_model                none
% 6.55/1.54  --bmc1_ucm_max_lemma_size               10
% 6.55/1.54  
% 6.55/1.54  ------ AIG Options
% 6.55/1.54  
% 6.55/1.54  --aig_mode                              false
% 6.55/1.54  
% 6.55/1.54  ------ Instantiation Options
% 6.55/1.54  
% 6.55/1.54  --instantiation_flag                    true
% 6.55/1.54  --inst_sos_flag                         false
% 6.55/1.54  --inst_sos_phase                        true
% 6.55/1.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.55/1.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.55/1.54  --inst_lit_sel_side                     none
% 6.55/1.54  --inst_solver_per_active                1400
% 6.55/1.54  --inst_solver_calls_frac                1.
% 6.55/1.54  --inst_passive_queue_type               priority_queues
% 6.55/1.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.55/1.54  --inst_passive_queues_freq              [25;2]
% 6.55/1.54  --inst_dismatching                      true
% 6.55/1.54  --inst_eager_unprocessed_to_passive     true
% 6.55/1.54  --inst_prop_sim_given                   true
% 6.55/1.54  --inst_prop_sim_new                     false
% 6.55/1.54  --inst_subs_new                         false
% 6.55/1.54  --inst_eq_res_simp                      false
% 6.55/1.54  --inst_subs_given                       false
% 6.55/1.54  --inst_orphan_elimination               true
% 6.55/1.54  --inst_learning_loop_flag               true
% 6.55/1.54  --inst_learning_start                   3000
% 6.55/1.54  --inst_learning_factor                  2
% 6.55/1.54  --inst_start_prop_sim_after_learn       3
% 6.55/1.54  --inst_sel_renew                        solver
% 6.55/1.54  --inst_lit_activity_flag                true
% 6.55/1.54  --inst_restr_to_given                   false
% 6.55/1.54  --inst_activity_threshold               500
% 6.55/1.54  --inst_out_proof                        true
% 6.55/1.54  
% 6.55/1.54  ------ Resolution Options
% 6.55/1.54  
% 6.55/1.54  --resolution_flag                       false
% 6.55/1.54  --res_lit_sel                           adaptive
% 6.55/1.54  --res_lit_sel_side                      none
% 6.55/1.54  --res_ordering                          kbo
% 6.55/1.54  --res_to_prop_solver                    active
% 6.55/1.54  --res_prop_simpl_new                    false
% 6.55/1.54  --res_prop_simpl_given                  true
% 6.55/1.54  --res_passive_queue_type                priority_queues
% 6.55/1.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.55/1.54  --res_passive_queues_freq               [15;5]
% 6.55/1.54  --res_forward_subs                      full
% 6.55/1.54  --res_backward_subs                     full
% 6.55/1.54  --res_forward_subs_resolution           true
% 6.55/1.54  --res_backward_subs_resolution          true
% 6.55/1.54  --res_orphan_elimination                true
% 6.55/1.54  --res_time_limit                        2.
% 6.55/1.54  --res_out_proof                         true
% 6.55/1.54  
% 6.55/1.54  ------ Superposition Options
% 6.55/1.54  
% 6.55/1.54  --superposition_flag                    true
% 6.55/1.54  --sup_passive_queue_type                priority_queues
% 6.55/1.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.55/1.54  --sup_passive_queues_freq               [8;1;4]
% 6.55/1.54  --demod_completeness_check              fast
% 6.55/1.54  --demod_use_ground                      true
% 6.55/1.54  --sup_to_prop_solver                    passive
% 6.55/1.54  --sup_prop_simpl_new                    true
% 6.55/1.54  --sup_prop_simpl_given                  true
% 6.55/1.54  --sup_fun_splitting                     false
% 6.55/1.54  --sup_smt_interval                      50000
% 6.55/1.54  
% 6.55/1.54  ------ Superposition Simplification Setup
% 6.55/1.54  
% 6.55/1.54  --sup_indices_passive                   []
% 6.55/1.54  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.55/1.54  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.55/1.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.55/1.54  --sup_full_triv                         [TrivRules;PropSubs]
% 6.55/1.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.55/1.54  --sup_full_bw                           [BwDemod]
% 6.55/1.54  --sup_immed_triv                        [TrivRules]
% 6.55/1.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.55/1.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.55/1.54  --sup_immed_bw_main                     []
% 6.55/1.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.55/1.54  --sup_input_triv                        [Unflattening;TrivRules]
% 6.55/1.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.55/1.54  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.55/1.54  
% 6.55/1.54  ------ Combination Options
% 6.55/1.54  
% 6.55/1.54  --comb_res_mult                         3
% 6.55/1.54  --comb_sup_mult                         2
% 6.55/1.54  --comb_inst_mult                        10
% 6.55/1.54  
% 6.55/1.54  ------ Debug Options
% 6.55/1.54  
% 6.55/1.54  --dbg_backtrace                         false
% 6.55/1.54  --dbg_dump_prop_clauses                 false
% 6.55/1.54  --dbg_dump_prop_clauses_file            -
% 6.55/1.54  --dbg_out_stat                          false
% 6.55/1.54  
% 6.55/1.54  
% 6.55/1.54  
% 6.55/1.54  
% 6.55/1.54  ------ Proving...
% 6.55/1.54  
% 6.55/1.54  
% 6.55/1.54  % SZS status Theorem for theBenchmark.p
% 6.55/1.54  
% 6.55/1.54  % SZS output start CNFRefutation for theBenchmark.p
% 6.55/1.54  
% 6.55/1.54  fof(f20,conjecture,(
% 6.55/1.54    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 6.55/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.55/1.54  
% 6.55/1.54  fof(f21,negated_conjecture,(
% 6.55/1.54    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 6.55/1.54    inference(negated_conjecture,[],[f20])).
% 6.55/1.54  
% 6.55/1.54  fof(f29,plain,(
% 6.55/1.54    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 6.55/1.54    inference(ennf_transformation,[],[f21])).
% 6.55/1.54  
% 6.55/1.54  fof(f42,plain,(
% 6.55/1.54    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k1_tarski(sK3),sK4) != sK4 & r2_hidden(sK3,sK4))),
% 6.55/1.54    introduced(choice_axiom,[])).
% 6.55/1.54  
% 6.55/1.54  fof(f43,plain,(
% 6.55/1.54    k2_xboole_0(k1_tarski(sK3),sK4) != sK4 & r2_hidden(sK3,sK4)),
% 6.55/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f42])).
% 6.55/1.54  
% 6.55/1.54  fof(f74,plain,(
% 6.55/1.54    r2_hidden(sK3,sK4)),
% 6.55/1.54    inference(cnf_transformation,[],[f43])).
% 6.55/1.54  
% 6.55/1.54  fof(f18,axiom,(
% 6.55/1.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 6.55/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.55/1.54  
% 6.55/1.54  fof(f41,plain,(
% 6.55/1.54    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 6.55/1.54    inference(nnf_transformation,[],[f18])).
% 6.55/1.54  
% 6.55/1.54  fof(f72,plain,(
% 6.55/1.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 6.55/1.54    inference(cnf_transformation,[],[f41])).
% 6.55/1.54  
% 6.55/1.54  fof(f14,axiom,(
% 6.55/1.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 6.55/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.55/1.54  
% 6.55/1.54  fof(f67,plain,(
% 6.55/1.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 6.55/1.54    inference(cnf_transformation,[],[f14])).
% 6.55/1.54  
% 6.55/1.54  fof(f15,axiom,(
% 6.55/1.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.55/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.55/1.54  
% 6.55/1.54  fof(f68,plain,(
% 6.55/1.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 6.55/1.54    inference(cnf_transformation,[],[f15])).
% 6.55/1.54  
% 6.55/1.54  fof(f16,axiom,(
% 6.55/1.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.55/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.55/1.54  
% 6.55/1.54  fof(f69,plain,(
% 6.55/1.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.55/1.54    inference(cnf_transformation,[],[f16])).
% 6.55/1.54  
% 6.55/1.54  fof(f17,axiom,(
% 6.55/1.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 6.55/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.55/1.54  
% 6.55/1.54  fof(f70,plain,(
% 6.55/1.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 6.55/1.54    inference(cnf_transformation,[],[f17])).
% 6.55/1.54  
% 6.55/1.54  fof(f76,plain,(
% 6.55/1.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 6.55/1.54    inference(definition_unfolding,[],[f69,f70])).
% 6.55/1.54  
% 6.55/1.54  fof(f77,plain,(
% 6.55/1.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 6.55/1.54    inference(definition_unfolding,[],[f68,f76])).
% 6.55/1.54  
% 6.55/1.54  fof(f79,plain,(
% 6.55/1.54    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 6.55/1.54    inference(definition_unfolding,[],[f67,f77])).
% 6.55/1.54  
% 6.55/1.54  fof(f86,plain,(
% 6.55/1.54    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 6.55/1.54    inference(definition_unfolding,[],[f72,f79])).
% 6.55/1.54  
% 6.55/1.54  fof(f9,axiom,(
% 6.55/1.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 6.55/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.55/1.54  
% 6.55/1.54  fof(f28,plain,(
% 6.55/1.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 6.55/1.54    inference(ennf_transformation,[],[f9])).
% 6.55/1.54  
% 6.55/1.54  fof(f62,plain,(
% 6.55/1.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 6.55/1.54    inference(cnf_transformation,[],[f28])).
% 6.55/1.54  
% 6.55/1.54  fof(f10,axiom,(
% 6.55/1.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 6.55/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.55/1.54  
% 6.55/1.54  fof(f63,plain,(
% 6.55/1.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 6.55/1.54    inference(cnf_transformation,[],[f10])).
% 6.55/1.54  
% 6.55/1.54  fof(f19,axiom,(
% 6.55/1.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 6.55/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.55/1.54  
% 6.55/1.54  fof(f73,plain,(
% 6.55/1.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 6.55/1.54    inference(cnf_transformation,[],[f19])).
% 6.55/1.54  
% 6.55/1.54  fof(f78,plain,(
% 6.55/1.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 6.55/1.54    inference(definition_unfolding,[],[f73,f77])).
% 6.55/1.54  
% 6.55/1.54  fof(f7,axiom,(
% 6.55/1.54    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 6.55/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.55/1.54  
% 6.55/1.54  fof(f60,plain,(
% 6.55/1.54    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 6.55/1.54    inference(cnf_transformation,[],[f7])).
% 6.55/1.54  
% 6.55/1.54  fof(f82,plain,(
% 6.55/1.54    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 6.55/1.54    inference(definition_unfolding,[],[f63,f78,f78,f60])).
% 6.55/1.54  
% 6.55/1.54  fof(f8,axiom,(
% 6.55/1.54    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 6.55/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.55/1.54  
% 6.55/1.54  fof(f61,plain,(
% 6.55/1.54    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.55/1.54    inference(cnf_transformation,[],[f8])).
% 6.55/1.54  
% 6.55/1.54  fof(f81,plain,(
% 6.55/1.54    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 6.55/1.54    inference(definition_unfolding,[],[f61,f78])).
% 6.55/1.54  
% 6.55/1.54  fof(f1,axiom,(
% 6.55/1.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 6.55/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.55/1.54  
% 6.55/1.54  fof(f44,plain,(
% 6.55/1.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 6.55/1.54    inference(cnf_transformation,[],[f1])).
% 6.55/1.54  
% 6.55/1.54  fof(f80,plain,(
% 6.55/1.54    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 6.55/1.54    inference(definition_unfolding,[],[f44,f78,f78])).
% 6.55/1.54  
% 6.55/1.54  fof(f11,axiom,(
% 6.55/1.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 6.55/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.55/1.54  
% 6.55/1.54  fof(f64,plain,(
% 6.55/1.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 6.55/1.54    inference(cnf_transformation,[],[f11])).
% 6.55/1.54  
% 6.55/1.54  fof(f83,plain,(
% 6.55/1.54    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 6.55/1.54    inference(definition_unfolding,[],[f64,f60,f60,f78])).
% 6.55/1.54  
% 6.55/1.54  fof(f13,axiom,(
% 6.55/1.54    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 6.55/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.55/1.54  
% 6.55/1.54  fof(f66,plain,(
% 6.55/1.54    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 6.55/1.54    inference(cnf_transformation,[],[f13])).
% 6.55/1.54  
% 6.55/1.54  fof(f85,plain,(
% 6.55/1.54    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 6.55/1.54    inference(definition_unfolding,[],[f66,f78])).
% 6.55/1.54  
% 6.55/1.54  fof(f6,axiom,(
% 6.55/1.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.55/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.55/1.54  
% 6.55/1.54  fof(f39,plain,(
% 6.55/1.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.55/1.54    inference(nnf_transformation,[],[f6])).
% 6.55/1.54  
% 6.55/1.54  fof(f40,plain,(
% 6.55/1.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.55/1.54    inference(flattening,[],[f39])).
% 6.55/1.54  
% 6.55/1.54  fof(f57,plain,(
% 6.55/1.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 6.55/1.54    inference(cnf_transformation,[],[f40])).
% 6.55/1.54  
% 6.55/1.54  fof(f90,plain,(
% 6.55/1.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.55/1.54    inference(equality_resolution,[],[f57])).
% 6.55/1.54  
% 6.55/1.54  fof(f75,plain,(
% 6.55/1.54    k2_xboole_0(k1_tarski(sK3),sK4) != sK4),
% 6.55/1.54    inference(cnf_transformation,[],[f43])).
% 6.55/1.54  
% 6.55/1.54  fof(f88,plain,(
% 6.55/1.54    k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) != sK4),
% 6.55/1.54    inference(definition_unfolding,[],[f75,f78,f79])).
% 6.55/1.54  
% 6.55/1.54  cnf(c_25,negated_conjecture,
% 6.55/1.54      ( r2_hidden(sK3,sK4) ),
% 6.55/1.54      inference(cnf_transformation,[],[f74]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_1045,plain,
% 6.55/1.54      ( r2_hidden(sK3,sK4) = iProver_top ),
% 6.55/1.54      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_22,plain,
% 6.55/1.54      ( ~ r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 6.55/1.54      inference(cnf_transformation,[],[f86]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_1047,plain,
% 6.55/1.54      ( r2_hidden(X0,X1) != iProver_top
% 6.55/1.54      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
% 6.55/1.54      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_17,plain,
% 6.55/1.54      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 6.55/1.54      inference(cnf_transformation,[],[f62]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_1049,plain,
% 6.55/1.54      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 6.55/1.54      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_2230,plain,
% 6.55/1.54      ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k3_enumset1(X0,X0,X0,X0,X0)
% 6.55/1.54      | r2_hidden(X0,X1) != iProver_top ),
% 6.55/1.54      inference(superposition,[status(thm)],[c_1047,c_1049]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_27160,plain,
% 6.55/1.54      ( k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 6.55/1.54      inference(superposition,[status(thm)],[c_1045,c_2230]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_18,plain,
% 6.55/1.54      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 6.55/1.54      inference(cnf_transformation,[],[f82]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_28624,plain,
% 6.55/1.54      ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
% 6.55/1.54      inference(superposition,[status(thm)],[c_27160,c_18]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_16,plain,
% 6.55/1.54      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 6.55/1.54      inference(cnf_transformation,[],[f81]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_0,plain,
% 6.55/1.54      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
% 6.55/1.54      inference(cnf_transformation,[],[f80]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_1464,plain,
% 6.55/1.54      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 6.55/1.54      inference(superposition,[status(thm)],[c_0,c_16]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_19,plain,
% 6.55/1.54      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 6.55/1.54      inference(cnf_transformation,[],[f83]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_1973,plain,
% 6.55/1.54      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
% 6.55/1.54      inference(superposition,[status(thm)],[c_1464,c_19]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_21,plain,
% 6.55/1.54      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
% 6.55/1.54      inference(cnf_transformation,[],[f85]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_1048,plain,
% 6.55/1.54      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
% 6.55/1.54      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_1286,plain,
% 6.55/1.54      ( k3_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X0 ),
% 6.55/1.54      inference(superposition,[status(thm)],[c_1048,c_1049]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_1976,plain,
% 6.55/1.54      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 6.55/1.54      inference(superposition,[status(thm)],[c_1464,c_1286]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_1987,plain,
% 6.55/1.54      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 6.55/1.54      inference(light_normalisation,[status(thm)],[c_1973,c_1976]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_15,plain,
% 6.55/1.54      ( r1_tarski(X0,X0) ),
% 6.55/1.54      inference(cnf_transformation,[],[f90]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_1050,plain,
% 6.55/1.54      ( r1_tarski(X0,X0) = iProver_top ),
% 6.55/1.54      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_1285,plain,
% 6.55/1.54      ( k3_xboole_0(X0,X0) = X0 ),
% 6.55/1.54      inference(superposition,[status(thm)],[c_1050,c_1049]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_1989,plain,
% 6.55/1.54      ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 6.55/1.54      inference(light_normalisation,[status(thm)],[c_1987,c_1285]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_1979,plain,
% 6.55/1.54      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 6.55/1.54      inference(superposition,[status(thm)],[c_1464,c_18]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_1980,plain,
% 6.55/1.54      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 6.55/1.54      inference(light_normalisation,[status(thm)],[c_1979,c_1464]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_2092,plain,
% 6.55/1.54      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 6.55/1.54      inference(superposition,[status(thm)],[c_1285,c_1980]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_2224,plain,
% 6.55/1.54      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 6.55/1.54      inference(light_normalisation,[status(thm)],[c_1989,c_2092]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_28626,plain,
% 6.55/1.54      ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = sK4 ),
% 6.55/1.54      inference(demodulation,[status(thm)],[c_28624,c_16,c_2224]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_24,negated_conjecture,
% 6.55/1.54      ( k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) != sK4 ),
% 6.55/1.54      inference(cnf_transformation,[],[f88]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(c_1456,plain,
% 6.55/1.54      ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) != sK4 ),
% 6.55/1.54      inference(demodulation,[status(thm)],[c_0,c_24]) ).
% 6.55/1.54  
% 6.55/1.54  cnf(contradiction,plain,
% 6.55/1.54      ( $false ),
% 6.55/1.54      inference(minisat,[status(thm)],[c_28626,c_1456]) ).
% 6.55/1.54  
% 6.55/1.54  
% 6.55/1.54  % SZS output end CNFRefutation for theBenchmark.p
% 6.55/1.54  
% 6.55/1.54  ------                               Statistics
% 6.55/1.54  
% 6.55/1.54  ------ General
% 6.55/1.54  
% 6.55/1.54  abstr_ref_over_cycles:                  0
% 6.55/1.54  abstr_ref_under_cycles:                 0
% 6.55/1.54  gc_basic_clause_elim:                   0
% 6.55/1.54  forced_gc_time:                         0
% 6.55/1.54  parsing_time:                           0.013
% 6.55/1.54  unif_index_cands_time:                  0.
% 6.55/1.54  unif_index_add_time:                    0.
% 6.55/1.54  orderings_time:                         0.
% 6.55/1.54  out_proof_time:                         0.007
% 6.55/1.54  total_time:                             0.857
% 6.55/1.54  num_of_symbols:                         44
% 6.55/1.54  num_of_terms:                           26570
% 6.55/1.54  
% 6.55/1.54  ------ Preprocessing
% 6.55/1.54  
% 6.55/1.54  num_of_splits:                          0
% 6.55/1.54  num_of_split_atoms:                     0
% 6.55/1.54  num_of_reused_defs:                     0
% 6.55/1.54  num_eq_ax_congr_red:                    27
% 6.55/1.54  num_of_sem_filtered_clauses:            1
% 6.55/1.54  num_of_subtypes:                        0
% 6.55/1.54  monotx_restored_types:                  0
% 6.55/1.54  sat_num_of_epr_types:                   0
% 6.55/1.54  sat_num_of_non_cyclic_types:            0
% 6.55/1.54  sat_guarded_non_collapsed_types:        0
% 6.55/1.54  num_pure_diseq_elim:                    0
% 6.55/1.54  simp_replaced_by:                       0
% 6.55/1.54  res_preprocessed:                       117
% 6.55/1.54  prep_upred:                             0
% 6.55/1.54  prep_unflattend:                        0
% 6.55/1.54  smt_new_axioms:                         0
% 6.55/1.54  pred_elim_cands:                        3
% 6.55/1.54  pred_elim:                              0
% 6.55/1.54  pred_elim_cl:                           0
% 6.55/1.54  pred_elim_cycles:                       2
% 6.55/1.54  merged_defs:                            8
% 6.55/1.54  merged_defs_ncl:                        0
% 6.55/1.54  bin_hyper_res:                          8
% 6.55/1.54  prep_cycles:                            4
% 6.55/1.54  pred_elim_time:                         0.004
% 6.55/1.54  splitting_time:                         0.
% 6.55/1.54  sem_filter_time:                        0.
% 6.55/1.54  monotx_time:                            0.001
% 6.55/1.54  subtype_inf_time:                       0.
% 6.55/1.54  
% 6.55/1.54  ------ Problem properties
% 6.55/1.54  
% 6.55/1.54  clauses:                                25
% 6.55/1.54  conjectures:                            2
% 6.55/1.54  epr:                                    5
% 6.55/1.54  horn:                                   18
% 6.55/1.54  ground:                                 2
% 6.55/1.54  unary:                                  9
% 6.55/1.54  binary:                                 9
% 6.55/1.54  lits:                                   48
% 6.55/1.54  lits_eq:                                8
% 6.55/1.54  fd_pure:                                0
% 6.55/1.54  fd_pseudo:                              0
% 6.55/1.54  fd_cond:                                0
% 6.55/1.54  fd_pseudo_cond:                         1
% 6.55/1.54  ac_symbols:                             0
% 6.55/1.54  
% 6.55/1.54  ------ Propositional Solver
% 6.55/1.54  
% 6.55/1.54  prop_solver_calls:                      28
% 6.55/1.54  prop_fast_solver_calls:                 729
% 6.55/1.54  smt_solver_calls:                       0
% 6.55/1.54  smt_fast_solver_calls:                  0
% 6.55/1.54  prop_num_of_clauses:                    8403
% 6.55/1.54  prop_preprocess_simplified:             15506
% 6.55/1.54  prop_fo_subsumed:                       0
% 6.55/1.54  prop_solver_time:                       0.
% 6.55/1.54  smt_solver_time:                        0.
% 6.55/1.54  smt_fast_solver_time:                   0.
% 6.55/1.54  prop_fast_solver_time:                  0.
% 6.55/1.54  prop_unsat_core_time:                   0.
% 6.55/1.54  
% 6.55/1.54  ------ QBF
% 6.55/1.54  
% 6.55/1.54  qbf_q_res:                              0
% 6.55/1.54  qbf_num_tautologies:                    0
% 6.55/1.54  qbf_prep_cycles:                        0
% 6.55/1.54  
% 6.55/1.54  ------ BMC1
% 6.55/1.54  
% 6.55/1.54  bmc1_current_bound:                     -1
% 6.55/1.54  bmc1_last_solved_bound:                 -1
% 6.55/1.54  bmc1_unsat_core_size:                   -1
% 6.55/1.54  bmc1_unsat_core_parents_size:           -1
% 6.55/1.54  bmc1_merge_next_fun:                    0
% 6.55/1.54  bmc1_unsat_core_clauses_time:           0.
% 6.55/1.54  
% 6.55/1.54  ------ Instantiation
% 6.55/1.54  
% 6.55/1.54  inst_num_of_clauses:                    1905
% 6.55/1.54  inst_num_in_passive:                    785
% 6.55/1.54  inst_num_in_active:                     414
% 6.55/1.54  inst_num_in_unprocessed:                706
% 6.55/1.54  inst_num_of_loops:                      740
% 6.55/1.54  inst_num_of_learning_restarts:          0
% 6.55/1.54  inst_num_moves_active_passive:          325
% 6.55/1.54  inst_lit_activity:                      0
% 6.55/1.54  inst_lit_activity_moves:                0
% 6.55/1.54  inst_num_tautologies:                   0
% 6.55/1.54  inst_num_prop_implied:                  0
% 6.55/1.54  inst_num_existing_simplified:           0
% 6.55/1.54  inst_num_eq_res_simplified:             0
% 6.55/1.54  inst_num_child_elim:                    0
% 6.55/1.54  inst_num_of_dismatching_blockings:      3621
% 6.55/1.54  inst_num_of_non_proper_insts:           2782
% 6.55/1.54  inst_num_of_duplicates:                 0
% 6.55/1.54  inst_inst_num_from_inst_to_res:         0
% 6.55/1.54  inst_dismatching_checking_time:         0.
% 6.55/1.54  
% 6.55/1.54  ------ Resolution
% 6.55/1.54  
% 6.55/1.54  res_num_of_clauses:                     0
% 6.55/1.54  res_num_in_passive:                     0
% 6.55/1.54  res_num_in_active:                      0
% 6.55/1.54  res_num_of_loops:                       121
% 6.55/1.54  res_forward_subset_subsumed:            306
% 6.55/1.54  res_backward_subset_subsumed:           0
% 6.55/1.54  res_forward_subsumed:                   0
% 6.55/1.54  res_backward_subsumed:                  0
% 6.55/1.54  res_forward_subsumption_resolution:     0
% 6.55/1.54  res_backward_subsumption_resolution:    0
% 6.55/1.54  res_clause_to_clause_subsumption:       3730
% 6.55/1.54  res_orphan_elimination:                 0
% 6.55/1.54  res_tautology_del:                      126
% 6.55/1.54  res_num_eq_res_simplified:              0
% 6.55/1.54  res_num_sel_changes:                    0
% 6.55/1.54  res_moves_from_active_to_pass:          0
% 6.55/1.54  
% 6.55/1.54  ------ Superposition
% 6.55/1.54  
% 6.55/1.54  sup_time_total:                         0.
% 6.55/1.54  sup_time_generating:                    0.
% 6.55/1.54  sup_time_sim_full:                      0.
% 6.55/1.54  sup_time_sim_immed:                     0.
% 6.55/1.54  
% 6.55/1.54  sup_num_of_clauses:                     515
% 6.55/1.54  sup_num_in_active:                      144
% 6.55/1.54  sup_num_in_passive:                     371
% 6.55/1.54  sup_num_of_loops:                       146
% 6.55/1.54  sup_fw_superposition:                   5635
% 6.55/1.54  sup_bw_superposition:                   683
% 6.55/1.54  sup_immediate_simplified:               588
% 6.55/1.54  sup_given_eliminated:                   0
% 6.55/1.54  comparisons_done:                       0
% 6.55/1.54  comparisons_avoided:                    0
% 6.55/1.54  
% 6.55/1.54  ------ Simplifications
% 6.55/1.54  
% 6.55/1.54  
% 6.55/1.54  sim_fw_subset_subsumed:                 1
% 6.55/1.54  sim_bw_subset_subsumed:                 0
% 6.55/1.54  sim_fw_subsumed:                        168
% 6.55/1.54  sim_bw_subsumed:                        4
% 6.55/1.54  sim_fw_subsumption_res:                 0
% 6.55/1.54  sim_bw_subsumption_res:                 0
% 6.55/1.54  sim_tautology_del:                      13
% 6.55/1.54  sim_eq_tautology_del:                   144
% 6.55/1.54  sim_eq_res_simp:                        0
% 6.55/1.54  sim_fw_demodulated:                     235
% 6.55/1.54  sim_bw_demodulated:                     14
% 6.55/1.54  sim_light_normalised:                   398
% 6.55/1.54  sim_joinable_taut:                      0
% 6.55/1.54  sim_joinable_simp:                      0
% 6.55/1.54  sim_ac_normalised:                      0
% 6.55/1.54  sim_smt_subsumption:                    0
% 6.55/1.54  
%------------------------------------------------------------------------------
