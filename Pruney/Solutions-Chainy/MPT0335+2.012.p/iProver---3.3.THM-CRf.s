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
% DateTime   : Thu Dec  3 11:38:26 EST 2020

% Result     : Theorem 51.38s
% Output     : CNFRefutation 51.38s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 479 expanded)
%              Number of clauses        :   47 ( 112 expanded)
%              Number of leaves         :   15 ( 140 expanded)
%              Depth                    :   17
%              Number of atoms          :  147 ( 698 expanded)
%              Number of equality atoms :  102 ( 530 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK0,sK2) != k1_tarski(sK3)
      & r2_hidden(sK3,sK0)
      & k3_xboole_0(sK1,sK2) = k1_tarski(sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( k3_xboole_0(sK0,sK2) != k1_tarski(sK3)
    & r2_hidden(sK3,sK0)
    & k3_xboole_0(sK1,sK2) = k1_tarski(sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f23])).

fof(f43,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f45])).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f46])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f47])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f25,f34,f34])).

fof(f42,plain,(
    k3_xboole_0(sK1,sK2) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f42,f34,f47])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f26,f34])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f32,f34,f34,f34,f34])).

fof(f41,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    k3_xboole_0(sK0,sK2) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f44,f34,f47])).

cnf(c_12,negated_conjecture,
    ( r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_413,plain,
    ( r2_hidden(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_414,plain,
    ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_800,plain,
    ( k2_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK0) = sK0 ),
    inference(superposition,[status(thm)],[c_413,c_414])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_13,negated_conjecture,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_690,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(demodulation,[status(thm)],[c_0,c_13])).

cnf(c_1343,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_800,c_690])).

cnf(c_9,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_415,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1345,plain,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1343,c_415])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_417,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1477,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1345,c_417])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_418,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1474,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_418,c_417])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_126519,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_1474,c_1])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_802,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_910,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_8,c_7])).

cnf(c_8282,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_802,c_910])).

cnf(c_8955,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_8282,c_8])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_412,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1476,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_412,c_417])).

cnf(c_887,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_0,c_7])).

cnf(c_3033,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_1476,c_887])).

cnf(c_9303,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,k1_xboole_0))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_8955,c_3033])).

cnf(c_10128,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,X0))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_9303,c_0])).

cnf(c_127469,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
    inference(demodulation,[status(thm)],[c_126519,c_10128])).

cnf(c_127637,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_127469,c_8])).

cnf(c_128704,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_127637])).

cnf(c_152318,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),k1_xboole_0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))) ),
    inference(superposition,[status(thm)],[c_1477,c_128704])).

cnf(c_8345,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1)))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(superposition,[status(thm)],[c_0,c_910])).

cnf(c_8640,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_8345,c_8,c_802])).

cnf(c_12441,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_0,c_8640])).

cnf(c_3089,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_887,c_8])).

cnf(c_128803,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK1))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_127637,c_3089])).

cnf(c_128856,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK1))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_128803,c_8])).

cnf(c_152607,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(demodulation,[status(thm)],[c_152318,c_12441,c_126519,c_128856])).

cnf(c_11,negated_conjecture,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_444,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_11,c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_152607,c_444])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:48:27 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 51.38/7.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.38/7.01  
% 51.38/7.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.38/7.01  
% 51.38/7.01  ------  iProver source info
% 51.38/7.01  
% 51.38/7.01  git: date: 2020-06-30 10:37:57 +0100
% 51.38/7.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.38/7.01  git: non_committed_changes: false
% 51.38/7.01  git: last_make_outside_of_git: false
% 51.38/7.01  
% 51.38/7.01  ------ 
% 51.38/7.01  ------ Parsing...
% 51.38/7.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.38/7.01  
% 51.38/7.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 51.38/7.01  
% 51.38/7.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.38/7.01  
% 51.38/7.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.38/7.01  ------ Proving...
% 51.38/7.01  ------ Problem Properties 
% 51.38/7.01  
% 51.38/7.01  
% 51.38/7.01  clauses                                 14
% 51.38/7.01  conjectures                             4
% 51.38/7.01  EPR                                     4
% 51.38/7.01  Horn                                    14
% 51.38/7.01  unary                                   10
% 51.38/7.01  binary                                  3
% 51.38/7.01  lits                                    19
% 51.38/7.01  lits eq                                 10
% 51.38/7.01  fd_pure                                 0
% 51.38/7.01  fd_pseudo                               0
% 51.38/7.01  fd_cond                                 0
% 51.38/7.01  fd_pseudo_cond                          1
% 51.38/7.01  AC symbols                              0
% 51.38/7.01  
% 51.38/7.01  ------ Input Options Time Limit: Unbounded
% 51.38/7.01  
% 51.38/7.01  
% 51.38/7.01  ------ 
% 51.38/7.01  Current options:
% 51.38/7.01  ------ 
% 51.38/7.01  
% 51.38/7.01  
% 51.38/7.01  
% 51.38/7.01  
% 51.38/7.01  ------ Proving...
% 51.38/7.01  
% 51.38/7.01  
% 51.38/7.01  % SZS status Theorem for theBenchmark.p
% 51.38/7.01  
% 51.38/7.01  % SZS output start CNFRefutation for theBenchmark.p
% 51.38/7.01  
% 51.38/7.01  fof(f14,conjecture,(
% 51.38/7.01    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 51.38/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.38/7.01  
% 51.38/7.01  fof(f15,negated_conjecture,(
% 51.38/7.01    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 51.38/7.01    inference(negated_conjecture,[],[f14])).
% 51.38/7.01  
% 51.38/7.01  fof(f18,plain,(
% 51.38/7.01    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 51.38/7.01    inference(ennf_transformation,[],[f15])).
% 51.38/7.01  
% 51.38/7.01  fof(f19,plain,(
% 51.38/7.01    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 51.38/7.01    inference(flattening,[],[f18])).
% 51.38/7.01  
% 51.38/7.01  fof(f23,plain,(
% 51.38/7.01    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK0,sK2) != k1_tarski(sK3) & r2_hidden(sK3,sK0) & k3_xboole_0(sK1,sK2) = k1_tarski(sK3) & r1_tarski(sK0,sK1))),
% 51.38/7.01    introduced(choice_axiom,[])).
% 51.38/7.01  
% 51.38/7.01  fof(f24,plain,(
% 51.38/7.01    k3_xboole_0(sK0,sK2) != k1_tarski(sK3) & r2_hidden(sK3,sK0) & k3_xboole_0(sK1,sK2) = k1_tarski(sK3) & r1_tarski(sK0,sK1)),
% 51.38/7.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f23])).
% 51.38/7.01  
% 51.38/7.01  fof(f43,plain,(
% 51.38/7.01    r2_hidden(sK3,sK0)),
% 51.38/7.01    inference(cnf_transformation,[],[f24])).
% 51.38/7.01  
% 51.38/7.01  fof(f13,axiom,(
% 51.38/7.01    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 51.38/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.38/7.01  
% 51.38/7.01  fof(f17,plain,(
% 51.38/7.01    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 51.38/7.01    inference(ennf_transformation,[],[f13])).
% 51.38/7.01  
% 51.38/7.01  fof(f40,plain,(
% 51.38/7.01    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 51.38/7.01    inference(cnf_transformation,[],[f17])).
% 51.38/7.01  
% 51.38/7.01  fof(f9,axiom,(
% 51.38/7.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 51.38/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.38/7.01  
% 51.38/7.01  fof(f36,plain,(
% 51.38/7.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 51.38/7.01    inference(cnf_transformation,[],[f9])).
% 51.38/7.01  
% 51.38/7.01  fof(f10,axiom,(
% 51.38/7.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 51.38/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.38/7.01  
% 51.38/7.01  fof(f37,plain,(
% 51.38/7.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 51.38/7.01    inference(cnf_transformation,[],[f10])).
% 51.38/7.01  
% 51.38/7.01  fof(f11,axiom,(
% 51.38/7.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 51.38/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.38/7.01  
% 51.38/7.01  fof(f38,plain,(
% 51.38/7.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 51.38/7.01    inference(cnf_transformation,[],[f11])).
% 51.38/7.01  
% 51.38/7.01  fof(f12,axiom,(
% 51.38/7.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 51.38/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.38/7.01  
% 51.38/7.01  fof(f39,plain,(
% 51.38/7.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 51.38/7.01    inference(cnf_transformation,[],[f12])).
% 51.38/7.01  
% 51.38/7.01  fof(f45,plain,(
% 51.38/7.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 51.38/7.01    inference(definition_unfolding,[],[f38,f39])).
% 51.38/7.01  
% 51.38/7.01  fof(f46,plain,(
% 51.38/7.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 51.38/7.01    inference(definition_unfolding,[],[f37,f45])).
% 51.38/7.01  
% 51.38/7.01  fof(f47,plain,(
% 51.38/7.01    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 51.38/7.01    inference(definition_unfolding,[],[f36,f46])).
% 51.38/7.01  
% 51.38/7.01  fof(f52,plain,(
% 51.38/7.01    ( ! [X0,X1] : (k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 51.38/7.01    inference(definition_unfolding,[],[f40,f47])).
% 51.38/7.01  
% 51.38/7.01  fof(f1,axiom,(
% 51.38/7.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 51.38/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.38/7.01  
% 51.38/7.01  fof(f25,plain,(
% 51.38/7.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 51.38/7.01    inference(cnf_transformation,[],[f1])).
% 51.38/7.01  
% 51.38/7.01  fof(f7,axiom,(
% 51.38/7.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 51.38/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.38/7.01  
% 51.38/7.01  fof(f34,plain,(
% 51.38/7.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 51.38/7.01    inference(cnf_transformation,[],[f7])).
% 51.38/7.01  
% 51.38/7.01  fof(f48,plain,(
% 51.38/7.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 51.38/7.01    inference(definition_unfolding,[],[f25,f34,f34])).
% 51.38/7.01  
% 51.38/7.01  fof(f42,plain,(
% 51.38/7.01    k3_xboole_0(sK1,sK2) = k1_tarski(sK3)),
% 51.38/7.01    inference(cnf_transformation,[],[f24])).
% 51.38/7.01  
% 51.38/7.01  fof(f54,plain,(
% 51.38/7.01    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 51.38/7.01    inference(definition_unfolding,[],[f42,f34,f47])).
% 51.38/7.01  
% 51.38/7.01  fof(f8,axiom,(
% 51.38/7.01    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 51.38/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.38/7.01  
% 51.38/7.01  fof(f35,plain,(
% 51.38/7.01    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 51.38/7.01    inference(cnf_transformation,[],[f8])).
% 51.38/7.01  
% 51.38/7.01  fof(f4,axiom,(
% 51.38/7.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 51.38/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.38/7.01  
% 51.38/7.01  fof(f22,plain,(
% 51.38/7.01    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 51.38/7.01    inference(nnf_transformation,[],[f4])).
% 51.38/7.01  
% 51.38/7.01  fof(f31,plain,(
% 51.38/7.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 51.38/7.01    inference(cnf_transformation,[],[f22])).
% 51.38/7.01  
% 51.38/7.01  fof(f3,axiom,(
% 51.38/7.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 51.38/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.38/7.01  
% 51.38/7.01  fof(f20,plain,(
% 51.38/7.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.38/7.01    inference(nnf_transformation,[],[f3])).
% 51.38/7.01  
% 51.38/7.01  fof(f21,plain,(
% 51.38/7.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.38/7.01    inference(flattening,[],[f20])).
% 51.38/7.01  
% 51.38/7.01  fof(f27,plain,(
% 51.38/7.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 51.38/7.01    inference(cnf_transformation,[],[f21])).
% 51.38/7.01  
% 51.38/7.01  fof(f56,plain,(
% 51.38/7.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 51.38/7.01    inference(equality_resolution,[],[f27])).
% 51.38/7.01  
% 51.38/7.01  fof(f2,axiom,(
% 51.38/7.01    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 51.38/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.38/7.01  
% 51.38/7.01  fof(f16,plain,(
% 51.38/7.01    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 51.38/7.01    inference(rectify,[],[f2])).
% 51.38/7.01  
% 51.38/7.01  fof(f26,plain,(
% 51.38/7.01    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 51.38/7.01    inference(cnf_transformation,[],[f16])).
% 51.38/7.01  
% 51.38/7.01  fof(f49,plain,(
% 51.38/7.01    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 51.38/7.01    inference(definition_unfolding,[],[f26,f34])).
% 51.38/7.01  
% 51.38/7.01  fof(f6,axiom,(
% 51.38/7.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 51.38/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.38/7.01  
% 51.38/7.01  fof(f33,plain,(
% 51.38/7.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 51.38/7.01    inference(cnf_transformation,[],[f6])).
% 51.38/7.01  
% 51.38/7.01  fof(f51,plain,(
% 51.38/7.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 51.38/7.01    inference(definition_unfolding,[],[f33,f34])).
% 51.38/7.01  
% 51.38/7.01  fof(f5,axiom,(
% 51.38/7.01    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 51.38/7.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.38/7.01  
% 51.38/7.01  fof(f32,plain,(
% 51.38/7.01    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 51.38/7.01    inference(cnf_transformation,[],[f5])).
% 51.38/7.01  
% 51.38/7.01  fof(f50,plain,(
% 51.38/7.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 51.38/7.01    inference(definition_unfolding,[],[f32,f34,f34,f34,f34])).
% 51.38/7.01  
% 51.38/7.01  fof(f41,plain,(
% 51.38/7.01    r1_tarski(sK0,sK1)),
% 51.38/7.01    inference(cnf_transformation,[],[f24])).
% 51.38/7.01  
% 51.38/7.01  fof(f44,plain,(
% 51.38/7.01    k3_xboole_0(sK0,sK2) != k1_tarski(sK3)),
% 51.38/7.01    inference(cnf_transformation,[],[f24])).
% 51.38/7.01  
% 51.38/7.01  fof(f53,plain,(
% 51.38/7.01    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 51.38/7.01    inference(definition_unfolding,[],[f44,f34,f47])).
% 51.38/7.01  
% 51.38/7.01  cnf(c_12,negated_conjecture,
% 51.38/7.01      ( r2_hidden(sK3,sK0) ),
% 51.38/7.01      inference(cnf_transformation,[],[f43]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_413,plain,
% 51.38/7.01      ( r2_hidden(sK3,sK0) = iProver_top ),
% 51.38/7.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_10,plain,
% 51.38/7.01      ( ~ r2_hidden(X0,X1)
% 51.38/7.01      | k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1 ),
% 51.38/7.01      inference(cnf_transformation,[],[f52]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_414,plain,
% 51.38/7.01      ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1
% 51.38/7.01      | r2_hidden(X0,X1) != iProver_top ),
% 51.38/7.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_800,plain,
% 51.38/7.01      ( k2_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK0) = sK0 ),
% 51.38/7.01      inference(superposition,[status(thm)],[c_413,c_414]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_0,plain,
% 51.38/7.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 51.38/7.01      inference(cnf_transformation,[],[f48]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_13,negated_conjecture,
% 51.38/7.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 51.38/7.01      inference(cnf_transformation,[],[f54]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_690,plain,
% 51.38/7.01      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
% 51.38/7.01      inference(demodulation,[status(thm)],[c_0,c_13]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_1343,plain,
% 51.38/7.01      ( k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0) = sK0 ),
% 51.38/7.01      inference(light_normalisation,[status(thm)],[c_800,c_690]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_9,plain,
% 51.38/7.01      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 51.38/7.01      inference(cnf_transformation,[],[f35]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_415,plain,
% 51.38/7.01      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 51.38/7.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_1345,plain,
% 51.38/7.01      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0) = iProver_top ),
% 51.38/7.01      inference(superposition,[status(thm)],[c_1343,c_415]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_5,plain,
% 51.38/7.01      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 51.38/7.01      inference(cnf_transformation,[],[f31]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_417,plain,
% 51.38/7.01      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 51.38/7.01      | r1_tarski(X0,X1) != iProver_top ),
% 51.38/7.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_1477,plain,
% 51.38/7.01      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0) = k1_xboole_0 ),
% 51.38/7.01      inference(superposition,[status(thm)],[c_1345,c_417]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_4,plain,
% 51.38/7.01      ( r1_tarski(X0,X0) ),
% 51.38/7.01      inference(cnf_transformation,[],[f56]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_418,plain,
% 51.38/7.01      ( r1_tarski(X0,X0) = iProver_top ),
% 51.38/7.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_1474,plain,
% 51.38/7.01      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 51.38/7.01      inference(superposition,[status(thm)],[c_418,c_417]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_1,plain,
% 51.38/7.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 51.38/7.01      inference(cnf_transformation,[],[f49]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_126519,plain,
% 51.38/7.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 51.38/7.01      inference(demodulation,[status(thm)],[c_1474,c_1]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_8,plain,
% 51.38/7.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 51.38/7.01      inference(cnf_transformation,[],[f51]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_802,plain,
% 51.38/7.01      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 51.38/7.01      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_7,plain,
% 51.38/7.01      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 51.38/7.01      inference(cnf_transformation,[],[f50]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_910,plain,
% 51.38/7.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) ),
% 51.38/7.01      inference(superposition,[status(thm)],[c_8,c_7]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_8282,plain,
% 51.38/7.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 51.38/7.01      inference(superposition,[status(thm)],[c_802,c_910]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_8955,plain,
% 51.38/7.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 51.38/7.01      inference(light_normalisation,[status(thm)],[c_8282,c_8]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_14,negated_conjecture,
% 51.38/7.01      ( r1_tarski(sK0,sK1) ),
% 51.38/7.01      inference(cnf_transformation,[],[f41]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_412,plain,
% 51.38/7.01      ( r1_tarski(sK0,sK1) = iProver_top ),
% 51.38/7.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_1476,plain,
% 51.38/7.01      ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 51.38/7.01      inference(superposition,[status(thm)],[c_412,c_417]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_887,plain,
% 51.38/7.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 51.38/7.01      inference(superposition,[status(thm)],[c_0,c_7]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_3033,plain,
% 51.38/7.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k1_xboole_0))) ),
% 51.38/7.01      inference(superposition,[status(thm)],[c_1476,c_887]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_9303,plain,
% 51.38/7.01      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,k1_xboole_0))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,X0))) ),
% 51.38/7.01      inference(superposition,[status(thm)],[c_8955,c_3033]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_10128,plain,
% 51.38/7.01      ( k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,X0))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,X0))) ),
% 51.38/7.01      inference(superposition,[status(thm)],[c_9303,c_0]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_127469,plain,
% 51.38/7.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
% 51.38/7.01      inference(demodulation,[status(thm)],[c_126519,c_10128]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_127637,plain,
% 51.38/7.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,X0) ),
% 51.38/7.01      inference(demodulation,[status(thm)],[c_127469,c_8]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_128704,plain,
% 51.38/7.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
% 51.38/7.01      inference(superposition,[status(thm)],[c_0,c_127637]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_152318,plain,
% 51.38/7.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),k1_xboole_0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))) ),
% 51.38/7.01      inference(superposition,[status(thm)],[c_1477,c_128704]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_8345,plain,
% 51.38/7.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1)))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
% 51.38/7.01      inference(superposition,[status(thm)],[c_0,c_910]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_8640,plain,
% 51.38/7.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 51.38/7.01      inference(demodulation,[status(thm)],[c_8345,c_8,c_802]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_12441,plain,
% 51.38/7.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 51.38/7.01      inference(superposition,[status(thm)],[c_0,c_8640]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_3089,plain,
% 51.38/7.01      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 51.38/7.01      inference(superposition,[status(thm)],[c_887,c_8]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_128803,plain,
% 51.38/7.01      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK1))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
% 51.38/7.01      inference(superposition,[status(thm)],[c_127637,c_3089]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_128856,plain,
% 51.38/7.01      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK1))) = k4_xboole_0(sK0,X0) ),
% 51.38/7.01      inference(demodulation,[status(thm)],[c_128803,c_8]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_152607,plain,
% 51.38/7.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
% 51.38/7.01      inference(demodulation,
% 51.38/7.01                [status(thm)],
% 51.38/7.01                [c_152318,c_12441,c_126519,c_128856]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_11,negated_conjecture,
% 51.38/7.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 51.38/7.01      inference(cnf_transformation,[],[f53]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(c_444,plain,
% 51.38/7.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
% 51.38/7.01      inference(light_normalisation,[status(thm)],[c_11,c_13]) ).
% 51.38/7.01  
% 51.38/7.01  cnf(contradiction,plain,
% 51.38/7.01      ( $false ),
% 51.38/7.01      inference(minisat,[status(thm)],[c_152607,c_444]) ).
% 51.38/7.01  
% 51.38/7.01  
% 51.38/7.01  % SZS output end CNFRefutation for theBenchmark.p
% 51.38/7.01  
% 51.38/7.01  ------                               Statistics
% 51.38/7.01  
% 51.38/7.01  ------ Selected
% 51.38/7.01  
% 51.38/7.01  total_time:                             6.476
% 51.38/7.01  
%------------------------------------------------------------------------------
