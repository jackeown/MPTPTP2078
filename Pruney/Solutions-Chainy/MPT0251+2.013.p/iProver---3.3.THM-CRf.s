%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:03 EST 2020

% Result     : Theorem 6.72s
% Output     : CNFRefutation 6.72s
% Verified   : 
% Statistics : Number of formulae       :   96 (1179 expanded)
%              Number of clauses        :   40 ( 269 expanded)
%              Number of leaves         :   18 ( 346 expanded)
%              Depth                    :   16
%              Number of atoms          :  144 (1346 expanded)
%              Number of equality atoms :   91 (1138 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK1),sK2) != sK2
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k2_xboole_0(k1_tarski(sK1),sK2) != sK2
    & r2_hidden(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f34])).

fof(f63,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f32])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f62,f67])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f65,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f53,f47])).

fof(f73,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f65,f67])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f54,f67,f67])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f69,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f48,f65])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f70,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) ),
    inference(definition_unfolding,[],[f51,f65,f65,f47])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) ),
    inference(definition_unfolding,[],[f52,f47,f47,f65])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f64,plain,(
    k2_xboole_0(k1_tarski(sK1),sK2) != sK2 ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f67])).

fof(f77,plain,(
    k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) != sK2 ),
    inference(definition_unfolding,[],[f64,f65,f68])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_548,plain,
    ( r2_hidden(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_551,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_553,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3057,plain,
    ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_551,c_553])).

cnf(c_22054,plain,
    ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,X0),sK2) = k3_enumset1(sK1,sK1,sK1,sK1,X0)
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_548,c_3057])).

cnf(c_22844,plain,
    ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(superposition,[status(thm)],[c_548,c_22054])).

cnf(c_17,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_23166,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[status(thm)],[c_22844,c_17])).

cnf(c_13,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_552,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_813,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_552,c_553])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1329,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_813,c_0])).

cnf(c_1355,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1329,c_17])).

cnf(c_16,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1017,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_17,c_11])).

cnf(c_1541,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_16,c_1017])).

cnf(c_2150,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1355,c_1541])).

cnf(c_14,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1357,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_1329,c_14])).

cnf(c_1362,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_1357,c_1329])).

cnf(c_2490,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1362,c_2150])).

cnf(c_2493,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_2150,c_2490])).

cnf(c_2500,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_2493,c_2150])).

cnf(c_15,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2652,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_2500,c_15])).

cnf(c_2661,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),X0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_2652,c_2500])).

cnf(c_10,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_554,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_812,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_554,c_553])).

cnf(c_2663,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2661,c_812,c_813,c_1329,c_2493])).

cnf(c_23183,plain,
    ( k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK2 ),
    inference(demodulation,[status(thm)],[c_23166,c_2493,c_2663])).

cnf(c_1011,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_16,c_17])).

cnf(c_21,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) != sK2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3070,plain,
    ( k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK2 ),
    inference(demodulation,[status(thm)],[c_1011,c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23183,c_3070])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:26:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 6.72/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.72/1.50  
% 6.72/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.72/1.50  
% 6.72/1.50  ------  iProver source info
% 6.72/1.50  
% 6.72/1.50  git: date: 2020-06-30 10:37:57 +0100
% 6.72/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.72/1.50  git: non_committed_changes: false
% 6.72/1.50  git: last_make_outside_of_git: false
% 6.72/1.50  
% 6.72/1.50  ------ 
% 6.72/1.50  
% 6.72/1.50  ------ Input Options
% 6.72/1.50  
% 6.72/1.50  --out_options                           all
% 6.72/1.50  --tptp_safe_out                         true
% 6.72/1.50  --problem_path                          ""
% 6.72/1.50  --include_path                          ""
% 6.72/1.50  --clausifier                            res/vclausify_rel
% 6.72/1.50  --clausifier_options                    --mode clausify
% 6.72/1.50  --stdin                                 false
% 6.72/1.50  --stats_out                             all
% 6.72/1.50  
% 6.72/1.50  ------ General Options
% 6.72/1.50  
% 6.72/1.50  --fof                                   false
% 6.72/1.50  --time_out_real                         305.
% 6.72/1.50  --time_out_virtual                      -1.
% 6.72/1.50  --symbol_type_check                     false
% 6.72/1.50  --clausify_out                          false
% 6.72/1.50  --sig_cnt_out                           false
% 6.72/1.50  --trig_cnt_out                          false
% 6.72/1.50  --trig_cnt_out_tolerance                1.
% 6.72/1.50  --trig_cnt_out_sk_spl                   false
% 6.72/1.50  --abstr_cl_out                          false
% 6.72/1.50  
% 6.72/1.50  ------ Global Options
% 6.72/1.50  
% 6.72/1.50  --schedule                              default
% 6.72/1.50  --add_important_lit                     false
% 6.72/1.50  --prop_solver_per_cl                    1000
% 6.72/1.50  --min_unsat_core                        false
% 6.72/1.50  --soft_assumptions                      false
% 6.72/1.50  --soft_lemma_size                       3
% 6.72/1.50  --prop_impl_unit_size                   0
% 6.72/1.50  --prop_impl_unit                        []
% 6.72/1.50  --share_sel_clauses                     true
% 6.72/1.50  --reset_solvers                         false
% 6.72/1.50  --bc_imp_inh                            [conj_cone]
% 6.72/1.50  --conj_cone_tolerance                   3.
% 6.72/1.50  --extra_neg_conj                        none
% 6.72/1.50  --large_theory_mode                     true
% 6.72/1.50  --prolific_symb_bound                   200
% 6.72/1.50  --lt_threshold                          2000
% 6.72/1.50  --clause_weak_htbl                      true
% 6.72/1.50  --gc_record_bc_elim                     false
% 6.72/1.50  
% 6.72/1.50  ------ Preprocessing Options
% 6.72/1.50  
% 6.72/1.50  --preprocessing_flag                    true
% 6.72/1.50  --time_out_prep_mult                    0.1
% 6.72/1.50  --splitting_mode                        input
% 6.72/1.50  --splitting_grd                         true
% 6.72/1.50  --splitting_cvd                         false
% 6.72/1.50  --splitting_cvd_svl                     false
% 6.72/1.50  --splitting_nvd                         32
% 6.72/1.50  --sub_typing                            true
% 6.72/1.50  --prep_gs_sim                           true
% 6.72/1.50  --prep_unflatten                        true
% 6.72/1.50  --prep_res_sim                          true
% 6.72/1.50  --prep_upred                            true
% 6.72/1.50  --prep_sem_filter                       exhaustive
% 6.72/1.50  --prep_sem_filter_out                   false
% 6.72/1.50  --pred_elim                             true
% 6.72/1.50  --res_sim_input                         true
% 6.72/1.50  --eq_ax_congr_red                       true
% 6.72/1.50  --pure_diseq_elim                       true
% 6.72/1.50  --brand_transform                       false
% 6.72/1.50  --non_eq_to_eq                          false
% 6.72/1.50  --prep_def_merge                        true
% 6.72/1.50  --prep_def_merge_prop_impl              false
% 6.72/1.50  --prep_def_merge_mbd                    true
% 6.72/1.50  --prep_def_merge_tr_red                 false
% 6.72/1.50  --prep_def_merge_tr_cl                  false
% 6.72/1.50  --smt_preprocessing                     true
% 6.72/1.50  --smt_ac_axioms                         fast
% 6.72/1.50  --preprocessed_out                      false
% 6.72/1.50  --preprocessed_stats                    false
% 6.72/1.50  
% 6.72/1.50  ------ Abstraction refinement Options
% 6.72/1.50  
% 6.72/1.50  --abstr_ref                             []
% 6.72/1.50  --abstr_ref_prep                        false
% 6.72/1.50  --abstr_ref_until_sat                   false
% 6.72/1.50  --abstr_ref_sig_restrict                funpre
% 6.72/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 6.72/1.50  --abstr_ref_under                       []
% 6.72/1.50  
% 6.72/1.50  ------ SAT Options
% 6.72/1.50  
% 6.72/1.50  --sat_mode                              false
% 6.72/1.50  --sat_fm_restart_options                ""
% 6.72/1.50  --sat_gr_def                            false
% 6.72/1.50  --sat_epr_types                         true
% 6.72/1.50  --sat_non_cyclic_types                  false
% 6.72/1.50  --sat_finite_models                     false
% 6.72/1.50  --sat_fm_lemmas                         false
% 6.72/1.50  --sat_fm_prep                           false
% 6.72/1.50  --sat_fm_uc_incr                        true
% 6.72/1.50  --sat_out_model                         small
% 6.72/1.50  --sat_out_clauses                       false
% 6.72/1.50  
% 6.72/1.50  ------ QBF Options
% 6.72/1.50  
% 6.72/1.50  --qbf_mode                              false
% 6.72/1.50  --qbf_elim_univ                         false
% 6.72/1.50  --qbf_dom_inst                          none
% 6.72/1.50  --qbf_dom_pre_inst                      false
% 6.72/1.50  --qbf_sk_in                             false
% 6.72/1.50  --qbf_pred_elim                         true
% 6.72/1.50  --qbf_split                             512
% 6.72/1.50  
% 6.72/1.50  ------ BMC1 Options
% 6.72/1.50  
% 6.72/1.50  --bmc1_incremental                      false
% 6.72/1.50  --bmc1_axioms                           reachable_all
% 6.72/1.50  --bmc1_min_bound                        0
% 6.72/1.50  --bmc1_max_bound                        -1
% 6.72/1.50  --bmc1_max_bound_default                -1
% 6.72/1.50  --bmc1_symbol_reachability              true
% 6.72/1.50  --bmc1_property_lemmas                  false
% 6.72/1.50  --bmc1_k_induction                      false
% 6.72/1.50  --bmc1_non_equiv_states                 false
% 6.72/1.50  --bmc1_deadlock                         false
% 6.72/1.50  --bmc1_ucm                              false
% 6.72/1.50  --bmc1_add_unsat_core                   none
% 6.72/1.50  --bmc1_unsat_core_children              false
% 6.72/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 6.72/1.50  --bmc1_out_stat                         full
% 6.72/1.50  --bmc1_ground_init                      false
% 6.72/1.50  --bmc1_pre_inst_next_state              false
% 6.72/1.50  --bmc1_pre_inst_state                   false
% 6.72/1.50  --bmc1_pre_inst_reach_state             false
% 6.72/1.50  --bmc1_out_unsat_core                   false
% 6.72/1.50  --bmc1_aig_witness_out                  false
% 6.72/1.50  --bmc1_verbose                          false
% 6.72/1.50  --bmc1_dump_clauses_tptp                false
% 6.72/1.50  --bmc1_dump_unsat_core_tptp             false
% 6.72/1.50  --bmc1_dump_file                        -
% 6.72/1.50  --bmc1_ucm_expand_uc_limit              128
% 6.72/1.50  --bmc1_ucm_n_expand_iterations          6
% 6.72/1.50  --bmc1_ucm_extend_mode                  1
% 6.72/1.50  --bmc1_ucm_init_mode                    2
% 6.72/1.50  --bmc1_ucm_cone_mode                    none
% 6.72/1.50  --bmc1_ucm_reduced_relation_type        0
% 6.72/1.50  --bmc1_ucm_relax_model                  4
% 6.72/1.50  --bmc1_ucm_full_tr_after_sat            true
% 6.72/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 6.72/1.50  --bmc1_ucm_layered_model                none
% 6.72/1.50  --bmc1_ucm_max_lemma_size               10
% 6.72/1.50  
% 6.72/1.50  ------ AIG Options
% 6.72/1.50  
% 6.72/1.50  --aig_mode                              false
% 6.72/1.50  
% 6.72/1.50  ------ Instantiation Options
% 6.72/1.50  
% 6.72/1.50  --instantiation_flag                    true
% 6.72/1.50  --inst_sos_flag                         false
% 6.72/1.50  --inst_sos_phase                        true
% 6.72/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.72/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.72/1.50  --inst_lit_sel_side                     num_symb
% 6.72/1.50  --inst_solver_per_active                1400
% 6.72/1.50  --inst_solver_calls_frac                1.
% 6.72/1.50  --inst_passive_queue_type               priority_queues
% 6.72/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.72/1.50  --inst_passive_queues_freq              [25;2]
% 6.72/1.50  --inst_dismatching                      true
% 6.72/1.50  --inst_eager_unprocessed_to_passive     true
% 6.72/1.50  --inst_prop_sim_given                   true
% 6.72/1.50  --inst_prop_sim_new                     false
% 6.72/1.50  --inst_subs_new                         false
% 6.72/1.50  --inst_eq_res_simp                      false
% 6.72/1.50  --inst_subs_given                       false
% 6.72/1.50  --inst_orphan_elimination               true
% 6.72/1.50  --inst_learning_loop_flag               true
% 6.72/1.50  --inst_learning_start                   3000
% 6.72/1.50  --inst_learning_factor                  2
% 6.72/1.50  --inst_start_prop_sim_after_learn       3
% 6.72/1.50  --inst_sel_renew                        solver
% 6.72/1.50  --inst_lit_activity_flag                true
% 6.72/1.50  --inst_restr_to_given                   false
% 6.72/1.50  --inst_activity_threshold               500
% 6.72/1.50  --inst_out_proof                        true
% 6.72/1.50  
% 6.72/1.50  ------ Resolution Options
% 6.72/1.50  
% 6.72/1.50  --resolution_flag                       true
% 6.72/1.50  --res_lit_sel                           adaptive
% 6.72/1.50  --res_lit_sel_side                      none
% 6.72/1.50  --res_ordering                          kbo
% 6.72/1.50  --res_to_prop_solver                    active
% 6.72/1.50  --res_prop_simpl_new                    false
% 6.72/1.50  --res_prop_simpl_given                  true
% 6.72/1.50  --res_passive_queue_type                priority_queues
% 6.72/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.72/1.50  --res_passive_queues_freq               [15;5]
% 6.72/1.50  --res_forward_subs                      full
% 6.72/1.50  --res_backward_subs                     full
% 6.72/1.50  --res_forward_subs_resolution           true
% 6.72/1.50  --res_backward_subs_resolution          true
% 6.72/1.50  --res_orphan_elimination                true
% 6.72/1.50  --res_time_limit                        2.
% 6.72/1.50  --res_out_proof                         true
% 6.72/1.50  
% 6.72/1.50  ------ Superposition Options
% 6.72/1.50  
% 6.72/1.50  --superposition_flag                    true
% 6.72/1.50  --sup_passive_queue_type                priority_queues
% 6.72/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.72/1.50  --sup_passive_queues_freq               [8;1;4]
% 6.72/1.50  --demod_completeness_check              fast
% 6.72/1.50  --demod_use_ground                      true
% 6.72/1.50  --sup_to_prop_solver                    passive
% 6.72/1.50  --sup_prop_simpl_new                    true
% 6.72/1.50  --sup_prop_simpl_given                  true
% 6.72/1.50  --sup_fun_splitting                     false
% 6.72/1.50  --sup_smt_interval                      50000
% 6.72/1.50  
% 6.72/1.50  ------ Superposition Simplification Setup
% 6.72/1.50  
% 6.72/1.50  --sup_indices_passive                   []
% 6.72/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.72/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.72/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.72/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 6.72/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.72/1.50  --sup_full_bw                           [BwDemod]
% 6.72/1.50  --sup_immed_triv                        [TrivRules]
% 6.72/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.72/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.72/1.50  --sup_immed_bw_main                     []
% 6.72/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.72/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 6.72/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.72/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.72/1.50  
% 6.72/1.50  ------ Combination Options
% 6.72/1.50  
% 6.72/1.50  --comb_res_mult                         3
% 6.72/1.50  --comb_sup_mult                         2
% 6.72/1.50  --comb_inst_mult                        10
% 6.72/1.50  
% 6.72/1.50  ------ Debug Options
% 6.72/1.50  
% 6.72/1.50  --dbg_backtrace                         false
% 6.72/1.50  --dbg_dump_prop_clauses                 false
% 6.72/1.50  --dbg_dump_prop_clauses_file            -
% 6.72/1.50  --dbg_out_stat                          false
% 6.72/1.50  ------ Parsing...
% 6.72/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.72/1.50  
% 6.72/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.72/1.50  
% 6.72/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.72/1.50  
% 6.72/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.72/1.50  ------ Proving...
% 6.72/1.50  ------ Problem Properties 
% 6.72/1.50  
% 6.72/1.50  
% 6.72/1.50  clauses                                 22
% 6.72/1.50  conjectures                             2
% 6.72/1.50  EPR                                     5
% 6.72/1.50  Horn                                    18
% 6.72/1.50  unary                                   10
% 6.72/1.50  binary                                  5
% 6.72/1.50  lits                                    41
% 6.72/1.50  lits eq                                 9
% 6.72/1.50  fd_pure                                 0
% 6.72/1.50  fd_pseudo                               0
% 6.72/1.50  fd_cond                                 0
% 6.72/1.50  fd_pseudo_cond                          1
% 6.72/1.50  AC symbols                              0
% 6.72/1.50  
% 6.72/1.50  ------ Schedule dynamic 5 is on 
% 6.72/1.50  
% 6.72/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.72/1.50  
% 6.72/1.50  
% 6.72/1.50  ------ 
% 6.72/1.50  Current options:
% 6.72/1.50  ------ 
% 6.72/1.50  
% 6.72/1.50  ------ Input Options
% 6.72/1.50  
% 6.72/1.50  --out_options                           all
% 6.72/1.50  --tptp_safe_out                         true
% 6.72/1.50  --problem_path                          ""
% 6.72/1.50  --include_path                          ""
% 6.72/1.50  --clausifier                            res/vclausify_rel
% 6.72/1.50  --clausifier_options                    --mode clausify
% 6.72/1.50  --stdin                                 false
% 6.72/1.50  --stats_out                             all
% 6.72/1.50  
% 6.72/1.50  ------ General Options
% 6.72/1.51  
% 6.72/1.51  --fof                                   false
% 6.72/1.51  --time_out_real                         305.
% 6.72/1.51  --time_out_virtual                      -1.
% 6.72/1.51  --symbol_type_check                     false
% 6.72/1.51  --clausify_out                          false
% 6.72/1.51  --sig_cnt_out                           false
% 6.72/1.51  --trig_cnt_out                          false
% 6.72/1.51  --trig_cnt_out_tolerance                1.
% 6.72/1.51  --trig_cnt_out_sk_spl                   false
% 6.72/1.51  --abstr_cl_out                          false
% 6.72/1.51  
% 6.72/1.51  ------ Global Options
% 6.72/1.51  
% 6.72/1.51  --schedule                              default
% 6.72/1.51  --add_important_lit                     false
% 6.72/1.51  --prop_solver_per_cl                    1000
% 6.72/1.51  --min_unsat_core                        false
% 6.72/1.51  --soft_assumptions                      false
% 6.72/1.51  --soft_lemma_size                       3
% 6.72/1.51  --prop_impl_unit_size                   0
% 6.72/1.51  --prop_impl_unit                        []
% 6.72/1.51  --share_sel_clauses                     true
% 6.72/1.51  --reset_solvers                         false
% 6.72/1.51  --bc_imp_inh                            [conj_cone]
% 6.72/1.51  --conj_cone_tolerance                   3.
% 6.72/1.51  --extra_neg_conj                        none
% 6.72/1.51  --large_theory_mode                     true
% 6.72/1.51  --prolific_symb_bound                   200
% 6.72/1.51  --lt_threshold                          2000
% 6.72/1.51  --clause_weak_htbl                      true
% 6.72/1.51  --gc_record_bc_elim                     false
% 6.72/1.51  
% 6.72/1.51  ------ Preprocessing Options
% 6.72/1.51  
% 6.72/1.51  --preprocessing_flag                    true
% 6.72/1.51  --time_out_prep_mult                    0.1
% 6.72/1.51  --splitting_mode                        input
% 6.72/1.51  --splitting_grd                         true
% 6.72/1.51  --splitting_cvd                         false
% 6.72/1.51  --splitting_cvd_svl                     false
% 6.72/1.51  --splitting_nvd                         32
% 6.72/1.51  --sub_typing                            true
% 6.72/1.51  --prep_gs_sim                           true
% 6.72/1.51  --prep_unflatten                        true
% 6.72/1.51  --prep_res_sim                          true
% 6.72/1.51  --prep_upred                            true
% 6.72/1.51  --prep_sem_filter                       exhaustive
% 6.72/1.51  --prep_sem_filter_out                   false
% 6.72/1.51  --pred_elim                             true
% 6.72/1.51  --res_sim_input                         true
% 6.72/1.51  --eq_ax_congr_red                       true
% 6.72/1.51  --pure_diseq_elim                       true
% 6.72/1.51  --brand_transform                       false
% 6.72/1.51  --non_eq_to_eq                          false
% 6.72/1.51  --prep_def_merge                        true
% 6.72/1.51  --prep_def_merge_prop_impl              false
% 6.72/1.51  --prep_def_merge_mbd                    true
% 6.72/1.51  --prep_def_merge_tr_red                 false
% 6.72/1.51  --prep_def_merge_tr_cl                  false
% 6.72/1.51  --smt_preprocessing                     true
% 6.72/1.51  --smt_ac_axioms                         fast
% 6.72/1.51  --preprocessed_out                      false
% 6.72/1.51  --preprocessed_stats                    false
% 6.72/1.51  
% 6.72/1.51  ------ Abstraction refinement Options
% 6.72/1.51  
% 6.72/1.51  --abstr_ref                             []
% 6.72/1.51  --abstr_ref_prep                        false
% 6.72/1.51  --abstr_ref_until_sat                   false
% 6.72/1.51  --abstr_ref_sig_restrict                funpre
% 6.72/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 6.72/1.51  --abstr_ref_under                       []
% 6.72/1.51  
% 6.72/1.51  ------ SAT Options
% 6.72/1.51  
% 6.72/1.51  --sat_mode                              false
% 6.72/1.51  --sat_fm_restart_options                ""
% 6.72/1.51  --sat_gr_def                            false
% 6.72/1.51  --sat_epr_types                         true
% 6.72/1.51  --sat_non_cyclic_types                  false
% 6.72/1.51  --sat_finite_models                     false
% 6.72/1.51  --sat_fm_lemmas                         false
% 6.72/1.51  --sat_fm_prep                           false
% 6.72/1.51  --sat_fm_uc_incr                        true
% 6.72/1.51  --sat_out_model                         small
% 6.72/1.51  --sat_out_clauses                       false
% 6.72/1.51  
% 6.72/1.51  ------ QBF Options
% 6.72/1.51  
% 6.72/1.51  --qbf_mode                              false
% 6.72/1.51  --qbf_elim_univ                         false
% 6.72/1.51  --qbf_dom_inst                          none
% 6.72/1.51  --qbf_dom_pre_inst                      false
% 6.72/1.51  --qbf_sk_in                             false
% 6.72/1.51  --qbf_pred_elim                         true
% 6.72/1.51  --qbf_split                             512
% 6.72/1.51  
% 6.72/1.51  ------ BMC1 Options
% 6.72/1.51  
% 6.72/1.51  --bmc1_incremental                      false
% 6.72/1.51  --bmc1_axioms                           reachable_all
% 6.72/1.51  --bmc1_min_bound                        0
% 6.72/1.51  --bmc1_max_bound                        -1
% 6.72/1.51  --bmc1_max_bound_default                -1
% 6.72/1.51  --bmc1_symbol_reachability              true
% 6.72/1.51  --bmc1_property_lemmas                  false
% 6.72/1.51  --bmc1_k_induction                      false
% 6.72/1.51  --bmc1_non_equiv_states                 false
% 6.72/1.51  --bmc1_deadlock                         false
% 6.72/1.51  --bmc1_ucm                              false
% 6.72/1.51  --bmc1_add_unsat_core                   none
% 6.72/1.51  --bmc1_unsat_core_children              false
% 6.72/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 6.72/1.51  --bmc1_out_stat                         full
% 6.72/1.51  --bmc1_ground_init                      false
% 6.72/1.51  --bmc1_pre_inst_next_state              false
% 6.72/1.51  --bmc1_pre_inst_state                   false
% 6.72/1.51  --bmc1_pre_inst_reach_state             false
% 6.72/1.51  --bmc1_out_unsat_core                   false
% 6.72/1.51  --bmc1_aig_witness_out                  false
% 6.72/1.51  --bmc1_verbose                          false
% 6.72/1.51  --bmc1_dump_clauses_tptp                false
% 6.72/1.51  --bmc1_dump_unsat_core_tptp             false
% 6.72/1.51  --bmc1_dump_file                        -
% 6.72/1.51  --bmc1_ucm_expand_uc_limit              128
% 6.72/1.51  --bmc1_ucm_n_expand_iterations          6
% 6.72/1.51  --bmc1_ucm_extend_mode                  1
% 6.72/1.51  --bmc1_ucm_init_mode                    2
% 6.72/1.51  --bmc1_ucm_cone_mode                    none
% 6.72/1.51  --bmc1_ucm_reduced_relation_type        0
% 6.72/1.51  --bmc1_ucm_relax_model                  4
% 6.72/1.51  --bmc1_ucm_full_tr_after_sat            true
% 6.72/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 6.72/1.51  --bmc1_ucm_layered_model                none
% 6.72/1.51  --bmc1_ucm_max_lemma_size               10
% 6.72/1.51  
% 6.72/1.51  ------ AIG Options
% 6.72/1.51  
% 6.72/1.51  --aig_mode                              false
% 6.72/1.51  
% 6.72/1.51  ------ Instantiation Options
% 6.72/1.51  
% 6.72/1.51  --instantiation_flag                    true
% 6.72/1.51  --inst_sos_flag                         false
% 6.72/1.51  --inst_sos_phase                        true
% 6.72/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.72/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.72/1.51  --inst_lit_sel_side                     none
% 6.72/1.51  --inst_solver_per_active                1400
% 6.72/1.51  --inst_solver_calls_frac                1.
% 6.72/1.51  --inst_passive_queue_type               priority_queues
% 6.72/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.72/1.51  --inst_passive_queues_freq              [25;2]
% 6.72/1.51  --inst_dismatching                      true
% 6.72/1.51  --inst_eager_unprocessed_to_passive     true
% 6.72/1.51  --inst_prop_sim_given                   true
% 6.72/1.51  --inst_prop_sim_new                     false
% 6.72/1.51  --inst_subs_new                         false
% 6.72/1.51  --inst_eq_res_simp                      false
% 6.72/1.51  --inst_subs_given                       false
% 6.72/1.51  --inst_orphan_elimination               true
% 6.72/1.51  --inst_learning_loop_flag               true
% 6.72/1.51  --inst_learning_start                   3000
% 6.72/1.51  --inst_learning_factor                  2
% 6.72/1.51  --inst_start_prop_sim_after_learn       3
% 6.72/1.51  --inst_sel_renew                        solver
% 6.72/1.51  --inst_lit_activity_flag                true
% 6.72/1.51  --inst_restr_to_given                   false
% 6.72/1.51  --inst_activity_threshold               500
% 6.72/1.51  --inst_out_proof                        true
% 6.72/1.51  
% 6.72/1.51  ------ Resolution Options
% 6.72/1.51  
% 6.72/1.51  --resolution_flag                       false
% 6.72/1.51  --res_lit_sel                           adaptive
% 6.72/1.51  --res_lit_sel_side                      none
% 6.72/1.51  --res_ordering                          kbo
% 6.72/1.51  --res_to_prop_solver                    active
% 6.72/1.51  --res_prop_simpl_new                    false
% 6.72/1.51  --res_prop_simpl_given                  true
% 6.72/1.51  --res_passive_queue_type                priority_queues
% 6.72/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.72/1.51  --res_passive_queues_freq               [15;5]
% 6.72/1.51  --res_forward_subs                      full
% 6.72/1.51  --res_backward_subs                     full
% 6.72/1.51  --res_forward_subs_resolution           true
% 6.72/1.51  --res_backward_subs_resolution          true
% 6.72/1.51  --res_orphan_elimination                true
% 6.72/1.51  --res_time_limit                        2.
% 6.72/1.51  --res_out_proof                         true
% 6.72/1.51  
% 6.72/1.51  ------ Superposition Options
% 6.72/1.51  
% 6.72/1.51  --superposition_flag                    true
% 6.72/1.51  --sup_passive_queue_type                priority_queues
% 6.72/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.72/1.51  --sup_passive_queues_freq               [8;1;4]
% 6.72/1.51  --demod_completeness_check              fast
% 6.72/1.51  --demod_use_ground                      true
% 6.72/1.51  --sup_to_prop_solver                    passive
% 6.72/1.51  --sup_prop_simpl_new                    true
% 6.72/1.51  --sup_prop_simpl_given                  true
% 6.72/1.51  --sup_fun_splitting                     false
% 6.72/1.51  --sup_smt_interval                      50000
% 6.72/1.51  
% 6.72/1.51  ------ Superposition Simplification Setup
% 6.72/1.51  
% 6.72/1.51  --sup_indices_passive                   []
% 6.72/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.72/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.72/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.72/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 6.72/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.72/1.51  --sup_full_bw                           [BwDemod]
% 6.72/1.51  --sup_immed_triv                        [TrivRules]
% 6.72/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.72/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.72/1.51  --sup_immed_bw_main                     []
% 6.72/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.72/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 6.72/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.72/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.72/1.51  
% 6.72/1.51  ------ Combination Options
% 6.72/1.51  
% 6.72/1.51  --comb_res_mult                         3
% 6.72/1.51  --comb_sup_mult                         2
% 6.72/1.51  --comb_inst_mult                        10
% 6.72/1.51  
% 6.72/1.51  ------ Debug Options
% 6.72/1.51  
% 6.72/1.51  --dbg_backtrace                         false
% 6.72/1.51  --dbg_dump_prop_clauses                 false
% 6.72/1.51  --dbg_dump_prop_clauses_file            -
% 6.72/1.51  --dbg_out_stat                          false
% 6.72/1.51  
% 6.72/1.51  
% 6.72/1.51  
% 6.72/1.51  
% 6.72/1.51  ------ Proving...
% 6.72/1.51  
% 6.72/1.51  
% 6.72/1.51  % SZS status Theorem for theBenchmark.p
% 6.72/1.51  
% 6.72/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 6.72/1.51  
% 6.72/1.51  fof(f19,conjecture,(
% 6.72/1.51    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 6.72/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.72/1.51  
% 6.72/1.51  fof(f20,negated_conjecture,(
% 6.72/1.51    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 6.72/1.51    inference(negated_conjecture,[],[f19])).
% 6.72/1.51  
% 6.72/1.51  fof(f24,plain,(
% 6.72/1.51    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 6.72/1.51    inference(ennf_transformation,[],[f20])).
% 6.72/1.51  
% 6.72/1.51  fof(f34,plain,(
% 6.72/1.51    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k1_tarski(sK1),sK2) != sK2 & r2_hidden(sK1,sK2))),
% 6.72/1.51    introduced(choice_axiom,[])).
% 6.72/1.51  
% 6.72/1.51  fof(f35,plain,(
% 6.72/1.51    k2_xboole_0(k1_tarski(sK1),sK2) != sK2 & r2_hidden(sK1,sK2)),
% 6.72/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f34])).
% 6.72/1.51  
% 6.72/1.51  fof(f63,plain,(
% 6.72/1.51    r2_hidden(sK1,sK2)),
% 6.72/1.51    inference(cnf_transformation,[],[f35])).
% 6.72/1.51  
% 6.72/1.51  fof(f18,axiom,(
% 6.72/1.51    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 6.72/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.72/1.51  
% 6.72/1.51  fof(f32,plain,(
% 6.72/1.51    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 6.72/1.51    inference(nnf_transformation,[],[f18])).
% 6.72/1.51  
% 6.72/1.51  fof(f33,plain,(
% 6.72/1.51    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 6.72/1.51    inference(flattening,[],[f32])).
% 6.72/1.51  
% 6.72/1.51  fof(f62,plain,(
% 6.72/1.51    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 6.72/1.51    inference(cnf_transformation,[],[f33])).
% 6.72/1.51  
% 6.72/1.51  fof(f14,axiom,(
% 6.72/1.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.72/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.72/1.51  
% 6.72/1.51  fof(f56,plain,(
% 6.72/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 6.72/1.51    inference(cnf_transformation,[],[f14])).
% 6.72/1.51  
% 6.72/1.51  fof(f15,axiom,(
% 6.72/1.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.72/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.72/1.51  
% 6.72/1.51  fof(f57,plain,(
% 6.72/1.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.72/1.51    inference(cnf_transformation,[],[f15])).
% 6.72/1.51  
% 6.72/1.51  fof(f16,axiom,(
% 6.72/1.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 6.72/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.72/1.51  
% 6.72/1.51  fof(f58,plain,(
% 6.72/1.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 6.72/1.51    inference(cnf_transformation,[],[f16])).
% 6.72/1.51  
% 6.72/1.51  fof(f66,plain,(
% 6.72/1.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 6.72/1.51    inference(definition_unfolding,[],[f57,f58])).
% 6.72/1.51  
% 6.72/1.51  fof(f67,plain,(
% 6.72/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 6.72/1.51    inference(definition_unfolding,[],[f56,f66])).
% 6.72/1.51  
% 6.72/1.51  fof(f74,plain,(
% 6.72/1.51    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 6.72/1.51    inference(definition_unfolding,[],[f62,f67])).
% 6.72/1.51  
% 6.72/1.51  fof(f7,axiom,(
% 6.72/1.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 6.72/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.72/1.51  
% 6.72/1.51  fof(f23,plain,(
% 6.72/1.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 6.72/1.51    inference(ennf_transformation,[],[f7])).
% 6.72/1.51  
% 6.72/1.51  fof(f49,plain,(
% 6.72/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 6.72/1.51    inference(cnf_transformation,[],[f23])).
% 6.72/1.51  
% 6.72/1.51  fof(f17,axiom,(
% 6.72/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 6.72/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.72/1.51  
% 6.72/1.51  fof(f59,plain,(
% 6.72/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 6.72/1.51    inference(cnf_transformation,[],[f17])).
% 6.72/1.51  
% 6.72/1.51  fof(f11,axiom,(
% 6.72/1.51    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 6.72/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.72/1.51  
% 6.72/1.51  fof(f53,plain,(
% 6.72/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 6.72/1.51    inference(cnf_transformation,[],[f11])).
% 6.72/1.51  
% 6.72/1.51  fof(f5,axiom,(
% 6.72/1.51    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 6.72/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.72/1.51  
% 6.72/1.51  fof(f47,plain,(
% 6.72/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 6.72/1.51    inference(cnf_transformation,[],[f5])).
% 6.72/1.51  
% 6.72/1.51  fof(f65,plain,(
% 6.72/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 6.72/1.51    inference(definition_unfolding,[],[f53,f47])).
% 6.72/1.51  
% 6.72/1.51  fof(f73,plain,(
% 6.72/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 6.72/1.51    inference(definition_unfolding,[],[f59,f65,f67])).
% 6.72/1.51  
% 6.72/1.51  fof(f8,axiom,(
% 6.72/1.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 6.72/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.72/1.51  
% 6.72/1.51  fof(f50,plain,(
% 6.72/1.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 6.72/1.51    inference(cnf_transformation,[],[f8])).
% 6.72/1.51  
% 6.72/1.51  fof(f1,axiom,(
% 6.72/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.72/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.72/1.51  
% 6.72/1.51  fof(f36,plain,(
% 6.72/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.72/1.51    inference(cnf_transformation,[],[f1])).
% 6.72/1.51  
% 6.72/1.51  fof(f12,axiom,(
% 6.72/1.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 6.72/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.72/1.51  
% 6.72/1.51  fof(f54,plain,(
% 6.72/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 6.72/1.51    inference(cnf_transformation,[],[f12])).
% 6.72/1.51  
% 6.72/1.51  fof(f72,plain,(
% 6.72/1.51    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 6.72/1.51    inference(definition_unfolding,[],[f54,f67,f67])).
% 6.72/1.51  
% 6.72/1.51  fof(f6,axiom,(
% 6.72/1.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 6.72/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.72/1.51  
% 6.72/1.51  fof(f48,plain,(
% 6.72/1.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.72/1.51    inference(cnf_transformation,[],[f6])).
% 6.72/1.51  
% 6.72/1.51  fof(f69,plain,(
% 6.72/1.51    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 6.72/1.51    inference(definition_unfolding,[],[f48,f65])).
% 6.72/1.51  
% 6.72/1.51  fof(f9,axiom,(
% 6.72/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 6.72/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.72/1.51  
% 6.72/1.51  fof(f51,plain,(
% 6.72/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 6.72/1.51    inference(cnf_transformation,[],[f9])).
% 6.72/1.51  
% 6.72/1.51  fof(f70,plain,(
% 6.72/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0)))) )),
% 6.72/1.51    inference(definition_unfolding,[],[f51,f65,f65,f47])).
% 6.72/1.51  
% 6.72/1.51  fof(f10,axiom,(
% 6.72/1.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 6.72/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.72/1.51  
% 6.72/1.51  fof(f52,plain,(
% 6.72/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 6.72/1.51    inference(cnf_transformation,[],[f10])).
% 6.72/1.51  
% 6.72/1.51  fof(f71,plain,(
% 6.72/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1))) )),
% 6.72/1.51    inference(definition_unfolding,[],[f52,f47,f47,f65])).
% 6.72/1.51  
% 6.72/1.51  fof(f4,axiom,(
% 6.72/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.72/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.72/1.51  
% 6.72/1.51  fof(f30,plain,(
% 6.72/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.72/1.51    inference(nnf_transformation,[],[f4])).
% 6.72/1.51  
% 6.72/1.51  fof(f31,plain,(
% 6.72/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.72/1.51    inference(flattening,[],[f30])).
% 6.72/1.51  
% 6.72/1.51  fof(f44,plain,(
% 6.72/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 6.72/1.51    inference(cnf_transformation,[],[f31])).
% 6.72/1.51  
% 6.72/1.51  fof(f79,plain,(
% 6.72/1.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.72/1.51    inference(equality_resolution,[],[f44])).
% 6.72/1.51  
% 6.72/1.51  fof(f64,plain,(
% 6.72/1.51    k2_xboole_0(k1_tarski(sK1),sK2) != sK2),
% 6.72/1.51    inference(cnf_transformation,[],[f35])).
% 6.72/1.51  
% 6.72/1.51  fof(f13,axiom,(
% 6.72/1.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 6.72/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.72/1.51  
% 6.72/1.51  fof(f55,plain,(
% 6.72/1.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 6.72/1.51    inference(cnf_transformation,[],[f13])).
% 6.72/1.51  
% 6.72/1.51  fof(f68,plain,(
% 6.72/1.51    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 6.72/1.51    inference(definition_unfolding,[],[f55,f67])).
% 6.72/1.51  
% 6.72/1.51  fof(f77,plain,(
% 6.72/1.51    k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) != sK2),
% 6.72/1.51    inference(definition_unfolding,[],[f64,f65,f68])).
% 6.72/1.51  
% 6.72/1.51  cnf(c_22,negated_conjecture,
% 6.72/1.51      ( r2_hidden(sK1,sK2) ),
% 6.72/1.51      inference(cnf_transformation,[],[f63]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_548,plain,
% 6.72/1.51      ( r2_hidden(sK1,sK2) = iProver_top ),
% 6.72/1.51      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_18,plain,
% 6.72/1.51      ( ~ r2_hidden(X0,X1)
% 6.72/1.51      | ~ r2_hidden(X2,X1)
% 6.72/1.51      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X2),X1) ),
% 6.72/1.51      inference(cnf_transformation,[],[f74]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_551,plain,
% 6.72/1.51      ( r2_hidden(X0,X1) != iProver_top
% 6.72/1.51      | r2_hidden(X2,X1) != iProver_top
% 6.72/1.51      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X2),X1) = iProver_top ),
% 6.72/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_12,plain,
% 6.72/1.51      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 6.72/1.51      inference(cnf_transformation,[],[f49]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_553,plain,
% 6.72/1.51      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 6.72/1.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_3057,plain,
% 6.72/1.51      ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
% 6.72/1.51      | r2_hidden(X0,X2) != iProver_top
% 6.72/1.51      | r2_hidden(X1,X2) != iProver_top ),
% 6.72/1.51      inference(superposition,[status(thm)],[c_551,c_553]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_22054,plain,
% 6.72/1.51      ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,X0),sK2) = k3_enumset1(sK1,sK1,sK1,sK1,X0)
% 6.72/1.51      | r2_hidden(X0,sK2) != iProver_top ),
% 6.72/1.51      inference(superposition,[status(thm)],[c_548,c_3057]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_22844,plain,
% 6.72/1.51      ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
% 6.72/1.51      inference(superposition,[status(thm)],[c_548,c_22054]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_17,plain,
% 6.72/1.51      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 6.72/1.51      inference(cnf_transformation,[],[f73]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_23166,plain,
% 6.72/1.51      ( k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
% 6.72/1.51      inference(superposition,[status(thm)],[c_22844,c_17]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_13,plain,
% 6.72/1.51      ( r1_tarski(k1_xboole_0,X0) ),
% 6.72/1.51      inference(cnf_transformation,[],[f50]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_552,plain,
% 6.72/1.51      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 6.72/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_813,plain,
% 6.72/1.51      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 6.72/1.51      inference(superposition,[status(thm)],[c_552,c_553]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_0,plain,
% 6.72/1.51      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 6.72/1.51      inference(cnf_transformation,[],[f36]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_1329,plain,
% 6.72/1.51      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 6.72/1.51      inference(superposition,[status(thm)],[c_813,c_0]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_1355,plain,
% 6.72/1.51      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
% 6.72/1.51      inference(superposition,[status(thm)],[c_1329,c_17]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_16,plain,
% 6.72/1.51      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 6.72/1.51      inference(cnf_transformation,[],[f72]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_11,plain,
% 6.72/1.51      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 6.72/1.51      inference(cnf_transformation,[],[f69]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_1017,plain,
% 6.72/1.51      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 6.72/1.51      inference(superposition,[status(thm)],[c_17,c_11]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_1541,plain,
% 6.72/1.51      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 6.72/1.51      inference(superposition,[status(thm)],[c_16,c_1017]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_2150,plain,
% 6.72/1.51      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) = X0 ),
% 6.72/1.51      inference(light_normalisation,[status(thm)],[c_1355,c_1541]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_14,plain,
% 6.72/1.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 6.72/1.51      inference(cnf_transformation,[],[f70]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_1357,plain,
% 6.72/1.51      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) ),
% 6.72/1.51      inference(superposition,[status(thm)],[c_1329,c_14]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_1362,plain,
% 6.72/1.51      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
% 6.72/1.51      inference(light_normalisation,[status(thm)],[c_1357,c_1329]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_2490,plain,
% 6.72/1.51      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0)) = X0 ),
% 6.72/1.51      inference(light_normalisation,[status(thm)],[c_1362,c_2150]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_2493,plain,
% 6.72/1.51      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 6.72/1.51      inference(superposition,[status(thm)],[c_2150,c_2490]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_2500,plain,
% 6.72/1.51      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 6.72/1.51      inference(demodulation,[status(thm)],[c_2493,c_2150]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_15,plain,
% 6.72/1.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 6.72/1.51      inference(cnf_transformation,[],[f71]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_2652,plain,
% 6.72/1.51      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
% 6.72/1.51      inference(superposition,[status(thm)],[c_2500,c_15]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_2661,plain,
% 6.72/1.51      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),X0)) = k3_xboole_0(k1_xboole_0,X0) ),
% 6.72/1.51      inference(demodulation,[status(thm)],[c_2652,c_2500]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_10,plain,
% 6.72/1.51      ( r1_tarski(X0,X0) ),
% 6.72/1.51      inference(cnf_transformation,[],[f79]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_554,plain,
% 6.72/1.51      ( r1_tarski(X0,X0) = iProver_top ),
% 6.72/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_812,plain,
% 6.72/1.51      ( k3_xboole_0(X0,X0) = X0 ),
% 6.72/1.51      inference(superposition,[status(thm)],[c_554,c_553]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_2663,plain,
% 6.72/1.51      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 6.72/1.51      inference(light_normalisation,
% 6.72/1.51                [status(thm)],
% 6.72/1.51                [c_2661,c_812,c_813,c_1329,c_2493]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_23183,plain,
% 6.72/1.51      ( k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK2 ),
% 6.72/1.51      inference(demodulation,[status(thm)],[c_23166,c_2493,c_2663]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_1011,plain,
% 6.72/1.51      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 6.72/1.51      inference(superposition,[status(thm)],[c_16,c_17]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_21,negated_conjecture,
% 6.72/1.51      ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) != sK2 ),
% 6.72/1.51      inference(cnf_transformation,[],[f77]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(c_3070,plain,
% 6.72/1.51      ( k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK2 ),
% 6.72/1.51      inference(demodulation,[status(thm)],[c_1011,c_21]) ).
% 6.72/1.51  
% 6.72/1.51  cnf(contradiction,plain,
% 6.72/1.51      ( $false ),
% 6.72/1.51      inference(minisat,[status(thm)],[c_23183,c_3070]) ).
% 6.72/1.51  
% 6.72/1.51  
% 6.72/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 6.72/1.51  
% 6.72/1.51  ------                               Statistics
% 6.72/1.51  
% 6.72/1.51  ------ General
% 6.72/1.51  
% 6.72/1.51  abstr_ref_over_cycles:                  0
% 6.72/1.51  abstr_ref_under_cycles:                 0
% 6.72/1.51  gc_basic_clause_elim:                   0
% 6.72/1.51  forced_gc_time:                         0
% 6.72/1.51  parsing_time:                           0.008
% 6.72/1.51  unif_index_cands_time:                  0.
% 6.72/1.51  unif_index_add_time:                    0.
% 6.72/1.51  orderings_time:                         0.
% 6.72/1.51  out_proof_time:                         0.006
% 6.72/1.51  total_time:                             0.545
% 6.72/1.51  num_of_symbols:                         41
% 6.72/1.51  num_of_terms:                           22425
% 6.72/1.51  
% 6.72/1.51  ------ Preprocessing
% 6.72/1.51  
% 6.72/1.51  num_of_splits:                          0
% 6.72/1.51  num_of_split_atoms:                     0
% 6.72/1.51  num_of_reused_defs:                     0
% 6.72/1.51  num_eq_ax_congr_red:                    9
% 6.72/1.51  num_of_sem_filtered_clauses:            1
% 6.72/1.51  num_of_subtypes:                        0
% 6.72/1.51  monotx_restored_types:                  0
% 6.72/1.51  sat_num_of_epr_types:                   0
% 6.72/1.51  sat_num_of_non_cyclic_types:            0
% 6.72/1.51  sat_guarded_non_collapsed_types:        0
% 6.72/1.51  num_pure_diseq_elim:                    0
% 6.72/1.51  simp_replaced_by:                       0
% 6.72/1.51  res_preprocessed:                       105
% 6.72/1.51  prep_upred:                             0
% 6.72/1.51  prep_unflattend:                        0
% 6.72/1.51  smt_new_axioms:                         0
% 6.72/1.51  pred_elim_cands:                        2
% 6.72/1.51  pred_elim:                              0
% 6.72/1.51  pred_elim_cl:                           0
% 6.72/1.51  pred_elim_cycles:                       2
% 6.72/1.51  merged_defs:                            0
% 6.72/1.51  merged_defs_ncl:                        0
% 6.72/1.51  bin_hyper_res:                          0
% 6.72/1.51  prep_cycles:                            4
% 6.72/1.51  pred_elim_time:                         0.
% 6.72/1.51  splitting_time:                         0.
% 6.72/1.51  sem_filter_time:                        0.
% 6.72/1.51  monotx_time:                            0.
% 6.72/1.51  subtype_inf_time:                       0.
% 6.72/1.51  
% 6.72/1.51  ------ Problem properties
% 6.72/1.51  
% 6.72/1.51  clauses:                                22
% 6.72/1.51  conjectures:                            2
% 6.72/1.51  epr:                                    5
% 6.72/1.51  horn:                                   18
% 6.72/1.51  ground:                                 2
% 6.72/1.51  unary:                                  10
% 6.72/1.51  binary:                                 5
% 6.72/1.51  lits:                                   41
% 6.72/1.51  lits_eq:                                9
% 6.72/1.51  fd_pure:                                0
% 6.72/1.51  fd_pseudo:                              0
% 6.72/1.51  fd_cond:                                0
% 6.72/1.51  fd_pseudo_cond:                         1
% 6.72/1.51  ac_symbols:                             0
% 6.72/1.51  
% 6.72/1.51  ------ Propositional Solver
% 6.72/1.51  
% 6.72/1.51  prop_solver_calls:                      29
% 6.72/1.51  prop_fast_solver_calls:                 592
% 6.72/1.51  smt_solver_calls:                       0
% 6.72/1.51  smt_fast_solver_calls:                  0
% 6.72/1.51  prop_num_of_clauses:                    5882
% 6.72/1.51  prop_preprocess_simplified:             12288
% 6.72/1.51  prop_fo_subsumed:                       1
% 6.72/1.51  prop_solver_time:                       0.
% 6.72/1.51  smt_solver_time:                        0.
% 6.72/1.51  smt_fast_solver_time:                   0.
% 6.72/1.51  prop_fast_solver_time:                  0.
% 6.72/1.51  prop_unsat_core_time:                   0.
% 6.72/1.51  
% 6.72/1.51  ------ QBF
% 6.72/1.51  
% 6.72/1.51  qbf_q_res:                              0
% 6.72/1.51  qbf_num_tautologies:                    0
% 6.72/1.51  qbf_prep_cycles:                        0
% 6.72/1.51  
% 6.72/1.51  ------ BMC1
% 6.72/1.51  
% 6.72/1.51  bmc1_current_bound:                     -1
% 6.72/1.51  bmc1_last_solved_bound:                 -1
% 6.72/1.51  bmc1_unsat_core_size:                   -1
% 6.72/1.51  bmc1_unsat_core_parents_size:           -1
% 6.72/1.51  bmc1_merge_next_fun:                    0
% 6.72/1.51  bmc1_unsat_core_clauses_time:           0.
% 6.72/1.51  
% 6.72/1.51  ------ Instantiation
% 6.72/1.51  
% 6.72/1.51  inst_num_of_clauses:                    1484
% 6.72/1.51  inst_num_in_passive:                    558
% 6.72/1.51  inst_num_in_active:                     488
% 6.72/1.51  inst_num_in_unprocessed:                438
% 6.72/1.51  inst_num_of_loops:                      630
% 6.72/1.51  inst_num_of_learning_restarts:          0
% 6.72/1.51  inst_num_moves_active_passive:          140
% 6.72/1.51  inst_lit_activity:                      0
% 6.72/1.51  inst_lit_activity_moves:                0
% 6.72/1.51  inst_num_tautologies:                   0
% 6.72/1.51  inst_num_prop_implied:                  0
% 6.72/1.51  inst_num_existing_simplified:           0
% 6.72/1.51  inst_num_eq_res_simplified:             0
% 6.72/1.51  inst_num_child_elim:                    0
% 6.72/1.51  inst_num_of_dismatching_blockings:      3229
% 6.72/1.51  inst_num_of_non_proper_insts:           2403
% 6.72/1.51  inst_num_of_duplicates:                 0
% 6.72/1.51  inst_inst_num_from_inst_to_res:         0
% 6.72/1.51  inst_dismatching_checking_time:         0.
% 6.72/1.51  
% 6.72/1.51  ------ Resolution
% 6.72/1.51  
% 6.72/1.51  res_num_of_clauses:                     0
% 6.72/1.51  res_num_in_passive:                     0
% 6.72/1.51  res_num_in_active:                      0
% 6.72/1.51  res_num_of_loops:                       109
% 6.72/1.51  res_forward_subset_subsumed:            122
% 6.72/1.51  res_backward_subset_subsumed:           0
% 6.72/1.51  res_forward_subsumed:                   0
% 6.72/1.51  res_backward_subsumed:                  0
% 6.72/1.51  res_forward_subsumption_resolution:     0
% 6.72/1.51  res_backward_subsumption_resolution:    0
% 6.72/1.51  res_clause_to_clause_subsumption:       7009
% 6.72/1.51  res_orphan_elimination:                 0
% 6.72/1.51  res_tautology_del:                      233
% 6.72/1.51  res_num_eq_res_simplified:              0
% 6.72/1.51  res_num_sel_changes:                    0
% 6.72/1.51  res_moves_from_active_to_pass:          0
% 6.72/1.51  
% 6.72/1.51  ------ Superposition
% 6.72/1.51  
% 6.72/1.51  sup_time_total:                         0.
% 6.72/1.51  sup_time_generating:                    0.
% 6.72/1.51  sup_time_sim_full:                      0.
% 6.72/1.51  sup_time_sim_immed:                     0.
% 6.72/1.51  
% 6.72/1.51  sup_num_of_clauses:                     610
% 6.72/1.51  sup_num_in_active:                      113
% 6.72/1.51  sup_num_in_passive:                     497
% 6.72/1.51  sup_num_of_loops:                       124
% 6.72/1.51  sup_fw_superposition:                   2658
% 6.72/1.51  sup_bw_superposition:                   1669
% 6.72/1.51  sup_immediate_simplified:               1336
% 6.72/1.51  sup_given_eliminated:                   0
% 6.72/1.51  comparisons_done:                       0
% 6.72/1.51  comparisons_avoided:                    0
% 6.72/1.51  
% 6.72/1.51  ------ Simplifications
% 6.72/1.51  
% 6.72/1.51  
% 6.72/1.51  sim_fw_subset_subsumed:                 33
% 6.72/1.51  sim_bw_subset_subsumed:                 0
% 6.72/1.51  sim_fw_subsumed:                        92
% 6.72/1.51  sim_bw_subsumed:                        2
% 6.72/1.51  sim_fw_subsumption_res:                 1
% 6.72/1.51  sim_bw_subsumption_res:                 0
% 6.72/1.51  sim_tautology_del:                      11
% 6.72/1.51  sim_eq_tautology_del:                   298
% 6.72/1.51  sim_eq_res_simp:                        0
% 6.72/1.51  sim_fw_demodulated:                     510
% 6.72/1.51  sim_bw_demodulated:                     61
% 6.72/1.51  sim_light_normalised:                   761
% 6.72/1.51  sim_joinable_taut:                      0
% 6.72/1.51  sim_joinable_simp:                      0
% 6.72/1.51  sim_ac_normalised:                      0
% 6.72/1.51  sim_smt_subsumption:                    0
% 6.72/1.51  
%------------------------------------------------------------------------------
