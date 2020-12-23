%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:47 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :  106 (1366 expanded)
%              Number of clauses        :   42 ( 126 expanded)
%              Number of leaves         :   21 ( 430 expanded)
%              Depth                    :   18
%              Number of atoms          :  155 (1516 expanded)
%              Number of equality atoms :  116 (1368 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f52,f59])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f60])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f61])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f62])).

fof(f71,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f47,f63,f63])).

fof(f22,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f22])).

fof(f28,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f23])).

fof(f32,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f32])).

fof(f58,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f55,f63])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f63])).

fof(f74,plain,(
    k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f58,f64,f67])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f44,f64])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f11,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f46,f64])).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f39,f65])).

fof(f73,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f56,f66,f67,f67,f67])).

fof(f77,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_282,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_11,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_673,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11,c_14])).

cnf(c_9,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_281,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1779,plain,
    ( r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_673,c_281])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_285,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5453,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1779,c_285])).

cnf(c_5788,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_282,c_5453])).

cnf(c_1780,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_281])).

cnf(c_1892,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_673,c_1780])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_286,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r2_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4148,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0
    | r2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1892,c_286])).

cnf(c_316,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | ~ r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X0)
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_388,plain,
    ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_389,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_388])).

cnf(c_391,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0
    | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_389])).

cnf(c_617,plain,
    ( r1_tarski(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_618,plain,
    ( r1_tarski(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_617])).

cnf(c_620,plain,
    ( r1_tarski(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_618])).

cnf(c_4563,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4148,c_391,c_620,c_1892])).

cnf(c_4567,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4563,c_673])).

cnf(c_4621,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_4567])).

cnf(c_5994,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5788,c_4621])).

cnf(c_13,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_10,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_170,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(theory_normalisation,[status(thm)],[c_13,c_10,c_0])).

cnf(c_4582,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_4563,c_170])).

cnf(c_4596,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))))) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4582,c_4563])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_477,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_0])).

cnf(c_294,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_10,c_0])).

cnf(c_728,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_8,c_294])).

cnf(c_743,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_10,c_728])).

cnf(c_1100,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_0,c_743])).

cnf(c_4597,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4596,c_477,c_1100])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5994,c_4597])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n005.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 20:03:47 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.17/0.33  % Running in FOF mode
% 3.83/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/0.98  
% 3.83/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.83/0.98  
% 3.83/0.98  ------  iProver source info
% 3.83/0.98  
% 3.83/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.83/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.83/0.98  git: non_committed_changes: false
% 3.83/0.98  git: last_make_outside_of_git: false
% 3.83/0.98  
% 3.83/0.98  ------ 
% 3.83/0.98  
% 3.83/0.98  ------ Input Options
% 3.83/0.98  
% 3.83/0.98  --out_options                           all
% 3.83/0.98  --tptp_safe_out                         true
% 3.83/0.98  --problem_path                          ""
% 3.83/0.98  --include_path                          ""
% 3.83/0.98  --clausifier                            res/vclausify_rel
% 3.83/0.98  --clausifier_options                    ""
% 3.83/0.98  --stdin                                 false
% 3.83/0.98  --stats_out                             all
% 3.83/0.98  
% 3.83/0.98  ------ General Options
% 3.83/0.98  
% 3.83/0.98  --fof                                   false
% 3.83/0.98  --time_out_real                         305.
% 3.83/0.98  --time_out_virtual                      -1.
% 3.83/0.98  --symbol_type_check                     false
% 3.83/0.98  --clausify_out                          false
% 3.83/0.98  --sig_cnt_out                           false
% 3.83/0.98  --trig_cnt_out                          false
% 3.83/0.98  --trig_cnt_out_tolerance                1.
% 3.83/0.98  --trig_cnt_out_sk_spl                   false
% 3.83/0.98  --abstr_cl_out                          false
% 3.83/0.98  
% 3.83/0.98  ------ Global Options
% 3.83/0.98  
% 3.83/0.98  --schedule                              default
% 3.83/0.98  --add_important_lit                     false
% 3.83/0.98  --prop_solver_per_cl                    1000
% 3.83/0.98  --min_unsat_core                        false
% 3.83/0.98  --soft_assumptions                      false
% 3.83/0.98  --soft_lemma_size                       3
% 3.83/0.98  --prop_impl_unit_size                   0
% 3.83/0.98  --prop_impl_unit                        []
% 3.83/0.98  --share_sel_clauses                     true
% 3.83/0.98  --reset_solvers                         false
% 3.83/0.98  --bc_imp_inh                            [conj_cone]
% 3.83/0.98  --conj_cone_tolerance                   3.
% 3.83/0.98  --extra_neg_conj                        none
% 3.83/0.98  --large_theory_mode                     true
% 3.83/0.98  --prolific_symb_bound                   200
% 3.83/0.98  --lt_threshold                          2000
% 3.83/0.98  --clause_weak_htbl                      true
% 3.83/0.98  --gc_record_bc_elim                     false
% 3.83/0.98  
% 3.83/0.98  ------ Preprocessing Options
% 3.83/0.98  
% 3.83/0.98  --preprocessing_flag                    true
% 3.83/0.98  --time_out_prep_mult                    0.1
% 3.83/0.98  --splitting_mode                        input
% 3.83/0.98  --splitting_grd                         true
% 3.83/0.98  --splitting_cvd                         false
% 3.83/0.98  --splitting_cvd_svl                     false
% 3.83/0.98  --splitting_nvd                         32
% 3.83/0.98  --sub_typing                            true
% 3.83/0.98  --prep_gs_sim                           true
% 3.83/0.98  --prep_unflatten                        true
% 3.83/0.98  --prep_res_sim                          true
% 3.83/0.98  --prep_upred                            true
% 3.83/0.98  --prep_sem_filter                       exhaustive
% 3.83/0.98  --prep_sem_filter_out                   false
% 3.83/0.98  --pred_elim                             true
% 3.83/0.98  --res_sim_input                         true
% 3.83/0.98  --eq_ax_congr_red                       true
% 3.83/0.98  --pure_diseq_elim                       true
% 3.83/0.98  --brand_transform                       false
% 3.83/0.98  --non_eq_to_eq                          false
% 3.83/0.98  --prep_def_merge                        true
% 3.83/0.98  --prep_def_merge_prop_impl              false
% 3.83/0.98  --prep_def_merge_mbd                    true
% 3.83/0.98  --prep_def_merge_tr_red                 false
% 3.83/0.98  --prep_def_merge_tr_cl                  false
% 3.83/0.98  --smt_preprocessing                     true
% 3.83/0.98  --smt_ac_axioms                         fast
% 3.83/0.98  --preprocessed_out                      false
% 3.83/0.98  --preprocessed_stats                    false
% 3.83/0.98  
% 3.83/0.98  ------ Abstraction refinement Options
% 3.83/0.98  
% 3.83/0.98  --abstr_ref                             []
% 3.83/0.98  --abstr_ref_prep                        false
% 3.83/0.98  --abstr_ref_until_sat                   false
% 3.83/0.98  --abstr_ref_sig_restrict                funpre
% 3.83/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.83/0.98  --abstr_ref_under                       []
% 3.83/0.98  
% 3.83/0.98  ------ SAT Options
% 3.83/0.98  
% 3.83/0.98  --sat_mode                              false
% 3.83/0.98  --sat_fm_restart_options                ""
% 3.83/0.98  --sat_gr_def                            false
% 3.83/0.98  --sat_epr_types                         true
% 3.83/0.98  --sat_non_cyclic_types                  false
% 3.83/0.98  --sat_finite_models                     false
% 3.83/0.98  --sat_fm_lemmas                         false
% 3.83/0.98  --sat_fm_prep                           false
% 3.83/0.98  --sat_fm_uc_incr                        true
% 3.83/0.98  --sat_out_model                         small
% 3.83/0.98  --sat_out_clauses                       false
% 3.83/0.98  
% 3.83/0.98  ------ QBF Options
% 3.83/0.98  
% 3.83/0.98  --qbf_mode                              false
% 3.83/0.98  --qbf_elim_univ                         false
% 3.83/0.98  --qbf_dom_inst                          none
% 3.83/0.98  --qbf_dom_pre_inst                      false
% 3.83/0.98  --qbf_sk_in                             false
% 3.83/0.98  --qbf_pred_elim                         true
% 3.83/0.98  --qbf_split                             512
% 3.83/0.98  
% 3.83/0.98  ------ BMC1 Options
% 3.83/0.98  
% 3.83/0.98  --bmc1_incremental                      false
% 3.83/0.98  --bmc1_axioms                           reachable_all
% 3.83/0.98  --bmc1_min_bound                        0
% 3.83/0.98  --bmc1_max_bound                        -1
% 3.83/0.98  --bmc1_max_bound_default                -1
% 3.83/0.98  --bmc1_symbol_reachability              true
% 3.83/0.98  --bmc1_property_lemmas                  false
% 3.83/0.98  --bmc1_k_induction                      false
% 3.83/0.98  --bmc1_non_equiv_states                 false
% 3.83/0.98  --bmc1_deadlock                         false
% 3.83/0.98  --bmc1_ucm                              false
% 3.83/0.98  --bmc1_add_unsat_core                   none
% 3.83/0.98  --bmc1_unsat_core_children              false
% 3.83/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.83/0.98  --bmc1_out_stat                         full
% 3.83/0.98  --bmc1_ground_init                      false
% 3.83/0.98  --bmc1_pre_inst_next_state              false
% 3.83/0.98  --bmc1_pre_inst_state                   false
% 3.83/0.98  --bmc1_pre_inst_reach_state             false
% 3.83/0.98  --bmc1_out_unsat_core                   false
% 3.83/0.98  --bmc1_aig_witness_out                  false
% 3.83/0.98  --bmc1_verbose                          false
% 3.83/0.98  --bmc1_dump_clauses_tptp                false
% 3.83/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.83/0.98  --bmc1_dump_file                        -
% 3.83/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.83/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.83/0.98  --bmc1_ucm_extend_mode                  1
% 3.83/0.98  --bmc1_ucm_init_mode                    2
% 3.83/0.98  --bmc1_ucm_cone_mode                    none
% 3.83/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.83/0.98  --bmc1_ucm_relax_model                  4
% 3.83/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.83/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.83/0.98  --bmc1_ucm_layered_model                none
% 3.83/0.98  --bmc1_ucm_max_lemma_size               10
% 3.83/0.98  
% 3.83/0.98  ------ AIG Options
% 3.83/0.98  
% 3.83/0.98  --aig_mode                              false
% 3.83/0.98  
% 3.83/0.98  ------ Instantiation Options
% 3.83/0.98  
% 3.83/0.98  --instantiation_flag                    true
% 3.83/0.98  --inst_sos_flag                         true
% 3.83/0.98  --inst_sos_phase                        true
% 3.83/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.83/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.83/0.98  --inst_lit_sel_side                     num_symb
% 3.83/0.98  --inst_solver_per_active                1400
% 3.83/0.98  --inst_solver_calls_frac                1.
% 3.83/0.98  --inst_passive_queue_type               priority_queues
% 3.83/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.83/0.98  --inst_passive_queues_freq              [25;2]
% 3.83/0.98  --inst_dismatching                      true
% 3.83/0.98  --inst_eager_unprocessed_to_passive     true
% 3.83/0.98  --inst_prop_sim_given                   true
% 3.83/0.98  --inst_prop_sim_new                     false
% 3.83/0.98  --inst_subs_new                         false
% 3.83/0.98  --inst_eq_res_simp                      false
% 3.83/0.98  --inst_subs_given                       false
% 3.83/0.98  --inst_orphan_elimination               true
% 3.83/0.98  --inst_learning_loop_flag               true
% 3.83/0.98  --inst_learning_start                   3000
% 3.83/0.98  --inst_learning_factor                  2
% 3.83/0.98  --inst_start_prop_sim_after_learn       3
% 3.83/0.98  --inst_sel_renew                        solver
% 3.83/0.98  --inst_lit_activity_flag                true
% 3.83/0.98  --inst_restr_to_given                   false
% 3.83/0.98  --inst_activity_threshold               500
% 3.83/0.98  --inst_out_proof                        true
% 3.83/0.98  
% 3.83/0.98  ------ Resolution Options
% 3.83/0.98  
% 3.83/0.98  --resolution_flag                       true
% 3.83/0.98  --res_lit_sel                           adaptive
% 3.83/0.98  --res_lit_sel_side                      none
% 3.83/0.98  --res_ordering                          kbo
% 3.83/0.98  --res_to_prop_solver                    active
% 3.83/0.98  --res_prop_simpl_new                    false
% 3.83/0.98  --res_prop_simpl_given                  true
% 3.83/0.98  --res_passive_queue_type                priority_queues
% 3.83/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.83/0.98  --res_passive_queues_freq               [15;5]
% 3.83/0.98  --res_forward_subs                      full
% 3.83/0.98  --res_backward_subs                     full
% 3.83/0.98  --res_forward_subs_resolution           true
% 3.83/0.98  --res_backward_subs_resolution          true
% 3.83/0.98  --res_orphan_elimination                true
% 3.83/0.98  --res_time_limit                        2.
% 3.83/0.98  --res_out_proof                         true
% 3.83/0.98  
% 3.83/0.98  ------ Superposition Options
% 3.83/0.98  
% 3.83/0.98  --superposition_flag                    true
% 3.83/0.98  --sup_passive_queue_type                priority_queues
% 3.83/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.83/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.83/0.98  --demod_completeness_check              fast
% 3.83/0.98  --demod_use_ground                      true
% 3.83/0.98  --sup_to_prop_solver                    passive
% 3.83/0.98  --sup_prop_simpl_new                    true
% 3.83/0.98  --sup_prop_simpl_given                  true
% 3.83/0.98  --sup_fun_splitting                     true
% 3.83/0.98  --sup_smt_interval                      50000
% 3.83/0.98  
% 3.83/0.98  ------ Superposition Simplification Setup
% 3.83/0.98  
% 3.83/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.83/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.83/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.83/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.83/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.83/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.83/0.98  --sup_immed_triv                        [TrivRules]
% 3.83/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.98  --sup_immed_bw_main                     []
% 3.83/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.83/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.83/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.98  --sup_input_bw                          []
% 3.83/0.98  
% 3.83/0.98  ------ Combination Options
% 3.83/0.98  
% 3.83/0.98  --comb_res_mult                         3
% 3.83/0.98  --comb_sup_mult                         2
% 3.83/0.98  --comb_inst_mult                        10
% 3.83/0.98  
% 3.83/0.98  ------ Debug Options
% 3.83/0.98  
% 3.83/0.98  --dbg_backtrace                         false
% 3.83/0.98  --dbg_dump_prop_clauses                 false
% 3.83/0.98  --dbg_dump_prop_clauses_file            -
% 3.83/0.98  --dbg_out_stat                          false
% 3.83/0.98  ------ Parsing...
% 3.83/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.83/0.98  
% 3.83/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.83/0.98  
% 3.83/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.83/0.98  
% 3.83/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.83/0.98  ------ Proving...
% 3.83/0.98  ------ Problem Properties 
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  clauses                                 14
% 3.83/0.98  conjectures                             1
% 3.83/0.98  EPR                                     4
% 3.83/0.98  Horn                                    12
% 3.83/0.98  unary                                   10
% 3.83/0.98  binary                                  2
% 3.83/0.98  lits                                    20
% 3.83/0.98  lits eq                                 12
% 3.83/0.98  fd_pure                                 0
% 3.83/0.98  fd_pseudo                               0
% 3.83/0.98  fd_cond                                 0
% 3.83/0.98  fd_pseudo_cond                          3
% 3.83/0.98  AC symbols                              1
% 3.83/0.98  
% 3.83/0.98  ------ Schedule dynamic 5 is on 
% 3.83/0.98  
% 3.83/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  ------ 
% 3.83/0.98  Current options:
% 3.83/0.98  ------ 
% 3.83/0.98  
% 3.83/0.98  ------ Input Options
% 3.83/0.98  
% 3.83/0.98  --out_options                           all
% 3.83/0.98  --tptp_safe_out                         true
% 3.83/0.98  --problem_path                          ""
% 3.83/0.98  --include_path                          ""
% 3.83/0.98  --clausifier                            res/vclausify_rel
% 3.83/0.98  --clausifier_options                    ""
% 3.83/0.98  --stdin                                 false
% 3.83/0.98  --stats_out                             all
% 3.83/0.98  
% 3.83/0.98  ------ General Options
% 3.83/0.98  
% 3.83/0.98  --fof                                   false
% 3.83/0.98  --time_out_real                         305.
% 3.83/0.98  --time_out_virtual                      -1.
% 3.83/0.98  --symbol_type_check                     false
% 3.83/0.98  --clausify_out                          false
% 3.83/0.98  --sig_cnt_out                           false
% 3.83/0.98  --trig_cnt_out                          false
% 3.83/0.98  --trig_cnt_out_tolerance                1.
% 3.83/0.98  --trig_cnt_out_sk_spl                   false
% 3.83/0.98  --abstr_cl_out                          false
% 3.83/0.98  
% 3.83/0.98  ------ Global Options
% 3.83/0.98  
% 3.83/0.98  --schedule                              default
% 3.83/0.98  --add_important_lit                     false
% 3.83/0.98  --prop_solver_per_cl                    1000
% 3.83/0.98  --min_unsat_core                        false
% 3.83/0.98  --soft_assumptions                      false
% 3.83/0.98  --soft_lemma_size                       3
% 3.83/0.98  --prop_impl_unit_size                   0
% 3.83/0.98  --prop_impl_unit                        []
% 3.83/0.98  --share_sel_clauses                     true
% 3.83/0.98  --reset_solvers                         false
% 3.83/0.98  --bc_imp_inh                            [conj_cone]
% 3.83/0.98  --conj_cone_tolerance                   3.
% 3.83/0.98  --extra_neg_conj                        none
% 3.83/0.98  --large_theory_mode                     true
% 3.83/0.98  --prolific_symb_bound                   200
% 3.83/0.98  --lt_threshold                          2000
% 3.83/0.98  --clause_weak_htbl                      true
% 3.83/0.98  --gc_record_bc_elim                     false
% 3.83/0.98  
% 3.83/0.98  ------ Preprocessing Options
% 3.83/0.98  
% 3.83/0.98  --preprocessing_flag                    true
% 3.83/0.98  --time_out_prep_mult                    0.1
% 3.83/0.98  --splitting_mode                        input
% 3.83/0.98  --splitting_grd                         true
% 3.83/0.98  --splitting_cvd                         false
% 3.83/0.98  --splitting_cvd_svl                     false
% 3.83/0.98  --splitting_nvd                         32
% 3.83/0.98  --sub_typing                            true
% 3.83/0.98  --prep_gs_sim                           true
% 3.83/0.98  --prep_unflatten                        true
% 3.83/0.98  --prep_res_sim                          true
% 3.83/0.98  --prep_upred                            true
% 3.83/0.98  --prep_sem_filter                       exhaustive
% 3.83/0.98  --prep_sem_filter_out                   false
% 3.83/0.98  --pred_elim                             true
% 3.83/0.98  --res_sim_input                         true
% 3.83/0.98  --eq_ax_congr_red                       true
% 3.83/0.98  --pure_diseq_elim                       true
% 3.83/0.98  --brand_transform                       false
% 3.83/0.98  --non_eq_to_eq                          false
% 3.83/0.98  --prep_def_merge                        true
% 3.83/0.98  --prep_def_merge_prop_impl              false
% 3.83/0.98  --prep_def_merge_mbd                    true
% 3.83/0.98  --prep_def_merge_tr_red                 false
% 3.83/0.98  --prep_def_merge_tr_cl                  false
% 3.83/0.98  --smt_preprocessing                     true
% 3.83/0.98  --smt_ac_axioms                         fast
% 3.83/0.98  --preprocessed_out                      false
% 3.83/0.98  --preprocessed_stats                    false
% 3.83/0.98  
% 3.83/0.98  ------ Abstraction refinement Options
% 3.83/0.98  
% 3.83/0.98  --abstr_ref                             []
% 3.83/0.98  --abstr_ref_prep                        false
% 3.83/0.98  --abstr_ref_until_sat                   false
% 3.83/0.98  --abstr_ref_sig_restrict                funpre
% 3.83/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.83/0.98  --abstr_ref_under                       []
% 3.83/0.98  
% 3.83/0.98  ------ SAT Options
% 3.83/0.98  
% 3.83/0.98  --sat_mode                              false
% 3.83/0.98  --sat_fm_restart_options                ""
% 3.83/0.98  --sat_gr_def                            false
% 3.83/0.98  --sat_epr_types                         true
% 3.83/0.98  --sat_non_cyclic_types                  false
% 3.83/0.98  --sat_finite_models                     false
% 3.83/0.98  --sat_fm_lemmas                         false
% 3.83/0.98  --sat_fm_prep                           false
% 3.83/0.98  --sat_fm_uc_incr                        true
% 3.83/0.98  --sat_out_model                         small
% 3.83/0.98  --sat_out_clauses                       false
% 3.83/0.98  
% 3.83/0.98  ------ QBF Options
% 3.83/0.98  
% 3.83/0.98  --qbf_mode                              false
% 3.83/0.98  --qbf_elim_univ                         false
% 3.83/0.98  --qbf_dom_inst                          none
% 3.83/0.98  --qbf_dom_pre_inst                      false
% 3.83/0.98  --qbf_sk_in                             false
% 3.83/0.98  --qbf_pred_elim                         true
% 3.83/0.98  --qbf_split                             512
% 3.83/0.98  
% 3.83/0.98  ------ BMC1 Options
% 3.83/0.98  
% 3.83/0.98  --bmc1_incremental                      false
% 3.83/0.98  --bmc1_axioms                           reachable_all
% 3.83/0.98  --bmc1_min_bound                        0
% 3.83/0.98  --bmc1_max_bound                        -1
% 3.83/0.98  --bmc1_max_bound_default                -1
% 3.83/0.98  --bmc1_symbol_reachability              true
% 3.83/0.98  --bmc1_property_lemmas                  false
% 3.83/0.98  --bmc1_k_induction                      false
% 3.83/0.98  --bmc1_non_equiv_states                 false
% 3.83/0.98  --bmc1_deadlock                         false
% 3.83/0.98  --bmc1_ucm                              false
% 3.83/0.98  --bmc1_add_unsat_core                   none
% 3.83/0.98  --bmc1_unsat_core_children              false
% 3.83/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.83/0.98  --bmc1_out_stat                         full
% 3.83/0.98  --bmc1_ground_init                      false
% 3.83/0.98  --bmc1_pre_inst_next_state              false
% 3.83/0.98  --bmc1_pre_inst_state                   false
% 3.83/0.98  --bmc1_pre_inst_reach_state             false
% 3.83/0.98  --bmc1_out_unsat_core                   false
% 3.83/0.98  --bmc1_aig_witness_out                  false
% 3.83/0.98  --bmc1_verbose                          false
% 3.83/0.98  --bmc1_dump_clauses_tptp                false
% 3.83/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.83/0.98  --bmc1_dump_file                        -
% 3.83/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.83/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.83/0.98  --bmc1_ucm_extend_mode                  1
% 3.83/0.98  --bmc1_ucm_init_mode                    2
% 3.83/0.98  --bmc1_ucm_cone_mode                    none
% 3.83/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.83/0.98  --bmc1_ucm_relax_model                  4
% 3.83/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.83/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.83/0.98  --bmc1_ucm_layered_model                none
% 3.83/0.98  --bmc1_ucm_max_lemma_size               10
% 3.83/0.98  
% 3.83/0.98  ------ AIG Options
% 3.83/0.98  
% 3.83/0.98  --aig_mode                              false
% 3.83/0.98  
% 3.83/0.98  ------ Instantiation Options
% 3.83/0.98  
% 3.83/0.98  --instantiation_flag                    true
% 3.83/0.98  --inst_sos_flag                         true
% 3.83/0.98  --inst_sos_phase                        true
% 3.83/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.83/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.83/0.98  --inst_lit_sel_side                     none
% 3.83/0.98  --inst_solver_per_active                1400
% 3.83/0.98  --inst_solver_calls_frac                1.
% 3.83/0.98  --inst_passive_queue_type               priority_queues
% 3.83/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.83/0.98  --inst_passive_queues_freq              [25;2]
% 3.83/0.98  --inst_dismatching                      true
% 3.83/0.98  --inst_eager_unprocessed_to_passive     true
% 3.83/0.98  --inst_prop_sim_given                   true
% 3.83/0.98  --inst_prop_sim_new                     false
% 3.83/0.98  --inst_subs_new                         false
% 3.83/0.98  --inst_eq_res_simp                      false
% 3.83/0.98  --inst_subs_given                       false
% 3.83/0.98  --inst_orphan_elimination               true
% 3.83/0.98  --inst_learning_loop_flag               true
% 3.83/0.98  --inst_learning_start                   3000
% 3.83/0.98  --inst_learning_factor                  2
% 3.83/0.98  --inst_start_prop_sim_after_learn       3
% 3.83/0.98  --inst_sel_renew                        solver
% 3.83/0.98  --inst_lit_activity_flag                true
% 3.83/0.98  --inst_restr_to_given                   false
% 3.83/0.98  --inst_activity_threshold               500
% 3.83/0.98  --inst_out_proof                        true
% 3.83/0.98  
% 3.83/0.98  ------ Resolution Options
% 3.83/0.98  
% 3.83/0.98  --resolution_flag                       false
% 3.83/0.98  --res_lit_sel                           adaptive
% 3.83/0.98  --res_lit_sel_side                      none
% 3.83/0.98  --res_ordering                          kbo
% 3.83/0.98  --res_to_prop_solver                    active
% 3.83/0.98  --res_prop_simpl_new                    false
% 3.83/0.98  --res_prop_simpl_given                  true
% 3.83/0.98  --res_passive_queue_type                priority_queues
% 3.83/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.83/0.98  --res_passive_queues_freq               [15;5]
% 3.83/0.98  --res_forward_subs                      full
% 3.83/0.98  --res_backward_subs                     full
% 3.83/0.98  --res_forward_subs_resolution           true
% 3.83/0.98  --res_backward_subs_resolution          true
% 3.83/0.98  --res_orphan_elimination                true
% 3.83/0.98  --res_time_limit                        2.
% 3.83/0.98  --res_out_proof                         true
% 3.83/0.98  
% 3.83/0.98  ------ Superposition Options
% 3.83/0.98  
% 3.83/0.98  --superposition_flag                    true
% 3.83/0.98  --sup_passive_queue_type                priority_queues
% 3.83/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.83/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.83/0.98  --demod_completeness_check              fast
% 3.83/0.98  --demod_use_ground                      true
% 3.83/0.98  --sup_to_prop_solver                    passive
% 3.83/0.98  --sup_prop_simpl_new                    true
% 3.83/0.98  --sup_prop_simpl_given                  true
% 3.83/0.98  --sup_fun_splitting                     true
% 3.83/0.98  --sup_smt_interval                      50000
% 3.83/0.98  
% 3.83/0.98  ------ Superposition Simplification Setup
% 3.83/0.98  
% 3.83/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.83/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.83/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.83/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.83/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.83/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.83/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.83/0.98  --sup_immed_triv                        [TrivRules]
% 3.83/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.98  --sup_immed_bw_main                     []
% 3.83/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.83/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.83/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/0.98  --sup_input_bw                          []
% 3.83/0.98  
% 3.83/0.98  ------ Combination Options
% 3.83/0.98  
% 3.83/0.98  --comb_res_mult                         3
% 3.83/0.98  --comb_sup_mult                         2
% 3.83/0.98  --comb_inst_mult                        10
% 3.83/0.98  
% 3.83/0.98  ------ Debug Options
% 3.83/0.98  
% 3.83/0.98  --dbg_backtrace                         false
% 3.83/0.98  --dbg_dump_prop_clauses                 false
% 3.83/0.98  --dbg_dump_prop_clauses_file            -
% 3.83/0.98  --dbg_out_stat                          false
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  ------ Proving...
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  % SZS status Theorem for theBenchmark.p
% 3.83/0.98  
% 3.83/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.83/0.98  
% 3.83/0.98  fof(f6,axiom,(
% 3.83/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.83/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.98  
% 3.83/0.98  fof(f41,plain,(
% 3.83/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.83/0.98    inference(cnf_transformation,[],[f6])).
% 3.83/0.98  
% 3.83/0.98  fof(f12,axiom,(
% 3.83/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.83/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f47,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f12])).
% 3.83/0.99  
% 3.83/0.99  fof(f14,axiom,(
% 3.83/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f49,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f14])).
% 3.83/0.99  
% 3.83/0.99  fof(f15,axiom,(
% 3.83/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f50,plain,(
% 3.83/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f15])).
% 3.83/0.99  
% 3.83/0.99  fof(f16,axiom,(
% 3.83/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f51,plain,(
% 3.83/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f16])).
% 3.83/0.99  
% 3.83/0.99  fof(f17,axiom,(
% 3.83/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f52,plain,(
% 3.83/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f17])).
% 3.83/0.99  
% 3.83/0.99  fof(f18,axiom,(
% 3.83/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f53,plain,(
% 3.83/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f18])).
% 3.83/0.99  
% 3.83/0.99  fof(f19,axiom,(
% 3.83/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f54,plain,(
% 3.83/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f19])).
% 3.83/0.99  
% 3.83/0.99  fof(f59,plain,(
% 3.83/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.83/0.99    inference(definition_unfolding,[],[f53,f54])).
% 3.83/0.99  
% 3.83/0.99  fof(f60,plain,(
% 3.83/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.83/0.99    inference(definition_unfolding,[],[f52,f59])).
% 3.83/0.99  
% 3.83/0.99  fof(f61,plain,(
% 3.83/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.83/0.99    inference(definition_unfolding,[],[f51,f60])).
% 3.83/0.99  
% 3.83/0.99  fof(f62,plain,(
% 3.83/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.83/0.99    inference(definition_unfolding,[],[f50,f61])).
% 3.83/0.99  
% 3.83/0.99  fof(f63,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.83/0.99    inference(definition_unfolding,[],[f49,f62])).
% 3.83/0.99  
% 3.83/0.99  fof(f71,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 3.83/0.99    inference(definition_unfolding,[],[f47,f63,f63])).
% 3.83/0.99  
% 3.83/0.99  fof(f22,conjecture,(
% 3.83/0.99    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f23,negated_conjecture,(
% 3.83/0.99    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 3.83/0.99    inference(negated_conjecture,[],[f22])).
% 3.83/0.99  
% 3.83/0.99  fof(f28,plain,(
% 3.83/0.99    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 3.83/0.99    inference(ennf_transformation,[],[f23])).
% 3.83/0.99  
% 3.83/0.99  fof(f32,plain,(
% 3.83/0.99    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 3.83/0.99    introduced(choice_axiom,[])).
% 3.83/0.99  
% 3.83/0.99  fof(f33,plain,(
% 3.83/0.99    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 3.83/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f32])).
% 3.83/0.99  
% 3.83/0.99  fof(f58,plain,(
% 3.83/0.99    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 3.83/0.99    inference(cnf_transformation,[],[f33])).
% 3.83/0.99  
% 3.83/0.99  fof(f20,axiom,(
% 3.83/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f55,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.83/0.99    inference(cnf_transformation,[],[f20])).
% 3.83/0.99  
% 3.83/0.99  fof(f64,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.83/0.99    inference(definition_unfolding,[],[f55,f63])).
% 3.83/0.99  
% 3.83/0.99  fof(f13,axiom,(
% 3.83/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f48,plain,(
% 3.83/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f13])).
% 3.83/0.99  
% 3.83/0.99  fof(f67,plain,(
% 3.83/0.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.83/0.99    inference(definition_unfolding,[],[f48,f63])).
% 3.83/0.99  
% 3.83/0.99  fof(f74,plain,(
% 3.83/0.99    k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 3.83/0.99    inference(definition_unfolding,[],[f58,f64,f67])).
% 3.83/0.99  
% 3.83/0.99  fof(f9,axiom,(
% 3.83/0.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f44,plain,(
% 3.83/0.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.83/0.99    inference(cnf_transformation,[],[f9])).
% 3.83/0.99  
% 3.83/0.99  fof(f70,plain,(
% 3.83/0.99    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.83/0.99    inference(definition_unfolding,[],[f44,f64])).
% 3.83/0.99  
% 3.83/0.99  fof(f3,axiom,(
% 3.83/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f29,plain,(
% 3.83/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.83/0.99    inference(nnf_transformation,[],[f3])).
% 3.83/0.99  
% 3.83/0.99  fof(f30,plain,(
% 3.83/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.83/0.99    inference(flattening,[],[f29])).
% 3.83/0.99  
% 3.83/0.99  fof(f38,plain,(
% 3.83/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f30])).
% 3.83/0.99  
% 3.83/0.99  fof(f2,axiom,(
% 3.83/0.99    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f24,plain,(
% 3.83/0.99    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 3.83/0.99    inference(unused_predicate_definition_removal,[],[f2])).
% 3.83/0.99  
% 3.83/0.99  fof(f25,plain,(
% 3.83/0.99    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 3.83/0.99    inference(ennf_transformation,[],[f24])).
% 3.83/0.99  
% 3.83/0.99  fof(f26,plain,(
% 3.83/0.99    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 3.83/0.99    inference(flattening,[],[f25])).
% 3.83/0.99  
% 3.83/0.99  fof(f35,plain,(
% 3.83/0.99    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f26])).
% 3.83/0.99  
% 3.83/0.99  fof(f21,axiom,(
% 3.83/0.99    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f31,plain,(
% 3.83/0.99    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 3.83/0.99    inference(nnf_transformation,[],[f21])).
% 3.83/0.99  
% 3.83/0.99  fof(f56,plain,(
% 3.83/0.99    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f31])).
% 3.83/0.99  
% 3.83/0.99  fof(f4,axiom,(
% 3.83/0.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f39,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f4])).
% 3.83/0.99  
% 3.83/0.99  fof(f11,axiom,(
% 3.83/0.99    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f46,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f11])).
% 3.83/0.99  
% 3.83/0.99  fof(f65,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 3.83/0.99    inference(definition_unfolding,[],[f46,f64])).
% 3.83/0.99  
% 3.83/0.99  fof(f66,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1)) )),
% 3.83/0.99    inference(definition_unfolding,[],[f39,f65])).
% 3.83/0.99  
% 3.83/0.99  fof(f73,plain,(
% 3.83/0.99    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.83/0.99    inference(definition_unfolding,[],[f56,f66,f67,f67,f67])).
% 3.83/0.99  
% 3.83/0.99  fof(f77,plain,(
% 3.83/0.99    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 3.83/0.99    inference(equality_resolution,[],[f73])).
% 3.83/0.99  
% 3.83/0.99  fof(f10,axiom,(
% 3.83/0.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f45,plain,(
% 3.83/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f10])).
% 3.83/0.99  
% 3.83/0.99  fof(f1,axiom,(
% 3.83/0.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f34,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f1])).
% 3.83/0.99  
% 3.83/0.99  fof(f8,axiom,(
% 3.83/0.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.83/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f43,plain,(
% 3.83/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.83/0.99    inference(cnf_transformation,[],[f8])).
% 3.83/0.99  
% 3.83/0.99  cnf(c_6,plain,
% 3.83/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.83/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_282,plain,
% 3.83/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_11,plain,
% 3.83/0.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 3.83/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_14,negated_conjecture,
% 3.83/0.99      ( k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
% 3.83/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_673,plain,
% 3.83/0.99      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k1_xboole_0 ),
% 3.83/0.99      inference(demodulation,[status(thm)],[c_11,c_14]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_9,plain,
% 3.83/0.99      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 3.83/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_281,plain,
% 3.83/0.99      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1779,plain,
% 3.83/0.99      ( r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_673,c_281]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_2,plain,
% 3.83/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.83/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_285,plain,
% 3.83/0.99      ( X0 = X1
% 3.83/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.83/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_5453,plain,
% 3.83/0.99      ( sK1 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_1779,c_285]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_5788,plain,
% 3.83/0.99      ( sK1 = k1_xboole_0 ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_282,c_5453]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1780,plain,
% 3.83/0.99      ( r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_11,c_281]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1892,plain,
% 3.83/0.99      ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_673,c_1780]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1,plain,
% 3.83/0.99      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 3.83/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_286,plain,
% 3.83/0.99      ( X0 = X1
% 3.83/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.83/0.99      | r2_xboole_0(X1,X0) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_4148,plain,
% 3.83/0.99      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0
% 3.83/0.99      | r2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_1892,c_286]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_316,plain,
% 3.83/0.99      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 3.83/0.99      | ~ r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X0)
% 3.83/0.99      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_388,plain,
% 3.83/0.99      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0)
% 3.83/0.99      | ~ r1_tarski(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.83/0.99      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0 ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_316]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_389,plain,
% 3.83/0.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
% 3.83/0.99      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) != iProver_top
% 3.83/0.99      | r1_tarski(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_388]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_391,plain,
% 3.83/0.99      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0
% 3.83/0.99      | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) != iProver_top
% 3.83/0.99      | r1_tarski(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != iProver_top ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_389]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_617,plain,
% 3.83/0.99      ( r1_tarski(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_618,plain,
% 3.83/0.99      ( r1_tarski(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_617]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_620,plain,
% 3.83/0.99      ( r1_tarski(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_618]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_4563,plain,
% 3.83/0.99      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0 ),
% 3.83/0.99      inference(global_propositional_subsumption,
% 3.83/0.99                [status(thm)],
% 3.83/0.99                [c_4148,c_391,c_620,c_1892]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_4567,plain,
% 3.83/0.99      ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k1_xboole_0)) = k1_xboole_0 ),
% 3.83/0.99      inference(demodulation,[status(thm)],[c_4563,c_673]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_4621,plain,
% 3.83/0.99      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1)) = k1_xboole_0 ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_11,c_4567]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_5994,plain,
% 3.83/0.99      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 3.83/0.99      inference(demodulation,[status(thm)],[c_5788,c_4621]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_13,plain,
% 3.83/0.99      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.83/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_10,plain,
% 3.83/0.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 3.83/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_0,plain,
% 3.83/0.99      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 3.83/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_170,plain,
% 3.83/0.99      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.83/0.99      inference(theory_normalisation,[status(thm)],[c_13,c_10,c_0]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_4582,plain,
% 3.83/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_4563,c_170]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_4596,plain,
% 3.83/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))))) != k1_xboole_0 ),
% 3.83/0.99      inference(demodulation,[status(thm)],[c_4582,c_4563]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_8,plain,
% 3.83/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.83/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_477,plain,
% 3.83/0.99      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_8,c_0]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_294,plain,
% 3.83/0.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_10,c_0]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_728,plain,
% 3.83/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_8,c_294]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_743,plain,
% 3.83/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_10,c_728]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1100,plain,
% 3.83/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_0,c_743]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_4597,plain,
% 3.83/0.99      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
% 3.83/0.99      inference(demodulation,[status(thm)],[c_4596,c_477,c_1100]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(contradiction,plain,
% 3.83/0.99      ( $false ),
% 3.83/0.99      inference(minisat,[status(thm)],[c_5994,c_4597]) ).
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.83/0.99  
% 3.83/0.99  ------                               Statistics
% 3.83/0.99  
% 3.83/0.99  ------ General
% 3.83/0.99  
% 3.83/0.99  abstr_ref_over_cycles:                  0
% 3.83/0.99  abstr_ref_under_cycles:                 0
% 3.83/0.99  gc_basic_clause_elim:                   0
% 3.83/0.99  forced_gc_time:                         0
% 3.83/0.99  parsing_time:                           0.012
% 3.83/0.99  unif_index_cands_time:                  0.
% 3.83/0.99  unif_index_add_time:                    0.
% 3.83/0.99  orderings_time:                         0.
% 3.83/0.99  out_proof_time:                         0.007
% 3.83/0.99  total_time:                             0.497
% 3.83/0.99  num_of_symbols:                         39
% 3.83/0.99  num_of_terms:                           9486
% 3.83/0.99  
% 3.83/0.99  ------ Preprocessing
% 3.83/0.99  
% 3.83/0.99  num_of_splits:                          0
% 3.83/0.99  num_of_split_atoms:                     0
% 3.83/0.99  num_of_reused_defs:                     0
% 3.83/0.99  num_eq_ax_congr_red:                    6
% 3.83/0.99  num_of_sem_filtered_clauses:            1
% 3.83/0.99  num_of_subtypes:                        0
% 3.83/0.99  monotx_restored_types:                  0
% 3.83/0.99  sat_num_of_epr_types:                   0
% 3.83/0.99  sat_num_of_non_cyclic_types:            0
% 3.83/0.99  sat_guarded_non_collapsed_types:        0
% 3.83/0.99  num_pure_diseq_elim:                    0
% 3.83/0.99  simp_replaced_by:                       0
% 3.83/0.99  res_preprocessed:                       69
% 3.83/0.99  prep_upred:                             0
% 3.83/0.99  prep_unflattend:                        0
% 3.83/0.99  smt_new_axioms:                         0
% 3.83/0.99  pred_elim_cands:                        2
% 3.83/0.99  pred_elim:                              0
% 3.83/0.99  pred_elim_cl:                           0
% 3.83/0.99  pred_elim_cycles:                       2
% 3.83/0.99  merged_defs:                            0
% 3.83/0.99  merged_defs_ncl:                        0
% 3.83/0.99  bin_hyper_res:                          0
% 3.83/0.99  prep_cycles:                            4
% 3.83/0.99  pred_elim_time:                         0.
% 3.83/0.99  splitting_time:                         0.
% 3.83/0.99  sem_filter_time:                        0.
% 3.83/0.99  monotx_time:                            0.001
% 3.83/0.99  subtype_inf_time:                       0.
% 3.83/0.99  
% 3.83/0.99  ------ Problem properties
% 3.83/0.99  
% 3.83/0.99  clauses:                                14
% 3.83/0.99  conjectures:                            1
% 3.83/0.99  epr:                                    4
% 3.83/0.99  horn:                                   12
% 3.83/0.99  ground:                                 1
% 3.83/0.99  unary:                                  10
% 3.83/0.99  binary:                                 2
% 3.83/0.99  lits:                                   20
% 3.83/0.99  lits_eq:                                12
% 3.83/0.99  fd_pure:                                0
% 3.83/0.99  fd_pseudo:                              0
% 3.83/0.99  fd_cond:                                0
% 3.83/0.99  fd_pseudo_cond:                         3
% 3.83/0.99  ac_symbols:                             1
% 3.83/0.99  
% 3.83/0.99  ------ Propositional Solver
% 3.83/0.99  
% 3.83/0.99  prop_solver_calls:                      29
% 3.83/0.99  prop_fast_solver_calls:                 336
% 3.83/0.99  smt_solver_calls:                       0
% 3.83/0.99  smt_fast_solver_calls:                  0
% 3.83/0.99  prop_num_of_clauses:                    1531
% 3.83/0.99  prop_preprocess_simplified:             3996
% 3.83/0.99  prop_fo_subsumed:                       1
% 3.83/0.99  prop_solver_time:                       0.
% 3.83/0.99  smt_solver_time:                        0.
% 3.83/0.99  smt_fast_solver_time:                   0.
% 3.83/0.99  prop_fast_solver_time:                  0.
% 3.83/0.99  prop_unsat_core_time:                   0.
% 3.83/0.99  
% 3.83/0.99  ------ QBF
% 3.83/0.99  
% 3.83/0.99  qbf_q_res:                              0
% 3.83/0.99  qbf_num_tautologies:                    0
% 3.83/0.99  qbf_prep_cycles:                        0
% 3.83/0.99  
% 3.83/0.99  ------ BMC1
% 3.83/0.99  
% 3.83/0.99  bmc1_current_bound:                     -1
% 3.83/0.99  bmc1_last_solved_bound:                 -1
% 3.83/0.99  bmc1_unsat_core_size:                   -1
% 3.83/0.99  bmc1_unsat_core_parents_size:           -1
% 3.83/0.99  bmc1_merge_next_fun:                    0
% 3.83/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.83/0.99  
% 3.83/0.99  ------ Instantiation
% 3.83/0.99  
% 3.83/0.99  inst_num_of_clauses:                    460
% 3.83/0.99  inst_num_in_passive:                    42
% 3.83/0.99  inst_num_in_active:                     211
% 3.83/0.99  inst_num_in_unprocessed:                210
% 3.83/0.99  inst_num_of_loops:                      290
% 3.83/0.99  inst_num_of_learning_restarts:          0
% 3.83/0.99  inst_num_moves_active_passive:          75
% 3.83/0.99  inst_lit_activity:                      0
% 3.83/0.99  inst_lit_activity_moves:                0
% 3.83/0.99  inst_num_tautologies:                   0
% 3.83/0.99  inst_num_prop_implied:                  0
% 3.83/0.99  inst_num_existing_simplified:           0
% 3.83/0.99  inst_num_eq_res_simplified:             0
% 3.83/0.99  inst_num_child_elim:                    0
% 3.83/0.99  inst_num_of_dismatching_blockings:      286
% 3.83/0.99  inst_num_of_non_proper_insts:           773
% 3.83/0.99  inst_num_of_duplicates:                 0
% 3.83/0.99  inst_inst_num_from_inst_to_res:         0
% 3.83/0.99  inst_dismatching_checking_time:         0.
% 3.83/0.99  
% 3.83/0.99  ------ Resolution
% 3.83/0.99  
% 3.83/0.99  res_num_of_clauses:                     0
% 3.83/0.99  res_num_in_passive:                     0
% 3.83/0.99  res_num_in_active:                      0
% 3.83/0.99  res_num_of_loops:                       73
% 3.83/0.99  res_forward_subset_subsumed:            31
% 3.83/0.99  res_backward_subset_subsumed:           6
% 3.83/0.99  res_forward_subsumed:                   0
% 3.83/0.99  res_backward_subsumed:                  0
% 3.83/0.99  res_forward_subsumption_resolution:     0
% 3.83/0.99  res_backward_subsumption_resolution:    0
% 3.83/0.99  res_clause_to_clause_subsumption:       3366
% 3.83/0.99  res_orphan_elimination:                 0
% 3.83/0.99  res_tautology_del:                      36
% 3.83/0.99  res_num_eq_res_simplified:              0
% 3.83/0.99  res_num_sel_changes:                    0
% 3.83/0.99  res_moves_from_active_to_pass:          0
% 3.83/0.99  
% 3.83/0.99  ------ Superposition
% 3.83/0.99  
% 3.83/0.99  sup_time_total:                         0.
% 3.83/0.99  sup_time_generating:                    0.
% 3.83/0.99  sup_time_sim_full:                      0.
% 3.83/0.99  sup_time_sim_immed:                     0.
% 3.83/0.99  
% 3.83/0.99  sup_num_of_clauses:                     251
% 3.83/0.99  sup_num_in_active:                      33
% 3.83/0.99  sup_num_in_passive:                     218
% 3.83/0.99  sup_num_of_loops:                       56
% 3.83/0.99  sup_fw_superposition:                   781
% 3.83/0.99  sup_bw_superposition:                   776
% 3.83/0.99  sup_immediate_simplified:               857
% 3.83/0.99  sup_given_eliminated:                   0
% 3.83/0.99  comparisons_done:                       0
% 3.83/0.99  comparisons_avoided:                    1
% 3.83/0.99  
% 3.83/0.99  ------ Simplifications
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  sim_fw_subset_subsumed:                 2
% 3.83/0.99  sim_bw_subset_subsumed:                 3
% 3.83/0.99  sim_fw_subsumed:                        46
% 3.83/0.99  sim_bw_subsumed:                        2
% 3.83/0.99  sim_fw_subsumption_res:                 0
% 3.83/0.99  sim_bw_subsumption_res:                 0
% 3.83/0.99  sim_tautology_del:                      0
% 3.83/0.99  sim_eq_tautology_del:                   88
% 3.83/0.99  sim_eq_res_simp:                        2
% 3.83/0.99  sim_fw_demodulated:                     663
% 3.83/0.99  sim_bw_demodulated:                     24
% 3.83/0.99  sim_light_normalised:                   154
% 3.83/0.99  sim_joinable_taut:                      103
% 3.83/0.99  sim_joinable_simp:                      0
% 3.83/0.99  sim_ac_normalised:                      0
% 3.83/0.99  sim_smt_subsumption:                    0
% 3.83/0.99  
%------------------------------------------------------------------------------
