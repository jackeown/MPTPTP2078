%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:52 EST 2020

% Result     : Theorem 7.87s
% Output     : CNFRefutation 7.87s
% Verified   : 
% Statistics : Number of formulae       :  117 (3119 expanded)
%              Number of clauses        :   56 ( 448 expanded)
%              Number of leaves         :   19 ( 965 expanded)
%              Depth                    :   32
%              Number of atoms          :  178 (3427 expanded)
%              Number of equality atoms :  163 (3412 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 )
   => ( k1_tarski(sK1) != sK0
      & k1_xboole_0 != sK0
      & k4_xboole_0(sK0,k1_tarski(sK1)) = k1_xboole_0 ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( k1_tarski(sK1) != sK0
    & k1_xboole_0 != sK0
    & k4_xboole_0(sK0,k1_tarski(sK1)) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f25])).

fof(f48,plain,(
    k4_xboole_0(sK0,k1_tarski(sK1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f55])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f33,f56])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f28,f57])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f38,f51])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f37,f52])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f36,f53])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f54])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f55])).

fof(f69,plain,(
    k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f48,f58,f59])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f27,f57])).

fof(f17,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f67,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f47,f59])).

fof(f3,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X2,X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) ),
    inference(definition_unfolding,[],[f29,f57,f56])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f23])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f41,f55,f59,f59,f55])).

fof(f50,plain,(
    k1_tarski(sK1) != sK0 ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK0 ),
    inference(definition_unfolding,[],[f50,f59])).

fof(f49,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_13,negated_conjecture,
    ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_423,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3,c_13])).

cnf(c_429,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_4])).

cnf(c_534,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_429])).

cnf(c_672,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_423,c_534])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_10,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_262,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_0,c_4,c_10])).

cnf(c_702,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_672,c_2,c_4,c_262])).

cnf(c_728,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_702,c_3])).

cnf(c_731,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_728,c_262])).

cnf(c_818,plain,
    ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4,c_731])).

cnf(c_832,plain,
    ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_818,c_2])).

cnf(c_1,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_261,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5871,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_832,c_261])).

cnf(c_669,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),k5_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_534])).

cnf(c_707,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),X1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_669,c_2])).

cnf(c_1337,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X0)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_707])).

cnf(c_679,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK0),k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),k5_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_423,c_534])).

cnf(c_697,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK0),k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_679,c_2])).

cnf(c_703,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK0),k5_xboole_0(k5_xboole_0(sK0,k1_xboole_0),X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_702,c_697])).

cnf(c_704,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK0),k5_xboole_0(sK0,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_703,c_2])).

cnf(c_792,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK0)),k5_xboole_0(sK0,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_704])).

cnf(c_799,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK0),k5_xboole_0(k5_xboole_0(sK0,X0),X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_704,c_3])).

cnf(c_806,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK0),k5_xboole_0(k5_xboole_0(sK0,X0),X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_799,c_262])).

cnf(c_1535,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,sK0),sK0),k1_xboole_0) = k5_xboole_0(sK0,k5_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_792,c_806])).

cnf(c_426,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_3])).

cnf(c_433,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_426,c_262])).

cnf(c_1565,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,sK0),sK0),k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_1535,c_2,c_433])).

cnf(c_1529,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK0),k1_xboole_0) = k5_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_4,c_806])).

cnf(c_2484,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK0,k1_xboole_0)) = k5_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_1529,c_3])).

cnf(c_2496,plain,
    ( k5_xboole_0(sK0,X0) = k5_xboole_0(X0,sK0) ),
    inference(demodulation,[status(thm)],[c_2484,c_2])).

cnf(c_3514,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK0),X1) = k5_xboole_0(sK0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2496,c_3])).

cnf(c_3531,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK0,X1)) = k5_xboole_0(k5_xboole_0(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_2496,c_3])).

cnf(c_3637,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK0),k5_xboole_0(sK0,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_1565,c_3514,c_3531])).

cnf(c_3638,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(X0,sK0)) = X0 ),
    inference(demodulation,[status(thm)],[c_3637,c_2,c_3514])).

cnf(c_3645,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK0,X0)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1337,c_3638])).

cnf(c_3688,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK0,X0)) = sK0 ),
    inference(demodulation,[status(thm)],[c_3645,c_2])).

cnf(c_839,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_832,c_731])).

cnf(c_3932,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) = k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_3688,c_839])).

cnf(c_4232,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_3932,c_3])).

cnf(c_5874,plain,
    ( r1_tarski(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5871,c_4232])).

cnf(c_3547,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = sK0 ),
    inference(superposition,[status(thm)],[c_2496,c_839])).

cnf(c_5875,plain,
    ( r1_tarski(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5874,c_3547])).

cnf(c_13963,plain,
    ( r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_832,c_5875])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_272,plain,
    ( ~ r1_tarski(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = sK0
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = sK0
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_273,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = sK0
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = sK0
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK0
    | k1_xboole_0 = sK0
    | r1_tarski(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_272])).

cnf(c_275,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
    | k1_xboole_0 = sK0
    | r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_273])).

cnf(c_11,negated_conjecture,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f49])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13963,c_275,c_11,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:48:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.76/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.76/1.49  
% 7.76/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.76/1.49  
% 7.76/1.49  ------  iProver source info
% 7.76/1.49  
% 7.76/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.76/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.76/1.49  git: non_committed_changes: false
% 7.76/1.49  git: last_make_outside_of_git: false
% 7.76/1.49  
% 7.76/1.49  ------ 
% 7.76/1.49  
% 7.76/1.49  ------ Input Options
% 7.76/1.49  
% 7.76/1.49  --out_options                           all
% 7.76/1.49  --tptp_safe_out                         true
% 7.76/1.49  --problem_path                          ""
% 7.76/1.49  --include_path                          ""
% 7.76/1.49  --clausifier                            res/vclausify_rel
% 7.76/1.49  --clausifier_options                    ""
% 7.76/1.49  --stdin                                 false
% 7.76/1.49  --stats_out                             all
% 7.76/1.49  
% 7.76/1.49  ------ General Options
% 7.76/1.49  
% 7.76/1.49  --fof                                   false
% 7.76/1.49  --time_out_real                         305.
% 7.76/1.49  --time_out_virtual                      -1.
% 7.76/1.49  --symbol_type_check                     false
% 7.76/1.49  --clausify_out                          false
% 7.76/1.49  --sig_cnt_out                           false
% 7.76/1.49  --trig_cnt_out                          false
% 7.76/1.49  --trig_cnt_out_tolerance                1.
% 7.76/1.49  --trig_cnt_out_sk_spl                   false
% 7.76/1.49  --abstr_cl_out                          false
% 7.76/1.49  
% 7.76/1.49  ------ Global Options
% 7.76/1.49  
% 7.76/1.49  --schedule                              default
% 7.76/1.49  --add_important_lit                     false
% 7.76/1.49  --prop_solver_per_cl                    1000
% 7.76/1.49  --min_unsat_core                        false
% 7.76/1.49  --soft_assumptions                      false
% 7.76/1.49  --soft_lemma_size                       3
% 7.76/1.49  --prop_impl_unit_size                   0
% 7.76/1.49  --prop_impl_unit                        []
% 7.76/1.49  --share_sel_clauses                     true
% 7.76/1.49  --reset_solvers                         false
% 7.76/1.49  --bc_imp_inh                            [conj_cone]
% 7.76/1.49  --conj_cone_tolerance                   3.
% 7.76/1.49  --extra_neg_conj                        none
% 7.76/1.49  --large_theory_mode                     true
% 7.76/1.49  --prolific_symb_bound                   200
% 7.76/1.49  --lt_threshold                          2000
% 7.76/1.49  --clause_weak_htbl                      true
% 7.76/1.49  --gc_record_bc_elim                     false
% 7.76/1.49  
% 7.76/1.49  ------ Preprocessing Options
% 7.76/1.49  
% 7.76/1.49  --preprocessing_flag                    true
% 7.76/1.49  --time_out_prep_mult                    0.1
% 7.76/1.49  --splitting_mode                        input
% 7.76/1.49  --splitting_grd                         true
% 7.76/1.49  --splitting_cvd                         false
% 7.76/1.49  --splitting_cvd_svl                     false
% 7.76/1.49  --splitting_nvd                         32
% 7.76/1.49  --sub_typing                            true
% 7.76/1.49  --prep_gs_sim                           true
% 7.76/1.49  --prep_unflatten                        true
% 7.76/1.49  --prep_res_sim                          true
% 7.76/1.49  --prep_upred                            true
% 7.76/1.49  --prep_sem_filter                       exhaustive
% 7.76/1.49  --prep_sem_filter_out                   false
% 7.76/1.49  --pred_elim                             true
% 7.76/1.49  --res_sim_input                         true
% 7.76/1.49  --eq_ax_congr_red                       true
% 7.76/1.49  --pure_diseq_elim                       true
% 7.76/1.49  --brand_transform                       false
% 7.76/1.49  --non_eq_to_eq                          false
% 7.76/1.49  --prep_def_merge                        true
% 7.76/1.49  --prep_def_merge_prop_impl              false
% 7.76/1.49  --prep_def_merge_mbd                    true
% 7.76/1.49  --prep_def_merge_tr_red                 false
% 7.76/1.49  --prep_def_merge_tr_cl                  false
% 7.76/1.49  --smt_preprocessing                     true
% 7.76/1.49  --smt_ac_axioms                         fast
% 7.76/1.49  --preprocessed_out                      false
% 7.76/1.49  --preprocessed_stats                    false
% 7.76/1.49  
% 7.76/1.49  ------ Abstraction refinement Options
% 7.76/1.49  
% 7.76/1.49  --abstr_ref                             []
% 7.76/1.49  --abstr_ref_prep                        false
% 7.76/1.49  --abstr_ref_until_sat                   false
% 7.76/1.49  --abstr_ref_sig_restrict                funpre
% 7.76/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.76/1.49  --abstr_ref_under                       []
% 7.76/1.49  
% 7.76/1.49  ------ SAT Options
% 7.76/1.49  
% 7.76/1.49  --sat_mode                              false
% 7.76/1.49  --sat_fm_restart_options                ""
% 7.76/1.49  --sat_gr_def                            false
% 7.76/1.49  --sat_epr_types                         true
% 7.76/1.49  --sat_non_cyclic_types                  false
% 7.76/1.49  --sat_finite_models                     false
% 7.76/1.49  --sat_fm_lemmas                         false
% 7.76/1.49  --sat_fm_prep                           false
% 7.76/1.49  --sat_fm_uc_incr                        true
% 7.76/1.49  --sat_out_model                         small
% 7.76/1.49  --sat_out_clauses                       false
% 7.76/1.49  
% 7.76/1.49  ------ QBF Options
% 7.76/1.49  
% 7.76/1.49  --qbf_mode                              false
% 7.76/1.49  --qbf_elim_univ                         false
% 7.76/1.49  --qbf_dom_inst                          none
% 7.76/1.49  --qbf_dom_pre_inst                      false
% 7.76/1.49  --qbf_sk_in                             false
% 7.76/1.49  --qbf_pred_elim                         true
% 7.76/1.49  --qbf_split                             512
% 7.76/1.49  
% 7.76/1.49  ------ BMC1 Options
% 7.76/1.49  
% 7.76/1.49  --bmc1_incremental                      false
% 7.76/1.49  --bmc1_axioms                           reachable_all
% 7.76/1.49  --bmc1_min_bound                        0
% 7.76/1.49  --bmc1_max_bound                        -1
% 7.76/1.49  --bmc1_max_bound_default                -1
% 7.76/1.49  --bmc1_symbol_reachability              true
% 7.76/1.49  --bmc1_property_lemmas                  false
% 7.76/1.49  --bmc1_k_induction                      false
% 7.76/1.49  --bmc1_non_equiv_states                 false
% 7.76/1.49  --bmc1_deadlock                         false
% 7.76/1.49  --bmc1_ucm                              false
% 7.76/1.49  --bmc1_add_unsat_core                   none
% 7.76/1.49  --bmc1_unsat_core_children              false
% 7.76/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.76/1.49  --bmc1_out_stat                         full
% 7.76/1.49  --bmc1_ground_init                      false
% 7.76/1.49  --bmc1_pre_inst_next_state              false
% 7.76/1.49  --bmc1_pre_inst_state                   false
% 7.76/1.49  --bmc1_pre_inst_reach_state             false
% 7.76/1.49  --bmc1_out_unsat_core                   false
% 7.76/1.49  --bmc1_aig_witness_out                  false
% 7.76/1.49  --bmc1_verbose                          false
% 7.76/1.49  --bmc1_dump_clauses_tptp                false
% 7.76/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.76/1.49  --bmc1_dump_file                        -
% 7.76/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.76/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.76/1.49  --bmc1_ucm_extend_mode                  1
% 7.76/1.49  --bmc1_ucm_init_mode                    2
% 7.76/1.49  --bmc1_ucm_cone_mode                    none
% 7.76/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.76/1.49  --bmc1_ucm_relax_model                  4
% 7.76/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.76/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.76/1.49  --bmc1_ucm_layered_model                none
% 7.76/1.49  --bmc1_ucm_max_lemma_size               10
% 7.76/1.49  
% 7.76/1.49  ------ AIG Options
% 7.76/1.49  
% 7.76/1.49  --aig_mode                              false
% 7.76/1.49  
% 7.76/1.49  ------ Instantiation Options
% 7.76/1.49  
% 7.76/1.49  --instantiation_flag                    true
% 7.76/1.49  --inst_sos_flag                         true
% 7.76/1.49  --inst_sos_phase                        true
% 7.76/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.76/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.76/1.49  --inst_lit_sel_side                     num_symb
% 7.76/1.49  --inst_solver_per_active                1400
% 7.76/1.49  --inst_solver_calls_frac                1.
% 7.76/1.49  --inst_passive_queue_type               priority_queues
% 7.76/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.76/1.49  --inst_passive_queues_freq              [25;2]
% 7.76/1.49  --inst_dismatching                      true
% 7.76/1.49  --inst_eager_unprocessed_to_passive     true
% 7.76/1.49  --inst_prop_sim_given                   true
% 7.76/1.49  --inst_prop_sim_new                     false
% 7.76/1.49  --inst_subs_new                         false
% 7.76/1.49  --inst_eq_res_simp                      false
% 7.76/1.49  --inst_subs_given                       false
% 7.76/1.49  --inst_orphan_elimination               true
% 7.76/1.49  --inst_learning_loop_flag               true
% 7.76/1.49  --inst_learning_start                   3000
% 7.76/1.49  --inst_learning_factor                  2
% 7.76/1.49  --inst_start_prop_sim_after_learn       3
% 7.76/1.49  --inst_sel_renew                        solver
% 7.76/1.49  --inst_lit_activity_flag                true
% 7.76/1.49  --inst_restr_to_given                   false
% 7.76/1.49  --inst_activity_threshold               500
% 7.76/1.49  --inst_out_proof                        true
% 7.76/1.49  
% 7.76/1.49  ------ Resolution Options
% 7.76/1.49  
% 7.76/1.49  --resolution_flag                       true
% 7.76/1.49  --res_lit_sel                           adaptive
% 7.76/1.49  --res_lit_sel_side                      none
% 7.76/1.49  --res_ordering                          kbo
% 7.76/1.49  --res_to_prop_solver                    active
% 7.76/1.49  --res_prop_simpl_new                    false
% 7.76/1.49  --res_prop_simpl_given                  true
% 7.76/1.49  --res_passive_queue_type                priority_queues
% 7.76/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.87/1.49  --res_passive_queues_freq               [15;5]
% 7.87/1.49  --res_forward_subs                      full
% 7.87/1.49  --res_backward_subs                     full
% 7.87/1.49  --res_forward_subs_resolution           true
% 7.87/1.49  --res_backward_subs_resolution          true
% 7.87/1.49  --res_orphan_elimination                true
% 7.87/1.49  --res_time_limit                        2.
% 7.87/1.49  --res_out_proof                         true
% 7.87/1.49  
% 7.87/1.49  ------ Superposition Options
% 7.87/1.49  
% 7.87/1.49  --superposition_flag                    true
% 7.87/1.49  --sup_passive_queue_type                priority_queues
% 7.87/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.87/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.87/1.49  --demod_completeness_check              fast
% 7.87/1.49  --demod_use_ground                      true
% 7.87/1.49  --sup_to_prop_solver                    passive
% 7.87/1.49  --sup_prop_simpl_new                    true
% 7.87/1.49  --sup_prop_simpl_given                  true
% 7.87/1.49  --sup_fun_splitting                     true
% 7.87/1.49  --sup_smt_interval                      50000
% 7.87/1.49  
% 7.87/1.49  ------ Superposition Simplification Setup
% 7.87/1.49  
% 7.87/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.87/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.87/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.87/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.87/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.87/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.87/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.87/1.49  --sup_immed_triv                        [TrivRules]
% 7.87/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.87/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.87/1.49  --sup_immed_bw_main                     []
% 7.87/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.87/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.87/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.87/1.49  --sup_input_bw                          []
% 7.87/1.49  
% 7.87/1.49  ------ Combination Options
% 7.87/1.49  
% 7.87/1.49  --comb_res_mult                         3
% 7.87/1.49  --comb_sup_mult                         2
% 7.87/1.49  --comb_inst_mult                        10
% 7.87/1.49  
% 7.87/1.49  ------ Debug Options
% 7.87/1.49  
% 7.87/1.49  --dbg_backtrace                         false
% 7.87/1.49  --dbg_dump_prop_clauses                 false
% 7.87/1.49  --dbg_dump_prop_clauses_file            -
% 7.87/1.49  --dbg_out_stat                          false
% 7.87/1.49  ------ Parsing...
% 7.87/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.87/1.49  
% 7.87/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.87/1.49  
% 7.87/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.87/1.49  
% 7.87/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.87/1.49  ------ Proving...
% 7.87/1.49  ------ Problem Properties 
% 7.87/1.49  
% 7.87/1.49  
% 7.87/1.49  clauses                                 14
% 7.87/1.49  conjectures                             3
% 7.87/1.49  EPR                                     1
% 7.87/1.49  Horn                                    13
% 7.87/1.49  unary                                   13
% 7.87/1.49  binary                                  0
% 7.87/1.49  lits                                    18
% 7.87/1.49  lits eq                                 12
% 7.87/1.49  fd_pure                                 0
% 7.87/1.49  fd_pseudo                               0
% 7.87/1.49  fd_cond                                 0
% 7.87/1.49  fd_pseudo_cond                          1
% 7.87/1.49  AC symbols                              0
% 7.87/1.49  
% 7.87/1.49  ------ Schedule dynamic 5 is on 
% 7.87/1.49  
% 7.87/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.87/1.49  
% 7.87/1.49  
% 7.87/1.49  ------ 
% 7.87/1.49  Current options:
% 7.87/1.49  ------ 
% 7.87/1.49  
% 7.87/1.49  ------ Input Options
% 7.87/1.49  
% 7.87/1.49  --out_options                           all
% 7.87/1.49  --tptp_safe_out                         true
% 7.87/1.49  --problem_path                          ""
% 7.87/1.49  --include_path                          ""
% 7.87/1.49  --clausifier                            res/vclausify_rel
% 7.87/1.49  --clausifier_options                    ""
% 7.87/1.49  --stdin                                 false
% 7.87/1.49  --stats_out                             all
% 7.87/1.49  
% 7.87/1.49  ------ General Options
% 7.87/1.49  
% 7.87/1.49  --fof                                   false
% 7.87/1.49  --time_out_real                         305.
% 7.87/1.49  --time_out_virtual                      -1.
% 7.87/1.49  --symbol_type_check                     false
% 7.87/1.49  --clausify_out                          false
% 7.87/1.49  --sig_cnt_out                           false
% 7.87/1.49  --trig_cnt_out                          false
% 7.87/1.49  --trig_cnt_out_tolerance                1.
% 7.87/1.49  --trig_cnt_out_sk_spl                   false
% 7.87/1.49  --abstr_cl_out                          false
% 7.87/1.49  
% 7.87/1.49  ------ Global Options
% 7.87/1.49  
% 7.87/1.49  --schedule                              default
% 7.87/1.49  --add_important_lit                     false
% 7.87/1.49  --prop_solver_per_cl                    1000
% 7.87/1.49  --min_unsat_core                        false
% 7.87/1.49  --soft_assumptions                      false
% 7.87/1.49  --soft_lemma_size                       3
% 7.87/1.49  --prop_impl_unit_size                   0
% 7.87/1.49  --prop_impl_unit                        []
% 7.87/1.49  --share_sel_clauses                     true
% 7.87/1.49  --reset_solvers                         false
% 7.87/1.49  --bc_imp_inh                            [conj_cone]
% 7.87/1.49  --conj_cone_tolerance                   3.
% 7.87/1.49  --extra_neg_conj                        none
% 7.87/1.49  --large_theory_mode                     true
% 7.87/1.49  --prolific_symb_bound                   200
% 7.87/1.49  --lt_threshold                          2000
% 7.87/1.49  --clause_weak_htbl                      true
% 7.87/1.49  --gc_record_bc_elim                     false
% 7.87/1.49  
% 7.87/1.49  ------ Preprocessing Options
% 7.87/1.49  
% 7.87/1.49  --preprocessing_flag                    true
% 7.87/1.49  --time_out_prep_mult                    0.1
% 7.87/1.49  --splitting_mode                        input
% 7.87/1.49  --splitting_grd                         true
% 7.87/1.49  --splitting_cvd                         false
% 7.87/1.49  --splitting_cvd_svl                     false
% 7.87/1.49  --splitting_nvd                         32
% 7.87/1.49  --sub_typing                            true
% 7.87/1.49  --prep_gs_sim                           true
% 7.87/1.49  --prep_unflatten                        true
% 7.87/1.49  --prep_res_sim                          true
% 7.87/1.49  --prep_upred                            true
% 7.87/1.49  --prep_sem_filter                       exhaustive
% 7.87/1.49  --prep_sem_filter_out                   false
% 7.87/1.49  --pred_elim                             true
% 7.87/1.49  --res_sim_input                         true
% 7.87/1.49  --eq_ax_congr_red                       true
% 7.87/1.49  --pure_diseq_elim                       true
% 7.87/1.49  --brand_transform                       false
% 7.87/1.49  --non_eq_to_eq                          false
% 7.87/1.49  --prep_def_merge                        true
% 7.87/1.49  --prep_def_merge_prop_impl              false
% 7.87/1.49  --prep_def_merge_mbd                    true
% 7.87/1.49  --prep_def_merge_tr_red                 false
% 7.87/1.49  --prep_def_merge_tr_cl                  false
% 7.87/1.49  --smt_preprocessing                     true
% 7.87/1.49  --smt_ac_axioms                         fast
% 7.87/1.49  --preprocessed_out                      false
% 7.87/1.49  --preprocessed_stats                    false
% 7.87/1.49  
% 7.87/1.49  ------ Abstraction refinement Options
% 7.87/1.49  
% 7.87/1.49  --abstr_ref                             []
% 7.87/1.49  --abstr_ref_prep                        false
% 7.87/1.49  --abstr_ref_until_sat                   false
% 7.87/1.49  --abstr_ref_sig_restrict                funpre
% 7.87/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.87/1.49  --abstr_ref_under                       []
% 7.87/1.49  
% 7.87/1.49  ------ SAT Options
% 7.87/1.49  
% 7.87/1.49  --sat_mode                              false
% 7.87/1.49  --sat_fm_restart_options                ""
% 7.87/1.49  --sat_gr_def                            false
% 7.87/1.49  --sat_epr_types                         true
% 7.87/1.49  --sat_non_cyclic_types                  false
% 7.87/1.49  --sat_finite_models                     false
% 7.87/1.49  --sat_fm_lemmas                         false
% 7.87/1.49  --sat_fm_prep                           false
% 7.87/1.49  --sat_fm_uc_incr                        true
% 7.87/1.49  --sat_out_model                         small
% 7.87/1.49  --sat_out_clauses                       false
% 7.87/1.49  
% 7.87/1.49  ------ QBF Options
% 7.87/1.49  
% 7.87/1.49  --qbf_mode                              false
% 7.87/1.49  --qbf_elim_univ                         false
% 7.87/1.49  --qbf_dom_inst                          none
% 7.87/1.49  --qbf_dom_pre_inst                      false
% 7.87/1.49  --qbf_sk_in                             false
% 7.87/1.49  --qbf_pred_elim                         true
% 7.87/1.49  --qbf_split                             512
% 7.87/1.49  
% 7.87/1.49  ------ BMC1 Options
% 7.87/1.49  
% 7.87/1.49  --bmc1_incremental                      false
% 7.87/1.49  --bmc1_axioms                           reachable_all
% 7.87/1.49  --bmc1_min_bound                        0
% 7.87/1.49  --bmc1_max_bound                        -1
% 7.87/1.49  --bmc1_max_bound_default                -1
% 7.87/1.49  --bmc1_symbol_reachability              true
% 7.87/1.49  --bmc1_property_lemmas                  false
% 7.87/1.49  --bmc1_k_induction                      false
% 7.87/1.49  --bmc1_non_equiv_states                 false
% 7.87/1.49  --bmc1_deadlock                         false
% 7.87/1.49  --bmc1_ucm                              false
% 7.87/1.49  --bmc1_add_unsat_core                   none
% 7.87/1.49  --bmc1_unsat_core_children              false
% 7.87/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.87/1.49  --bmc1_out_stat                         full
% 7.87/1.49  --bmc1_ground_init                      false
% 7.87/1.49  --bmc1_pre_inst_next_state              false
% 7.87/1.49  --bmc1_pre_inst_state                   false
% 7.87/1.49  --bmc1_pre_inst_reach_state             false
% 7.87/1.49  --bmc1_out_unsat_core                   false
% 7.87/1.49  --bmc1_aig_witness_out                  false
% 7.87/1.49  --bmc1_verbose                          false
% 7.87/1.49  --bmc1_dump_clauses_tptp                false
% 7.87/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.87/1.49  --bmc1_dump_file                        -
% 7.87/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.87/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.87/1.49  --bmc1_ucm_extend_mode                  1
% 7.87/1.49  --bmc1_ucm_init_mode                    2
% 7.87/1.49  --bmc1_ucm_cone_mode                    none
% 7.87/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.87/1.49  --bmc1_ucm_relax_model                  4
% 7.87/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.87/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.87/1.49  --bmc1_ucm_layered_model                none
% 7.87/1.49  --bmc1_ucm_max_lemma_size               10
% 7.87/1.49  
% 7.87/1.49  ------ AIG Options
% 7.87/1.49  
% 7.87/1.49  --aig_mode                              false
% 7.87/1.49  
% 7.87/1.49  ------ Instantiation Options
% 7.87/1.49  
% 7.87/1.49  --instantiation_flag                    true
% 7.87/1.49  --inst_sos_flag                         true
% 7.87/1.49  --inst_sos_phase                        true
% 7.87/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.87/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.87/1.49  --inst_lit_sel_side                     none
% 7.87/1.49  --inst_solver_per_active                1400
% 7.87/1.49  --inst_solver_calls_frac                1.
% 7.87/1.49  --inst_passive_queue_type               priority_queues
% 7.87/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.87/1.49  --inst_passive_queues_freq              [25;2]
% 7.87/1.49  --inst_dismatching                      true
% 7.87/1.49  --inst_eager_unprocessed_to_passive     true
% 7.87/1.49  --inst_prop_sim_given                   true
% 7.87/1.49  --inst_prop_sim_new                     false
% 7.87/1.49  --inst_subs_new                         false
% 7.87/1.49  --inst_eq_res_simp                      false
% 7.87/1.49  --inst_subs_given                       false
% 7.87/1.49  --inst_orphan_elimination               true
% 7.87/1.49  --inst_learning_loop_flag               true
% 7.87/1.49  --inst_learning_start                   3000
% 7.87/1.49  --inst_learning_factor                  2
% 7.87/1.49  --inst_start_prop_sim_after_learn       3
% 7.87/1.49  --inst_sel_renew                        solver
% 7.87/1.49  --inst_lit_activity_flag                true
% 7.87/1.49  --inst_restr_to_given                   false
% 7.87/1.49  --inst_activity_threshold               500
% 7.87/1.49  --inst_out_proof                        true
% 7.87/1.49  
% 7.87/1.49  ------ Resolution Options
% 7.87/1.49  
% 7.87/1.49  --resolution_flag                       false
% 7.87/1.49  --res_lit_sel                           adaptive
% 7.87/1.49  --res_lit_sel_side                      none
% 7.87/1.49  --res_ordering                          kbo
% 7.87/1.49  --res_to_prop_solver                    active
% 7.87/1.49  --res_prop_simpl_new                    false
% 7.87/1.49  --res_prop_simpl_given                  true
% 7.87/1.49  --res_passive_queue_type                priority_queues
% 7.87/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.87/1.49  --res_passive_queues_freq               [15;5]
% 7.87/1.49  --res_forward_subs                      full
% 7.87/1.49  --res_backward_subs                     full
% 7.87/1.49  --res_forward_subs_resolution           true
% 7.87/1.49  --res_backward_subs_resolution          true
% 7.87/1.49  --res_orphan_elimination                true
% 7.87/1.49  --res_time_limit                        2.
% 7.87/1.49  --res_out_proof                         true
% 7.87/1.49  
% 7.87/1.49  ------ Superposition Options
% 7.87/1.49  
% 7.87/1.49  --superposition_flag                    true
% 7.87/1.49  --sup_passive_queue_type                priority_queues
% 7.87/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.87/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.87/1.49  --demod_completeness_check              fast
% 7.87/1.49  --demod_use_ground                      true
% 7.87/1.49  --sup_to_prop_solver                    passive
% 7.87/1.49  --sup_prop_simpl_new                    true
% 7.87/1.49  --sup_prop_simpl_given                  true
% 7.87/1.49  --sup_fun_splitting                     true
% 7.87/1.49  --sup_smt_interval                      50000
% 7.87/1.49  
% 7.87/1.49  ------ Superposition Simplification Setup
% 7.87/1.49  
% 7.87/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.87/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.87/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.87/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.87/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.87/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.87/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.87/1.49  --sup_immed_triv                        [TrivRules]
% 7.87/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.87/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.87/1.49  --sup_immed_bw_main                     []
% 7.87/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.87/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.87/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.87/1.49  --sup_input_bw                          []
% 7.87/1.49  
% 7.87/1.49  ------ Combination Options
% 7.87/1.49  
% 7.87/1.49  --comb_res_mult                         3
% 7.87/1.49  --comb_sup_mult                         2
% 7.87/1.49  --comb_inst_mult                        10
% 7.87/1.49  
% 7.87/1.49  ------ Debug Options
% 7.87/1.49  
% 7.87/1.49  --dbg_backtrace                         false
% 7.87/1.49  --dbg_dump_prop_clauses                 false
% 7.87/1.49  --dbg_dump_prop_clauses_file            -
% 7.87/1.49  --dbg_out_stat                          false
% 7.87/1.49  
% 7.87/1.49  
% 7.87/1.49  
% 7.87/1.49  
% 7.87/1.49  ------ Proving...
% 7.87/1.49  
% 7.87/1.49  
% 7.87/1.49  % SZS status Theorem for theBenchmark.p
% 7.87/1.49  
% 7.87/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.87/1.49  
% 7.87/1.49  fof(f6,axiom,(
% 7.87/1.49    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f32,plain,(
% 7.87/1.49    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.87/1.49    inference(cnf_transformation,[],[f6])).
% 7.87/1.49  
% 7.87/1.49  fof(f5,axiom,(
% 7.87/1.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f31,plain,(
% 7.87/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f5])).
% 7.87/1.49  
% 7.87/1.49  fof(f18,conjecture,(
% 7.87/1.49    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0)),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f19,negated_conjecture,(
% 7.87/1.49    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0)),
% 7.87/1.49    inference(negated_conjecture,[],[f18])).
% 7.87/1.49  
% 7.87/1.49  fof(f22,plain,(
% 7.87/1.49    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0)),
% 7.87/1.49    inference(ennf_transformation,[],[f19])).
% 7.87/1.49  
% 7.87/1.49  fof(f25,plain,(
% 7.87/1.49    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k4_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0) => (k1_tarski(sK1) != sK0 & k1_xboole_0 != sK0 & k4_xboole_0(sK0,k1_tarski(sK1)) = k1_xboole_0)),
% 7.87/1.49    introduced(choice_axiom,[])).
% 7.87/1.49  
% 7.87/1.49  fof(f26,plain,(
% 7.87/1.49    k1_tarski(sK1) != sK0 & k1_xboole_0 != sK0 & k4_xboole_0(sK0,k1_tarski(sK1)) = k1_xboole_0),
% 7.87/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f25])).
% 7.87/1.49  
% 7.87/1.49  fof(f48,plain,(
% 7.87/1.49    k4_xboole_0(sK0,k1_tarski(sK1)) = k1_xboole_0),
% 7.87/1.49    inference(cnf_transformation,[],[f26])).
% 7.87/1.49  
% 7.87/1.49  fof(f2,axiom,(
% 7.87/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f28,plain,(
% 7.87/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.87/1.49    inference(cnf_transformation,[],[f2])).
% 7.87/1.49  
% 7.87/1.49  fof(f7,axiom,(
% 7.87/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f33,plain,(
% 7.87/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 7.87/1.49    inference(cnf_transformation,[],[f7])).
% 7.87/1.49  
% 7.87/1.49  fof(f16,axiom,(
% 7.87/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f46,plain,(
% 7.87/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.87/1.49    inference(cnf_transformation,[],[f16])).
% 7.87/1.49  
% 7.87/1.49  fof(f56,plain,(
% 7.87/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.87/1.49    inference(definition_unfolding,[],[f46,f55])).
% 7.87/1.49  
% 7.87/1.49  fof(f57,plain,(
% 7.87/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 7.87/1.49    inference(definition_unfolding,[],[f33,f56])).
% 7.87/1.49  
% 7.87/1.49  fof(f58,plain,(
% 7.87/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 7.87/1.49    inference(definition_unfolding,[],[f28,f57])).
% 7.87/1.49  
% 7.87/1.49  fof(f8,axiom,(
% 7.87/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f34,plain,(
% 7.87/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f8])).
% 7.87/1.49  
% 7.87/1.49  fof(f9,axiom,(
% 7.87/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f35,plain,(
% 7.87/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f9])).
% 7.87/1.49  
% 7.87/1.49  fof(f10,axiom,(
% 7.87/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f36,plain,(
% 7.87/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f10])).
% 7.87/1.49  
% 7.87/1.49  fof(f11,axiom,(
% 7.87/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f37,plain,(
% 7.87/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f11])).
% 7.87/1.49  
% 7.87/1.49  fof(f12,axiom,(
% 7.87/1.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f38,plain,(
% 7.87/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f12])).
% 7.87/1.49  
% 7.87/1.49  fof(f13,axiom,(
% 7.87/1.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f39,plain,(
% 7.87/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f13])).
% 7.87/1.49  
% 7.87/1.49  fof(f14,axiom,(
% 7.87/1.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f40,plain,(
% 7.87/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f14])).
% 7.87/1.49  
% 7.87/1.49  fof(f51,plain,(
% 7.87/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.87/1.49    inference(definition_unfolding,[],[f39,f40])).
% 7.87/1.49  
% 7.87/1.49  fof(f52,plain,(
% 7.87/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.87/1.49    inference(definition_unfolding,[],[f38,f51])).
% 7.87/1.49  
% 7.87/1.49  fof(f53,plain,(
% 7.87/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.87/1.49    inference(definition_unfolding,[],[f37,f52])).
% 7.87/1.49  
% 7.87/1.49  fof(f54,plain,(
% 7.87/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.87/1.49    inference(definition_unfolding,[],[f36,f53])).
% 7.87/1.49  
% 7.87/1.49  fof(f55,plain,(
% 7.87/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.87/1.49    inference(definition_unfolding,[],[f35,f54])).
% 7.87/1.49  
% 7.87/1.49  fof(f59,plain,(
% 7.87/1.49    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.87/1.49    inference(definition_unfolding,[],[f34,f55])).
% 7.87/1.49  
% 7.87/1.49  fof(f69,plain,(
% 7.87/1.49    k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) = k1_xboole_0),
% 7.87/1.49    inference(definition_unfolding,[],[f48,f58,f59])).
% 7.87/1.49  
% 7.87/1.49  fof(f4,axiom,(
% 7.87/1.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f30,plain,(
% 7.87/1.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.87/1.49    inference(cnf_transformation,[],[f4])).
% 7.87/1.49  
% 7.87/1.49  fof(f1,axiom,(
% 7.87/1.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f20,plain,(
% 7.87/1.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.87/1.49    inference(rectify,[],[f1])).
% 7.87/1.49  
% 7.87/1.49  fof(f27,plain,(
% 7.87/1.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.87/1.49    inference(cnf_transformation,[],[f20])).
% 7.87/1.49  
% 7.87/1.49  fof(f60,plain,(
% 7.87/1.49    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 7.87/1.49    inference(definition_unfolding,[],[f27,f57])).
% 7.87/1.49  
% 7.87/1.49  fof(f17,axiom,(
% 7.87/1.49    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f47,plain,(
% 7.87/1.49    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 7.87/1.49    inference(cnf_transformation,[],[f17])).
% 7.87/1.49  
% 7.87/1.49  fof(f67,plain,(
% 7.87/1.49    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 7.87/1.49    inference(definition_unfolding,[],[f47,f59])).
% 7.87/1.49  
% 7.87/1.49  fof(f3,axiom,(
% 7.87/1.49    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f29,plain,(
% 7.87/1.49    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 7.87/1.49    inference(cnf_transformation,[],[f3])).
% 7.87/1.49  
% 7.87/1.49  fof(f61,plain,(
% 7.87/1.49    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)))) )),
% 7.87/1.49    inference(definition_unfolding,[],[f29,f57,f56])).
% 7.87/1.49  
% 7.87/1.49  fof(f15,axiom,(
% 7.87/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f21,plain,(
% 7.87/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 7.87/1.49    inference(ennf_transformation,[],[f15])).
% 7.87/1.49  
% 7.87/1.49  fof(f23,plain,(
% 7.87/1.49    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 7.87/1.49    inference(nnf_transformation,[],[f21])).
% 7.87/1.49  
% 7.87/1.49  fof(f24,plain,(
% 7.87/1.49    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 7.87/1.49    inference(flattening,[],[f23])).
% 7.87/1.49  
% 7.87/1.49  fof(f41,plain,(
% 7.87/1.49    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 7.87/1.49    inference(cnf_transformation,[],[f24])).
% 7.87/1.49  
% 7.87/1.49  fof(f66,plain,(
% 7.87/1.49    ( ! [X2,X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0 | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 7.87/1.49    inference(definition_unfolding,[],[f41,f55,f59,f59,f55])).
% 7.87/1.49  
% 7.87/1.49  fof(f50,plain,(
% 7.87/1.49    k1_tarski(sK1) != sK0),
% 7.87/1.49    inference(cnf_transformation,[],[f26])).
% 7.87/1.49  
% 7.87/1.49  fof(f68,plain,(
% 7.87/1.49    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK0),
% 7.87/1.49    inference(definition_unfolding,[],[f50,f59])).
% 7.87/1.49  
% 7.87/1.49  fof(f49,plain,(
% 7.87/1.49    k1_xboole_0 != sK0),
% 7.87/1.49    inference(cnf_transformation,[],[f26])).
% 7.87/1.49  
% 7.87/1.49  cnf(c_4,plain,
% 7.87/1.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.87/1.49      inference(cnf_transformation,[],[f32]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_3,plain,
% 7.87/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.87/1.49      inference(cnf_transformation,[],[f31]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_13,negated_conjecture,
% 7.87/1.49      ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) = k1_xboole_0 ),
% 7.87/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_423,plain,
% 7.87/1.49      ( k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))) = k1_xboole_0 ),
% 7.87/1.49      inference(demodulation,[status(thm)],[c_3,c_13]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_429,plain,
% 7.87/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_3,c_4]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_534,plain,
% 7.87/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = k1_xboole_0 ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_3,c_429]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_672,plain,
% 7.87/1.49      ( k5_xboole_0(k5_xboole_0(sK0,sK0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),k1_xboole_0)) = k1_xboole_0 ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_423,c_534]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2,plain,
% 7.87/1.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.87/1.49      inference(cnf_transformation,[],[f30]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_0,plain,
% 7.87/1.49      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
% 7.87/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_10,plain,
% 7.87/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 7.87/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_262,plain,
% 7.87/1.49      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.87/1.49      inference(light_normalisation,[status(thm)],[c_0,c_4,c_10]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_702,plain,
% 7.87/1.49      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k1_xboole_0 ),
% 7.87/1.49      inference(demodulation,[status(thm)],[c_672,c_2,c_4,c_262]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_728,plain,
% 7.87/1.49      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_702,c_3]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_731,plain,
% 7.87/1.49      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),X0)) = X0 ),
% 7.87/1.49      inference(light_normalisation,[status(thm)],[c_728,c_262]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_818,plain,
% 7.87/1.49      ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_4,c_731]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_832,plain,
% 7.87/1.49      ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 7.87/1.49      inference(demodulation,[status(thm)],[c_818,c_2]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1,plain,
% 7.87/1.49      ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) ),
% 7.87/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_261,plain,
% 7.87/1.49      ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) = iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_5871,plain,
% 7.87/1.49      ( r1_tarski(k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0))) = iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_832,c_261]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_669,plain,
% 7.87/1.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),k5_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_4,c_534]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_707,plain,
% 7.87/1.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),X1) = k1_xboole_0 ),
% 7.87/1.49      inference(demodulation,[status(thm)],[c_669,c_2]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1337,plain,
% 7.87/1.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X0)),X1) = k1_xboole_0 ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_3,c_707]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_679,plain,
% 7.87/1.49      ( k5_xboole_0(k5_xboole_0(X0,sK0),k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),k5_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_423,c_534]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_697,plain,
% 7.87/1.49      ( k5_xboole_0(k5_xboole_0(X0,sK0),k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),X0)) = k1_xboole_0 ),
% 7.87/1.49      inference(light_normalisation,[status(thm)],[c_679,c_2]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_703,plain,
% 7.87/1.49      ( k5_xboole_0(k5_xboole_0(X0,sK0),k5_xboole_0(k5_xboole_0(sK0,k1_xboole_0),X0)) = k1_xboole_0 ),
% 7.87/1.49      inference(demodulation,[status(thm)],[c_702,c_697]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_704,plain,
% 7.87/1.49      ( k5_xboole_0(k5_xboole_0(X0,sK0),k5_xboole_0(sK0,X0)) = k1_xboole_0 ),
% 7.87/1.49      inference(demodulation,[status(thm)],[c_703,c_2]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_792,plain,
% 7.87/1.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK0)),k5_xboole_0(sK0,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_3,c_704]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_799,plain,
% 7.87/1.49      ( k5_xboole_0(k5_xboole_0(X0,sK0),k5_xboole_0(k5_xboole_0(sK0,X0),X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_704,c_3]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_806,plain,
% 7.87/1.49      ( k5_xboole_0(k5_xboole_0(X0,sK0),k5_xboole_0(k5_xboole_0(sK0,X0),X1)) = X1 ),
% 7.87/1.49      inference(demodulation,[status(thm)],[c_799,c_262]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1535,plain,
% 7.87/1.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,sK0),sK0),k1_xboole_0) = k5_xboole_0(sK0,k5_xboole_0(sK0,X0)) ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_792,c_806]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_426,plain,
% 7.87/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_4,c_3]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_433,plain,
% 7.87/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 7.87/1.49      inference(demodulation,[status(thm)],[c_426,c_262]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1565,plain,
% 7.87/1.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,sK0),sK0),k1_xboole_0) = X0 ),
% 7.87/1.49      inference(demodulation,[status(thm)],[c_1535,c_2,c_433]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_1529,plain,
% 7.87/1.49      ( k5_xboole_0(k5_xboole_0(X0,sK0),k1_xboole_0) = k5_xboole_0(sK0,X0) ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_4,c_806]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2484,plain,
% 7.87/1.49      ( k5_xboole_0(X0,k5_xboole_0(sK0,k1_xboole_0)) = k5_xboole_0(sK0,X0) ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_1529,c_3]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_2496,plain,
% 7.87/1.49      ( k5_xboole_0(sK0,X0) = k5_xboole_0(X0,sK0) ),
% 7.87/1.49      inference(demodulation,[status(thm)],[c_2484,c_2]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_3514,plain,
% 7.87/1.49      ( k5_xboole_0(k5_xboole_0(X0,sK0),X1) = k5_xboole_0(sK0,k5_xboole_0(X0,X1)) ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_2496,c_3]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_3531,plain,
% 7.87/1.49      ( k5_xboole_0(X0,k5_xboole_0(sK0,X1)) = k5_xboole_0(k5_xboole_0(sK0,X0),X1) ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_2496,c_3]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_3637,plain,
% 7.87/1.49      ( k5_xboole_0(k5_xboole_0(X0,sK0),k5_xboole_0(sK0,k1_xboole_0)) = X0 ),
% 7.87/1.49      inference(demodulation,[status(thm)],[c_1565,c_3514,c_3531]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_3638,plain,
% 7.87/1.49      ( k5_xboole_0(sK0,k5_xboole_0(X0,sK0)) = X0 ),
% 7.87/1.49      inference(demodulation,[status(thm)],[c_3637,c_2,c_3514]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_3645,plain,
% 7.87/1.49      ( k5_xboole_0(X0,k5_xboole_0(sK0,X0)) = k5_xboole_0(sK0,k1_xboole_0) ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_1337,c_3638]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_3688,plain,
% 7.87/1.49      ( k5_xboole_0(X0,k5_xboole_0(sK0,X0)) = sK0 ),
% 7.87/1.49      inference(demodulation,[status(thm)],[c_3645,c_2]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_839,plain,
% 7.87/1.49      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) = X0 ),
% 7.87/1.49      inference(demodulation,[status(thm)],[c_832,c_731]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_3932,plain,
% 7.87/1.49      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) = k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_3688,c_839]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_4232,plain,
% 7.87/1.49      ( k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK0,X0)) ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_3932,c_3]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_5874,plain,
% 7.87/1.49      ( r1_tarski(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0))) = iProver_top ),
% 7.87/1.49      inference(demodulation,[status(thm)],[c_5871,c_4232]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_3547,plain,
% 7.87/1.49      ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = sK0 ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_2496,c_839]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_5875,plain,
% 7.87/1.49      ( r1_tarski(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0))) = iProver_top ),
% 7.87/1.49      inference(light_normalisation,[status(thm)],[c_5874,c_3547]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_13963,plain,
% 7.87/1.49      ( r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
% 7.87/1.49      inference(superposition,[status(thm)],[c_832,c_5875]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_9,plain,
% 7.87/1.49      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
% 7.87/1.49      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
% 7.87/1.49      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
% 7.87/1.49      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 7.87/1.49      | k1_xboole_0 = X0 ),
% 7.87/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_272,plain,
% 7.87/1.49      ( ~ r1_tarski(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
% 7.87/1.49      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = sK0
% 7.87/1.49      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = sK0
% 7.87/1.49      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK0
% 7.87/1.49      | k1_xboole_0 = sK0 ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_273,plain,
% 7.87/1.49      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = sK0
% 7.87/1.49      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = sK0
% 7.87/1.49      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK0
% 7.87/1.49      | k1_xboole_0 = sK0
% 7.87/1.49      | r1_tarski(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
% 7.87/1.49      inference(predicate_to_equality,[status(thm)],[c_272]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_275,plain,
% 7.87/1.49      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = sK0
% 7.87/1.49      | k1_xboole_0 = sK0
% 7.87/1.49      | r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != iProver_top ),
% 7.87/1.49      inference(instantiation,[status(thm)],[c_273]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_11,negated_conjecture,
% 7.87/1.49      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != sK0 ),
% 7.87/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(c_12,negated_conjecture,
% 7.87/1.49      ( k1_xboole_0 != sK0 ),
% 7.87/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.87/1.49  
% 7.87/1.49  cnf(contradiction,plain,
% 7.87/1.49      ( $false ),
% 7.87/1.49      inference(minisat,[status(thm)],[c_13963,c_275,c_11,c_12]) ).
% 7.87/1.49  
% 7.87/1.49  
% 7.87/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.87/1.49  
% 7.87/1.49  ------                               Statistics
% 7.87/1.49  
% 7.87/1.49  ------ General
% 7.87/1.49  
% 7.87/1.49  abstr_ref_over_cycles:                  0
% 7.87/1.49  abstr_ref_under_cycles:                 0
% 7.87/1.49  gc_basic_clause_elim:                   0
% 7.87/1.49  forced_gc_time:                         0
% 7.87/1.49  parsing_time:                           0.006
% 7.87/1.49  unif_index_cands_time:                  0.
% 7.87/1.49  unif_index_add_time:                    0.
% 7.87/1.49  orderings_time:                         0.
% 7.87/1.49  out_proof_time:                         0.01
% 7.87/1.49  total_time:                             0.658
% 7.87/1.49  num_of_symbols:                         39
% 7.87/1.49  num_of_terms:                           23318
% 7.87/1.49  
% 7.87/1.49  ------ Preprocessing
% 7.87/1.49  
% 7.87/1.49  num_of_splits:                          0
% 7.87/1.49  num_of_split_atoms:                     1
% 7.87/1.49  num_of_reused_defs:                     0
% 7.87/1.49  num_eq_ax_congr_red:                    0
% 7.87/1.49  num_of_sem_filtered_clauses:            1
% 7.87/1.49  num_of_subtypes:                        0
% 7.87/1.49  monotx_restored_types:                  0
% 7.87/1.49  sat_num_of_epr_types:                   0
% 7.87/1.49  sat_num_of_non_cyclic_types:            0
% 7.87/1.49  sat_guarded_non_collapsed_types:        0
% 7.87/1.49  num_pure_diseq_elim:                    0
% 7.87/1.49  simp_replaced_by:                       0
% 7.87/1.49  res_preprocessed:                       55
% 7.87/1.49  prep_upred:                             0
% 7.87/1.49  prep_unflattend:                        5
% 7.87/1.49  smt_new_axioms:                         0
% 7.87/1.49  pred_elim_cands:                        1
% 7.87/1.49  pred_elim:                              0
% 7.87/1.49  pred_elim_cl:                           0
% 7.87/1.49  pred_elim_cycles:                       1
% 7.87/1.49  merged_defs:                            0
% 7.87/1.49  merged_defs_ncl:                        0
% 7.87/1.49  bin_hyper_res:                          0
% 7.87/1.49  prep_cycles:                            3
% 7.87/1.49  pred_elim_time:                         0.001
% 7.87/1.49  splitting_time:                         0.
% 7.87/1.49  sem_filter_time:                        0.
% 7.87/1.49  monotx_time:                            0.
% 7.87/1.49  subtype_inf_time:                       0.
% 7.87/1.49  
% 7.87/1.49  ------ Problem properties
% 7.87/1.49  
% 7.87/1.49  clauses:                                14
% 7.87/1.49  conjectures:                            3
% 7.87/1.49  epr:                                    1
% 7.87/1.49  horn:                                   13
% 7.87/1.49  ground:                                 3
% 7.87/1.49  unary:                                  13
% 7.87/1.49  binary:                                 0
% 7.87/1.49  lits:                                   18
% 7.87/1.49  lits_eq:                                12
% 7.87/1.49  fd_pure:                                0
% 7.87/1.49  fd_pseudo:                              0
% 7.87/1.49  fd_cond:                                0
% 7.87/1.49  fd_pseudo_cond:                         1
% 7.87/1.49  ac_symbols:                             1
% 7.87/1.49  
% 7.87/1.49  ------ Propositional Solver
% 7.87/1.49  
% 7.87/1.49  prop_solver_calls:                      29
% 7.87/1.49  prop_fast_solver_calls:                 356
% 7.87/1.49  smt_solver_calls:                       0
% 7.87/1.49  smt_fast_solver_calls:                  0
% 7.87/1.49  prop_num_of_clauses:                    3337
% 7.87/1.49  prop_preprocess_simplified:             5245
% 7.87/1.49  prop_fo_subsumed:                       0
% 7.87/1.49  prop_solver_time:                       0.
% 7.87/1.49  smt_solver_time:                        0.
% 7.87/1.49  smt_fast_solver_time:                   0.
% 7.87/1.49  prop_fast_solver_time:                  0.
% 7.87/1.49  prop_unsat_core_time:                   0.
% 7.87/1.49  
% 7.87/1.49  ------ QBF
% 7.87/1.49  
% 7.87/1.49  qbf_q_res:                              0
% 7.87/1.49  qbf_num_tautologies:                    0
% 7.87/1.49  qbf_prep_cycles:                        0
% 7.87/1.49  
% 7.87/1.49  ------ BMC1
% 7.87/1.49  
% 7.87/1.49  bmc1_current_bound:                     -1
% 7.87/1.49  bmc1_last_solved_bound:                 -1
% 7.87/1.49  bmc1_unsat_core_size:                   -1
% 7.87/1.49  bmc1_unsat_core_parents_size:           -1
% 7.87/1.49  bmc1_merge_next_fun:                    0
% 7.87/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.87/1.49  
% 7.87/1.49  ------ Instantiation
% 7.87/1.49  
% 7.87/1.49  inst_num_of_clauses:                    1017
% 7.87/1.49  inst_num_in_passive:                    407
% 7.87/1.49  inst_num_in_active:                     410
% 7.87/1.49  inst_num_in_unprocessed:                200
% 7.87/1.49  inst_num_of_loops:                      440
% 7.87/1.49  inst_num_of_learning_restarts:          0
% 7.87/1.49  inst_num_moves_active_passive:          25
% 7.87/1.49  inst_lit_activity:                      0
% 7.87/1.49  inst_lit_activity_moves:                0
% 7.87/1.49  inst_num_tautologies:                   0
% 7.87/1.49  inst_num_prop_implied:                  0
% 7.87/1.49  inst_num_existing_simplified:           0
% 7.87/1.49  inst_num_eq_res_simplified:             0
% 7.87/1.49  inst_num_child_elim:                    0
% 7.87/1.49  inst_num_of_dismatching_blockings:      702
% 7.87/1.49  inst_num_of_non_proper_insts:           1558
% 7.87/1.49  inst_num_of_duplicates:                 0
% 7.87/1.49  inst_inst_num_from_inst_to_res:         0
% 7.87/1.49  inst_dismatching_checking_time:         0.
% 7.87/1.49  
% 7.87/1.49  ------ Resolution
% 7.87/1.49  
% 7.87/1.49  res_num_of_clauses:                     0
% 7.87/1.49  res_num_in_passive:                     0
% 7.87/1.49  res_num_in_active:                      0
% 7.87/1.49  res_num_of_loops:                       58
% 7.87/1.49  res_forward_subset_subsumed:            169
% 7.87/1.49  res_backward_subset_subsumed:           0
% 7.87/1.49  res_forward_subsumed:                   0
% 7.87/1.49  res_backward_subsumed:                  0
% 7.87/1.49  res_forward_subsumption_resolution:     0
% 7.87/1.49  res_backward_subsumption_resolution:    0
% 7.87/1.49  res_clause_to_clause_subsumption:       13048
% 7.87/1.49  res_orphan_elimination:                 0
% 7.87/1.49  res_tautology_del:                      206
% 7.87/1.49  res_num_eq_res_simplified:              0
% 7.87/1.49  res_num_sel_changes:                    0
% 7.87/1.49  res_moves_from_active_to_pass:          0
% 7.87/1.49  
% 7.87/1.49  ------ Superposition
% 7.87/1.49  
% 7.87/1.49  sup_time_total:                         0.
% 7.87/1.49  sup_time_generating:                    0.
% 7.87/1.49  sup_time_sim_full:                      0.
% 7.87/1.49  sup_time_sim_immed:                     0.
% 7.87/1.49  
% 7.87/1.49  sup_num_of_clauses:                     876
% 7.87/1.49  sup_num_in_active:                      55
% 7.87/1.49  sup_num_in_passive:                     821
% 7.87/1.49  sup_num_of_loops:                       87
% 7.87/1.49  sup_fw_superposition:                   2400
% 7.87/1.49  sup_bw_superposition:                   2140
% 7.87/1.49  sup_immediate_simplified:               2958
% 7.87/1.49  sup_given_eliminated:                   11
% 7.87/1.49  comparisons_done:                       0
% 7.87/1.49  comparisons_avoided:                    0
% 7.87/1.49  
% 7.87/1.49  ------ Simplifications
% 7.87/1.49  
% 7.87/1.49  
% 7.87/1.49  sim_fw_subset_subsumed:                 0
% 7.87/1.49  sim_bw_subset_subsumed:                 0
% 7.87/1.49  sim_fw_subsumed:                        190
% 7.87/1.49  sim_bw_subsumed:                        40
% 7.87/1.49  sim_fw_subsumption_res:                 0
% 7.87/1.49  sim_bw_subsumption_res:                 0
% 7.87/1.49  sim_tautology_del:                      0
% 7.87/1.49  sim_eq_tautology_del:                   1008
% 7.87/1.49  sim_eq_res_simp:                        0
% 7.87/1.49  sim_fw_demodulated:                     2401
% 7.87/1.49  sim_bw_demodulated:                     80
% 7.87/1.49  sim_light_normalised:                   1385
% 7.87/1.49  sim_joinable_taut:                      102
% 7.87/1.49  sim_joinable_simp:                      0
% 7.87/1.49  sim_ac_normalised:                      0
% 7.87/1.49  sim_smt_subsumption:                    0
% 7.87/1.49  
%------------------------------------------------------------------------------
