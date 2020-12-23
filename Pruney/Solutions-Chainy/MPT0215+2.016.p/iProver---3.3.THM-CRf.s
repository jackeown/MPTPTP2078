%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:56 EST 2020

% Result     : Theorem 4.02s
% Output     : CNFRefutation 4.02s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 410 expanded)
%              Number of clauses        :   35 (  78 expanded)
%              Number of leaves         :   20 ( 125 expanded)
%              Depth                    :   16
%              Number of atoms          :  107 ( 438 expanded)
%              Number of equality atoms :   96 ( 427 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f27,f31])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X1,X2) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & k2_tarski(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & k2_tarski(X1,X2) = k1_tarski(X0) )
   => ( sK0 != sK1
      & k2_tarski(sK1,sK2) = k1_tarski(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( sK0 != sK1
    & k2_tarski(sK1,sK2) = k1_tarski(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f24])).

fof(f44,plain,(
    k2_tarski(sK1,sK2) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f39,f46])).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f47])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f49])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f50])).

fof(f58,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    inference(definition_unfolding,[],[f44,f50,f51])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k4_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X1,X2,X3))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f35,f34,f47,f47])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f42,f48])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f43,f51,f51])).

fof(f45,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_497,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_498,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_504,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_498,c_6])).

cnf(c_500,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_502,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_500,c_5])).

cnf(c_505,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_504,c_502])).

cnf(c_506,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_497,c_505])).

cnf(c_10,negated_conjecture,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_588,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(X0,X0,X0,X0,X0,X1,X2))) = k5_enumset1(X0,X1,X2,sK1,sK1,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_10,c_1])).

cnf(c_592,plain,
    ( k5_enumset1(X0,X1,X2,sK0,sK0,sK0,sK0) = k5_enumset1(X0,X1,X2,sK1,sK1,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_588,c_1])).

cnf(c_751,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK0,sK0,sK0,sK0) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_592,c_10])).

cnf(c_7,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_590,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)),X7)) = k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),X7) ),
    inference(superposition,[status(thm)],[c_1,c_7])).

cnf(c_1044,plain,
    ( k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k4_xboole_0(k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)),k4_xboole_0(k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)),X7))) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k4_xboole_0(k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)),X7)) ),
    inference(superposition,[status(thm)],[c_0,c_590])).

cnf(c_3248,plain,
    ( k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k4_xboole_0(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0))) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) ),
    inference(superposition,[status(thm)],[c_751,c_1044])).

cnf(c_4208,plain,
    ( k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_506,c_3248])).

cnf(c_945,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_505,c_7])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_238,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_2])).

cnf(c_947,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_945,c_238])).

cnf(c_1302,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_947])).

cnf(c_4248,plain,
    ( k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_4208,c_6,c_504,c_506,c_1302])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_110,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8756,plain,
    ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4248,c_110])).

cnf(c_8,plain,
    ( ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_117,plain,
    ( ~ r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_118,plain,
    ( sK0 = sK1
    | r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_117])).

cnf(c_9,negated_conjecture,
    ( sK0 != sK1 ),
    inference(cnf_transformation,[],[f45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8756,c_118,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:38:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.02/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/0.99  
% 4.02/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.02/0.99  
% 4.02/0.99  ------  iProver source info
% 4.02/0.99  
% 4.02/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.02/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.02/0.99  git: non_committed_changes: false
% 4.02/0.99  git: last_make_outside_of_git: false
% 4.02/0.99  
% 4.02/0.99  ------ 
% 4.02/0.99  
% 4.02/0.99  ------ Input Options
% 4.02/0.99  
% 4.02/0.99  --out_options                           all
% 4.02/0.99  --tptp_safe_out                         true
% 4.02/0.99  --problem_path                          ""
% 4.02/0.99  --include_path                          ""
% 4.02/0.99  --clausifier                            res/vclausify_rel
% 4.02/0.99  --clausifier_options                    ""
% 4.02/0.99  --stdin                                 false
% 4.02/0.99  --stats_out                             all
% 4.02/0.99  
% 4.02/0.99  ------ General Options
% 4.02/0.99  
% 4.02/0.99  --fof                                   false
% 4.02/0.99  --time_out_real                         305.
% 4.02/0.99  --time_out_virtual                      -1.
% 4.02/0.99  --symbol_type_check                     false
% 4.02/0.99  --clausify_out                          false
% 4.02/0.99  --sig_cnt_out                           false
% 4.02/0.99  --trig_cnt_out                          false
% 4.02/0.99  --trig_cnt_out_tolerance                1.
% 4.02/0.99  --trig_cnt_out_sk_spl                   false
% 4.02/0.99  --abstr_cl_out                          false
% 4.02/0.99  
% 4.02/0.99  ------ Global Options
% 4.02/0.99  
% 4.02/0.99  --schedule                              default
% 4.02/0.99  --add_important_lit                     false
% 4.02/0.99  --prop_solver_per_cl                    1000
% 4.02/0.99  --min_unsat_core                        false
% 4.02/0.99  --soft_assumptions                      false
% 4.02/0.99  --soft_lemma_size                       3
% 4.02/0.99  --prop_impl_unit_size                   0
% 4.02/0.99  --prop_impl_unit                        []
% 4.02/0.99  --share_sel_clauses                     true
% 4.02/0.99  --reset_solvers                         false
% 4.02/0.99  --bc_imp_inh                            [conj_cone]
% 4.02/0.99  --conj_cone_tolerance                   3.
% 4.02/0.99  --extra_neg_conj                        none
% 4.02/0.99  --large_theory_mode                     true
% 4.02/0.99  --prolific_symb_bound                   200
% 4.02/0.99  --lt_threshold                          2000
% 4.02/0.99  --clause_weak_htbl                      true
% 4.02/0.99  --gc_record_bc_elim                     false
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing Options
% 4.02/0.99  
% 4.02/0.99  --preprocessing_flag                    true
% 4.02/0.99  --time_out_prep_mult                    0.1
% 4.02/0.99  --splitting_mode                        input
% 4.02/0.99  --splitting_grd                         true
% 4.02/0.99  --splitting_cvd                         false
% 4.02/0.99  --splitting_cvd_svl                     false
% 4.02/0.99  --splitting_nvd                         32
% 4.02/0.99  --sub_typing                            true
% 4.02/0.99  --prep_gs_sim                           true
% 4.02/0.99  --prep_unflatten                        true
% 4.02/0.99  --prep_res_sim                          true
% 4.02/0.99  --prep_upred                            true
% 4.02/0.99  --prep_sem_filter                       exhaustive
% 4.02/0.99  --prep_sem_filter_out                   false
% 4.02/0.99  --pred_elim                             true
% 4.02/0.99  --res_sim_input                         true
% 4.02/0.99  --eq_ax_congr_red                       true
% 4.02/0.99  --pure_diseq_elim                       true
% 4.02/0.99  --brand_transform                       false
% 4.02/0.99  --non_eq_to_eq                          false
% 4.02/0.99  --prep_def_merge                        true
% 4.02/0.99  --prep_def_merge_prop_impl              false
% 4.02/0.99  --prep_def_merge_mbd                    true
% 4.02/0.99  --prep_def_merge_tr_red                 false
% 4.02/0.99  --prep_def_merge_tr_cl                  false
% 4.02/0.99  --smt_preprocessing                     true
% 4.02/0.99  --smt_ac_axioms                         fast
% 4.02/0.99  --preprocessed_out                      false
% 4.02/0.99  --preprocessed_stats                    false
% 4.02/0.99  
% 4.02/0.99  ------ Abstraction refinement Options
% 4.02/0.99  
% 4.02/0.99  --abstr_ref                             []
% 4.02/0.99  --abstr_ref_prep                        false
% 4.02/0.99  --abstr_ref_until_sat                   false
% 4.02/0.99  --abstr_ref_sig_restrict                funpre
% 4.02/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.02/0.99  --abstr_ref_under                       []
% 4.02/0.99  
% 4.02/0.99  ------ SAT Options
% 4.02/0.99  
% 4.02/0.99  --sat_mode                              false
% 4.02/0.99  --sat_fm_restart_options                ""
% 4.02/0.99  --sat_gr_def                            false
% 4.02/0.99  --sat_epr_types                         true
% 4.02/0.99  --sat_non_cyclic_types                  false
% 4.02/0.99  --sat_finite_models                     false
% 4.02/0.99  --sat_fm_lemmas                         false
% 4.02/0.99  --sat_fm_prep                           false
% 4.02/0.99  --sat_fm_uc_incr                        true
% 4.02/0.99  --sat_out_model                         small
% 4.02/0.99  --sat_out_clauses                       false
% 4.02/0.99  
% 4.02/0.99  ------ QBF Options
% 4.02/0.99  
% 4.02/0.99  --qbf_mode                              false
% 4.02/0.99  --qbf_elim_univ                         false
% 4.02/0.99  --qbf_dom_inst                          none
% 4.02/0.99  --qbf_dom_pre_inst                      false
% 4.02/0.99  --qbf_sk_in                             false
% 4.02/0.99  --qbf_pred_elim                         true
% 4.02/0.99  --qbf_split                             512
% 4.02/0.99  
% 4.02/0.99  ------ BMC1 Options
% 4.02/0.99  
% 4.02/0.99  --bmc1_incremental                      false
% 4.02/0.99  --bmc1_axioms                           reachable_all
% 4.02/0.99  --bmc1_min_bound                        0
% 4.02/0.99  --bmc1_max_bound                        -1
% 4.02/0.99  --bmc1_max_bound_default                -1
% 4.02/0.99  --bmc1_symbol_reachability              true
% 4.02/0.99  --bmc1_property_lemmas                  false
% 4.02/0.99  --bmc1_k_induction                      false
% 4.02/0.99  --bmc1_non_equiv_states                 false
% 4.02/0.99  --bmc1_deadlock                         false
% 4.02/0.99  --bmc1_ucm                              false
% 4.02/0.99  --bmc1_add_unsat_core                   none
% 4.02/0.99  --bmc1_unsat_core_children              false
% 4.02/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.02/0.99  --bmc1_out_stat                         full
% 4.02/0.99  --bmc1_ground_init                      false
% 4.02/0.99  --bmc1_pre_inst_next_state              false
% 4.02/0.99  --bmc1_pre_inst_state                   false
% 4.02/0.99  --bmc1_pre_inst_reach_state             false
% 4.02/0.99  --bmc1_out_unsat_core                   false
% 4.02/0.99  --bmc1_aig_witness_out                  false
% 4.02/0.99  --bmc1_verbose                          false
% 4.02/0.99  --bmc1_dump_clauses_tptp                false
% 4.02/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.02/0.99  --bmc1_dump_file                        -
% 4.02/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.02/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.02/0.99  --bmc1_ucm_extend_mode                  1
% 4.02/0.99  --bmc1_ucm_init_mode                    2
% 4.02/0.99  --bmc1_ucm_cone_mode                    none
% 4.02/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.02/0.99  --bmc1_ucm_relax_model                  4
% 4.02/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.02/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.02/0.99  --bmc1_ucm_layered_model                none
% 4.02/0.99  --bmc1_ucm_max_lemma_size               10
% 4.02/0.99  
% 4.02/0.99  ------ AIG Options
% 4.02/0.99  
% 4.02/0.99  --aig_mode                              false
% 4.02/0.99  
% 4.02/0.99  ------ Instantiation Options
% 4.02/0.99  
% 4.02/0.99  --instantiation_flag                    true
% 4.02/0.99  --inst_sos_flag                         true
% 4.02/0.99  --inst_sos_phase                        true
% 4.02/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.02/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.02/0.99  --inst_lit_sel_side                     num_symb
% 4.02/0.99  --inst_solver_per_active                1400
% 4.02/0.99  --inst_solver_calls_frac                1.
% 4.02/0.99  --inst_passive_queue_type               priority_queues
% 4.02/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.02/0.99  --inst_passive_queues_freq              [25;2]
% 4.02/0.99  --inst_dismatching                      true
% 4.02/0.99  --inst_eager_unprocessed_to_passive     true
% 4.02/0.99  --inst_prop_sim_given                   true
% 4.02/0.99  --inst_prop_sim_new                     false
% 4.02/0.99  --inst_subs_new                         false
% 4.02/0.99  --inst_eq_res_simp                      false
% 4.02/0.99  --inst_subs_given                       false
% 4.02/0.99  --inst_orphan_elimination               true
% 4.02/0.99  --inst_learning_loop_flag               true
% 4.02/0.99  --inst_learning_start                   3000
% 4.02/0.99  --inst_learning_factor                  2
% 4.02/0.99  --inst_start_prop_sim_after_learn       3
% 4.02/0.99  --inst_sel_renew                        solver
% 4.02/0.99  --inst_lit_activity_flag                true
% 4.02/0.99  --inst_restr_to_given                   false
% 4.02/0.99  --inst_activity_threshold               500
% 4.02/0.99  --inst_out_proof                        true
% 4.02/0.99  
% 4.02/0.99  ------ Resolution Options
% 4.02/0.99  
% 4.02/0.99  --resolution_flag                       true
% 4.02/0.99  --res_lit_sel                           adaptive
% 4.02/0.99  --res_lit_sel_side                      none
% 4.02/0.99  --res_ordering                          kbo
% 4.02/0.99  --res_to_prop_solver                    active
% 4.02/0.99  --res_prop_simpl_new                    false
% 4.02/0.99  --res_prop_simpl_given                  true
% 4.02/0.99  --res_passive_queue_type                priority_queues
% 4.02/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.02/0.99  --res_passive_queues_freq               [15;5]
% 4.02/0.99  --res_forward_subs                      full
% 4.02/0.99  --res_backward_subs                     full
% 4.02/0.99  --res_forward_subs_resolution           true
% 4.02/0.99  --res_backward_subs_resolution          true
% 4.02/0.99  --res_orphan_elimination                true
% 4.02/0.99  --res_time_limit                        2.
% 4.02/0.99  --res_out_proof                         true
% 4.02/0.99  
% 4.02/0.99  ------ Superposition Options
% 4.02/0.99  
% 4.02/0.99  --superposition_flag                    true
% 4.02/0.99  --sup_passive_queue_type                priority_queues
% 4.02/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.02/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.02/0.99  --demod_completeness_check              fast
% 4.02/0.99  --demod_use_ground                      true
% 4.02/0.99  --sup_to_prop_solver                    passive
% 4.02/0.99  --sup_prop_simpl_new                    true
% 4.02/0.99  --sup_prop_simpl_given                  true
% 4.02/0.99  --sup_fun_splitting                     true
% 4.02/0.99  --sup_smt_interval                      50000
% 4.02/0.99  
% 4.02/0.99  ------ Superposition Simplification Setup
% 4.02/0.99  
% 4.02/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.02/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.02/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.02/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.02/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.02/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.02/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.02/0.99  --sup_immed_triv                        [TrivRules]
% 4.02/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_immed_bw_main                     []
% 4.02/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.02/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.02/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_input_bw                          []
% 4.02/0.99  
% 4.02/0.99  ------ Combination Options
% 4.02/0.99  
% 4.02/0.99  --comb_res_mult                         3
% 4.02/0.99  --comb_sup_mult                         2
% 4.02/0.99  --comb_inst_mult                        10
% 4.02/0.99  
% 4.02/0.99  ------ Debug Options
% 4.02/0.99  
% 4.02/0.99  --dbg_backtrace                         false
% 4.02/0.99  --dbg_dump_prop_clauses                 false
% 4.02/0.99  --dbg_dump_prop_clauses_file            -
% 4.02/0.99  --dbg_out_stat                          false
% 4.02/0.99  ------ Parsing...
% 4.02/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/0.99  ------ Proving...
% 4.02/0.99  ------ Problem Properties 
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  clauses                                 11
% 4.02/0.99  conjectures                             2
% 4.02/0.99  EPR                                     1
% 4.02/0.99  Horn                                    11
% 4.02/0.99  unary                                   10
% 4.02/0.99  binary                                  1
% 4.02/0.99  lits                                    12
% 4.02/0.99  lits eq                                 10
% 4.02/0.99  fd_pure                                 0
% 4.02/0.99  fd_pseudo                               0
% 4.02/0.99  fd_cond                                 0
% 4.02/0.99  fd_pseudo_cond                          1
% 4.02/0.99  AC symbols                              1
% 4.02/0.99  
% 4.02/0.99  ------ Schedule dynamic 5 is on 
% 4.02/0.99  
% 4.02/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  ------ 
% 4.02/0.99  Current options:
% 4.02/0.99  ------ 
% 4.02/0.99  
% 4.02/0.99  ------ Input Options
% 4.02/0.99  
% 4.02/0.99  --out_options                           all
% 4.02/0.99  --tptp_safe_out                         true
% 4.02/0.99  --problem_path                          ""
% 4.02/0.99  --include_path                          ""
% 4.02/0.99  --clausifier                            res/vclausify_rel
% 4.02/0.99  --clausifier_options                    ""
% 4.02/0.99  --stdin                                 false
% 4.02/0.99  --stats_out                             all
% 4.02/0.99  
% 4.02/0.99  ------ General Options
% 4.02/0.99  
% 4.02/0.99  --fof                                   false
% 4.02/0.99  --time_out_real                         305.
% 4.02/0.99  --time_out_virtual                      -1.
% 4.02/0.99  --symbol_type_check                     false
% 4.02/0.99  --clausify_out                          false
% 4.02/0.99  --sig_cnt_out                           false
% 4.02/0.99  --trig_cnt_out                          false
% 4.02/0.99  --trig_cnt_out_tolerance                1.
% 4.02/0.99  --trig_cnt_out_sk_spl                   false
% 4.02/0.99  --abstr_cl_out                          false
% 4.02/0.99  
% 4.02/0.99  ------ Global Options
% 4.02/0.99  
% 4.02/0.99  --schedule                              default
% 4.02/0.99  --add_important_lit                     false
% 4.02/0.99  --prop_solver_per_cl                    1000
% 4.02/0.99  --min_unsat_core                        false
% 4.02/0.99  --soft_assumptions                      false
% 4.02/0.99  --soft_lemma_size                       3
% 4.02/0.99  --prop_impl_unit_size                   0
% 4.02/0.99  --prop_impl_unit                        []
% 4.02/0.99  --share_sel_clauses                     true
% 4.02/0.99  --reset_solvers                         false
% 4.02/0.99  --bc_imp_inh                            [conj_cone]
% 4.02/0.99  --conj_cone_tolerance                   3.
% 4.02/0.99  --extra_neg_conj                        none
% 4.02/0.99  --large_theory_mode                     true
% 4.02/0.99  --prolific_symb_bound                   200
% 4.02/0.99  --lt_threshold                          2000
% 4.02/0.99  --clause_weak_htbl                      true
% 4.02/0.99  --gc_record_bc_elim                     false
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing Options
% 4.02/0.99  
% 4.02/0.99  --preprocessing_flag                    true
% 4.02/0.99  --time_out_prep_mult                    0.1
% 4.02/0.99  --splitting_mode                        input
% 4.02/0.99  --splitting_grd                         true
% 4.02/0.99  --splitting_cvd                         false
% 4.02/0.99  --splitting_cvd_svl                     false
% 4.02/0.99  --splitting_nvd                         32
% 4.02/0.99  --sub_typing                            true
% 4.02/0.99  --prep_gs_sim                           true
% 4.02/0.99  --prep_unflatten                        true
% 4.02/0.99  --prep_res_sim                          true
% 4.02/0.99  --prep_upred                            true
% 4.02/0.99  --prep_sem_filter                       exhaustive
% 4.02/0.99  --prep_sem_filter_out                   false
% 4.02/0.99  --pred_elim                             true
% 4.02/0.99  --res_sim_input                         true
% 4.02/0.99  --eq_ax_congr_red                       true
% 4.02/0.99  --pure_diseq_elim                       true
% 4.02/0.99  --brand_transform                       false
% 4.02/0.99  --non_eq_to_eq                          false
% 4.02/0.99  --prep_def_merge                        true
% 4.02/0.99  --prep_def_merge_prop_impl              false
% 4.02/0.99  --prep_def_merge_mbd                    true
% 4.02/0.99  --prep_def_merge_tr_red                 false
% 4.02/0.99  --prep_def_merge_tr_cl                  false
% 4.02/0.99  --smt_preprocessing                     true
% 4.02/0.99  --smt_ac_axioms                         fast
% 4.02/0.99  --preprocessed_out                      false
% 4.02/0.99  --preprocessed_stats                    false
% 4.02/0.99  
% 4.02/0.99  ------ Abstraction refinement Options
% 4.02/0.99  
% 4.02/0.99  --abstr_ref                             []
% 4.02/0.99  --abstr_ref_prep                        false
% 4.02/0.99  --abstr_ref_until_sat                   false
% 4.02/0.99  --abstr_ref_sig_restrict                funpre
% 4.02/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.02/0.99  --abstr_ref_under                       []
% 4.02/0.99  
% 4.02/0.99  ------ SAT Options
% 4.02/0.99  
% 4.02/0.99  --sat_mode                              false
% 4.02/0.99  --sat_fm_restart_options                ""
% 4.02/0.99  --sat_gr_def                            false
% 4.02/0.99  --sat_epr_types                         true
% 4.02/0.99  --sat_non_cyclic_types                  false
% 4.02/0.99  --sat_finite_models                     false
% 4.02/0.99  --sat_fm_lemmas                         false
% 4.02/0.99  --sat_fm_prep                           false
% 4.02/0.99  --sat_fm_uc_incr                        true
% 4.02/0.99  --sat_out_model                         small
% 4.02/0.99  --sat_out_clauses                       false
% 4.02/0.99  
% 4.02/0.99  ------ QBF Options
% 4.02/0.99  
% 4.02/0.99  --qbf_mode                              false
% 4.02/0.99  --qbf_elim_univ                         false
% 4.02/0.99  --qbf_dom_inst                          none
% 4.02/0.99  --qbf_dom_pre_inst                      false
% 4.02/0.99  --qbf_sk_in                             false
% 4.02/0.99  --qbf_pred_elim                         true
% 4.02/0.99  --qbf_split                             512
% 4.02/0.99  
% 4.02/0.99  ------ BMC1 Options
% 4.02/0.99  
% 4.02/0.99  --bmc1_incremental                      false
% 4.02/0.99  --bmc1_axioms                           reachable_all
% 4.02/0.99  --bmc1_min_bound                        0
% 4.02/0.99  --bmc1_max_bound                        -1
% 4.02/0.99  --bmc1_max_bound_default                -1
% 4.02/0.99  --bmc1_symbol_reachability              true
% 4.02/0.99  --bmc1_property_lemmas                  false
% 4.02/0.99  --bmc1_k_induction                      false
% 4.02/0.99  --bmc1_non_equiv_states                 false
% 4.02/0.99  --bmc1_deadlock                         false
% 4.02/0.99  --bmc1_ucm                              false
% 4.02/0.99  --bmc1_add_unsat_core                   none
% 4.02/0.99  --bmc1_unsat_core_children              false
% 4.02/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.02/0.99  --bmc1_out_stat                         full
% 4.02/0.99  --bmc1_ground_init                      false
% 4.02/0.99  --bmc1_pre_inst_next_state              false
% 4.02/0.99  --bmc1_pre_inst_state                   false
% 4.02/0.99  --bmc1_pre_inst_reach_state             false
% 4.02/0.99  --bmc1_out_unsat_core                   false
% 4.02/0.99  --bmc1_aig_witness_out                  false
% 4.02/0.99  --bmc1_verbose                          false
% 4.02/0.99  --bmc1_dump_clauses_tptp                false
% 4.02/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.02/0.99  --bmc1_dump_file                        -
% 4.02/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.02/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.02/0.99  --bmc1_ucm_extend_mode                  1
% 4.02/0.99  --bmc1_ucm_init_mode                    2
% 4.02/0.99  --bmc1_ucm_cone_mode                    none
% 4.02/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.02/0.99  --bmc1_ucm_relax_model                  4
% 4.02/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.02/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.02/0.99  --bmc1_ucm_layered_model                none
% 4.02/0.99  --bmc1_ucm_max_lemma_size               10
% 4.02/0.99  
% 4.02/0.99  ------ AIG Options
% 4.02/0.99  
% 4.02/0.99  --aig_mode                              false
% 4.02/0.99  
% 4.02/0.99  ------ Instantiation Options
% 4.02/0.99  
% 4.02/0.99  --instantiation_flag                    true
% 4.02/0.99  --inst_sos_flag                         true
% 4.02/0.99  --inst_sos_phase                        true
% 4.02/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.02/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.02/0.99  --inst_lit_sel_side                     none
% 4.02/0.99  --inst_solver_per_active                1400
% 4.02/0.99  --inst_solver_calls_frac                1.
% 4.02/0.99  --inst_passive_queue_type               priority_queues
% 4.02/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.02/0.99  --inst_passive_queues_freq              [25;2]
% 4.02/0.99  --inst_dismatching                      true
% 4.02/0.99  --inst_eager_unprocessed_to_passive     true
% 4.02/0.99  --inst_prop_sim_given                   true
% 4.02/0.99  --inst_prop_sim_new                     false
% 4.02/0.99  --inst_subs_new                         false
% 4.02/0.99  --inst_eq_res_simp                      false
% 4.02/0.99  --inst_subs_given                       false
% 4.02/0.99  --inst_orphan_elimination               true
% 4.02/0.99  --inst_learning_loop_flag               true
% 4.02/0.99  --inst_learning_start                   3000
% 4.02/0.99  --inst_learning_factor                  2
% 4.02/0.99  --inst_start_prop_sim_after_learn       3
% 4.02/0.99  --inst_sel_renew                        solver
% 4.02/0.99  --inst_lit_activity_flag                true
% 4.02/0.99  --inst_restr_to_given                   false
% 4.02/0.99  --inst_activity_threshold               500
% 4.02/0.99  --inst_out_proof                        true
% 4.02/0.99  
% 4.02/0.99  ------ Resolution Options
% 4.02/0.99  
% 4.02/0.99  --resolution_flag                       false
% 4.02/0.99  --res_lit_sel                           adaptive
% 4.02/0.99  --res_lit_sel_side                      none
% 4.02/0.99  --res_ordering                          kbo
% 4.02/0.99  --res_to_prop_solver                    active
% 4.02/0.99  --res_prop_simpl_new                    false
% 4.02/0.99  --res_prop_simpl_given                  true
% 4.02/0.99  --res_passive_queue_type                priority_queues
% 4.02/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.02/0.99  --res_passive_queues_freq               [15;5]
% 4.02/0.99  --res_forward_subs                      full
% 4.02/0.99  --res_backward_subs                     full
% 4.02/0.99  --res_forward_subs_resolution           true
% 4.02/0.99  --res_backward_subs_resolution          true
% 4.02/0.99  --res_orphan_elimination                true
% 4.02/0.99  --res_time_limit                        2.
% 4.02/0.99  --res_out_proof                         true
% 4.02/0.99  
% 4.02/0.99  ------ Superposition Options
% 4.02/0.99  
% 4.02/0.99  --superposition_flag                    true
% 4.02/0.99  --sup_passive_queue_type                priority_queues
% 4.02/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.02/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.02/0.99  --demod_completeness_check              fast
% 4.02/0.99  --demod_use_ground                      true
% 4.02/0.99  --sup_to_prop_solver                    passive
% 4.02/0.99  --sup_prop_simpl_new                    true
% 4.02/0.99  --sup_prop_simpl_given                  true
% 4.02/0.99  --sup_fun_splitting                     true
% 4.02/0.99  --sup_smt_interval                      50000
% 4.02/0.99  
% 4.02/0.99  ------ Superposition Simplification Setup
% 4.02/0.99  
% 4.02/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.02/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.02/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.02/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.02/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.02/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.02/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.02/0.99  --sup_immed_triv                        [TrivRules]
% 4.02/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_immed_bw_main                     []
% 4.02/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.02/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.02/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/0.99  --sup_input_bw                          []
% 4.02/0.99  
% 4.02/0.99  ------ Combination Options
% 4.02/0.99  
% 4.02/0.99  --comb_res_mult                         3
% 4.02/0.99  --comb_sup_mult                         2
% 4.02/0.99  --comb_inst_mult                        10
% 4.02/0.99  
% 4.02/0.99  ------ Debug Options
% 4.02/0.99  
% 4.02/0.99  --dbg_backtrace                         false
% 4.02/0.99  --dbg_dump_prop_clauses                 false
% 4.02/0.99  --dbg_dump_prop_clauses_file            -
% 4.02/0.99  --dbg_out_stat                          false
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  ------ Proving...
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  % SZS status Theorem for theBenchmark.p
% 4.02/0.99  
% 4.02/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.02/0.99  
% 4.02/0.99  fof(f2,axiom,(
% 4.02/0.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f21,plain,(
% 4.02/0.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 4.02/0.99    inference(rectify,[],[f2])).
% 4.02/0.99  
% 4.02/0.99  fof(f27,plain,(
% 4.02/0.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 4.02/0.99    inference(cnf_transformation,[],[f21])).
% 4.02/0.99  
% 4.02/0.99  fof(f6,axiom,(
% 4.02/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f31,plain,(
% 4.02/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.02/0.99    inference(cnf_transformation,[],[f6])).
% 4.02/0.99  
% 4.02/0.99  fof(f54,plain,(
% 4.02/0.99    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 4.02/0.99    inference(definition_unfolding,[],[f27,f31])).
% 4.02/0.99  
% 4.02/0.99  fof(f3,axiom,(
% 4.02/0.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f28,plain,(
% 4.02/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f3])).
% 4.02/0.99  
% 4.02/0.99  fof(f52,plain,(
% 4.02/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1)) )),
% 4.02/0.99    inference(definition_unfolding,[],[f28,f31])).
% 4.02/0.99  
% 4.02/0.99  fof(f5,axiom,(
% 4.02/0.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f30,plain,(
% 4.02/0.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 4.02/0.99    inference(cnf_transformation,[],[f5])).
% 4.02/0.99  
% 4.02/0.99  fof(f56,plain,(
% 4.02/0.99    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 4.02/0.99    inference(definition_unfolding,[],[f30,f31])).
% 4.02/0.99  
% 4.02/0.99  fof(f7,axiom,(
% 4.02/0.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f32,plain,(
% 4.02/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.02/0.99    inference(cnf_transformation,[],[f7])).
% 4.02/0.99  
% 4.02/0.99  fof(f19,conjecture,(
% 4.02/0.99    ! [X0,X1,X2] : (k2_tarski(X1,X2) = k1_tarski(X0) => X0 = X1)),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f20,negated_conjecture,(
% 4.02/0.99    ~! [X0,X1,X2] : (k2_tarski(X1,X2) = k1_tarski(X0) => X0 = X1)),
% 4.02/0.99    inference(negated_conjecture,[],[f19])).
% 4.02/0.99  
% 4.02/0.99  fof(f23,plain,(
% 4.02/0.99    ? [X0,X1,X2] : (X0 != X1 & k2_tarski(X1,X2) = k1_tarski(X0))),
% 4.02/0.99    inference(ennf_transformation,[],[f20])).
% 4.02/0.99  
% 4.02/0.99  fof(f24,plain,(
% 4.02/0.99    ? [X0,X1,X2] : (X0 != X1 & k2_tarski(X1,X2) = k1_tarski(X0)) => (sK0 != sK1 & k2_tarski(sK1,sK2) = k1_tarski(sK0))),
% 4.02/0.99    introduced(choice_axiom,[])).
% 4.02/0.99  
% 4.02/0.99  fof(f25,plain,(
% 4.02/0.99    sK0 != sK1 & k2_tarski(sK1,sK2) = k1_tarski(sK0)),
% 4.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f24])).
% 4.02/0.99  
% 4.02/0.99  fof(f44,plain,(
% 4.02/0.99    k2_tarski(sK1,sK2) = k1_tarski(sK0)),
% 4.02/0.99    inference(cnf_transformation,[],[f25])).
% 4.02/0.99  
% 4.02/0.99  fof(f11,axiom,(
% 4.02/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f36,plain,(
% 4.02/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f11])).
% 4.02/0.99  
% 4.02/0.99  fof(f12,axiom,(
% 4.02/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f37,plain,(
% 4.02/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f12])).
% 4.02/0.99  
% 4.02/0.99  fof(f13,axiom,(
% 4.02/0.99    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f38,plain,(
% 4.02/0.99    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f13])).
% 4.02/0.99  
% 4.02/0.99  fof(f14,axiom,(
% 4.02/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f39,plain,(
% 4.02/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f14])).
% 4.02/0.99  
% 4.02/0.99  fof(f15,axiom,(
% 4.02/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f40,plain,(
% 4.02/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f15])).
% 4.02/0.99  
% 4.02/0.99  fof(f16,axiom,(
% 4.02/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f41,plain,(
% 4.02/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f16])).
% 4.02/0.99  
% 4.02/0.99  fof(f46,plain,(
% 4.02/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 4.02/0.99    inference(definition_unfolding,[],[f40,f41])).
% 4.02/0.99  
% 4.02/0.99  fof(f47,plain,(
% 4.02/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 4.02/0.99    inference(definition_unfolding,[],[f39,f46])).
% 4.02/0.99  
% 4.02/0.99  fof(f49,plain,(
% 4.02/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 4.02/0.99    inference(definition_unfolding,[],[f38,f47])).
% 4.02/0.99  
% 4.02/0.99  fof(f50,plain,(
% 4.02/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 4.02/0.99    inference(definition_unfolding,[],[f37,f49])).
% 4.02/0.99  
% 4.02/0.99  fof(f51,plain,(
% 4.02/0.99    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 4.02/0.99    inference(definition_unfolding,[],[f36,f50])).
% 4.02/0.99  
% 4.02/0.99  fof(f58,plain,(
% 4.02/0.99    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),
% 4.02/0.99    inference(definition_unfolding,[],[f44,f50,f51])).
% 4.02/0.99  
% 4.02/0.99  fof(f17,axiom,(
% 4.02/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f42,plain,(
% 4.02/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f17])).
% 4.02/0.99  
% 4.02/0.99  fof(f10,axiom,(
% 4.02/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f35,plain,(
% 4.02/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f10])).
% 4.02/0.99  
% 4.02/0.99  fof(f9,axiom,(
% 4.02/0.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f34,plain,(
% 4.02/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f9])).
% 4.02/0.99  
% 4.02/0.99  fof(f48,plain,(
% 4.02/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k4_xboole_0(k5_enumset1(X4,X4,X4,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X1,X2,X3))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 4.02/0.99    inference(definition_unfolding,[],[f35,f34,f47,f47])).
% 4.02/0.99  
% 4.02/0.99  fof(f53,plain,(
% 4.02/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 4.02/0.99    inference(definition_unfolding,[],[f42,f48])).
% 4.02/0.99  
% 4.02/0.99  fof(f8,axiom,(
% 4.02/0.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f33,plain,(
% 4.02/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f8])).
% 4.02/0.99  
% 4.02/0.99  fof(f1,axiom,(
% 4.02/0.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f26,plain,(
% 4.02/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f1])).
% 4.02/0.99  
% 4.02/0.99  fof(f4,axiom,(
% 4.02/0.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f29,plain,(
% 4.02/0.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 4.02/0.99    inference(cnf_transformation,[],[f4])).
% 4.02/0.99  
% 4.02/0.99  fof(f55,plain,(
% 4.02/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 4.02/0.99    inference(definition_unfolding,[],[f29,f31])).
% 4.02/0.99  
% 4.02/0.99  fof(f18,axiom,(
% 4.02/0.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 4.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.02/0.99  
% 4.02/0.99  fof(f22,plain,(
% 4.02/0.99    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 4.02/0.99    inference(ennf_transformation,[],[f18])).
% 4.02/0.99  
% 4.02/0.99  fof(f43,plain,(
% 4.02/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1))) )),
% 4.02/0.99    inference(cnf_transformation,[],[f22])).
% 4.02/0.99  
% 4.02/0.99  fof(f57,plain,(
% 4.02/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) )),
% 4.02/0.99    inference(definition_unfolding,[],[f43,f51,f51])).
% 4.02/0.99  
% 4.02/0.99  fof(f45,plain,(
% 4.02/0.99    sK0 != sK1),
% 4.02/0.99    inference(cnf_transformation,[],[f25])).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3,plain,
% 4.02/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 4.02/0.99      inference(cnf_transformation,[],[f54]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_0,plain,
% 4.02/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 4.02/0.99      inference(cnf_transformation,[],[f52]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_497,plain,
% 4.02/0.99      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_5,plain,
% 4.02/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 4.02/0.99      inference(cnf_transformation,[],[f56]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_498,plain,
% 4.02/0.99      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_6,plain,
% 4.02/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 4.02/0.99      inference(cnf_transformation,[],[f32]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_504,plain,
% 4.02/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 4.02/0.99      inference(light_normalisation,[status(thm)],[c_498,c_6]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_500,plain,
% 4.02/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_502,plain,
% 4.02/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 4.02/0.99      inference(light_normalisation,[status(thm)],[c_500,c_5]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_505,plain,
% 4.02/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 4.02/0.99      inference(demodulation,[status(thm)],[c_504,c_502]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_506,plain,
% 4.02/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 4.02/0.99      inference(demodulation,[status(thm)],[c_497,c_505]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_10,negated_conjecture,
% 4.02/0.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
% 4.02/0.99      inference(cnf_transformation,[],[f58]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1,plain,
% 4.02/0.99      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 4.02/0.99      inference(cnf_transformation,[],[f53]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_588,plain,
% 4.02/0.99      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(X0,X0,X0,X0,X0,X1,X2))) = k5_enumset1(X0,X1,X2,sK1,sK1,sK1,sK2) ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_10,c_1]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_592,plain,
% 4.02/0.99      ( k5_enumset1(X0,X1,X2,sK0,sK0,sK0,sK0) = k5_enumset1(X0,X1,X2,sK1,sK1,sK1,sK2) ),
% 4.02/0.99      inference(demodulation,[status(thm)],[c_588,c_1]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_751,plain,
% 4.02/0.99      ( k5_enumset1(sK1,sK1,sK1,sK0,sK0,sK0,sK0) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_592,c_10]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_7,plain,
% 4.02/0.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 4.02/0.99      inference(cnf_transformation,[],[f33]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_590,plain,
% 4.02/0.99      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)),X7)) = k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),X7) ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_1,c_7]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1044,plain,
% 4.02/0.99      ( k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k4_xboole_0(k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)),k4_xboole_0(k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)),X7))) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k4_xboole_0(k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)),X7)) ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_0,c_590]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_3248,plain,
% 4.02/0.99      ( k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k4_xboole_0(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0))) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_751,c_1044]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4208,plain,
% 4.02/0.99      ( k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k4_xboole_0(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k1_xboole_0)) ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_506,c_3248]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_945,plain,
% 4.02/0.99      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_505,c_7]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_2,plain,
% 4.02/0.99      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 4.02/0.99      inference(cnf_transformation,[],[f26]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_238,plain,
% 4.02/0.99      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_6,c_2]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_947,plain,
% 4.02/0.99      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 4.02/0.99      inference(demodulation,[status(thm)],[c_945,c_238]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_1302,plain,
% 4.02/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_0,c_947]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4248,plain,
% 4.02/0.99      ( k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 4.02/0.99      inference(demodulation,
% 4.02/0.99                [status(thm)],
% 4.02/0.99                [c_4208,c_6,c_504,c_506,c_1302]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_4,plain,
% 4.02/0.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 4.02/0.99      inference(cnf_transformation,[],[f55]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_110,plain,
% 4.02/0.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_8756,plain,
% 4.02/0.99      ( r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 4.02/0.99      inference(superposition,[status(thm)],[c_4248,c_110]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_8,plain,
% 4.02/0.99      ( ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
% 4.02/0.99      | X1 = X0 ),
% 4.02/0.99      inference(cnf_transformation,[],[f57]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_117,plain,
% 4.02/0.99      ( ~ r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 4.02/0.99      | sK0 = sK1 ),
% 4.02/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_118,plain,
% 4.02/0.99      ( sK0 = sK1
% 4.02/0.99      | r1_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != iProver_top ),
% 4.02/0.99      inference(predicate_to_equality,[status(thm)],[c_117]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(c_9,negated_conjecture,
% 4.02/0.99      ( sK0 != sK1 ),
% 4.02/0.99      inference(cnf_transformation,[],[f45]) ).
% 4.02/0.99  
% 4.02/0.99  cnf(contradiction,plain,
% 4.02/0.99      ( $false ),
% 4.02/0.99      inference(minisat,[status(thm)],[c_8756,c_118,c_9]) ).
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.02/0.99  
% 4.02/0.99  ------                               Statistics
% 4.02/0.99  
% 4.02/0.99  ------ General
% 4.02/0.99  
% 4.02/0.99  abstr_ref_over_cycles:                  0
% 4.02/0.99  abstr_ref_under_cycles:                 0
% 4.02/0.99  gc_basic_clause_elim:                   0
% 4.02/0.99  forced_gc_time:                         0
% 4.02/0.99  parsing_time:                           0.007
% 4.02/0.99  unif_index_cands_time:                  0.
% 4.02/0.99  unif_index_add_time:                    0.
% 4.02/0.99  orderings_time:                         0.
% 4.02/0.99  out_proof_time:                         0.007
% 4.02/0.99  total_time:                             0.424
% 4.02/0.99  num_of_symbols:                         39
% 4.02/0.99  num_of_terms:                           14426
% 4.02/0.99  
% 4.02/0.99  ------ Preprocessing
% 4.02/0.99  
% 4.02/0.99  num_of_splits:                          0
% 4.02/0.99  num_of_split_atoms:                     0
% 4.02/0.99  num_of_reused_defs:                     0
% 4.02/0.99  num_eq_ax_congr_red:                    0
% 4.02/0.99  num_of_sem_filtered_clauses:            1
% 4.02/0.99  num_of_subtypes:                        0
% 4.02/0.99  monotx_restored_types:                  0
% 4.02/0.99  sat_num_of_epr_types:                   0
% 4.02/0.99  sat_num_of_non_cyclic_types:            0
% 4.02/0.99  sat_guarded_non_collapsed_types:        0
% 4.02/0.99  num_pure_diseq_elim:                    0
% 4.02/0.99  simp_replaced_by:                       0
% 4.02/0.99  res_preprocessed:                       46
% 4.02/0.99  prep_upred:                             0
% 4.02/0.99  prep_unflattend:                        1
% 4.02/0.99  smt_new_axioms:                         0
% 4.02/0.99  pred_elim_cands:                        1
% 4.02/0.99  pred_elim:                              0
% 4.02/0.99  pred_elim_cl:                           0
% 4.02/0.99  pred_elim_cycles:                       1
% 4.02/0.99  merged_defs:                            0
% 4.02/0.99  merged_defs_ncl:                        0
% 4.02/0.99  bin_hyper_res:                          0
% 4.02/0.99  prep_cycles:                            3
% 4.02/0.99  pred_elim_time:                         0.
% 4.02/0.99  splitting_time:                         0.
% 4.02/0.99  sem_filter_time:                        0.
% 4.02/0.99  monotx_time:                            0.
% 4.02/0.99  subtype_inf_time:                       0.
% 4.02/0.99  
% 4.02/0.99  ------ Problem properties
% 4.02/0.99  
% 4.02/0.99  clauses:                                11
% 4.02/0.99  conjectures:                            2
% 4.02/0.99  epr:                                    1
% 4.02/0.99  horn:                                   11
% 4.02/0.99  ground:                                 2
% 4.02/0.99  unary:                                  10
% 4.02/0.99  binary:                                 1
% 4.02/0.99  lits:                                   12
% 4.02/0.99  lits_eq:                                10
% 4.02/0.99  fd_pure:                                0
% 4.02/0.99  fd_pseudo:                              0
% 4.02/0.99  fd_cond:                                0
% 4.02/0.99  fd_pseudo_cond:                         1
% 4.02/0.99  ac_symbols:                             1
% 4.02/0.99  
% 4.02/0.99  ------ Propositional Solver
% 4.02/0.99  
% 4.02/0.99  prop_solver_calls:                      27
% 4.02/0.99  prop_fast_solver_calls:                 247
% 4.02/0.99  smt_solver_calls:                       0
% 4.02/0.99  smt_fast_solver_calls:                  0
% 4.02/0.99  prop_num_of_clauses:                    2757
% 4.02/0.99  prop_preprocess_simplified:             4500
% 4.02/0.99  prop_fo_subsumed:                       0
% 4.02/0.99  prop_solver_time:                       0.
% 4.02/0.99  smt_solver_time:                        0.
% 4.02/0.99  smt_fast_solver_time:                   0.
% 4.02/0.99  prop_fast_solver_time:                  0.
% 4.02/0.99  prop_unsat_core_time:                   0.
% 4.02/0.99  
% 4.02/0.99  ------ QBF
% 4.02/0.99  
% 4.02/0.99  qbf_q_res:                              0
% 4.02/0.99  qbf_num_tautologies:                    0
% 4.02/0.99  qbf_prep_cycles:                        0
% 4.02/0.99  
% 4.02/0.99  ------ BMC1
% 4.02/0.99  
% 4.02/0.99  bmc1_current_bound:                     -1
% 4.02/0.99  bmc1_last_solved_bound:                 -1
% 4.02/0.99  bmc1_unsat_core_size:                   -1
% 4.02/0.99  bmc1_unsat_core_parents_size:           -1
% 4.02/0.99  bmc1_merge_next_fun:                    0
% 4.02/0.99  bmc1_unsat_core_clauses_time:           0.
% 4.02/0.99  
% 4.02/0.99  ------ Instantiation
% 4.02/0.99  
% 4.02/0.99  inst_num_of_clauses:                    770
% 4.02/0.99  inst_num_in_passive:                    355
% 4.02/0.99  inst_num_in_active:                     326
% 4.02/0.99  inst_num_in_unprocessed:                89
% 4.02/0.99  inst_num_of_loops:                      350
% 4.02/0.99  inst_num_of_learning_restarts:          0
% 4.02/0.99  inst_num_moves_active_passive:          20
% 4.02/0.99  inst_lit_activity:                      0
% 4.02/0.99  inst_lit_activity_moves:                0
% 4.02/0.99  inst_num_tautologies:                   0
% 4.02/0.99  inst_num_prop_implied:                  0
% 4.02/0.99  inst_num_existing_simplified:           0
% 4.02/0.99  inst_num_eq_res_simplified:             0
% 4.02/0.99  inst_num_child_elim:                    0
% 4.02/0.99  inst_num_of_dismatching_blockings:      254
% 4.02/0.99  inst_num_of_non_proper_insts:           1005
% 4.02/0.99  inst_num_of_duplicates:                 0
% 4.02/0.99  inst_inst_num_from_inst_to_res:         0
% 4.02/0.99  inst_dismatching_checking_time:         0.
% 4.02/0.99  
% 4.02/0.99  ------ Resolution
% 4.02/0.99  
% 4.02/0.99  res_num_of_clauses:                     0
% 4.02/0.99  res_num_in_passive:                     0
% 4.02/0.99  res_num_in_active:                      0
% 4.02/0.99  res_num_of_loops:                       49
% 4.02/0.99  res_forward_subset_subsumed:            218
% 4.02/0.99  res_backward_subset_subsumed:           0
% 4.02/0.99  res_forward_subsumed:                   0
% 4.02/0.99  res_backward_subsumed:                  0
% 4.02/0.99  res_forward_subsumption_resolution:     0
% 4.02/0.99  res_backward_subsumption_resolution:    0
% 4.02/0.99  res_clause_to_clause_subsumption:       11088
% 4.02/0.99  res_orphan_elimination:                 0
% 4.02/0.99  res_tautology_del:                      111
% 4.02/0.99  res_num_eq_res_simplified:              0
% 4.02/0.99  res_num_sel_changes:                    0
% 4.02/0.99  res_moves_from_active_to_pass:          0
% 4.02/0.99  
% 4.02/0.99  ------ Superposition
% 4.02/0.99  
% 4.02/0.99  sup_time_total:                         0.
% 4.02/0.99  sup_time_generating:                    0.
% 4.02/0.99  sup_time_sim_full:                      0.
% 4.02/0.99  sup_time_sim_immed:                     0.
% 4.02/0.99  
% 4.02/0.99  sup_num_of_clauses:                     631
% 4.02/0.99  sup_num_in_active:                      65
% 4.02/0.99  sup_num_in_passive:                     566
% 4.02/0.99  sup_num_of_loops:                       69
% 4.02/0.99  sup_fw_superposition:                   1654
% 4.02/0.99  sup_bw_superposition:                   1355
% 4.02/0.99  sup_immediate_simplified:               1234
% 4.02/0.99  sup_given_eliminated:                   2
% 4.02/0.99  comparisons_done:                       0
% 4.02/0.99  comparisons_avoided:                    0
% 4.02/0.99  
% 4.02/0.99  ------ Simplifications
% 4.02/0.99  
% 4.02/0.99  
% 4.02/0.99  sim_fw_subset_subsumed:                 0
% 4.02/0.99  sim_bw_subset_subsumed:                 0
% 4.02/0.99  sim_fw_subsumed:                        259
% 4.02/0.99  sim_bw_subsumed:                        3
% 4.02/0.99  sim_fw_subsumption_res:                 0
% 4.02/0.99  sim_bw_subsumption_res:                 0
% 4.02/0.99  sim_tautology_del:                      0
% 4.02/0.99  sim_eq_tautology_del:                   192
% 4.02/0.99  sim_eq_res_simp:                        0
% 4.02/0.99  sim_fw_demodulated:                     972
% 4.02/0.99  sim_bw_demodulated:                     51
% 4.02/0.99  sim_light_normalised:                   425
% 4.02/0.99  sim_joinable_taut:                      80
% 4.02/0.99  sim_joinable_simp:                      0
% 4.02/0.99  sim_ac_normalised:                      0
% 4.02/0.99  sim_smt_subsumption:                    0
% 4.02/0.99  
%------------------------------------------------------------------------------
