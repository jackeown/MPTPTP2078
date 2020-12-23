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
% DateTime   : Thu Dec  3 11:58:29 EST 2020

% Result     : Theorem 31.74s
% Output     : CNFRefutation 31.74s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 718 expanded)
%              Number of clauses        :   27 (  53 expanded)
%              Number of leaves         :   20 ( 247 expanded)
%              Depth                    :   19
%              Number of atoms          :   85 ( 720 expanded)
%              Number of equality atoms :   84 ( 719 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
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

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f33,f44])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f32,f45])).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f31,f46])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f47])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1) ),
    inference(definition_unfolding,[],[f36,f47,f47])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) ),
    inference(definition_unfolding,[],[f25,f37,f45,f46])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))) ),
    inference(definition_unfolding,[],[f26,f48,f37,f44,f47])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(cnf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) ),
    inference(definition_unfolding,[],[f27,f48,f37,f35])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) ),
    inference(definition_unfolding,[],[f28,f37,f44])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0) ),
    inference(definition_unfolding,[],[f24,f47,f47])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(negated_conjecture,[],[f19])).

fof(f21,plain,(
    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(ennf_transformation,[],[f20])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))
   => k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f22])).

fof(f43,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f23])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f58,plain,(
    k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) ),
    inference(definition_unfolding,[],[f43,f46,f41,f41,f41,f41,f42,f29])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f39,f29])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(definition_unfolding,[],[f38,f46])).

cnf(c_0,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_5,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3,plain,
    ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4,plain,
    ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_52,plain,
    ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) ),
    inference(light_normalisation,[status(thm)],[c_3,c_4])).

cnf(c_286,plain,
    ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_tarski(X8,X7))) ),
    inference(superposition,[status(thm)],[c_5,c_52])).

cnf(c_69,plain,
    ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_tarski(X6,X7))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) ),
    inference(superposition,[status(thm)],[c_0,c_52])).

cnf(c_1,plain,
    ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_940,plain,
    ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_tarski(X6,X7))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(light_normalisation,[status(thm)],[c_69,c_1])).

cnf(c_944,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X1,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_940])).

cnf(c_2,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1424,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k3_tarski(k2_tarski(k2_tarski(X2,X0),k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_944,c_2])).

cnf(c_181,plain,
    ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X8),k2_tarski(X6,X7))) ),
    inference(superposition,[status(thm)],[c_2,c_52])).

cnf(c_3112,plain,
    ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k3_tarski(k2_tarski(k2_tarski(X6,X7),k2_tarski(X7,X8))))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) ),
    inference(demodulation,[status(thm)],[c_181,c_1424])).

cnf(c_4172,plain,
    ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X7),k2_tarski(X6,X8))) ),
    inference(demodulation,[status(thm)],[c_286,c_1424,c_3112])).

cnf(c_4208,plain,
    ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k2_tarski(X2,X3))) = k3_tarski(k2_tarski(k2_tarski(X0,X2),k2_tarski(X1,X3))) ),
    inference(superposition,[status(thm)],[c_0,c_4172])).

cnf(c_4318,plain,
    ( k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) = k3_tarski(k2_tarski(k2_tarski(X0,X2),k2_tarski(X1,X3))) ),
    inference(light_normalisation,[status(thm)],[c_4208,c_0])).

cnf(c_296,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) ),
    inference(superposition,[status(thm)],[c_0,c_1])).

cnf(c_9,negated_conjecture,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_55,plain,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_9,c_8])).

cnf(c_1088,plain,
    ( k3_tarski(k2_tarski(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)))) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_296,c_55])).

cnf(c_85208,plain,
    ( k3_tarski(k2_tarski(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)))) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_4318,c_1088])).

cnf(c_6,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k2_tarski(X0,X3),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1113,plain,
    ( k3_tarski(k2_tarski(k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)),k2_tarski(k4_tarski(X3,X1),k4_tarski(X3,X2)))) = k2_zfmisc_1(k2_tarski(X0,X3),k2_tarski(X1,X2)) ),
    inference(superposition,[status(thm)],[c_296,c_6])).

cnf(c_85210,plain,
    ( k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_85208,c_1113])).

cnf(c_85211,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_85210])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:47:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 31.74/4.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.74/4.49  
% 31.74/4.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.74/4.49  
% 31.74/4.49  ------  iProver source info
% 31.74/4.49  
% 31.74/4.49  git: date: 2020-06-30 10:37:57 +0100
% 31.74/4.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.74/4.49  git: non_committed_changes: false
% 31.74/4.49  git: last_make_outside_of_git: false
% 31.74/4.49  
% 31.74/4.49  ------ 
% 31.74/4.49  
% 31.74/4.49  ------ Input Options
% 31.74/4.49  
% 31.74/4.49  --out_options                           all
% 31.74/4.49  --tptp_safe_out                         true
% 31.74/4.49  --problem_path                          ""
% 31.74/4.49  --include_path                          ""
% 31.74/4.49  --clausifier                            res/vclausify_rel
% 31.74/4.49  --clausifier_options                    --mode clausify
% 31.74/4.49  --stdin                                 false
% 31.74/4.49  --stats_out                             sel
% 31.74/4.49  
% 31.74/4.49  ------ General Options
% 31.74/4.49  
% 31.74/4.49  --fof                                   false
% 31.74/4.49  --time_out_real                         604.99
% 31.74/4.49  --time_out_virtual                      -1.
% 31.74/4.49  --symbol_type_check                     false
% 31.74/4.49  --clausify_out                          false
% 31.74/4.49  --sig_cnt_out                           false
% 31.74/4.49  --trig_cnt_out                          false
% 31.74/4.49  --trig_cnt_out_tolerance                1.
% 31.74/4.49  --trig_cnt_out_sk_spl                   false
% 31.74/4.49  --abstr_cl_out                          false
% 31.74/4.49  
% 31.74/4.49  ------ Global Options
% 31.74/4.49  
% 31.74/4.49  --schedule                              none
% 31.74/4.49  --add_important_lit                     false
% 31.74/4.49  --prop_solver_per_cl                    1000
% 31.74/4.49  --min_unsat_core                        false
% 31.74/4.49  --soft_assumptions                      false
% 31.74/4.49  --soft_lemma_size                       3
% 31.74/4.49  --prop_impl_unit_size                   0
% 31.74/4.49  --prop_impl_unit                        []
% 31.74/4.49  --share_sel_clauses                     true
% 31.74/4.49  --reset_solvers                         false
% 31.74/4.49  --bc_imp_inh                            [conj_cone]
% 31.74/4.49  --conj_cone_tolerance                   3.
% 31.74/4.49  --extra_neg_conj                        none
% 31.74/4.49  --large_theory_mode                     true
% 31.74/4.49  --prolific_symb_bound                   200
% 31.74/4.49  --lt_threshold                          2000
% 31.74/4.49  --clause_weak_htbl                      true
% 31.74/4.49  --gc_record_bc_elim                     false
% 31.74/4.49  
% 31.74/4.49  ------ Preprocessing Options
% 31.74/4.49  
% 31.74/4.49  --preprocessing_flag                    true
% 31.74/4.49  --time_out_prep_mult                    0.1
% 31.74/4.49  --splitting_mode                        input
% 31.74/4.49  --splitting_grd                         true
% 31.74/4.49  --splitting_cvd                         false
% 31.74/4.49  --splitting_cvd_svl                     false
% 31.74/4.49  --splitting_nvd                         32
% 31.74/4.49  --sub_typing                            true
% 31.74/4.49  --prep_gs_sim                           false
% 31.74/4.49  --prep_unflatten                        true
% 31.74/4.49  --prep_res_sim                          true
% 31.74/4.49  --prep_upred                            true
% 31.74/4.49  --prep_sem_filter                       exhaustive
% 31.74/4.49  --prep_sem_filter_out                   false
% 31.74/4.49  --pred_elim                             false
% 31.74/4.49  --res_sim_input                         true
% 31.74/4.49  --eq_ax_congr_red                       true
% 31.74/4.49  --pure_diseq_elim                       true
% 31.74/4.49  --brand_transform                       false
% 31.74/4.49  --non_eq_to_eq                          false
% 31.74/4.49  --prep_def_merge                        true
% 31.74/4.49  --prep_def_merge_prop_impl              false
% 31.74/4.49  --prep_def_merge_mbd                    true
% 31.74/4.49  --prep_def_merge_tr_red                 false
% 31.74/4.49  --prep_def_merge_tr_cl                  false
% 31.74/4.49  --smt_preprocessing                     true
% 31.74/4.49  --smt_ac_axioms                         fast
% 31.74/4.49  --preprocessed_out                      false
% 31.74/4.49  --preprocessed_stats                    false
% 31.74/4.49  
% 31.74/4.49  ------ Abstraction refinement Options
% 31.74/4.49  
% 31.74/4.49  --abstr_ref                             []
% 31.74/4.49  --abstr_ref_prep                        false
% 31.74/4.49  --abstr_ref_until_sat                   false
% 31.74/4.49  --abstr_ref_sig_restrict                funpre
% 31.74/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.74/4.49  --abstr_ref_under                       []
% 31.74/4.49  
% 31.74/4.49  ------ SAT Options
% 31.74/4.49  
% 31.74/4.49  --sat_mode                              false
% 31.74/4.49  --sat_fm_restart_options                ""
% 31.74/4.49  --sat_gr_def                            false
% 31.74/4.49  --sat_epr_types                         true
% 31.74/4.49  --sat_non_cyclic_types                  false
% 31.74/4.49  --sat_finite_models                     false
% 31.74/4.49  --sat_fm_lemmas                         false
% 31.74/4.49  --sat_fm_prep                           false
% 31.74/4.49  --sat_fm_uc_incr                        true
% 31.74/4.49  --sat_out_model                         small
% 31.74/4.49  --sat_out_clauses                       false
% 31.74/4.49  
% 31.74/4.49  ------ QBF Options
% 31.74/4.49  
% 31.74/4.49  --qbf_mode                              false
% 31.74/4.49  --qbf_elim_univ                         false
% 31.74/4.49  --qbf_dom_inst                          none
% 31.74/4.49  --qbf_dom_pre_inst                      false
% 31.74/4.49  --qbf_sk_in                             false
% 31.74/4.49  --qbf_pred_elim                         true
% 31.74/4.49  --qbf_split                             512
% 31.74/4.49  
% 31.74/4.49  ------ BMC1 Options
% 31.74/4.49  
% 31.74/4.49  --bmc1_incremental                      false
% 31.74/4.49  --bmc1_axioms                           reachable_all
% 31.74/4.49  --bmc1_min_bound                        0
% 31.74/4.49  --bmc1_max_bound                        -1
% 31.74/4.49  --bmc1_max_bound_default                -1
% 31.74/4.49  --bmc1_symbol_reachability              true
% 31.74/4.49  --bmc1_property_lemmas                  false
% 31.74/4.49  --bmc1_k_induction                      false
% 31.74/4.49  --bmc1_non_equiv_states                 false
% 31.74/4.49  --bmc1_deadlock                         false
% 31.74/4.49  --bmc1_ucm                              false
% 31.74/4.49  --bmc1_add_unsat_core                   none
% 31.74/4.49  --bmc1_unsat_core_children              false
% 31.74/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.74/4.49  --bmc1_out_stat                         full
% 31.74/4.49  --bmc1_ground_init                      false
% 31.74/4.49  --bmc1_pre_inst_next_state              false
% 31.74/4.49  --bmc1_pre_inst_state                   false
% 31.74/4.49  --bmc1_pre_inst_reach_state             false
% 31.74/4.49  --bmc1_out_unsat_core                   false
% 31.74/4.49  --bmc1_aig_witness_out                  false
% 31.74/4.49  --bmc1_verbose                          false
% 31.74/4.49  --bmc1_dump_clauses_tptp                false
% 31.74/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.74/4.49  --bmc1_dump_file                        -
% 31.74/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.74/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.74/4.49  --bmc1_ucm_extend_mode                  1
% 31.74/4.49  --bmc1_ucm_init_mode                    2
% 31.74/4.49  --bmc1_ucm_cone_mode                    none
% 31.74/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.74/4.49  --bmc1_ucm_relax_model                  4
% 31.74/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.74/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.74/4.49  --bmc1_ucm_layered_model                none
% 31.74/4.49  --bmc1_ucm_max_lemma_size               10
% 31.74/4.49  
% 31.74/4.49  ------ AIG Options
% 31.74/4.49  
% 31.74/4.49  --aig_mode                              false
% 31.74/4.49  
% 31.74/4.49  ------ Instantiation Options
% 31.74/4.49  
% 31.74/4.49  --instantiation_flag                    true
% 31.74/4.49  --inst_sos_flag                         false
% 31.74/4.49  --inst_sos_phase                        true
% 31.74/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.74/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.74/4.49  --inst_lit_sel_side                     num_symb
% 31.74/4.49  --inst_solver_per_active                1400
% 31.74/4.49  --inst_solver_calls_frac                1.
% 31.74/4.49  --inst_passive_queue_type               priority_queues
% 31.74/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.74/4.49  --inst_passive_queues_freq              [25;2]
% 31.74/4.49  --inst_dismatching                      true
% 31.74/4.49  --inst_eager_unprocessed_to_passive     true
% 31.74/4.49  --inst_prop_sim_given                   true
% 31.74/4.49  --inst_prop_sim_new                     false
% 31.74/4.49  --inst_subs_new                         false
% 31.74/4.49  --inst_eq_res_simp                      false
% 31.74/4.49  --inst_subs_given                       false
% 31.74/4.49  --inst_orphan_elimination               true
% 31.74/4.49  --inst_learning_loop_flag               true
% 31.74/4.49  --inst_learning_start                   3000
% 31.74/4.49  --inst_learning_factor                  2
% 31.74/4.49  --inst_start_prop_sim_after_learn       3
% 31.74/4.49  --inst_sel_renew                        solver
% 31.74/4.49  --inst_lit_activity_flag                true
% 31.74/4.49  --inst_restr_to_given                   false
% 31.74/4.49  --inst_activity_threshold               500
% 31.74/4.49  --inst_out_proof                        true
% 31.74/4.49  
% 31.74/4.49  ------ Resolution Options
% 31.74/4.49  
% 31.74/4.49  --resolution_flag                       true
% 31.74/4.49  --res_lit_sel                           adaptive
% 31.74/4.49  --res_lit_sel_side                      none
% 31.74/4.49  --res_ordering                          kbo
% 31.74/4.49  --res_to_prop_solver                    active
% 31.74/4.49  --res_prop_simpl_new                    false
% 31.74/4.49  --res_prop_simpl_given                  true
% 31.74/4.49  --res_passive_queue_type                priority_queues
% 31.74/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.74/4.49  --res_passive_queues_freq               [15;5]
% 31.74/4.49  --res_forward_subs                      full
% 31.74/4.49  --res_backward_subs                     full
% 31.74/4.49  --res_forward_subs_resolution           true
% 31.74/4.49  --res_backward_subs_resolution          true
% 31.74/4.49  --res_orphan_elimination                true
% 31.74/4.49  --res_time_limit                        2.
% 31.74/4.49  --res_out_proof                         true
% 31.74/4.49  
% 31.74/4.49  ------ Superposition Options
% 31.74/4.49  
% 31.74/4.49  --superposition_flag                    true
% 31.74/4.49  --sup_passive_queue_type                priority_queues
% 31.74/4.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.74/4.49  --sup_passive_queues_freq               [1;4]
% 31.74/4.49  --demod_completeness_check              fast
% 31.74/4.49  --demod_use_ground                      true
% 31.74/4.49  --sup_to_prop_solver                    passive
% 31.74/4.49  --sup_prop_simpl_new                    true
% 31.74/4.49  --sup_prop_simpl_given                  true
% 31.74/4.49  --sup_fun_splitting                     false
% 31.74/4.49  --sup_smt_interval                      50000
% 31.74/4.49  
% 31.74/4.49  ------ Superposition Simplification Setup
% 31.74/4.49  
% 31.74/4.49  --sup_indices_passive                   []
% 31.74/4.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.74/4.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.74/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.74/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.74/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.74/4.49  --sup_full_bw                           [BwDemod]
% 31.74/4.49  --sup_immed_triv                        [TrivRules]
% 31.74/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.74/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.74/4.49  --sup_immed_bw_main                     []
% 31.74/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.74/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.74/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.74/4.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.74/4.49  
% 31.74/4.49  ------ Combination Options
% 31.74/4.49  
% 31.74/4.49  --comb_res_mult                         3
% 31.74/4.49  --comb_sup_mult                         2
% 31.74/4.49  --comb_inst_mult                        10
% 31.74/4.49  
% 31.74/4.49  ------ Debug Options
% 31.74/4.49  
% 31.74/4.49  --dbg_backtrace                         false
% 31.74/4.49  --dbg_dump_prop_clauses                 false
% 31.74/4.49  --dbg_dump_prop_clauses_file            -
% 31.74/4.49  --dbg_out_stat                          false
% 31.74/4.49  ------ Parsing...
% 31.74/4.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.74/4.49  
% 31.74/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.74/4.49  
% 31.74/4.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.74/4.49  
% 31.74/4.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.74/4.49  ------ Proving...
% 31.74/4.49  ------ Problem Properties 
% 31.74/4.49  
% 31.74/4.49  
% 31.74/4.49  clauses                                 10
% 31.74/4.49  conjectures                             1
% 31.74/4.49  EPR                                     0
% 31.74/4.49  Horn                                    10
% 31.74/4.49  unary                                   10
% 31.74/4.49  binary                                  0
% 31.74/4.49  lits                                    10
% 31.74/4.49  lits eq                                 10
% 31.74/4.49  fd_pure                                 0
% 31.74/4.49  fd_pseudo                               0
% 31.74/4.49  fd_cond                                 0
% 31.74/4.49  fd_pseudo_cond                          0
% 31.74/4.49  AC symbols                              0
% 31.74/4.49  
% 31.74/4.49  ------ Input Options Time Limit: Unbounded
% 31.74/4.49  
% 31.74/4.49  
% 31.74/4.49  ------ 
% 31.74/4.49  Current options:
% 31.74/4.49  ------ 
% 31.74/4.49  
% 31.74/4.49  ------ Input Options
% 31.74/4.49  
% 31.74/4.49  --out_options                           all
% 31.74/4.49  --tptp_safe_out                         true
% 31.74/4.49  --problem_path                          ""
% 31.74/4.49  --include_path                          ""
% 31.74/4.49  --clausifier                            res/vclausify_rel
% 31.74/4.49  --clausifier_options                    --mode clausify
% 31.74/4.49  --stdin                                 false
% 31.74/4.49  --stats_out                             sel
% 31.74/4.49  
% 31.74/4.49  ------ General Options
% 31.74/4.49  
% 31.74/4.49  --fof                                   false
% 31.74/4.49  --time_out_real                         604.99
% 31.74/4.49  --time_out_virtual                      -1.
% 31.74/4.49  --symbol_type_check                     false
% 31.74/4.49  --clausify_out                          false
% 31.74/4.49  --sig_cnt_out                           false
% 31.74/4.49  --trig_cnt_out                          false
% 31.74/4.49  --trig_cnt_out_tolerance                1.
% 31.74/4.49  --trig_cnt_out_sk_spl                   false
% 31.74/4.49  --abstr_cl_out                          false
% 31.74/4.49  
% 31.74/4.49  ------ Global Options
% 31.74/4.49  
% 31.74/4.49  --schedule                              none
% 31.74/4.49  --add_important_lit                     false
% 31.74/4.49  --prop_solver_per_cl                    1000
% 31.74/4.49  --min_unsat_core                        false
% 31.74/4.49  --soft_assumptions                      false
% 31.74/4.49  --soft_lemma_size                       3
% 31.74/4.49  --prop_impl_unit_size                   0
% 31.74/4.49  --prop_impl_unit                        []
% 31.74/4.49  --share_sel_clauses                     true
% 31.74/4.49  --reset_solvers                         false
% 31.74/4.49  --bc_imp_inh                            [conj_cone]
% 31.74/4.49  --conj_cone_tolerance                   3.
% 31.74/4.49  --extra_neg_conj                        none
% 31.74/4.49  --large_theory_mode                     true
% 31.74/4.49  --prolific_symb_bound                   200
% 31.74/4.49  --lt_threshold                          2000
% 31.74/4.49  --clause_weak_htbl                      true
% 31.74/4.49  --gc_record_bc_elim                     false
% 31.74/4.49  
% 31.74/4.49  ------ Preprocessing Options
% 31.74/4.49  
% 31.74/4.49  --preprocessing_flag                    true
% 31.74/4.49  --time_out_prep_mult                    0.1
% 31.74/4.49  --splitting_mode                        input
% 31.74/4.49  --splitting_grd                         true
% 31.74/4.49  --splitting_cvd                         false
% 31.74/4.49  --splitting_cvd_svl                     false
% 31.74/4.49  --splitting_nvd                         32
% 31.74/4.49  --sub_typing                            true
% 31.74/4.49  --prep_gs_sim                           false
% 31.74/4.49  --prep_unflatten                        true
% 31.74/4.49  --prep_res_sim                          true
% 31.74/4.49  --prep_upred                            true
% 31.74/4.49  --prep_sem_filter                       exhaustive
% 31.74/4.49  --prep_sem_filter_out                   false
% 31.74/4.49  --pred_elim                             false
% 31.74/4.49  --res_sim_input                         true
% 31.74/4.49  --eq_ax_congr_red                       true
% 31.74/4.49  --pure_diseq_elim                       true
% 31.74/4.49  --brand_transform                       false
% 31.74/4.49  --non_eq_to_eq                          false
% 31.74/4.49  --prep_def_merge                        true
% 31.74/4.49  --prep_def_merge_prop_impl              false
% 31.74/4.49  --prep_def_merge_mbd                    true
% 31.74/4.49  --prep_def_merge_tr_red                 false
% 31.74/4.49  --prep_def_merge_tr_cl                  false
% 31.74/4.49  --smt_preprocessing                     true
% 31.74/4.49  --smt_ac_axioms                         fast
% 31.74/4.49  --preprocessed_out                      false
% 31.74/4.49  --preprocessed_stats                    false
% 31.74/4.49  
% 31.74/4.49  ------ Abstraction refinement Options
% 31.74/4.49  
% 31.74/4.49  --abstr_ref                             []
% 31.74/4.49  --abstr_ref_prep                        false
% 31.74/4.49  --abstr_ref_until_sat                   false
% 31.74/4.49  --abstr_ref_sig_restrict                funpre
% 31.74/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.74/4.49  --abstr_ref_under                       []
% 31.74/4.49  
% 31.74/4.49  ------ SAT Options
% 31.74/4.49  
% 31.74/4.49  --sat_mode                              false
% 31.74/4.49  --sat_fm_restart_options                ""
% 31.74/4.49  --sat_gr_def                            false
% 31.74/4.49  --sat_epr_types                         true
% 31.74/4.49  --sat_non_cyclic_types                  false
% 31.74/4.49  --sat_finite_models                     false
% 31.74/4.49  --sat_fm_lemmas                         false
% 31.74/4.49  --sat_fm_prep                           false
% 31.74/4.49  --sat_fm_uc_incr                        true
% 31.74/4.49  --sat_out_model                         small
% 31.74/4.49  --sat_out_clauses                       false
% 31.74/4.49  
% 31.74/4.49  ------ QBF Options
% 31.74/4.49  
% 31.74/4.49  --qbf_mode                              false
% 31.74/4.49  --qbf_elim_univ                         false
% 31.74/4.49  --qbf_dom_inst                          none
% 31.74/4.49  --qbf_dom_pre_inst                      false
% 31.74/4.49  --qbf_sk_in                             false
% 31.74/4.49  --qbf_pred_elim                         true
% 31.74/4.49  --qbf_split                             512
% 31.74/4.49  
% 31.74/4.49  ------ BMC1 Options
% 31.74/4.49  
% 31.74/4.49  --bmc1_incremental                      false
% 31.74/4.49  --bmc1_axioms                           reachable_all
% 31.74/4.49  --bmc1_min_bound                        0
% 31.74/4.49  --bmc1_max_bound                        -1
% 31.74/4.49  --bmc1_max_bound_default                -1
% 31.74/4.49  --bmc1_symbol_reachability              true
% 31.74/4.49  --bmc1_property_lemmas                  false
% 31.74/4.49  --bmc1_k_induction                      false
% 31.74/4.49  --bmc1_non_equiv_states                 false
% 31.74/4.49  --bmc1_deadlock                         false
% 31.74/4.49  --bmc1_ucm                              false
% 31.74/4.49  --bmc1_add_unsat_core                   none
% 31.74/4.49  --bmc1_unsat_core_children              false
% 31.74/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.74/4.49  --bmc1_out_stat                         full
% 31.74/4.49  --bmc1_ground_init                      false
% 31.74/4.49  --bmc1_pre_inst_next_state              false
% 31.74/4.49  --bmc1_pre_inst_state                   false
% 31.74/4.49  --bmc1_pre_inst_reach_state             false
% 31.74/4.49  --bmc1_out_unsat_core                   false
% 31.74/4.49  --bmc1_aig_witness_out                  false
% 31.74/4.49  --bmc1_verbose                          false
% 31.74/4.49  --bmc1_dump_clauses_tptp                false
% 31.74/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.74/4.49  --bmc1_dump_file                        -
% 31.74/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.74/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.74/4.49  --bmc1_ucm_extend_mode                  1
% 31.74/4.49  --bmc1_ucm_init_mode                    2
% 31.74/4.49  --bmc1_ucm_cone_mode                    none
% 31.74/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.74/4.49  --bmc1_ucm_relax_model                  4
% 31.74/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.74/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.74/4.49  --bmc1_ucm_layered_model                none
% 31.74/4.49  --bmc1_ucm_max_lemma_size               10
% 31.74/4.49  
% 31.74/4.49  ------ AIG Options
% 31.74/4.49  
% 31.74/4.49  --aig_mode                              false
% 31.74/4.49  
% 31.74/4.49  ------ Instantiation Options
% 31.74/4.49  
% 31.74/4.49  --instantiation_flag                    true
% 31.74/4.49  --inst_sos_flag                         false
% 31.74/4.49  --inst_sos_phase                        true
% 31.74/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.74/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.74/4.49  --inst_lit_sel_side                     num_symb
% 31.74/4.49  --inst_solver_per_active                1400
% 31.74/4.49  --inst_solver_calls_frac                1.
% 31.74/4.49  --inst_passive_queue_type               priority_queues
% 31.74/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.74/4.49  --inst_passive_queues_freq              [25;2]
% 31.74/4.49  --inst_dismatching                      true
% 31.74/4.49  --inst_eager_unprocessed_to_passive     true
% 31.74/4.49  --inst_prop_sim_given                   true
% 31.74/4.49  --inst_prop_sim_new                     false
% 31.74/4.49  --inst_subs_new                         false
% 31.74/4.49  --inst_eq_res_simp                      false
% 31.74/4.49  --inst_subs_given                       false
% 31.74/4.49  --inst_orphan_elimination               true
% 31.74/4.49  --inst_learning_loop_flag               true
% 31.74/4.49  --inst_learning_start                   3000
% 31.74/4.49  --inst_learning_factor                  2
% 31.74/4.49  --inst_start_prop_sim_after_learn       3
% 31.74/4.49  --inst_sel_renew                        solver
% 31.74/4.49  --inst_lit_activity_flag                true
% 31.74/4.49  --inst_restr_to_given                   false
% 31.74/4.49  --inst_activity_threshold               500
% 31.74/4.49  --inst_out_proof                        true
% 31.74/4.49  
% 31.74/4.49  ------ Resolution Options
% 31.74/4.49  
% 31.74/4.49  --resolution_flag                       true
% 31.74/4.49  --res_lit_sel                           adaptive
% 31.74/4.49  --res_lit_sel_side                      none
% 31.74/4.49  --res_ordering                          kbo
% 31.74/4.49  --res_to_prop_solver                    active
% 31.74/4.49  --res_prop_simpl_new                    false
% 31.74/4.49  --res_prop_simpl_given                  true
% 31.74/4.49  --res_passive_queue_type                priority_queues
% 31.74/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.74/4.49  --res_passive_queues_freq               [15;5]
% 31.74/4.49  --res_forward_subs                      full
% 31.74/4.49  --res_backward_subs                     full
% 31.74/4.49  --res_forward_subs_resolution           true
% 31.74/4.49  --res_backward_subs_resolution          true
% 31.74/4.49  --res_orphan_elimination                true
% 31.74/4.49  --res_time_limit                        2.
% 31.74/4.49  --res_out_proof                         true
% 31.74/4.49  
% 31.74/4.49  ------ Superposition Options
% 31.74/4.49  
% 31.74/4.49  --superposition_flag                    true
% 31.74/4.49  --sup_passive_queue_type                priority_queues
% 31.74/4.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.74/4.49  --sup_passive_queues_freq               [1;4]
% 31.74/4.49  --demod_completeness_check              fast
% 31.74/4.49  --demod_use_ground                      true
% 31.74/4.49  --sup_to_prop_solver                    passive
% 31.74/4.49  --sup_prop_simpl_new                    true
% 31.74/4.49  --sup_prop_simpl_given                  true
% 31.74/4.49  --sup_fun_splitting                     false
% 31.74/4.49  --sup_smt_interval                      50000
% 31.74/4.49  
% 31.74/4.49  ------ Superposition Simplification Setup
% 31.74/4.49  
% 31.74/4.49  --sup_indices_passive                   []
% 31.74/4.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.74/4.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.74/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.74/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.74/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.74/4.49  --sup_full_bw                           [BwDemod]
% 31.74/4.49  --sup_immed_triv                        [TrivRules]
% 31.74/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.74/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.74/4.49  --sup_immed_bw_main                     []
% 31.74/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.74/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.74/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.74/4.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.74/4.49  
% 31.74/4.49  ------ Combination Options
% 31.74/4.49  
% 31.74/4.49  --comb_res_mult                         3
% 31.74/4.49  --comb_sup_mult                         2
% 31.74/4.49  --comb_inst_mult                        10
% 31.74/4.49  
% 31.74/4.49  ------ Debug Options
% 31.74/4.49  
% 31.74/4.49  --dbg_backtrace                         false
% 31.74/4.49  --dbg_dump_prop_clauses                 false
% 31.74/4.49  --dbg_dump_prop_clauses_file            -
% 31.74/4.49  --dbg_out_stat                          false
% 31.74/4.49  
% 31.74/4.49  
% 31.74/4.49  
% 31.74/4.49  
% 31.74/4.49  ------ Proving...
% 31.74/4.49  
% 31.74/4.49  
% 31.74/4.49  % SZS status Theorem for theBenchmark.p
% 31.74/4.49  
% 31.74/4.49   Resolution empty clause
% 31.74/4.49  
% 31.74/4.49  % SZS output start CNFRefutation for theBenchmark.p
% 31.74/4.49  
% 31.74/4.49  fof(f7,axiom,(
% 31.74/4.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 31.74/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.74/4.49  
% 31.74/4.49  fof(f30,plain,(
% 31.74/4.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 31.74/4.49    inference(cnf_transformation,[],[f7])).
% 31.74/4.49  
% 31.74/4.49  fof(f8,axiom,(
% 31.74/4.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 31.74/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.74/4.49  
% 31.74/4.49  fof(f31,plain,(
% 31.74/4.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 31.74/4.49    inference(cnf_transformation,[],[f8])).
% 31.74/4.49  
% 31.74/4.49  fof(f9,axiom,(
% 31.74/4.49    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 31.74/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.74/4.49  
% 31.74/4.49  fof(f32,plain,(
% 31.74/4.49    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 31.74/4.49    inference(cnf_transformation,[],[f9])).
% 31.74/4.49  
% 31.74/4.49  fof(f10,axiom,(
% 31.74/4.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 31.74/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.74/4.49  
% 31.74/4.49  fof(f33,plain,(
% 31.74/4.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 31.74/4.49    inference(cnf_transformation,[],[f10])).
% 31.74/4.49  
% 31.74/4.49  fof(f11,axiom,(
% 31.74/4.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 31.74/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.74/4.49  
% 31.74/4.49  fof(f34,plain,(
% 31.74/4.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 31.74/4.49    inference(cnf_transformation,[],[f11])).
% 31.74/4.49  
% 31.74/4.49  fof(f12,axiom,(
% 31.74/4.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 31.74/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.74/4.49  
% 31.74/4.49  fof(f35,plain,(
% 31.74/4.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 31.74/4.49    inference(cnf_transformation,[],[f12])).
% 31.74/4.49  
% 31.74/4.49  fof(f44,plain,(
% 31.74/4.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 31.74/4.49    inference(definition_unfolding,[],[f34,f35])).
% 31.74/4.49  
% 31.74/4.49  fof(f45,plain,(
% 31.74/4.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 31.74/4.49    inference(definition_unfolding,[],[f33,f44])).
% 31.74/4.49  
% 31.74/4.49  fof(f46,plain,(
% 31.74/4.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 31.74/4.49    inference(definition_unfolding,[],[f32,f45])).
% 31.74/4.49  
% 31.74/4.49  fof(f47,plain,(
% 31.74/4.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 31.74/4.49    inference(definition_unfolding,[],[f31,f46])).
% 31.74/4.49  
% 31.74/4.49  fof(f49,plain,(
% 31.74/4.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 31.74/4.49    inference(definition_unfolding,[],[f30,f47])).
% 31.74/4.49  
% 31.74/4.49  fof(f13,axiom,(
% 31.74/4.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 31.74/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.74/4.49  
% 31.74/4.49  fof(f36,plain,(
% 31.74/4.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 31.74/4.49    inference(cnf_transformation,[],[f13])).
% 31.74/4.49  
% 31.74/4.49  fof(f54,plain,(
% 31.74/4.49    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1)) )),
% 31.74/4.49    inference(definition_unfolding,[],[f36,f47,f47])).
% 31.74/4.49  
% 31.74/4.49  fof(f3,axiom,(
% 31.74/4.49    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 31.74/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.74/4.49  
% 31.74/4.49  fof(f26,plain,(
% 31.74/4.49    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))) )),
% 31.74/4.49    inference(cnf_transformation,[],[f3])).
% 31.74/4.49  
% 31.74/4.49  fof(f2,axiom,(
% 31.74/4.49    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 31.74/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.74/4.49  
% 31.74/4.49  fof(f25,plain,(
% 31.74/4.49    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) )),
% 31.74/4.49    inference(cnf_transformation,[],[f2])).
% 31.74/4.49  
% 31.74/4.49  fof(f48,plain,(
% 31.74/4.49    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8)))) )),
% 31.74/4.49    inference(definition_unfolding,[],[f25,f37,f45,f46])).
% 31.74/4.49  
% 31.74/4.49  fof(f14,axiom,(
% 31.74/4.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 31.74/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.74/4.49  
% 31.74/4.49  fof(f37,plain,(
% 31.74/4.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 31.74/4.49    inference(cnf_transformation,[],[f14])).
% 31.74/4.49  
% 31.74/4.49  fof(f52,plain,(
% 31.74/4.49    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8)))) )),
% 31.74/4.49    inference(definition_unfolding,[],[f26,f48,f37,f44,f47])).
% 31.74/4.49  
% 31.74/4.49  fof(f4,axiom,(
% 31.74/4.49    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))),
% 31.74/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.74/4.49  
% 31.74/4.49  fof(f27,plain,(
% 31.74/4.49    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) )),
% 31.74/4.49    inference(cnf_transformation,[],[f4])).
% 31.74/4.49  
% 31.74/4.49  fof(f53,plain,(
% 31.74/4.49    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8)))) )),
% 31.74/4.49    inference(definition_unfolding,[],[f27,f48,f37,f35])).
% 31.74/4.49  
% 31.74/4.49  fof(f5,axiom,(
% 31.74/4.49    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 31.74/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.74/4.49  
% 31.74/4.49  fof(f28,plain,(
% 31.74/4.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 31.74/4.49    inference(cnf_transformation,[],[f5])).
% 31.74/4.49  
% 31.74/4.49  fof(f50,plain,(
% 31.74/4.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)))) )),
% 31.74/4.49    inference(definition_unfolding,[],[f28,f37,f44])).
% 31.74/4.49  
% 31.74/4.49  fof(f1,axiom,(
% 31.74/4.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 31.74/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.74/4.49  
% 31.74/4.49  fof(f24,plain,(
% 31.74/4.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 31.74/4.49    inference(cnf_transformation,[],[f1])).
% 31.74/4.49  
% 31.74/4.49  fof(f51,plain,(
% 31.74/4.49    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) )),
% 31.74/4.49    inference(definition_unfolding,[],[f24,f47,f47])).
% 31.74/4.49  
% 31.74/4.49  fof(f19,conjecture,(
% 31.74/4.49    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))),
% 31.74/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.74/4.49  
% 31.74/4.49  fof(f20,negated_conjecture,(
% 31.74/4.49    ~! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))),
% 31.74/4.49    inference(negated_conjecture,[],[f19])).
% 31.74/4.49  
% 31.74/4.49  fof(f21,plain,(
% 31.74/4.49    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))),
% 31.74/4.49    inference(ennf_transformation,[],[f20])).
% 31.74/4.49  
% 31.74/4.49  fof(f22,plain,(
% 31.74/4.49    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) => k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 31.74/4.49    introduced(choice_axiom,[])).
% 31.74/4.49  
% 31.74/4.49  fof(f23,plain,(
% 31.74/4.49    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 31.74/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f22])).
% 31.74/4.49  
% 31.74/4.49  fof(f43,plain,(
% 31.74/4.49    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 31.74/4.49    inference(cnf_transformation,[],[f23])).
% 31.74/4.49  
% 31.74/4.49  fof(f17,axiom,(
% 31.74/4.49    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 31.74/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.74/4.49  
% 31.74/4.49  fof(f41,plain,(
% 31.74/4.49    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 31.74/4.49    inference(cnf_transformation,[],[f17])).
% 31.74/4.49  
% 31.74/4.49  fof(f18,axiom,(
% 31.74/4.49    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 31.74/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.74/4.49  
% 31.74/4.49  fof(f42,plain,(
% 31.74/4.49    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 31.74/4.49    inference(cnf_transformation,[],[f18])).
% 31.74/4.49  
% 31.74/4.49  fof(f6,axiom,(
% 31.74/4.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 31.74/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.74/4.49  
% 31.74/4.49  fof(f29,plain,(
% 31.74/4.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 31.74/4.49    inference(cnf_transformation,[],[f6])).
% 31.74/4.49  
% 31.74/4.49  fof(f58,plain,(
% 31.74/4.49    k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4))),
% 31.74/4.49    inference(definition_unfolding,[],[f43,f46,f41,f41,f41,f41,f42,f29])).
% 31.74/4.49  
% 31.74/4.49  fof(f16,axiom,(
% 31.74/4.49    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 31.74/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.74/4.49  
% 31.74/4.49  fof(f39,plain,(
% 31.74/4.49    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 31.74/4.49    inference(cnf_transformation,[],[f16])).
% 31.74/4.49  
% 31.74/4.49  fof(f57,plain,(
% 31.74/4.49    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2))) )),
% 31.74/4.49    inference(definition_unfolding,[],[f39,f29])).
% 31.74/4.49  
% 31.74/4.49  fof(f15,axiom,(
% 31.74/4.49    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 31.74/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.74/4.49  
% 31.74/4.49  fof(f38,plain,(
% 31.74/4.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 31.74/4.49    inference(cnf_transformation,[],[f15])).
% 31.74/4.49  
% 31.74/4.49  fof(f55,plain,(
% 31.74/4.49    ( ! [X2,X0,X3,X1] : (k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 31.74/4.49    inference(definition_unfolding,[],[f38,f46])).
% 31.74/4.49  
% 31.74/4.49  cnf(c_0,plain,
% 31.74/4.49      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
% 31.74/4.49      inference(cnf_transformation,[],[f49]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_5,plain,
% 31.74/4.49      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1) ),
% 31.74/4.49      inference(cnf_transformation,[],[f54]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_3,plain,
% 31.74/4.49      ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) ),
% 31.74/4.49      inference(cnf_transformation,[],[f52]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_4,plain,
% 31.74/4.49      ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) ),
% 31.74/4.49      inference(cnf_transformation,[],[f53]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_52,plain,
% 31.74/4.49      ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) ),
% 31.74/4.49      inference(light_normalisation,[status(thm)],[c_3,c_4]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_286,plain,
% 31.74/4.49      ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_tarski(X8,X7))) ),
% 31.74/4.49      inference(superposition,[status(thm)],[c_5,c_52]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_69,plain,
% 31.74/4.49      ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_tarski(X6,X7))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) ),
% 31.74/4.49      inference(superposition,[status(thm)],[c_0,c_52]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_1,plain,
% 31.74/4.49      ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 31.74/4.49      inference(cnf_transformation,[],[f50]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_940,plain,
% 31.74/4.49      ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_tarski(X6,X7))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 31.74/4.49      inference(light_normalisation,[status(thm)],[c_69,c_1]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_944,plain,
% 31.74/4.49      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X1,X2))) ),
% 31.74/4.49      inference(superposition,[status(thm)],[c_0,c_940]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_2,plain,
% 31.74/4.49      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X0,X1) ),
% 31.74/4.49      inference(cnf_transformation,[],[f51]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_1424,plain,
% 31.74/4.49      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k3_tarski(k2_tarski(k2_tarski(X2,X0),k2_tarski(X0,X1))) ),
% 31.74/4.49      inference(superposition,[status(thm)],[c_944,c_2]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_181,plain,
% 31.74/4.49      ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X8),k2_tarski(X6,X7))) ),
% 31.74/4.49      inference(superposition,[status(thm)],[c_2,c_52]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_3112,plain,
% 31.74/4.49      ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k3_tarski(k2_tarski(k2_tarski(X6,X7),k2_tarski(X7,X8))))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) ),
% 31.74/4.49      inference(demodulation,[status(thm)],[c_181,c_1424]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_4172,plain,
% 31.74/4.49      ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X7),k2_tarski(X6,X8))) ),
% 31.74/4.49      inference(demodulation,[status(thm)],[c_286,c_1424,c_3112]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_4208,plain,
% 31.74/4.49      ( k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k2_tarski(X2,X3))) = k3_tarski(k2_tarski(k2_tarski(X0,X2),k2_tarski(X1,X3))) ),
% 31.74/4.49      inference(superposition,[status(thm)],[c_0,c_4172]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_4318,plain,
% 31.74/4.49      ( k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) = k3_tarski(k2_tarski(k2_tarski(X0,X2),k2_tarski(X1,X3))) ),
% 31.74/4.49      inference(light_normalisation,[status(thm)],[c_4208,c_0]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_296,plain,
% 31.74/4.49      ( k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) ),
% 31.74/4.49      inference(superposition,[status(thm)],[c_0,c_1]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_9,negated_conjecture,
% 31.74/4.49      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) ),
% 31.74/4.49      inference(cnf_transformation,[],[f58]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_8,plain,
% 31.74/4.49      ( k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
% 31.74/4.49      inference(cnf_transformation,[],[f57]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_55,plain,
% 31.74/4.49      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) ),
% 31.74/4.49      inference(demodulation,[status(thm)],[c_9,c_8]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_1088,plain,
% 31.74/4.49      ( k3_tarski(k2_tarski(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)))) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) ),
% 31.74/4.49      inference(demodulation,[status(thm)],[c_296,c_55]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_85208,plain,
% 31.74/4.49      ( k3_tarski(k2_tarski(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)))) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) ),
% 31.74/4.49      inference(superposition,[status(thm)],[c_4318,c_1088]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_6,plain,
% 31.74/4.49      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k2_tarski(X0,X3),k2_tarski(X1,X2)) ),
% 31.74/4.49      inference(cnf_transformation,[],[f55]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_1113,plain,
% 31.74/4.49      ( k3_tarski(k2_tarski(k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)),k2_tarski(k4_tarski(X3,X1),k4_tarski(X3,X2)))) = k2_zfmisc_1(k2_tarski(X0,X3),k2_tarski(X1,X2)) ),
% 31.74/4.49      inference(superposition,[status(thm)],[c_296,c_6]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_85210,plain,
% 31.74/4.49      ( k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) ),
% 31.74/4.49      inference(demodulation,[status(thm)],[c_85208,c_1113]) ).
% 31.74/4.49  
% 31.74/4.49  cnf(c_85211,plain,
% 31.74/4.49      ( $false ),
% 31.74/4.49      inference(equality_resolution_simp,[status(thm)],[c_85210]) ).
% 31.74/4.49  
% 31.74/4.49  
% 31.74/4.49  % SZS output end CNFRefutation for theBenchmark.p
% 31.74/4.49  
% 31.74/4.49  ------                               Statistics
% 31.74/4.49  
% 31.74/4.49  ------ Selected
% 31.74/4.49  
% 31.74/4.49  total_time:                             3.745
% 31.74/4.49  
%------------------------------------------------------------------------------
