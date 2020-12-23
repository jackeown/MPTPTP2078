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
% DateTime   : Thu Dec  3 11:58:20 EST 2020

% Result     : Theorem 12.15s
% Output     : CNFRefutation 12.15s
% Verified   : 
% Statistics : Number of formulae       :  108 (1030 expanded)
%              Number of clauses        :   51 (  98 expanded)
%              Number of leaves         :   23 ( 343 expanded)
%              Depth                    :   19
%              Number of atoms          :  132 (1056 expanded)
%              Number of equality atoms :  131 (1055 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f38,f48])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f37,f49])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f36,f50])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f51])).

fof(f56,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f27,f52,f52])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f34,f52])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k4_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f33,f26,f40,f54])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0) ),
    inference(definition_unfolding,[],[f28,f51,f51])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(definition_unfolding,[],[f29,f26,f49,f50])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) ),
    inference(definition_unfolding,[],[f32,f26,f54,f53])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f61,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f26,f52])).

fof(f21,conjecture,(
    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) ),
    inference(negated_conjecture,[],[f21])).

fof(f23,plain,(
    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) ),
    inference(ennf_transformation,[],[f22])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))
   => k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f23,f24])).

fof(f47,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f25])).

fof(f19,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f47,f50,f45,f45,f45,f45,f46,f52,f54,f52])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
    inference(definition_unfolding,[],[f42,f50,f52,f52])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f63,plain,(
    ! [X2,X0,X1] : k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(definition_unfolding,[],[f44,f52,f52,f54])).

cnf(c_1,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_33,plain,
    ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X0_39) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_0,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k4_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_34,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39),k4_xboole_0(k6_enumset1(X7_39,X7_39,X7_39,X7_39,X7_39,X7_39,X7_39,X7_39),k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_448,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39),k4_xboole_0(k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39))) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X0_39,X2_39) ),
    inference(superposition,[status(thm)],[c_33,c_34])).

cnf(c_2,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_32,plain,
    ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39) = k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X0_39,X1_39) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_446,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39),k4_xboole_0(k6_enumset1(X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39))) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X0_39,X3_39) ),
    inference(superposition,[status(thm)],[c_32,c_34])).

cnf(c_11757,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X1_39),k4_xboole_0(k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X1_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39),k4_xboole_0(k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39))) ),
    inference(superposition,[status(thm)],[c_448,c_446])).

cnf(c_11782,plain,
    ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X1_39,X2_39) = k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39) ),
    inference(demodulation,[status(thm)],[c_11757,c_34])).

cnf(c_12347,plain,
    ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X1_39,X2_39) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X0_39) ),
    inference(superposition,[status(thm)],[c_11782,c_32])).

cnf(c_5,plain,
    ( k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_29,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39),k4_xboole_0(k6_enumset1(X8_39,X8_39,X8_39,X8_39,X8_39,X8_39,X8_39,X8_39),k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39,X8_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_15987,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39),k4_xboole_0(k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X3_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39))) = k5_xboole_0(k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X0_39),k4_xboole_0(k6_enumset1(X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X0_39))) ),
    inference(superposition,[status(thm)],[c_12347,c_29])).

cnf(c_6,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_28,plain,
    ( k3_tarski(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39)) = k5_xboole_0(X0_39,k4_xboole_0(X1_39,X0_39)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_186,plain,
    ( k3_tarski(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39)) = k5_xboole_0(X1_39,k4_xboole_0(X0_39,X1_39)) ),
    inference(superposition,[status(thm)],[c_33,c_28])).

cnf(c_296,plain,
    ( k5_xboole_0(X0_39,k4_xboole_0(X1_39,X0_39)) = k5_xboole_0(X1_39,k4_xboole_0(X0_39,X1_39)) ),
    inference(superposition,[status(thm)],[c_186,c_28])).

cnf(c_449,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39),k4_xboole_0(k6_enumset1(X1_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39))) = k6_enumset1(X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39,X0_39) ),
    inference(superposition,[status(thm)],[c_34,c_296])).

cnf(c_16242,plain,
    ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39) = k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X3_39,X2_39) ),
    inference(demodulation,[status(thm)],[c_15987,c_34,c_449])).

cnf(c_4965,plain,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39),k4_xboole_0(k6_enumset1(X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39))),k4_xboole_0(k6_enumset1(X4_39,X4_39,X4_39,X4_39,X4_39,X4_39,X4_39,X4_39),k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39),k4_xboole_0(k6_enumset1(X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39))))) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X2_39,X0_39,X3_39,X4_39) ),
    inference(superposition,[status(thm)],[c_446,c_34])).

cnf(c_5022,plain,
    ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39) = k6_enumset1(X2_39,X2_39,X2_39,X2_39,X0_39,X1_39,X3_39,X4_39) ),
    inference(demodulation,[status(thm)],[c_4965,c_34])).

cnf(c_4877,plain,
    ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39) = k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X0_39,X1_39,X3_39) ),
    inference(superposition,[status(thm)],[c_34,c_446])).

cnf(c_5702,plain,
    ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X0_39,X2_39,X3_39) = k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X0_39,X1_39,X3_39) ),
    inference(superposition,[status(thm)],[c_5022,c_4877])).

cnf(c_25230,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X0_39,X2_39,X3_39),k4_xboole_0(k6_enumset1(X4_39,X4_39,X4_39,X4_39,X4_39,X4_39,X4_39,X4_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X0_39,X2_39,X3_39))) = k5_xboole_0(k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39),k4_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X3_39,X4_39),k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39))) ),
    inference(superposition,[status(thm)],[c_5702,c_29])).

cnf(c_25414,plain,
    ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39) = k6_enumset1(X0_39,X0_39,X0_39,X1_39,X0_39,X4_39,X2_39,X3_39) ),
    inference(demodulation,[status(thm)],[c_25230,c_34,c_449])).

cnf(c_10,negated_conjecture,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_24,negated_conjecture,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_27608,plain,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_25414,c_24])).

cnf(c_30510,plain,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_16242,c_27608])).

cnf(c_37,plain,
    ( X0_39 != X1_39
    | X2_39 != X1_39
    | X2_39 = X0_39 ),
    theory(equality)).

cnf(c_224,plain,
    ( X0_39 != X1_39
    | X0_39 = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != X1_39 ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_1653,plain,
    ( X0_39 != k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | X0_39 = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(c_8000,plain,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)) = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1653])).

cnf(c_7,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_27,plain,
    ( k6_enumset1(k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X2_39),k4_tarski(X3_39,X1_39),k4_tarski(X3_39,X2_39)) = k2_zfmisc_1(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X3_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3994,plain,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)) = k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_43,plain,
    ( X0_39 != X1_39
    | X2_39 != X3_39
    | k2_zfmisc_1(X0_39,X2_39) = k2_zfmisc_1(X1_39,X3_39) ),
    theory(equality)).

cnf(c_144,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != X0_39
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != X1_39
    | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k2_zfmisc_1(X1_39,X0_39) ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_761,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != X0_39
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))
    | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),X0_39) ),
    inference(instantiation,[status(thm)],[c_144])).

cnf(c_1419,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))
    | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_35,plain,
    ( X0_39 = X0_39 ),
    theory(equality)).

cnf(c_356,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_8,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_26,plain,
    ( k6_enumset1(k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X2_39,X1_39)) = k2_zfmisc_1(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X2_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_270,plain,
    ( k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)) = k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_159,plain,
    ( X0_39 != X1_39
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != X1_39
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = X0_39 ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_173,plain,
    ( X0_39 != k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = X0_39
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_159])).

cnf(c_269,plain,
    ( k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)) != k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_157,plain,
    ( k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30510,c_8000,c_3994,c_1419,c_356,c_270,c_269,c_157])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:02:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 12.15/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.15/1.99  
% 12.15/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.15/1.99  
% 12.15/1.99  ------  iProver source info
% 12.15/1.99  
% 12.15/1.99  git: date: 2020-06-30 10:37:57 +0100
% 12.15/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.15/1.99  git: non_committed_changes: false
% 12.15/1.99  git: last_make_outside_of_git: false
% 12.15/1.99  
% 12.15/1.99  ------ 
% 12.15/1.99  ------ Parsing...
% 12.15/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.15/1.99  
% 12.15/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 12.15/1.99  
% 12.15/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.15/1.99  
% 12.15/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 12.15/1.99  ------ Proving...
% 12.15/1.99  ------ Problem Properties 
% 12.15/1.99  
% 12.15/1.99  
% 12.15/1.99  clauses                                 11
% 12.15/1.99  conjectures                             1
% 12.15/1.99  EPR                                     0
% 12.15/1.99  Horn                                    11
% 12.15/1.99  unary                                   11
% 12.15/1.99  binary                                  0
% 12.15/1.99  lits                                    11
% 12.15/1.99  lits eq                                 11
% 12.15/1.99  fd_pure                                 0
% 12.15/1.99  fd_pseudo                               0
% 12.15/1.99  fd_cond                                 0
% 12.15/1.99  fd_pseudo_cond                          0
% 12.15/1.99  AC symbols                              0
% 12.15/1.99  
% 12.15/1.99  ------ Input Options Time Limit: Unbounded
% 12.15/1.99  
% 12.15/1.99  
% 12.15/1.99  ------ 
% 12.15/1.99  Current options:
% 12.15/1.99  ------ 
% 12.15/1.99  
% 12.15/1.99  
% 12.15/1.99  
% 12.15/1.99  
% 12.15/1.99  ------ Proving...
% 12.15/1.99  
% 12.15/1.99  
% 12.15/1.99  % SZS status Theorem for theBenchmark.p
% 12.15/1.99  
% 12.15/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 12.15/1.99  
% 12.15/1.99  fof(f2,axiom,(
% 12.15/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 12.15/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.15/1.99  
% 12.15/1.99  fof(f27,plain,(
% 12.15/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 12.15/1.99    inference(cnf_transformation,[],[f2])).
% 12.15/1.99  
% 12.15/1.99  fof(f10,axiom,(
% 12.15/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 12.15/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.15/1.99  
% 12.15/1.99  fof(f35,plain,(
% 12.15/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 12.15/1.99    inference(cnf_transformation,[],[f10])).
% 12.15/1.99  
% 12.15/1.99  fof(f11,axiom,(
% 12.15/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 12.15/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.15/1.99  
% 12.15/1.99  fof(f36,plain,(
% 12.15/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 12.15/1.99    inference(cnf_transformation,[],[f11])).
% 12.15/1.99  
% 12.15/1.99  fof(f12,axiom,(
% 12.15/1.99    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 12.15/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.15/1.99  
% 12.15/1.99  fof(f37,plain,(
% 12.15/1.99    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 12.15/1.99    inference(cnf_transformation,[],[f12])).
% 12.15/1.99  
% 12.15/1.99  fof(f13,axiom,(
% 12.15/1.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 12.15/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.15/1.99  
% 12.15/1.99  fof(f38,plain,(
% 12.15/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 12.15/1.99    inference(cnf_transformation,[],[f13])).
% 12.15/1.99  
% 12.15/1.99  fof(f14,axiom,(
% 12.15/1.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 12.15/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.15/1.99  
% 12.15/1.99  fof(f39,plain,(
% 12.15/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 12.15/1.99    inference(cnf_transformation,[],[f14])).
% 12.15/1.99  
% 12.15/1.99  fof(f15,axiom,(
% 12.15/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 12.15/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.15/1.99  
% 12.15/1.99  fof(f40,plain,(
% 12.15/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 12.15/1.99    inference(cnf_transformation,[],[f15])).
% 12.15/1.99  
% 12.15/1.99  fof(f48,plain,(
% 12.15/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 12.15/1.99    inference(definition_unfolding,[],[f39,f40])).
% 12.15/1.99  
% 12.15/1.99  fof(f49,plain,(
% 12.15/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 12.15/1.99    inference(definition_unfolding,[],[f38,f48])).
% 12.15/1.99  
% 12.15/1.99  fof(f50,plain,(
% 12.15/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 12.15/1.99    inference(definition_unfolding,[],[f37,f49])).
% 12.15/1.99  
% 12.15/1.99  fof(f51,plain,(
% 12.15/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 12.15/1.99    inference(definition_unfolding,[],[f36,f50])).
% 12.15/1.99  
% 12.15/1.99  fof(f52,plain,(
% 12.15/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 12.15/1.99    inference(definition_unfolding,[],[f35,f51])).
% 12.15/1.99  
% 12.15/1.99  fof(f56,plain,(
% 12.15/1.99    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 12.15/1.99    inference(definition_unfolding,[],[f27,f52,f52])).
% 12.15/1.99  
% 12.15/1.99  fof(f8,axiom,(
% 12.15/1.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 12.15/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.15/1.99  
% 12.15/1.99  fof(f33,plain,(
% 12.15/1.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 12.15/1.99    inference(cnf_transformation,[],[f8])).
% 12.15/1.99  
% 12.15/1.99  fof(f1,axiom,(
% 12.15/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 12.15/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.15/1.99  
% 12.15/1.99  fof(f26,plain,(
% 12.15/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 12.15/1.99    inference(cnf_transformation,[],[f1])).
% 12.15/1.99  
% 12.15/1.99  fof(f9,axiom,(
% 12.15/1.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 12.15/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.15/1.99  
% 12.15/1.99  fof(f34,plain,(
% 12.15/1.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 12.15/1.99    inference(cnf_transformation,[],[f9])).
% 12.15/1.99  
% 12.15/1.99  fof(f54,plain,(
% 12.15/1.99    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 12.15/1.99    inference(definition_unfolding,[],[f34,f52])).
% 12.15/1.99  
% 12.15/1.99  fof(f55,plain,(
% 12.15/1.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k4_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 12.15/1.99    inference(definition_unfolding,[],[f33,f26,f40,f54])).
% 12.15/1.99  
% 12.15/1.99  fof(f3,axiom,(
% 12.15/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 12.15/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.15/1.99  
% 12.15/1.99  fof(f28,plain,(
% 12.15/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 12.15/1.99    inference(cnf_transformation,[],[f3])).
% 12.15/1.99  
% 12.15/1.99  fof(f57,plain,(
% 12.15/1.99    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) )),
% 12.15/1.99    inference(definition_unfolding,[],[f28,f51,f51])).
% 12.15/1.99  
% 12.15/1.99  fof(f7,axiom,(
% 12.15/1.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 12.15/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.15/1.99  
% 12.15/1.99  fof(f32,plain,(
% 12.15/1.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 12.15/1.99    inference(cnf_transformation,[],[f7])).
% 12.15/1.99  
% 12.15/1.99  fof(f4,axiom,(
% 12.15/1.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 12.15/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.15/1.99  
% 12.15/1.99  fof(f29,plain,(
% 12.15/1.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 12.15/1.99    inference(cnf_transformation,[],[f4])).
% 12.15/1.99  
% 12.15/1.99  fof(f53,plain,(
% 12.15/1.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 12.15/1.99    inference(definition_unfolding,[],[f29,f26,f49,f50])).
% 12.15/1.99  
% 12.15/1.99  fof(f60,plain,(
% 12.15/1.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) )),
% 12.15/1.99    inference(definition_unfolding,[],[f32,f26,f54,f53])).
% 12.15/1.99  
% 12.15/1.99  fof(f16,axiom,(
% 12.15/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 12.15/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.15/1.99  
% 12.15/1.99  fof(f41,plain,(
% 12.15/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 12.15/1.99    inference(cnf_transformation,[],[f16])).
% 12.15/1.99  
% 12.15/1.99  fof(f61,plain,(
% 12.15/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 12.15/1.99    inference(definition_unfolding,[],[f41,f26,f52])).
% 12.15/1.99  
% 12.15/1.99  fof(f21,conjecture,(
% 12.15/1.99    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 12.15/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.15/1.99  
% 12.15/1.99  fof(f22,negated_conjecture,(
% 12.15/1.99    ~! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 12.15/1.99    inference(negated_conjecture,[],[f21])).
% 12.15/1.99  
% 12.15/1.99  fof(f23,plain,(
% 12.15/1.99    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 12.15/1.99    inference(ennf_transformation,[],[f22])).
% 12.15/1.99  
% 12.15/1.99  fof(f24,plain,(
% 12.15/1.99    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) => k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 12.15/1.99    introduced(choice_axiom,[])).
% 12.15/1.99  
% 12.15/1.99  fof(f25,plain,(
% 12.15/1.99    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 12.15/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f23,f24])).
% 12.15/1.99  
% 12.15/1.99  fof(f47,plain,(
% 12.15/1.99    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 12.15/1.99    inference(cnf_transformation,[],[f25])).
% 12.15/1.99  
% 12.15/1.99  fof(f19,axiom,(
% 12.15/1.99    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 12.15/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.15/1.99  
% 12.15/1.99  fof(f45,plain,(
% 12.15/1.99    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 12.15/1.99    inference(cnf_transformation,[],[f19])).
% 12.15/1.99  
% 12.15/1.99  fof(f20,axiom,(
% 12.15/1.99    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 12.15/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.15/1.99  
% 12.15/1.99  fof(f46,plain,(
% 12.15/1.99    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 12.15/1.99    inference(cnf_transformation,[],[f20])).
% 12.15/1.99  
% 12.15/1.99  fof(f65,plain,(
% 12.15/1.99    k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 12.15/1.99    inference(definition_unfolding,[],[f47,f50,f45,f45,f45,f45,f46,f52,f54,f52])).
% 12.15/1.99  
% 12.15/1.99  fof(f17,axiom,(
% 12.15/1.99    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 12.15/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.15/1.99  
% 12.15/1.99  fof(f42,plain,(
% 12.15/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 12.15/1.99    inference(cnf_transformation,[],[f17])).
% 12.15/1.99  
% 12.15/1.99  fof(f62,plain,(
% 12.15/1.99    ( ! [X2,X0,X3,X1] : (k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) )),
% 12.15/1.99    inference(definition_unfolding,[],[f42,f50,f52,f52])).
% 12.15/1.99  
% 12.15/1.99  fof(f18,axiom,(
% 12.15/1.99    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 12.15/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.15/1.99  
% 12.15/1.99  fof(f44,plain,(
% 12.15/1.99    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 12.15/1.99    inference(cnf_transformation,[],[f18])).
% 12.15/1.99  
% 12.15/1.99  fof(f63,plain,(
% 12.15/1.99    ( ! [X2,X0,X1] : (k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) )),
% 12.15/1.99    inference(definition_unfolding,[],[f44,f52,f52,f54])).
% 12.15/1.99  
% 12.15/1.99  cnf(c_1,plain,
% 12.15/1.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 12.15/1.99      inference(cnf_transformation,[],[f56]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_33,plain,
% 12.15/1.99      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X0_39) ),
% 12.15/1.99      inference(subtyping,[status(esa)],[c_1]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_0,plain,
% 12.15/1.99      ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k4_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 12.15/1.99      inference(cnf_transformation,[],[f55]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_34,plain,
% 12.15/1.99      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39),k4_xboole_0(k6_enumset1(X7_39,X7_39,X7_39,X7_39,X7_39,X7_39,X7_39,X7_39),k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) ),
% 12.15/1.99      inference(subtyping,[status(esa)],[c_0]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_448,plain,
% 12.15/1.99      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39),k4_xboole_0(k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39))) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X0_39,X2_39) ),
% 12.15/1.99      inference(superposition,[status(thm)],[c_33,c_34]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_2,plain,
% 12.15/1.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X0,X1) ),
% 12.15/1.99      inference(cnf_transformation,[],[f57]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_32,plain,
% 12.15/1.99      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39) = k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X0_39,X1_39) ),
% 12.15/1.99      inference(subtyping,[status(esa)],[c_2]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_446,plain,
% 12.15/1.99      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39),k4_xboole_0(k6_enumset1(X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39))) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X0_39,X3_39) ),
% 12.15/1.99      inference(superposition,[status(thm)],[c_32,c_34]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_11757,plain,
% 12.15/1.99      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X1_39),k4_xboole_0(k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X1_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39),k4_xboole_0(k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39))) ),
% 12.15/1.99      inference(superposition,[status(thm)],[c_448,c_446]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_11782,plain,
% 12.15/1.99      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X1_39,X2_39) = k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39) ),
% 12.15/1.99      inference(demodulation,[status(thm)],[c_11757,c_34]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_12347,plain,
% 12.15/1.99      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X1_39,X2_39) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X0_39) ),
% 12.15/1.99      inference(superposition,[status(thm)],[c_11782,c_32]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_5,plain,
% 12.15/1.99      ( k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) ),
% 12.15/1.99      inference(cnf_transformation,[],[f60]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_29,plain,
% 12.15/1.99      ( k5_xboole_0(k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39),k4_xboole_0(k6_enumset1(X8_39,X8_39,X8_39,X8_39,X8_39,X8_39,X8_39,X8_39),k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39,X8_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) ),
% 12.15/1.99      inference(subtyping,[status(esa)],[c_5]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_15987,plain,
% 12.15/1.99      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39),k4_xboole_0(k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X3_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39))) = k5_xboole_0(k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X0_39),k4_xboole_0(k6_enumset1(X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X0_39))) ),
% 12.15/1.99      inference(superposition,[status(thm)],[c_12347,c_29]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_6,plain,
% 12.15/1.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 12.15/1.99      inference(cnf_transformation,[],[f61]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_28,plain,
% 12.15/1.99      ( k3_tarski(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39)) = k5_xboole_0(X0_39,k4_xboole_0(X1_39,X0_39)) ),
% 12.15/1.99      inference(subtyping,[status(esa)],[c_6]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_186,plain,
% 12.15/1.99      ( k3_tarski(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39)) = k5_xboole_0(X1_39,k4_xboole_0(X0_39,X1_39)) ),
% 12.15/1.99      inference(superposition,[status(thm)],[c_33,c_28]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_296,plain,
% 12.15/1.99      ( k5_xboole_0(X0_39,k4_xboole_0(X1_39,X0_39)) = k5_xboole_0(X1_39,k4_xboole_0(X0_39,X1_39)) ),
% 12.15/1.99      inference(superposition,[status(thm)],[c_186,c_28]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_449,plain,
% 12.15/1.99      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39),k4_xboole_0(k6_enumset1(X1_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39))) = k6_enumset1(X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39,X0_39) ),
% 12.15/1.99      inference(superposition,[status(thm)],[c_34,c_296]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_16242,plain,
% 12.15/1.99      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39) = k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X3_39,X2_39) ),
% 12.15/1.99      inference(demodulation,[status(thm)],[c_15987,c_34,c_449]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_4965,plain,
% 12.15/1.99      ( k5_xboole_0(k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39),k4_xboole_0(k6_enumset1(X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39))),k4_xboole_0(k6_enumset1(X4_39,X4_39,X4_39,X4_39,X4_39,X4_39,X4_39,X4_39),k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39),k4_xboole_0(k6_enumset1(X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39))))) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X2_39,X0_39,X3_39,X4_39) ),
% 12.15/1.99      inference(superposition,[status(thm)],[c_446,c_34]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_5022,plain,
% 12.15/1.99      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39) = k6_enumset1(X2_39,X2_39,X2_39,X2_39,X0_39,X1_39,X3_39,X4_39) ),
% 12.15/1.99      inference(demodulation,[status(thm)],[c_4965,c_34]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_4877,plain,
% 12.15/1.99      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39) = k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X0_39,X1_39,X3_39) ),
% 12.15/1.99      inference(superposition,[status(thm)],[c_34,c_446]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_5702,plain,
% 12.15/1.99      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X0_39,X2_39,X3_39) = k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X0_39,X1_39,X3_39) ),
% 12.15/1.99      inference(superposition,[status(thm)],[c_5022,c_4877]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_25230,plain,
% 12.15/1.99      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X0_39,X2_39,X3_39),k4_xboole_0(k6_enumset1(X4_39,X4_39,X4_39,X4_39,X4_39,X4_39,X4_39,X4_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X0_39,X2_39,X3_39))) = k5_xboole_0(k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39),k4_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X3_39,X4_39),k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39))) ),
% 12.15/1.99      inference(superposition,[status(thm)],[c_5702,c_29]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_25414,plain,
% 12.15/1.99      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39) = k6_enumset1(X0_39,X0_39,X0_39,X1_39,X0_39,X4_39,X2_39,X3_39) ),
% 12.15/1.99      inference(demodulation,[status(thm)],[c_25230,c_34,c_449]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_10,negated_conjecture,
% 12.15/1.99      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 12.15/1.99      inference(cnf_transformation,[],[f65]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_24,negated_conjecture,
% 12.15/1.99      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 12.15/1.99      inference(subtyping,[status(esa)],[c_10]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_27608,plain,
% 12.15/1.99      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 12.15/1.99      inference(demodulation,[status(thm)],[c_25414,c_24]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_30510,plain,
% 12.15/1.99      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 12.15/1.99      inference(superposition,[status(thm)],[c_16242,c_27608]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_37,plain,
% 12.15/1.99      ( X0_39 != X1_39 | X2_39 != X1_39 | X2_39 = X0_39 ),
% 12.15/1.99      theory(equality) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_224,plain,
% 12.15/1.99      ( X0_39 != X1_39
% 12.15/1.99      | X0_39 = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 12.15/1.99      | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != X1_39 ),
% 12.15/1.99      inference(instantiation,[status(thm)],[c_37]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_1653,plain,
% 12.15/1.99      ( X0_39 != k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 12.15/1.99      | X0_39 = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 12.15/1.99      | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 12.15/1.99      inference(instantiation,[status(thm)],[c_224]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_8000,plain,
% 12.15/1.99      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 12.15/1.99      | k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)) = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 12.15/1.99      | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 12.15/1.99      inference(instantiation,[status(thm)],[c_1653]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_7,plain,
% 12.15/1.99      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
% 12.15/1.99      inference(cnf_transformation,[],[f62]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_27,plain,
% 12.15/1.99      ( k6_enumset1(k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X2_39),k4_tarski(X3_39,X1_39),k4_tarski(X3_39,X2_39)) = k2_zfmisc_1(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X3_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39)) ),
% 12.15/1.99      inference(subtyping,[status(esa)],[c_7]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_3994,plain,
% 12.15/1.99      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)) = k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 12.15/1.99      inference(instantiation,[status(thm)],[c_27]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_43,plain,
% 12.15/1.99      ( X0_39 != X1_39
% 12.15/1.99      | X2_39 != X3_39
% 12.15/1.99      | k2_zfmisc_1(X0_39,X2_39) = k2_zfmisc_1(X1_39,X3_39) ),
% 12.15/1.99      theory(equality) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_144,plain,
% 12.15/1.99      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != X0_39
% 12.15/1.99      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != X1_39
% 12.15/1.99      | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k2_zfmisc_1(X1_39,X0_39) ),
% 12.15/1.99      inference(instantiation,[status(thm)],[c_43]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_761,plain,
% 12.15/1.99      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != X0_39
% 12.15/1.99      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))
% 12.15/1.99      | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),X0_39) ),
% 12.15/1.99      inference(instantiation,[status(thm)],[c_144]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_1419,plain,
% 12.15/1.99      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 12.15/1.99      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))
% 12.15/1.99      | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 12.15/1.99      inference(instantiation,[status(thm)],[c_761]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_35,plain,( X0_39 = X0_39 ),theory(equality) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_356,plain,
% 12.15/1.99      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
% 12.15/1.99      inference(instantiation,[status(thm)],[c_35]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_8,plain,
% 12.15/1.99      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
% 12.15/1.99      inference(cnf_transformation,[],[f63]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_26,plain,
% 12.15/1.99      ( k6_enumset1(k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X2_39,X1_39)) = k2_zfmisc_1(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X2_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39)) ),
% 12.15/1.99      inference(subtyping,[status(esa)],[c_8]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_270,plain,
% 12.15/1.99      ( k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)) = k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 12.15/1.99      inference(instantiation,[status(thm)],[c_26]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_159,plain,
% 12.15/1.99      ( X0_39 != X1_39
% 12.15/1.99      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != X1_39
% 12.15/1.99      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = X0_39 ),
% 12.15/1.99      inference(instantiation,[status(thm)],[c_37]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_173,plain,
% 12.15/1.99      ( X0_39 != k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 12.15/1.99      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = X0_39
% 12.15/1.99      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 12.15/1.99      inference(instantiation,[status(thm)],[c_159]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_269,plain,
% 12.15/1.99      ( k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)) != k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 12.15/1.99      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))
% 12.15/1.99      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 12.15/1.99      inference(instantiation,[status(thm)],[c_173]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(c_157,plain,
% 12.15/1.99      ( k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 12.15/1.99      inference(instantiation,[status(thm)],[c_35]) ).
% 12.15/1.99  
% 12.15/1.99  cnf(contradiction,plain,
% 12.15/1.99      ( $false ),
% 12.15/1.99      inference(minisat,
% 12.15/1.99                [status(thm)],
% 12.15/1.99                [c_30510,c_8000,c_3994,c_1419,c_356,c_270,c_269,c_157]) ).
% 12.15/1.99  
% 12.15/1.99  
% 12.15/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 12.15/1.99  
% 12.15/1.99  ------                               Statistics
% 12.15/1.99  
% 12.15/1.99  ------ Selected
% 12.15/1.99  
% 12.15/1.99  total_time:                             1.476
% 12.15/1.99  
%------------------------------------------------------------------------------
