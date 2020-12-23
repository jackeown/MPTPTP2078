%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:26 EST 2020

% Result     : Theorem 14.90s
% Output     : CNFRefutation 14.90s
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
    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(negated_conjecture,[],[f21])).

fof(f23,plain,(
    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(ennf_transformation,[],[f22])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))
   => k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f23,f24])).

fof(f47,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
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
    k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f47,f50,f45,f45,f45,f45,f46,f54,f52,f52])).

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

fof(f43,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,(
    ! [X2,X0,X1] : k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(definition_unfolding,[],[f43,f52,f54,f52])).

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

cnf(c_442,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39),k4_xboole_0(k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39))) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X0_39,X2_39) ),
    inference(superposition,[status(thm)],[c_33,c_34])).

cnf(c_2,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_32,plain,
    ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39) = k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X0_39,X1_39) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_440,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39),k4_xboole_0(k6_enumset1(X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39))) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X0_39,X3_39) ),
    inference(superposition,[status(thm)],[c_32,c_34])).

cnf(c_12059,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X1_39),k4_xboole_0(k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X1_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39),k4_xboole_0(k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39))) ),
    inference(superposition,[status(thm)],[c_442,c_440])).

cnf(c_12084,plain,
    ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X1_39,X2_39) = k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39) ),
    inference(demodulation,[status(thm)],[c_12059,c_34])).

cnf(c_12663,plain,
    ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X1_39,X2_39) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X0_39) ),
    inference(superposition,[status(thm)],[c_12084,c_32])).

cnf(c_5,plain,
    ( k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_29,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39),k4_xboole_0(k6_enumset1(X8_39,X8_39,X8_39,X8_39,X8_39,X8_39,X8_39,X8_39),k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39,X8_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_16298,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39),k4_xboole_0(k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X3_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39))) = k5_xboole_0(k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X0_39),k4_xboole_0(k6_enumset1(X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X0_39))) ),
    inference(superposition,[status(thm)],[c_12663,c_29])).

cnf(c_6,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_28,plain,
    ( k3_tarski(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39)) = k5_xboole_0(X0_39,k4_xboole_0(X1_39,X0_39)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_186,plain,
    ( k3_tarski(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39)) = k5_xboole_0(X1_39,k4_xboole_0(X0_39,X1_39)) ),
    inference(superposition,[status(thm)],[c_33,c_28])).

cnf(c_290,plain,
    ( k5_xboole_0(X0_39,k4_xboole_0(X1_39,X0_39)) = k5_xboole_0(X1_39,k4_xboole_0(X0_39,X1_39)) ),
    inference(superposition,[status(thm)],[c_186,c_28])).

cnf(c_443,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39),k4_xboole_0(k6_enumset1(X1_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39))) = k6_enumset1(X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39,X0_39) ),
    inference(superposition,[status(thm)],[c_34,c_290])).

cnf(c_16553,plain,
    ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39) = k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X3_39,X2_39) ),
    inference(demodulation,[status(thm)],[c_16298,c_34,c_443])).

cnf(c_4954,plain,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39),k4_xboole_0(k6_enumset1(X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39))),k4_xboole_0(k6_enumset1(X4_39,X4_39,X4_39,X4_39,X4_39,X4_39,X4_39,X4_39),k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39),k4_xboole_0(k6_enumset1(X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39))))) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X2_39,X0_39,X3_39,X4_39) ),
    inference(superposition,[status(thm)],[c_440,c_34])).

cnf(c_5011,plain,
    ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39) = k6_enumset1(X2_39,X2_39,X2_39,X2_39,X0_39,X1_39,X3_39,X4_39) ),
    inference(demodulation,[status(thm)],[c_4954,c_34])).

cnf(c_4866,plain,
    ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39) = k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X0_39,X1_39,X3_39) ),
    inference(superposition,[status(thm)],[c_34,c_440])).

cnf(c_5654,plain,
    ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X0_39,X2_39,X3_39) = k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X0_39,X1_39,X3_39) ),
    inference(superposition,[status(thm)],[c_5011,c_4866])).

cnf(c_25516,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X0_39,X2_39,X3_39),k4_xboole_0(k6_enumset1(X4_39,X4_39,X4_39,X4_39,X4_39,X4_39,X4_39,X4_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X0_39,X2_39,X3_39))) = k5_xboole_0(k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39),k4_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X3_39,X4_39),k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39))) ),
    inference(superposition,[status(thm)],[c_5654,c_29])).

cnf(c_25700,plain,
    ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39) = k6_enumset1(X0_39,X0_39,X0_39,X1_39,X0_39,X4_39,X2_39,X3_39) ),
    inference(demodulation,[status(thm)],[c_25516,c_34,c_443])).

cnf(c_10,negated_conjecture,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_24,negated_conjecture,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_27892,plain,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_25700,c_24])).

cnf(c_30826,plain,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_16553,c_27892])).

cnf(c_37,plain,
    ( X0_39 != X1_39
    | X2_39 != X1_39
    | X2_39 = X0_39 ),
    theory(equality)).

cnf(c_224,plain,
    ( X0_39 != X1_39
    | X0_39 = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != X1_39 ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_1666,plain,
    ( X0_39 != k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | X0_39 = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(c_8993,plain,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1666])).

cnf(c_7,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_27,plain,
    ( k6_enumset1(k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X2_39),k4_tarski(X3_39,X1_39),k4_tarski(X3_39,X2_39)) = k2_zfmisc_1(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X3_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_4033,plain,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) = k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_43,plain,
    ( X0_39 != X1_39
    | X2_39 != X3_39
    | k2_zfmisc_1(X0_39,X2_39) = k2_zfmisc_1(X1_39,X3_39) ),
    theory(equality)).

cnf(c_144,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != X0_39
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != X1_39
    | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k2_zfmisc_1(X1_39,X0_39) ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_726,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != X0_39
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))
    | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),X0_39) ),
    inference(instantiation,[status(thm)],[c_144])).

cnf(c_1448,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))
    | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_35,plain,
    ( X0_39 = X0_39 ),
    theory(equality)).

cnf(c_350,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_9,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_25,plain,
    ( k6_enumset1(k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X2_39)) = k2_zfmisc_1(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_264,plain,
    ( k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) = k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_159,plain,
    ( X0_39 != X1_39
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != X1_39
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = X0_39 ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_173,plain,
    ( X0_39 != k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = X0_39
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_159])).

cnf(c_263,plain,
    ( k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) != k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_157,plain,
    ( k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30826,c_8993,c_4033,c_1448,c_350,c_264,c_263,c_157])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:38:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 14.90/2.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.90/2.50  
% 14.90/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 14.90/2.50  
% 14.90/2.50  ------  iProver source info
% 14.90/2.50  
% 14.90/2.50  git: date: 2020-06-30 10:37:57 +0100
% 14.90/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 14.90/2.50  git: non_committed_changes: false
% 14.90/2.50  git: last_make_outside_of_git: false
% 14.90/2.50  
% 14.90/2.50  ------ 
% 14.90/2.50  ------ Parsing...
% 14.90/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 14.90/2.50  
% 14.90/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 14.90/2.50  
% 14.90/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 14.90/2.50  
% 14.90/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 14.90/2.50  ------ Proving...
% 14.90/2.50  ------ Problem Properties 
% 14.90/2.50  
% 14.90/2.50  
% 14.90/2.50  clauses                                 11
% 14.90/2.50  conjectures                             1
% 14.90/2.50  EPR                                     0
% 14.90/2.50  Horn                                    11
% 14.90/2.50  unary                                   11
% 14.90/2.50  binary                                  0
% 14.90/2.50  lits                                    11
% 14.90/2.50  lits eq                                 11
% 14.90/2.50  fd_pure                                 0
% 14.90/2.50  fd_pseudo                               0
% 14.90/2.50  fd_cond                                 0
% 14.90/2.50  fd_pseudo_cond                          0
% 14.90/2.50  AC symbols                              0
% 14.90/2.50  
% 14.90/2.50  ------ Input Options Time Limit: Unbounded
% 14.90/2.50  
% 14.90/2.50  
% 14.90/2.50  ------ 
% 14.90/2.50  Current options:
% 14.90/2.50  ------ 
% 14.90/2.50  
% 14.90/2.50  
% 14.90/2.50  
% 14.90/2.50  
% 14.90/2.50  ------ Proving...
% 14.90/2.50  
% 14.90/2.50  
% 14.90/2.50  % SZS status Theorem for theBenchmark.p
% 14.90/2.50  
% 14.90/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 14.90/2.50  
% 14.90/2.50  fof(f2,axiom,(
% 14.90/2.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 14.90/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.90/2.50  
% 14.90/2.50  fof(f27,plain,(
% 14.90/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 14.90/2.50    inference(cnf_transformation,[],[f2])).
% 14.90/2.50  
% 14.90/2.50  fof(f10,axiom,(
% 14.90/2.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 14.90/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.90/2.50  
% 14.90/2.50  fof(f35,plain,(
% 14.90/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 14.90/2.50    inference(cnf_transformation,[],[f10])).
% 14.90/2.50  
% 14.90/2.50  fof(f11,axiom,(
% 14.90/2.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 14.90/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.90/2.50  
% 14.90/2.50  fof(f36,plain,(
% 14.90/2.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 14.90/2.50    inference(cnf_transformation,[],[f11])).
% 14.90/2.50  
% 14.90/2.50  fof(f12,axiom,(
% 14.90/2.50    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 14.90/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.90/2.50  
% 14.90/2.50  fof(f37,plain,(
% 14.90/2.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 14.90/2.50    inference(cnf_transformation,[],[f12])).
% 14.90/2.50  
% 14.90/2.50  fof(f13,axiom,(
% 14.90/2.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 14.90/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.90/2.50  
% 14.90/2.50  fof(f38,plain,(
% 14.90/2.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 14.90/2.50    inference(cnf_transformation,[],[f13])).
% 14.90/2.50  
% 14.90/2.50  fof(f14,axiom,(
% 14.90/2.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 14.90/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.90/2.50  
% 14.90/2.50  fof(f39,plain,(
% 14.90/2.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 14.90/2.50    inference(cnf_transformation,[],[f14])).
% 14.90/2.50  
% 14.90/2.50  fof(f15,axiom,(
% 14.90/2.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 14.90/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.90/2.50  
% 14.90/2.50  fof(f40,plain,(
% 14.90/2.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 14.90/2.50    inference(cnf_transformation,[],[f15])).
% 14.90/2.50  
% 14.90/2.50  fof(f48,plain,(
% 14.90/2.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 14.90/2.50    inference(definition_unfolding,[],[f39,f40])).
% 14.90/2.50  
% 14.90/2.50  fof(f49,plain,(
% 14.90/2.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 14.90/2.50    inference(definition_unfolding,[],[f38,f48])).
% 14.90/2.50  
% 14.90/2.50  fof(f50,plain,(
% 14.90/2.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 14.90/2.50    inference(definition_unfolding,[],[f37,f49])).
% 14.90/2.50  
% 14.90/2.50  fof(f51,plain,(
% 14.90/2.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 14.90/2.50    inference(definition_unfolding,[],[f36,f50])).
% 14.90/2.50  
% 14.90/2.50  fof(f52,plain,(
% 14.90/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 14.90/2.50    inference(definition_unfolding,[],[f35,f51])).
% 14.90/2.50  
% 14.90/2.50  fof(f56,plain,(
% 14.90/2.50    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 14.90/2.50    inference(definition_unfolding,[],[f27,f52,f52])).
% 14.90/2.50  
% 14.90/2.50  fof(f8,axiom,(
% 14.90/2.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 14.90/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.90/2.50  
% 14.90/2.50  fof(f33,plain,(
% 14.90/2.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 14.90/2.50    inference(cnf_transformation,[],[f8])).
% 14.90/2.50  
% 14.90/2.50  fof(f1,axiom,(
% 14.90/2.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 14.90/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.90/2.50  
% 14.90/2.50  fof(f26,plain,(
% 14.90/2.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 14.90/2.50    inference(cnf_transformation,[],[f1])).
% 14.90/2.50  
% 14.90/2.50  fof(f9,axiom,(
% 14.90/2.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 14.90/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.90/2.50  
% 14.90/2.50  fof(f34,plain,(
% 14.90/2.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 14.90/2.50    inference(cnf_transformation,[],[f9])).
% 14.90/2.50  
% 14.90/2.50  fof(f54,plain,(
% 14.90/2.50    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 14.90/2.50    inference(definition_unfolding,[],[f34,f52])).
% 14.90/2.50  
% 14.90/2.50  fof(f55,plain,(
% 14.90/2.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k4_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 14.90/2.50    inference(definition_unfolding,[],[f33,f26,f40,f54])).
% 14.90/2.50  
% 14.90/2.50  fof(f3,axiom,(
% 14.90/2.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 14.90/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.90/2.50  
% 14.90/2.50  fof(f28,plain,(
% 14.90/2.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 14.90/2.50    inference(cnf_transformation,[],[f3])).
% 14.90/2.50  
% 14.90/2.50  fof(f57,plain,(
% 14.90/2.50    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) )),
% 14.90/2.50    inference(definition_unfolding,[],[f28,f51,f51])).
% 14.90/2.50  
% 14.90/2.50  fof(f7,axiom,(
% 14.90/2.50    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 14.90/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.90/2.50  
% 14.90/2.50  fof(f32,plain,(
% 14.90/2.50    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 14.90/2.50    inference(cnf_transformation,[],[f7])).
% 14.90/2.50  
% 14.90/2.50  fof(f4,axiom,(
% 14.90/2.50    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 14.90/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.90/2.50  
% 14.90/2.50  fof(f29,plain,(
% 14.90/2.50    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 14.90/2.50    inference(cnf_transformation,[],[f4])).
% 14.90/2.50  
% 14.90/2.50  fof(f53,plain,(
% 14.90/2.50    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 14.90/2.50    inference(definition_unfolding,[],[f29,f26,f49,f50])).
% 14.90/2.50  
% 14.90/2.50  fof(f60,plain,(
% 14.90/2.50    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) )),
% 14.90/2.50    inference(definition_unfolding,[],[f32,f26,f54,f53])).
% 14.90/2.50  
% 14.90/2.50  fof(f16,axiom,(
% 14.90/2.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 14.90/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.90/2.50  
% 14.90/2.50  fof(f41,plain,(
% 14.90/2.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 14.90/2.50    inference(cnf_transformation,[],[f16])).
% 14.90/2.50  
% 14.90/2.50  fof(f61,plain,(
% 14.90/2.50    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 14.90/2.50    inference(definition_unfolding,[],[f41,f26,f52])).
% 14.90/2.50  
% 14.90/2.50  fof(f21,conjecture,(
% 14.90/2.50    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))),
% 14.90/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.90/2.50  
% 14.90/2.50  fof(f22,negated_conjecture,(
% 14.90/2.50    ~! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))),
% 14.90/2.50    inference(negated_conjecture,[],[f21])).
% 14.90/2.50  
% 14.90/2.50  fof(f23,plain,(
% 14.90/2.50    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))),
% 14.90/2.50    inference(ennf_transformation,[],[f22])).
% 14.90/2.50  
% 14.90/2.50  fof(f24,plain,(
% 14.90/2.50    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) => k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 14.90/2.50    introduced(choice_axiom,[])).
% 14.90/2.50  
% 14.90/2.50  fof(f25,plain,(
% 14.90/2.50    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 14.90/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f23,f24])).
% 14.90/2.50  
% 14.90/2.50  fof(f47,plain,(
% 14.90/2.50    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 14.90/2.50    inference(cnf_transformation,[],[f25])).
% 14.90/2.50  
% 14.90/2.50  fof(f19,axiom,(
% 14.90/2.50    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 14.90/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.90/2.50  
% 14.90/2.50  fof(f45,plain,(
% 14.90/2.50    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 14.90/2.50    inference(cnf_transformation,[],[f19])).
% 14.90/2.50  
% 14.90/2.50  fof(f20,axiom,(
% 14.90/2.50    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 14.90/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.90/2.50  
% 14.90/2.50  fof(f46,plain,(
% 14.90/2.50    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 14.90/2.50    inference(cnf_transformation,[],[f20])).
% 14.90/2.50  
% 14.90/2.50  fof(f65,plain,(
% 14.90/2.50    k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 14.90/2.50    inference(definition_unfolding,[],[f47,f50,f45,f45,f45,f45,f46,f54,f52,f52])).
% 14.90/2.50  
% 14.90/2.50  fof(f17,axiom,(
% 14.90/2.50    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 14.90/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.90/2.50  
% 14.90/2.50  fof(f42,plain,(
% 14.90/2.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 14.90/2.50    inference(cnf_transformation,[],[f17])).
% 14.90/2.50  
% 14.90/2.50  fof(f62,plain,(
% 14.90/2.50    ( ! [X2,X0,X3,X1] : (k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) )),
% 14.90/2.50    inference(definition_unfolding,[],[f42,f50,f52,f52])).
% 14.90/2.50  
% 14.90/2.50  fof(f18,axiom,(
% 14.90/2.50    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 14.90/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.90/2.50  
% 14.90/2.50  fof(f43,plain,(
% 14.90/2.50    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 14.90/2.50    inference(cnf_transformation,[],[f18])).
% 14.90/2.50  
% 14.90/2.50  fof(f64,plain,(
% 14.90/2.50    ( ! [X2,X0,X1] : (k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 14.90/2.50    inference(definition_unfolding,[],[f43,f52,f54,f52])).
% 14.90/2.50  
% 14.90/2.50  cnf(c_1,plain,
% 14.90/2.50      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 14.90/2.50      inference(cnf_transformation,[],[f56]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_33,plain,
% 14.90/2.50      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X0_39) ),
% 14.90/2.50      inference(subtyping,[status(esa)],[c_1]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_0,plain,
% 14.90/2.50      ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k4_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 14.90/2.50      inference(cnf_transformation,[],[f55]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_34,plain,
% 14.90/2.50      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39),k4_xboole_0(k6_enumset1(X7_39,X7_39,X7_39,X7_39,X7_39,X7_39,X7_39,X7_39),k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) ),
% 14.90/2.50      inference(subtyping,[status(esa)],[c_0]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_442,plain,
% 14.90/2.50      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39),k4_xboole_0(k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39))) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X0_39,X2_39) ),
% 14.90/2.50      inference(superposition,[status(thm)],[c_33,c_34]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_2,plain,
% 14.90/2.50      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X0,X1) ),
% 14.90/2.50      inference(cnf_transformation,[],[f57]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_32,plain,
% 14.90/2.50      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39) = k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X0_39,X1_39) ),
% 14.90/2.50      inference(subtyping,[status(esa)],[c_2]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_440,plain,
% 14.90/2.50      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39),k4_xboole_0(k6_enumset1(X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39))) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X0_39,X3_39) ),
% 14.90/2.50      inference(superposition,[status(thm)],[c_32,c_34]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_12059,plain,
% 14.90/2.50      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X1_39),k4_xboole_0(k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X1_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39),k4_xboole_0(k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39))) ),
% 14.90/2.50      inference(superposition,[status(thm)],[c_442,c_440]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_12084,plain,
% 14.90/2.50      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X1_39,X2_39) = k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39) ),
% 14.90/2.50      inference(demodulation,[status(thm)],[c_12059,c_34]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_12663,plain,
% 14.90/2.50      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X1_39,X2_39) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X0_39) ),
% 14.90/2.50      inference(superposition,[status(thm)],[c_12084,c_32]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_5,plain,
% 14.90/2.50      ( k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k4_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) ),
% 14.90/2.50      inference(cnf_transformation,[],[f60]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_29,plain,
% 14.90/2.50      ( k5_xboole_0(k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39),k4_xboole_0(k6_enumset1(X8_39,X8_39,X8_39,X8_39,X8_39,X8_39,X8_39,X8_39),k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39,X8_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) ),
% 14.90/2.50      inference(subtyping,[status(esa)],[c_5]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_16298,plain,
% 14.90/2.50      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39),k4_xboole_0(k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X3_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39))) = k5_xboole_0(k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X0_39),k4_xboole_0(k6_enumset1(X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X0_39))) ),
% 14.90/2.50      inference(superposition,[status(thm)],[c_12663,c_29]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_6,plain,
% 14.90/2.50      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 14.90/2.50      inference(cnf_transformation,[],[f61]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_28,plain,
% 14.90/2.50      ( k3_tarski(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39)) = k5_xboole_0(X0_39,k4_xboole_0(X1_39,X0_39)) ),
% 14.90/2.50      inference(subtyping,[status(esa)],[c_6]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_186,plain,
% 14.90/2.50      ( k3_tarski(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39)) = k5_xboole_0(X1_39,k4_xboole_0(X0_39,X1_39)) ),
% 14.90/2.50      inference(superposition,[status(thm)],[c_33,c_28]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_290,plain,
% 14.90/2.50      ( k5_xboole_0(X0_39,k4_xboole_0(X1_39,X0_39)) = k5_xboole_0(X1_39,k4_xboole_0(X0_39,X1_39)) ),
% 14.90/2.50      inference(superposition,[status(thm)],[c_186,c_28]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_443,plain,
% 14.90/2.50      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39),k4_xboole_0(k6_enumset1(X1_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39))) = k6_enumset1(X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39,X0_39) ),
% 14.90/2.50      inference(superposition,[status(thm)],[c_34,c_290]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_16553,plain,
% 14.90/2.50      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39) = k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X3_39,X2_39) ),
% 14.90/2.50      inference(demodulation,[status(thm)],[c_16298,c_34,c_443]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_4954,plain,
% 14.90/2.50      ( k5_xboole_0(k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39),k4_xboole_0(k6_enumset1(X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39))),k4_xboole_0(k6_enumset1(X4_39,X4_39,X4_39,X4_39,X4_39,X4_39,X4_39,X4_39),k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39),k4_xboole_0(k6_enumset1(X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39))))) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X2_39,X0_39,X3_39,X4_39) ),
% 14.90/2.50      inference(superposition,[status(thm)],[c_440,c_34]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_5011,plain,
% 14.90/2.50      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39) = k6_enumset1(X2_39,X2_39,X2_39,X2_39,X0_39,X1_39,X3_39,X4_39) ),
% 14.90/2.50      inference(demodulation,[status(thm)],[c_4954,c_34]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_4866,plain,
% 14.90/2.50      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39) = k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X0_39,X1_39,X3_39) ),
% 14.90/2.50      inference(superposition,[status(thm)],[c_34,c_440]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_5654,plain,
% 14.90/2.50      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X0_39,X2_39,X3_39) = k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X0_39,X1_39,X3_39) ),
% 14.90/2.50      inference(superposition,[status(thm)],[c_5011,c_4866]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_25516,plain,
% 14.90/2.50      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X0_39,X2_39,X3_39),k4_xboole_0(k6_enumset1(X4_39,X4_39,X4_39,X4_39,X4_39,X4_39,X4_39,X4_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X0_39,X2_39,X3_39))) = k5_xboole_0(k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39),k4_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X3_39,X4_39),k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39))) ),
% 14.90/2.50      inference(superposition,[status(thm)],[c_5654,c_29]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_25700,plain,
% 14.90/2.50      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39) = k6_enumset1(X0_39,X0_39,X0_39,X1_39,X0_39,X4_39,X2_39,X3_39) ),
% 14.90/2.50      inference(demodulation,[status(thm)],[c_25516,c_34,c_443]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_10,negated_conjecture,
% 14.90/2.50      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 14.90/2.50      inference(cnf_transformation,[],[f65]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_24,negated_conjecture,
% 14.90/2.50      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 14.90/2.50      inference(subtyping,[status(esa)],[c_10]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_27892,plain,
% 14.90/2.50      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 14.90/2.50      inference(demodulation,[status(thm)],[c_25700,c_24]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_30826,plain,
% 14.90/2.50      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 14.90/2.50      inference(superposition,[status(thm)],[c_16553,c_27892]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_37,plain,
% 14.90/2.50      ( X0_39 != X1_39 | X2_39 != X1_39 | X2_39 = X0_39 ),
% 14.90/2.50      theory(equality) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_224,plain,
% 14.90/2.50      ( X0_39 != X1_39
% 14.90/2.50      | X0_39 = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 14.90/2.50      | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != X1_39 ),
% 14.90/2.50      inference(instantiation,[status(thm)],[c_37]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_1666,plain,
% 14.90/2.50      ( X0_39 != k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 14.90/2.50      | X0_39 = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 14.90/2.50      | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 14.90/2.50      inference(instantiation,[status(thm)],[c_224]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_8993,plain,
% 14.90/2.50      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 14.90/2.50      | k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 14.90/2.50      | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 14.90/2.50      inference(instantiation,[status(thm)],[c_1666]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_7,plain,
% 14.90/2.50      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
% 14.90/2.50      inference(cnf_transformation,[],[f62]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_27,plain,
% 14.90/2.50      ( k6_enumset1(k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X2_39),k4_tarski(X3_39,X1_39),k4_tarski(X3_39,X2_39)) = k2_zfmisc_1(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X3_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39)) ),
% 14.90/2.50      inference(subtyping,[status(esa)],[c_7]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_4033,plain,
% 14.90/2.50      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) = k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 14.90/2.50      inference(instantiation,[status(thm)],[c_27]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_43,plain,
% 14.90/2.50      ( X0_39 != X1_39
% 14.90/2.50      | X2_39 != X3_39
% 14.90/2.50      | k2_zfmisc_1(X0_39,X2_39) = k2_zfmisc_1(X1_39,X3_39) ),
% 14.90/2.50      theory(equality) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_144,plain,
% 14.90/2.50      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != X0_39
% 14.90/2.50      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != X1_39
% 14.90/2.50      | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k2_zfmisc_1(X1_39,X0_39) ),
% 14.90/2.50      inference(instantiation,[status(thm)],[c_43]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_726,plain,
% 14.90/2.50      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != X0_39
% 14.90/2.50      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))
% 14.90/2.50      | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),X0_39) ),
% 14.90/2.50      inference(instantiation,[status(thm)],[c_144]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_1448,plain,
% 14.90/2.50      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 14.90/2.50      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))
% 14.90/2.50      | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 14.90/2.50      inference(instantiation,[status(thm)],[c_726]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_35,plain,( X0_39 = X0_39 ),theory(equality) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_350,plain,
% 14.90/2.50      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
% 14.90/2.50      inference(instantiation,[status(thm)],[c_35]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_9,plain,
% 14.90/2.50      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
% 14.90/2.50      inference(cnf_transformation,[],[f64]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_25,plain,
% 14.90/2.50      ( k6_enumset1(k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X2_39)) = k2_zfmisc_1(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39)) ),
% 14.90/2.50      inference(subtyping,[status(esa)],[c_9]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_264,plain,
% 14.90/2.50      ( k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) = k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 14.90/2.50      inference(instantiation,[status(thm)],[c_25]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_159,plain,
% 14.90/2.50      ( X0_39 != X1_39
% 14.90/2.50      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != X1_39
% 14.90/2.50      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = X0_39 ),
% 14.90/2.50      inference(instantiation,[status(thm)],[c_37]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_173,plain,
% 14.90/2.50      ( X0_39 != k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
% 14.90/2.50      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = X0_39
% 14.90/2.50      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 14.90/2.50      inference(instantiation,[status(thm)],[c_159]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_263,plain,
% 14.90/2.50      ( k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) != k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
% 14.90/2.50      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))
% 14.90/2.50      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 14.90/2.50      inference(instantiation,[status(thm)],[c_173]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(c_157,plain,
% 14.90/2.50      ( k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 14.90/2.50      inference(instantiation,[status(thm)],[c_35]) ).
% 14.90/2.50  
% 14.90/2.50  cnf(contradiction,plain,
% 14.90/2.50      ( $false ),
% 14.90/2.50      inference(minisat,
% 14.90/2.50                [status(thm)],
% 14.90/2.50                [c_30826,c_8993,c_4033,c_1448,c_350,c_264,c_263,c_157]) ).
% 14.90/2.50  
% 14.90/2.50  
% 14.90/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 14.90/2.50  
% 14.90/2.50  ------                               Statistics
% 14.90/2.50  
% 14.90/2.50  ------ Selected
% 14.90/2.50  
% 14.90/2.50  total_time:                             1.589
% 14.90/2.50  
%------------------------------------------------------------------------------
