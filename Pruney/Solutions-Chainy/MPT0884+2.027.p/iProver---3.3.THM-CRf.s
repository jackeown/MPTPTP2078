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
% DateTime   : Thu Dec  3 11:58:23 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   84 (1277 expanded)
%              Number of clauses        :   30 (  89 expanded)
%              Number of leaves         :   19 ( 438 expanded)
%              Depth                    :   19
%              Number of atoms          :   86 (1279 expanded)
%              Number of equality atoms :   85 (1278 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
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

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f31,f46])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f48])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
    inference(definition_unfolding,[],[f38,f46,f49,f49])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(definition_unfolding,[],[f25,f24,f45,f46])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k4_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) ),
    inference(definition_unfolding,[],[f27,f24,f35,f49,f47])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f28,f24,f44,f49])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2) ),
    inference(definition_unfolding,[],[f36,f48,f48])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) ),
    inference(definition_unfolding,[],[f26,f24,f44,f48,f47])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) ),
    inference(negated_conjecture,[],[f19])).

fof(f21,plain,(
    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) ),
    inference(ennf_transformation,[],[f20])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))
   => k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f22])).

fof(f43,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
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

fof(f50,plain,(
    ! [X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f29,f49])).

fof(f59,plain,(
    k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f43,f46,f41,f41,f41,f41,f42,f49,f50,f49])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X2,X0,X1] : k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(definition_unfolding,[],[f40,f49,f49,f50])).

cnf(c_5,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_25,plain,
    ( k6_enumset1(k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X2_39),k4_tarski(X3_39,X1_39),k4_tarski(X3_39,X2_39)) = k2_zfmisc_1(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X3_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k4_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_28,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39),k4_xboole_0(k6_enumset1(X7_39,X7_39,X7_39,X7_39,X7_39,X7_39,X7_39,X8_39),k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39,X8_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_0,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_30,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39),k4_xboole_0(k6_enumset1(X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_184,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39),k4_xboole_0(k6_enumset1(X4_39,X4_39,X4_39,X4_39,X4_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) ),
    inference(superposition,[status(thm)],[c_28,c_30])).

cnf(c_3,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_27,plain,
    ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X0_39,X2_39) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_53,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39),k4_xboole_0(k6_enumset1(X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X4_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39))) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X0_39,X2_39,X3_39,X4_39) ),
    inference(superposition,[status(thm)],[c_27,c_30])).

cnf(c_349,plain,
    ( k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X3_39,X3_39,X4_39) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X0_39,X2_39,X3_39,X4_39) ),
    inference(superposition,[status(thm)],[c_184,c_53])).

cnf(c_385,plain,
    ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X1_39,X1_39,X2_39) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X0_39,X2_39) ),
    inference(superposition,[status(thm)],[c_349,c_27])).

cnf(c_458,plain,
    ( k6_enumset1(X0_39,X0_39,X1_39,X0_39,X0_39,X0_39,X0_39,X2_39) = k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39) ),
    inference(superposition,[status(thm)],[c_385,c_349])).

cnf(c_870,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X6_39,X5_39,X5_39,X5_39,X5_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X5_39),k4_xboole_0(k6_enumset1(X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X5_39))) ),
    inference(superposition,[status(thm)],[c_458,c_28])).

cnf(c_1,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_29,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39),k4_xboole_0(k6_enumset1(X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X7_39,X8_39),k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39,X8_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_262,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X5_39),k4_xboole_0(k6_enumset1(X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X5_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39),k4_xboole_0(k6_enumset1(X4_39,X4_39,X4_39,X4_39,X4_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39))) ),
    inference(superposition,[status(thm)],[c_29,c_28])).

cnf(c_274,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X5_39),k4_xboole_0(k6_enumset1(X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X5_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) ),
    inference(light_normalisation,[status(thm)],[c_262,c_184])).

cnf(c_411,plain,
    ( k6_enumset1(X0_39,X0_39,X1_39,X0_39,X0_39,X0_39,X0_39,X2_39) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X0_39,X2_39) ),
    inference(superposition,[status(thm)],[c_349,c_349])).

cnf(c_807,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X6_39,X5_39,X5_39,X5_39,X5_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X6_39,X6_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X7_39),k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X6_39,X6_39))) ),
    inference(superposition,[status(thm)],[c_411,c_28])).

cnf(c_824,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X6_39,X5_39,X5_39,X5_39,X5_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X6_39,X5_39,X7_39) ),
    inference(demodulation,[status(thm)],[c_807,c_274])).

cnf(c_888,plain,
    ( k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X6_39,X5_39,X7_39) ),
    inference(light_normalisation,[status(thm)],[c_870,c_274,c_824])).

cnf(c_8,negated_conjecture,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,negated_conjecture,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2684,plain,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_888,c_22])).

cnf(c_2875,plain,
    ( k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_25,c_2684])).

cnf(c_6,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_24,plain,
    ( k6_enumset1(k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X2_39,X1_39)) = k2_zfmisc_1(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X2_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2876,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_2875,c_24])).

cnf(c_2877,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2876])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:23:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.52/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.00  
% 3.52/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.52/1.00  
% 3.52/1.00  ------  iProver source info
% 3.52/1.00  
% 3.52/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.52/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.52/1.00  git: non_committed_changes: false
% 3.52/1.00  git: last_make_outside_of_git: false
% 3.52/1.00  
% 3.52/1.00  ------ 
% 3.52/1.00  
% 3.52/1.00  ------ Input Options
% 3.52/1.00  
% 3.52/1.00  --out_options                           all
% 3.52/1.00  --tptp_safe_out                         true
% 3.52/1.00  --problem_path                          ""
% 3.52/1.00  --include_path                          ""
% 3.52/1.00  --clausifier                            res/vclausify_rel
% 3.52/1.00  --clausifier_options                    --mode clausify
% 3.52/1.00  --stdin                                 false
% 3.52/1.00  --stats_out                             all
% 3.52/1.00  
% 3.52/1.00  ------ General Options
% 3.52/1.00  
% 3.52/1.00  --fof                                   false
% 3.52/1.00  --time_out_real                         305.
% 3.52/1.00  --time_out_virtual                      -1.
% 3.52/1.00  --symbol_type_check                     false
% 3.52/1.00  --clausify_out                          false
% 3.52/1.00  --sig_cnt_out                           false
% 3.52/1.00  --trig_cnt_out                          false
% 3.52/1.00  --trig_cnt_out_tolerance                1.
% 3.52/1.00  --trig_cnt_out_sk_spl                   false
% 3.52/1.00  --abstr_cl_out                          false
% 3.52/1.00  
% 3.52/1.00  ------ Global Options
% 3.52/1.00  
% 3.52/1.00  --schedule                              default
% 3.52/1.00  --add_important_lit                     false
% 3.52/1.00  --prop_solver_per_cl                    1000
% 3.52/1.00  --min_unsat_core                        false
% 3.52/1.00  --soft_assumptions                      false
% 3.52/1.00  --soft_lemma_size                       3
% 3.52/1.00  --prop_impl_unit_size                   0
% 3.52/1.00  --prop_impl_unit                        []
% 3.52/1.00  --share_sel_clauses                     true
% 3.52/1.00  --reset_solvers                         false
% 3.52/1.00  --bc_imp_inh                            [conj_cone]
% 3.52/1.00  --conj_cone_tolerance                   3.
% 3.52/1.00  --extra_neg_conj                        none
% 3.52/1.00  --large_theory_mode                     true
% 3.52/1.00  --prolific_symb_bound                   200
% 3.52/1.00  --lt_threshold                          2000
% 3.52/1.00  --clause_weak_htbl                      true
% 3.52/1.00  --gc_record_bc_elim                     false
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing Options
% 3.52/1.00  
% 3.52/1.00  --preprocessing_flag                    true
% 3.52/1.00  --time_out_prep_mult                    0.1
% 3.52/1.00  --splitting_mode                        input
% 3.52/1.00  --splitting_grd                         true
% 3.52/1.00  --splitting_cvd                         false
% 3.52/1.00  --splitting_cvd_svl                     false
% 3.52/1.00  --splitting_nvd                         32
% 3.52/1.00  --sub_typing                            true
% 3.52/1.00  --prep_gs_sim                           true
% 3.52/1.00  --prep_unflatten                        true
% 3.52/1.00  --prep_res_sim                          true
% 3.52/1.00  --prep_upred                            true
% 3.52/1.00  --prep_sem_filter                       exhaustive
% 3.52/1.00  --prep_sem_filter_out                   false
% 3.52/1.00  --pred_elim                             true
% 3.52/1.00  --res_sim_input                         true
% 3.52/1.00  --eq_ax_congr_red                       true
% 3.52/1.00  --pure_diseq_elim                       true
% 3.52/1.00  --brand_transform                       false
% 3.52/1.00  --non_eq_to_eq                          false
% 3.52/1.00  --prep_def_merge                        true
% 3.52/1.00  --prep_def_merge_prop_impl              false
% 3.52/1.00  --prep_def_merge_mbd                    true
% 3.52/1.00  --prep_def_merge_tr_red                 false
% 3.52/1.00  --prep_def_merge_tr_cl                  false
% 3.52/1.00  --smt_preprocessing                     true
% 3.52/1.00  --smt_ac_axioms                         fast
% 3.52/1.00  --preprocessed_out                      false
% 3.52/1.00  --preprocessed_stats                    false
% 3.52/1.00  
% 3.52/1.00  ------ Abstraction refinement Options
% 3.52/1.00  
% 3.52/1.00  --abstr_ref                             []
% 3.52/1.00  --abstr_ref_prep                        false
% 3.52/1.00  --abstr_ref_until_sat                   false
% 3.52/1.00  --abstr_ref_sig_restrict                funpre
% 3.52/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.52/1.00  --abstr_ref_under                       []
% 3.52/1.00  
% 3.52/1.00  ------ SAT Options
% 3.52/1.00  
% 3.52/1.00  --sat_mode                              false
% 3.52/1.00  --sat_fm_restart_options                ""
% 3.52/1.00  --sat_gr_def                            false
% 3.52/1.00  --sat_epr_types                         true
% 3.52/1.00  --sat_non_cyclic_types                  false
% 3.52/1.00  --sat_finite_models                     false
% 3.52/1.00  --sat_fm_lemmas                         false
% 3.52/1.00  --sat_fm_prep                           false
% 3.52/1.00  --sat_fm_uc_incr                        true
% 3.52/1.00  --sat_out_model                         small
% 3.52/1.00  --sat_out_clauses                       false
% 3.52/1.00  
% 3.52/1.00  ------ QBF Options
% 3.52/1.00  
% 3.52/1.00  --qbf_mode                              false
% 3.52/1.00  --qbf_elim_univ                         false
% 3.52/1.00  --qbf_dom_inst                          none
% 3.52/1.00  --qbf_dom_pre_inst                      false
% 3.52/1.00  --qbf_sk_in                             false
% 3.52/1.00  --qbf_pred_elim                         true
% 3.52/1.00  --qbf_split                             512
% 3.52/1.00  
% 3.52/1.00  ------ BMC1 Options
% 3.52/1.00  
% 3.52/1.00  --bmc1_incremental                      false
% 3.52/1.00  --bmc1_axioms                           reachable_all
% 3.52/1.00  --bmc1_min_bound                        0
% 3.52/1.00  --bmc1_max_bound                        -1
% 3.52/1.00  --bmc1_max_bound_default                -1
% 3.52/1.00  --bmc1_symbol_reachability              true
% 3.52/1.00  --bmc1_property_lemmas                  false
% 3.52/1.00  --bmc1_k_induction                      false
% 3.52/1.00  --bmc1_non_equiv_states                 false
% 3.52/1.00  --bmc1_deadlock                         false
% 3.52/1.00  --bmc1_ucm                              false
% 3.52/1.00  --bmc1_add_unsat_core                   none
% 3.52/1.00  --bmc1_unsat_core_children              false
% 3.52/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.52/1.00  --bmc1_out_stat                         full
% 3.52/1.00  --bmc1_ground_init                      false
% 3.52/1.00  --bmc1_pre_inst_next_state              false
% 3.52/1.00  --bmc1_pre_inst_state                   false
% 3.52/1.00  --bmc1_pre_inst_reach_state             false
% 3.52/1.00  --bmc1_out_unsat_core                   false
% 3.52/1.00  --bmc1_aig_witness_out                  false
% 3.52/1.00  --bmc1_verbose                          false
% 3.52/1.00  --bmc1_dump_clauses_tptp                false
% 3.52/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.52/1.00  --bmc1_dump_file                        -
% 3.52/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.52/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.52/1.00  --bmc1_ucm_extend_mode                  1
% 3.52/1.00  --bmc1_ucm_init_mode                    2
% 3.52/1.00  --bmc1_ucm_cone_mode                    none
% 3.52/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.52/1.00  --bmc1_ucm_relax_model                  4
% 3.52/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.52/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.52/1.00  --bmc1_ucm_layered_model                none
% 3.52/1.00  --bmc1_ucm_max_lemma_size               10
% 3.52/1.00  
% 3.52/1.00  ------ AIG Options
% 3.52/1.00  
% 3.52/1.00  --aig_mode                              false
% 3.52/1.00  
% 3.52/1.00  ------ Instantiation Options
% 3.52/1.00  
% 3.52/1.00  --instantiation_flag                    true
% 3.52/1.00  --inst_sos_flag                         false
% 3.52/1.00  --inst_sos_phase                        true
% 3.52/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.52/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.52/1.00  --inst_lit_sel_side                     num_symb
% 3.52/1.00  --inst_solver_per_active                1400
% 3.52/1.00  --inst_solver_calls_frac                1.
% 3.52/1.00  --inst_passive_queue_type               priority_queues
% 3.52/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.52/1.00  --inst_passive_queues_freq              [25;2]
% 3.52/1.00  --inst_dismatching                      true
% 3.52/1.00  --inst_eager_unprocessed_to_passive     true
% 3.52/1.00  --inst_prop_sim_given                   true
% 3.52/1.00  --inst_prop_sim_new                     false
% 3.52/1.00  --inst_subs_new                         false
% 3.52/1.00  --inst_eq_res_simp                      false
% 3.52/1.00  --inst_subs_given                       false
% 3.52/1.00  --inst_orphan_elimination               true
% 3.52/1.00  --inst_learning_loop_flag               true
% 3.52/1.00  --inst_learning_start                   3000
% 3.52/1.00  --inst_learning_factor                  2
% 3.52/1.00  --inst_start_prop_sim_after_learn       3
% 3.52/1.00  --inst_sel_renew                        solver
% 3.52/1.00  --inst_lit_activity_flag                true
% 3.52/1.00  --inst_restr_to_given                   false
% 3.52/1.00  --inst_activity_threshold               500
% 3.52/1.00  --inst_out_proof                        true
% 3.52/1.00  
% 3.52/1.00  ------ Resolution Options
% 3.52/1.00  
% 3.52/1.00  --resolution_flag                       true
% 3.52/1.00  --res_lit_sel                           adaptive
% 3.52/1.00  --res_lit_sel_side                      none
% 3.52/1.00  --res_ordering                          kbo
% 3.52/1.00  --res_to_prop_solver                    active
% 3.52/1.00  --res_prop_simpl_new                    false
% 3.52/1.00  --res_prop_simpl_given                  true
% 3.52/1.00  --res_passive_queue_type                priority_queues
% 3.52/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.52/1.00  --res_passive_queues_freq               [15;5]
% 3.52/1.00  --res_forward_subs                      full
% 3.52/1.00  --res_backward_subs                     full
% 3.52/1.00  --res_forward_subs_resolution           true
% 3.52/1.00  --res_backward_subs_resolution          true
% 3.52/1.00  --res_orphan_elimination                true
% 3.52/1.00  --res_time_limit                        2.
% 3.52/1.00  --res_out_proof                         true
% 3.52/1.00  
% 3.52/1.00  ------ Superposition Options
% 3.52/1.00  
% 3.52/1.00  --superposition_flag                    true
% 3.52/1.00  --sup_passive_queue_type                priority_queues
% 3.52/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.52/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.52/1.00  --demod_completeness_check              fast
% 3.52/1.00  --demod_use_ground                      true
% 3.52/1.00  --sup_to_prop_solver                    passive
% 3.52/1.00  --sup_prop_simpl_new                    true
% 3.52/1.00  --sup_prop_simpl_given                  true
% 3.52/1.00  --sup_fun_splitting                     false
% 3.52/1.00  --sup_smt_interval                      50000
% 3.52/1.00  
% 3.52/1.00  ------ Superposition Simplification Setup
% 3.52/1.00  
% 3.52/1.00  --sup_indices_passive                   []
% 3.52/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.52/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.00  --sup_full_bw                           [BwDemod]
% 3.52/1.00  --sup_immed_triv                        [TrivRules]
% 3.52/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.00  --sup_immed_bw_main                     []
% 3.52/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.52/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/1.00  
% 3.52/1.00  ------ Combination Options
% 3.52/1.00  
% 3.52/1.00  --comb_res_mult                         3
% 3.52/1.00  --comb_sup_mult                         2
% 3.52/1.00  --comb_inst_mult                        10
% 3.52/1.00  
% 3.52/1.00  ------ Debug Options
% 3.52/1.00  
% 3.52/1.00  --dbg_backtrace                         false
% 3.52/1.00  --dbg_dump_prop_clauses                 false
% 3.52/1.00  --dbg_dump_prop_clauses_file            -
% 3.52/1.00  --dbg_out_stat                          false
% 3.52/1.00  ------ Parsing...
% 3.52/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.52/1.00  ------ Proving...
% 3.52/1.00  ------ Problem Properties 
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  clauses                                 9
% 3.52/1.00  conjectures                             1
% 3.52/1.00  EPR                                     0
% 3.52/1.00  Horn                                    9
% 3.52/1.00  unary                                   9
% 3.52/1.00  binary                                  0
% 3.52/1.00  lits                                    9
% 3.52/1.00  lits eq                                 9
% 3.52/1.00  fd_pure                                 0
% 3.52/1.00  fd_pseudo                               0
% 3.52/1.00  fd_cond                                 0
% 3.52/1.00  fd_pseudo_cond                          0
% 3.52/1.00  AC symbols                              0
% 3.52/1.00  
% 3.52/1.00  ------ Schedule UEQ
% 3.52/1.00  
% 3.52/1.00  ------ pure equality problem: resolution off 
% 3.52/1.00  
% 3.52/1.00  ------ Option_UEQ Time Limit: Unbounded
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  ------ 
% 3.52/1.00  Current options:
% 3.52/1.00  ------ 
% 3.52/1.00  
% 3.52/1.00  ------ Input Options
% 3.52/1.00  
% 3.52/1.00  --out_options                           all
% 3.52/1.00  --tptp_safe_out                         true
% 3.52/1.00  --problem_path                          ""
% 3.52/1.00  --include_path                          ""
% 3.52/1.00  --clausifier                            res/vclausify_rel
% 3.52/1.00  --clausifier_options                    --mode clausify
% 3.52/1.00  --stdin                                 false
% 3.52/1.00  --stats_out                             all
% 3.52/1.00  
% 3.52/1.00  ------ General Options
% 3.52/1.00  
% 3.52/1.00  --fof                                   false
% 3.52/1.00  --time_out_real                         305.
% 3.52/1.00  --time_out_virtual                      -1.
% 3.52/1.00  --symbol_type_check                     false
% 3.52/1.00  --clausify_out                          false
% 3.52/1.00  --sig_cnt_out                           false
% 3.52/1.00  --trig_cnt_out                          false
% 3.52/1.00  --trig_cnt_out_tolerance                1.
% 3.52/1.00  --trig_cnt_out_sk_spl                   false
% 3.52/1.00  --abstr_cl_out                          false
% 3.52/1.00  
% 3.52/1.00  ------ Global Options
% 3.52/1.00  
% 3.52/1.00  --schedule                              default
% 3.52/1.00  --add_important_lit                     false
% 3.52/1.00  --prop_solver_per_cl                    1000
% 3.52/1.00  --min_unsat_core                        false
% 3.52/1.00  --soft_assumptions                      false
% 3.52/1.00  --soft_lemma_size                       3
% 3.52/1.00  --prop_impl_unit_size                   0
% 3.52/1.00  --prop_impl_unit                        []
% 3.52/1.00  --share_sel_clauses                     true
% 3.52/1.00  --reset_solvers                         false
% 3.52/1.00  --bc_imp_inh                            [conj_cone]
% 3.52/1.00  --conj_cone_tolerance                   3.
% 3.52/1.00  --extra_neg_conj                        none
% 3.52/1.00  --large_theory_mode                     true
% 3.52/1.00  --prolific_symb_bound                   200
% 3.52/1.00  --lt_threshold                          2000
% 3.52/1.00  --clause_weak_htbl                      true
% 3.52/1.00  --gc_record_bc_elim                     false
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing Options
% 3.52/1.00  
% 3.52/1.00  --preprocessing_flag                    true
% 3.52/1.00  --time_out_prep_mult                    0.1
% 3.52/1.00  --splitting_mode                        input
% 3.52/1.00  --splitting_grd                         true
% 3.52/1.00  --splitting_cvd                         false
% 3.52/1.00  --splitting_cvd_svl                     false
% 3.52/1.00  --splitting_nvd                         32
% 3.52/1.00  --sub_typing                            true
% 3.52/1.00  --prep_gs_sim                           true
% 3.52/1.00  --prep_unflatten                        true
% 3.52/1.00  --prep_res_sim                          true
% 3.52/1.00  --prep_upred                            true
% 3.52/1.00  --prep_sem_filter                       exhaustive
% 3.52/1.00  --prep_sem_filter_out                   false
% 3.52/1.00  --pred_elim                             true
% 3.52/1.00  --res_sim_input                         true
% 3.52/1.00  --eq_ax_congr_red                       true
% 3.52/1.00  --pure_diseq_elim                       true
% 3.52/1.00  --brand_transform                       false
% 3.52/1.00  --non_eq_to_eq                          false
% 3.52/1.00  --prep_def_merge                        true
% 3.52/1.00  --prep_def_merge_prop_impl              false
% 3.52/1.00  --prep_def_merge_mbd                    true
% 3.52/1.00  --prep_def_merge_tr_red                 false
% 3.52/1.00  --prep_def_merge_tr_cl                  false
% 3.52/1.00  --smt_preprocessing                     true
% 3.52/1.00  --smt_ac_axioms                         fast
% 3.52/1.00  --preprocessed_out                      false
% 3.52/1.00  --preprocessed_stats                    false
% 3.52/1.00  
% 3.52/1.00  ------ Abstraction refinement Options
% 3.52/1.00  
% 3.52/1.00  --abstr_ref                             []
% 3.52/1.00  --abstr_ref_prep                        false
% 3.52/1.00  --abstr_ref_until_sat                   false
% 3.52/1.00  --abstr_ref_sig_restrict                funpre
% 3.52/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.52/1.00  --abstr_ref_under                       []
% 3.52/1.00  
% 3.52/1.00  ------ SAT Options
% 3.52/1.00  
% 3.52/1.00  --sat_mode                              false
% 3.52/1.00  --sat_fm_restart_options                ""
% 3.52/1.00  --sat_gr_def                            false
% 3.52/1.00  --sat_epr_types                         true
% 3.52/1.00  --sat_non_cyclic_types                  false
% 3.52/1.00  --sat_finite_models                     false
% 3.52/1.00  --sat_fm_lemmas                         false
% 3.52/1.00  --sat_fm_prep                           false
% 3.52/1.00  --sat_fm_uc_incr                        true
% 3.52/1.00  --sat_out_model                         small
% 3.52/1.00  --sat_out_clauses                       false
% 3.52/1.00  
% 3.52/1.00  ------ QBF Options
% 3.52/1.00  
% 3.52/1.00  --qbf_mode                              false
% 3.52/1.00  --qbf_elim_univ                         false
% 3.52/1.00  --qbf_dom_inst                          none
% 3.52/1.00  --qbf_dom_pre_inst                      false
% 3.52/1.00  --qbf_sk_in                             false
% 3.52/1.00  --qbf_pred_elim                         true
% 3.52/1.00  --qbf_split                             512
% 3.52/1.00  
% 3.52/1.00  ------ BMC1 Options
% 3.52/1.00  
% 3.52/1.00  --bmc1_incremental                      false
% 3.52/1.00  --bmc1_axioms                           reachable_all
% 3.52/1.00  --bmc1_min_bound                        0
% 3.52/1.00  --bmc1_max_bound                        -1
% 3.52/1.00  --bmc1_max_bound_default                -1
% 3.52/1.00  --bmc1_symbol_reachability              true
% 3.52/1.00  --bmc1_property_lemmas                  false
% 3.52/1.00  --bmc1_k_induction                      false
% 3.52/1.00  --bmc1_non_equiv_states                 false
% 3.52/1.00  --bmc1_deadlock                         false
% 3.52/1.00  --bmc1_ucm                              false
% 3.52/1.00  --bmc1_add_unsat_core                   none
% 3.52/1.00  --bmc1_unsat_core_children              false
% 3.52/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.52/1.00  --bmc1_out_stat                         full
% 3.52/1.00  --bmc1_ground_init                      false
% 3.52/1.00  --bmc1_pre_inst_next_state              false
% 3.52/1.00  --bmc1_pre_inst_state                   false
% 3.52/1.00  --bmc1_pre_inst_reach_state             false
% 3.52/1.00  --bmc1_out_unsat_core                   false
% 3.52/1.00  --bmc1_aig_witness_out                  false
% 3.52/1.00  --bmc1_verbose                          false
% 3.52/1.00  --bmc1_dump_clauses_tptp                false
% 3.52/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.52/1.00  --bmc1_dump_file                        -
% 3.52/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.52/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.52/1.00  --bmc1_ucm_extend_mode                  1
% 3.52/1.00  --bmc1_ucm_init_mode                    2
% 3.52/1.00  --bmc1_ucm_cone_mode                    none
% 3.52/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.52/1.00  --bmc1_ucm_relax_model                  4
% 3.52/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.52/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.52/1.00  --bmc1_ucm_layered_model                none
% 3.52/1.00  --bmc1_ucm_max_lemma_size               10
% 3.52/1.00  
% 3.52/1.00  ------ AIG Options
% 3.52/1.00  
% 3.52/1.00  --aig_mode                              false
% 3.52/1.00  
% 3.52/1.00  ------ Instantiation Options
% 3.52/1.00  
% 3.52/1.00  --instantiation_flag                    false
% 3.52/1.00  --inst_sos_flag                         false
% 3.52/1.00  --inst_sos_phase                        true
% 3.52/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.52/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.52/1.00  --inst_lit_sel_side                     num_symb
% 3.52/1.00  --inst_solver_per_active                1400
% 3.52/1.00  --inst_solver_calls_frac                1.
% 3.52/1.00  --inst_passive_queue_type               priority_queues
% 3.52/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.52/1.00  --inst_passive_queues_freq              [25;2]
% 3.52/1.00  --inst_dismatching                      true
% 3.52/1.00  --inst_eager_unprocessed_to_passive     true
% 3.52/1.00  --inst_prop_sim_given                   true
% 3.52/1.00  --inst_prop_sim_new                     false
% 3.52/1.00  --inst_subs_new                         false
% 3.52/1.00  --inst_eq_res_simp                      false
% 3.52/1.00  --inst_subs_given                       false
% 3.52/1.00  --inst_orphan_elimination               true
% 3.52/1.00  --inst_learning_loop_flag               true
% 3.52/1.00  --inst_learning_start                   3000
% 3.52/1.00  --inst_learning_factor                  2
% 3.52/1.00  --inst_start_prop_sim_after_learn       3
% 3.52/1.00  --inst_sel_renew                        solver
% 3.52/1.00  --inst_lit_activity_flag                true
% 3.52/1.00  --inst_restr_to_given                   false
% 3.52/1.00  --inst_activity_threshold               500
% 3.52/1.00  --inst_out_proof                        true
% 3.52/1.00  
% 3.52/1.00  ------ Resolution Options
% 3.52/1.00  
% 3.52/1.00  --resolution_flag                       false
% 3.52/1.00  --res_lit_sel                           adaptive
% 3.52/1.00  --res_lit_sel_side                      none
% 3.52/1.00  --res_ordering                          kbo
% 3.52/1.00  --res_to_prop_solver                    active
% 3.52/1.00  --res_prop_simpl_new                    false
% 3.52/1.00  --res_prop_simpl_given                  true
% 3.52/1.00  --res_passive_queue_type                priority_queues
% 3.52/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.52/1.00  --res_passive_queues_freq               [15;5]
% 3.52/1.00  --res_forward_subs                      full
% 3.52/1.00  --res_backward_subs                     full
% 3.52/1.00  --res_forward_subs_resolution           true
% 3.52/1.00  --res_backward_subs_resolution          true
% 3.52/1.00  --res_orphan_elimination                true
% 3.52/1.00  --res_time_limit                        2.
% 3.52/1.00  --res_out_proof                         true
% 3.52/1.00  
% 3.52/1.00  ------ Superposition Options
% 3.52/1.00  
% 3.52/1.00  --superposition_flag                    true
% 3.52/1.00  --sup_passive_queue_type                priority_queues
% 3.52/1.00  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.52/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.52/1.00  --demod_completeness_check              fast
% 3.52/1.00  --demod_use_ground                      true
% 3.52/1.00  --sup_to_prop_solver                    active
% 3.52/1.00  --sup_prop_simpl_new                    false
% 3.52/1.00  --sup_prop_simpl_given                  false
% 3.52/1.00  --sup_fun_splitting                     true
% 3.52/1.00  --sup_smt_interval                      10000
% 3.52/1.00  
% 3.52/1.00  ------ Superposition Simplification Setup
% 3.52/1.00  
% 3.52/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.52/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.52/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.00  --sup_full_triv                         [TrivRules]
% 3.52/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.52/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.52/1.00  --sup_immed_triv                        [TrivRules]
% 3.52/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/1.00  --sup_immed_bw_main                     []
% 3.52/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.52/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.52/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/1.00  --sup_input_bw                          [BwDemod;BwSubsumption]
% 3.52/1.00  
% 3.52/1.00  ------ Combination Options
% 3.52/1.00  
% 3.52/1.00  --comb_res_mult                         1
% 3.52/1.00  --comb_sup_mult                         1
% 3.52/1.00  --comb_inst_mult                        1000000
% 3.52/1.00  
% 3.52/1.00  ------ Debug Options
% 3.52/1.00  
% 3.52/1.00  --dbg_backtrace                         false
% 3.52/1.00  --dbg_dump_prop_clauses                 false
% 3.52/1.00  --dbg_dump_prop_clauses_file            -
% 3.52/1.00  --dbg_out_stat                          false
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  ------ Proving...
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  % SZS status Theorem for theBenchmark.p
% 3.52/1.00  
% 3.52/1.00   Resolution empty clause
% 3.52/1.00  
% 3.52/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.52/1.00  
% 3.52/1.00  fof(f15,axiom,(
% 3.52/1.00    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f38,plain,(
% 3.52/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f15])).
% 3.52/1.00  
% 3.52/1.00  fof(f7,axiom,(
% 3.52/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f30,plain,(
% 3.52/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f7])).
% 3.52/1.00  
% 3.52/1.00  fof(f8,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f31,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f8])).
% 3.52/1.00  
% 3.52/1.00  fof(f9,axiom,(
% 3.52/1.00    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f32,plain,(
% 3.52/1.00    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f9])).
% 3.52/1.00  
% 3.52/1.00  fof(f10,axiom,(
% 3.52/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f33,plain,(
% 3.52/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f10])).
% 3.52/1.00  
% 3.52/1.00  fof(f11,axiom,(
% 3.52/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f34,plain,(
% 3.52/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f11])).
% 3.52/1.00  
% 3.52/1.00  fof(f12,axiom,(
% 3.52/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f35,plain,(
% 3.52/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f12])).
% 3.52/1.00  
% 3.52/1.00  fof(f44,plain,(
% 3.52/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.52/1.00    inference(definition_unfolding,[],[f34,f35])).
% 3.52/1.00  
% 3.52/1.00  fof(f45,plain,(
% 3.52/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.52/1.00    inference(definition_unfolding,[],[f33,f44])).
% 3.52/1.00  
% 3.52/1.00  fof(f46,plain,(
% 3.52/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.52/1.00    inference(definition_unfolding,[],[f32,f45])).
% 3.52/1.00  
% 3.52/1.00  fof(f48,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.52/1.00    inference(definition_unfolding,[],[f31,f46])).
% 3.52/1.00  
% 3.52/1.00  fof(f49,plain,(
% 3.52/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.52/1.00    inference(definition_unfolding,[],[f30,f48])).
% 3.52/1.00  
% 3.52/1.00  fof(f56,plain,(
% 3.52/1.00    ( ! [X2,X0,X3,X1] : (k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) )),
% 3.52/1.00    inference(definition_unfolding,[],[f38,f46,f49,f49])).
% 3.52/1.00  
% 3.52/1.00  fof(f4,axiom,(
% 3.52/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f27,plain,(
% 3.52/1.00    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f4])).
% 3.52/1.00  
% 3.52/1.00  fof(f2,axiom,(
% 3.52/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f25,plain,(
% 3.52/1.00    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f2])).
% 3.52/1.00  
% 3.52/1.00  fof(f1,axiom,(
% 3.52/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f24,plain,(
% 3.52/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f1])).
% 3.52/1.00  
% 3.52/1.00  fof(f47,plain,(
% 3.52/1.00    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.52/1.00    inference(definition_unfolding,[],[f25,f24,f45,f46])).
% 3.52/1.00  
% 3.52/1.00  fof(f53,plain,(
% 3.52/1.00    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k4_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) )),
% 3.52/1.00    inference(definition_unfolding,[],[f27,f24,f35,f49,f47])).
% 3.52/1.00  
% 3.52/1.00  fof(f5,axiom,(
% 3.52/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f28,plain,(
% 3.52/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f5])).
% 3.52/1.00  
% 3.52/1.00  fof(f51,plain,(
% 3.52/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.52/1.00    inference(definition_unfolding,[],[f28,f24,f44,f49])).
% 3.52/1.00  
% 3.52/1.00  fof(f13,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f36,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f13])).
% 3.52/1.00  
% 3.52/1.00  fof(f54,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) )),
% 3.52/1.00    inference(definition_unfolding,[],[f36,f48,f48])).
% 3.52/1.00  
% 3.52/1.00  fof(f3,axiom,(
% 3.52/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f26,plain,(
% 3.52/1.00    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f3])).
% 3.52/1.00  
% 3.52/1.00  fof(f52,plain,(
% 3.52/1.00    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) )),
% 3.52/1.00    inference(definition_unfolding,[],[f26,f24,f44,f48,f47])).
% 3.52/1.00  
% 3.52/1.00  fof(f19,conjecture,(
% 3.52/1.00    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f20,negated_conjecture,(
% 3.52/1.00    ~! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 3.52/1.00    inference(negated_conjecture,[],[f19])).
% 3.52/1.00  
% 3.52/1.00  fof(f21,plain,(
% 3.52/1.00    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 3.52/1.00    inference(ennf_transformation,[],[f20])).
% 3.52/1.00  
% 3.52/1.00  fof(f22,plain,(
% 3.52/1.00    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) => k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 3.52/1.00    introduced(choice_axiom,[])).
% 3.52/1.00  
% 3.52/1.00  fof(f23,plain,(
% 3.52/1.00    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 3.52/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f22])).
% 3.52/1.00  
% 3.52/1.00  fof(f43,plain,(
% 3.52/1.00    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 3.52/1.00    inference(cnf_transformation,[],[f23])).
% 3.52/1.00  
% 3.52/1.00  fof(f17,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f41,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f17])).
% 3.52/1.00  
% 3.52/1.00  fof(f18,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f42,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f18])).
% 3.52/1.00  
% 3.52/1.00  fof(f6,axiom,(
% 3.52/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f29,plain,(
% 3.52/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f6])).
% 3.52/1.00  
% 3.52/1.00  fof(f50,plain,(
% 3.52/1.00    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.52/1.00    inference(definition_unfolding,[],[f29,f49])).
% 3.52/1.00  
% 3.52/1.00  fof(f59,plain,(
% 3.52/1.00    k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 3.52/1.00    inference(definition_unfolding,[],[f43,f46,f41,f41,f41,f41,f42,f49,f50,f49])).
% 3.52/1.00  
% 3.52/1.00  fof(f16,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f40,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f16])).
% 3.52/1.00  
% 3.52/1.00  fof(f57,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) )),
% 3.52/1.00    inference(definition_unfolding,[],[f40,f49,f49,f50])).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5,plain,
% 3.52/1.00      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
% 3.52/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_25,plain,
% 3.52/1.00      ( k6_enumset1(k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X2_39),k4_tarski(X3_39,X1_39),k4_tarski(X3_39,X2_39)) = k2_zfmisc_1(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X3_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39)) ),
% 3.52/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2,plain,
% 3.52/1.00      ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k4_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) ),
% 3.52/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_28,plain,
% 3.52/1.00      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39),k4_xboole_0(k6_enumset1(X7_39,X7_39,X7_39,X7_39,X7_39,X7_39,X7_39,X8_39),k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39,X8_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) ),
% 3.52/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_0,plain,
% 3.52/1.00      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 3.52/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_30,plain,
% 3.52/1.00      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39),k4_xboole_0(k6_enumset1(X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) ),
% 3.52/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_184,plain,
% 3.52/1.00      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39),k4_xboole_0(k6_enumset1(X4_39,X4_39,X4_39,X4_39,X4_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_28,c_30]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3,plain,
% 3.52/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2) ),
% 3.52/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_27,plain,
% 3.52/1.00      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X0_39,X2_39) ),
% 3.52/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_53,plain,
% 3.52/1.00      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39),k4_xboole_0(k6_enumset1(X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X3_39,X4_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39))) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X0_39,X2_39,X3_39,X4_39) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_27,c_30]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_349,plain,
% 3.52/1.00      ( k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X3_39,X3_39,X4_39) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X0_39,X2_39,X3_39,X4_39) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_184,c_53]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_385,plain,
% 3.52/1.00      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X1_39,X1_39,X2_39) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X0_39,X2_39) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_349,c_27]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_458,plain,
% 3.52/1.00      ( k6_enumset1(X0_39,X0_39,X1_39,X0_39,X0_39,X0_39,X0_39,X2_39) = k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_385,c_349]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_870,plain,
% 3.52/1.00      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X6_39,X5_39,X5_39,X5_39,X5_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X5_39),k4_xboole_0(k6_enumset1(X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X5_39))) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_458,c_28]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1,plain,
% 3.52/1.00      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) ),
% 3.52/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_29,plain,
% 3.52/1.00      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39),k4_xboole_0(k6_enumset1(X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X7_39,X8_39),k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39,X8_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) ),
% 3.52/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_262,plain,
% 3.52/1.00      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X5_39),k4_xboole_0(k6_enumset1(X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X5_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39),k4_xboole_0(k6_enumset1(X4_39,X4_39,X4_39,X4_39,X4_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39))) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_29,c_28]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_274,plain,
% 3.52/1.00      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X5_39),k4_xboole_0(k6_enumset1(X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X5_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_262,c_184]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_411,plain,
% 3.52/1.00      ( k6_enumset1(X0_39,X0_39,X1_39,X0_39,X0_39,X0_39,X0_39,X2_39) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X0_39,X2_39) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_349,c_349]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_807,plain,
% 3.52/1.00      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X6_39,X5_39,X5_39,X5_39,X5_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X6_39,X6_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X7_39),k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X6_39,X6_39))) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_411,c_28]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_824,plain,
% 3.52/1.00      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X6_39,X5_39,X5_39,X5_39,X5_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X6_39,X5_39,X7_39) ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_807,c_274]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_888,plain,
% 3.52/1.00      ( k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X6_39,X5_39,X7_39) ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_870,c_274,c_824]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_8,negated_conjecture,
% 3.52/1.00      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 3.52/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_22,negated_conjecture,
% 3.52/1.00      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 3.52/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2684,plain,
% 3.52/1.00      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_888,c_22]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2875,plain,
% 3.52/1.00      ( k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_25,c_2684]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_6,plain,
% 3.52/1.00      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
% 3.52/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_24,plain,
% 3.52/1.00      ( k6_enumset1(k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X2_39,X1_39)) = k2_zfmisc_1(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X2_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39)) ),
% 3.52/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2876,plain,
% 3.52/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_2875,c_24]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2877,plain,
% 3.52/1.00      ( $false ),
% 3.52/1.00      inference(equality_resolution_simp,[status(thm)],[c_2876]) ).
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.52/1.00  
% 3.52/1.00  ------                               Statistics
% 3.52/1.00  
% 3.52/1.00  ------ General
% 3.52/1.00  
% 3.52/1.00  abstr_ref_over_cycles:                  0
% 3.52/1.00  abstr_ref_under_cycles:                 0
% 3.52/1.00  gc_basic_clause_elim:                   0
% 3.52/1.00  forced_gc_time:                         0
% 3.52/1.00  parsing_time:                           0.012
% 3.52/1.00  unif_index_cands_time:                  0.
% 3.52/1.00  unif_index_add_time:                    0.
% 3.52/1.00  orderings_time:                         0.
% 3.52/1.00  out_proof_time:                         0.011
% 3.52/1.00  total_time:                             0.421
% 3.52/1.00  num_of_symbols:                         44
% 3.52/1.00  num_of_terms:                           4883
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing
% 3.52/1.00  
% 3.52/1.00  num_of_splits:                          0
% 3.52/1.00  num_of_split_atoms:                     0
% 3.52/1.00  num_of_reused_defs:                     0
% 3.52/1.00  num_eq_ax_congr_red:                    0
% 3.52/1.00  num_of_sem_filtered_clauses:            0
% 3.52/1.00  num_of_subtypes:                        2
% 3.52/1.00  monotx_restored_types:                  0
% 3.52/1.00  sat_num_of_epr_types:                   0
% 3.52/1.00  sat_num_of_non_cyclic_types:            0
% 3.52/1.00  sat_guarded_non_collapsed_types:        0
% 3.52/1.00  num_pure_diseq_elim:                    0
% 3.52/1.00  simp_replaced_by:                       0
% 3.52/1.00  res_preprocessed:                       27
% 3.52/1.00  prep_upred:                             0
% 3.52/1.00  prep_unflattend:                        0
% 3.52/1.00  smt_new_axioms:                         0
% 3.52/1.00  pred_elim_cands:                        0
% 3.52/1.00  pred_elim:                              0
% 3.52/1.00  pred_elim_cl:                           0
% 3.52/1.00  pred_elim_cycles:                       0
% 3.52/1.00  merged_defs:                            0
% 3.52/1.00  merged_defs_ncl:                        0
% 3.52/1.00  bin_hyper_res:                          0
% 3.52/1.00  prep_cycles:                            2
% 3.52/1.00  pred_elim_time:                         0.
% 3.52/1.00  splitting_time:                         0.
% 3.52/1.00  sem_filter_time:                        0.
% 3.52/1.00  monotx_time:                            0.
% 3.52/1.00  subtype_inf_time:                       0.
% 3.52/1.00  
% 3.52/1.00  ------ Problem properties
% 3.52/1.00  
% 3.52/1.00  clauses:                                9
% 3.52/1.00  conjectures:                            1
% 3.52/1.00  epr:                                    0
% 3.52/1.00  horn:                                   9
% 3.52/1.00  ground:                                 1
% 3.52/1.00  unary:                                  9
% 3.52/1.00  binary:                                 0
% 3.52/1.00  lits:                                   9
% 3.52/1.00  lits_eq:                                9
% 3.52/1.00  fd_pure:                                0
% 3.52/1.00  fd_pseudo:                              0
% 3.52/1.00  fd_cond:                                0
% 3.52/1.00  fd_pseudo_cond:                         0
% 3.52/1.00  ac_symbols:                             0
% 3.52/1.00  
% 3.52/1.00  ------ Propositional Solver
% 3.52/1.00  
% 3.52/1.00  prop_solver_calls:                      13
% 3.52/1.00  prop_fast_solver_calls:                 92
% 3.52/1.00  smt_solver_calls:                       0
% 3.52/1.00  smt_fast_solver_calls:                  0
% 3.52/1.00  prop_num_of_clauses:                    91
% 3.52/1.00  prop_preprocess_simplified:             392
% 3.52/1.00  prop_fo_subsumed:                       0
% 3.52/1.00  prop_solver_time:                       0.
% 3.52/1.00  smt_solver_time:                        0.
% 3.52/1.00  smt_fast_solver_time:                   0.
% 3.52/1.00  prop_fast_solver_time:                  0.
% 3.52/1.00  prop_unsat_core_time:                   0.
% 3.52/1.00  
% 3.52/1.00  ------ QBF
% 3.52/1.00  
% 3.52/1.00  qbf_q_res:                              0
% 3.52/1.00  qbf_num_tautologies:                    0
% 3.52/1.00  qbf_prep_cycles:                        0
% 3.52/1.00  
% 3.52/1.00  ------ BMC1
% 3.52/1.00  
% 3.52/1.00  bmc1_current_bound:                     -1
% 3.52/1.00  bmc1_last_solved_bound:                 -1
% 3.52/1.00  bmc1_unsat_core_size:                   -1
% 3.52/1.00  bmc1_unsat_core_parents_size:           -1
% 3.52/1.00  bmc1_merge_next_fun:                    0
% 3.52/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.52/1.00  
% 3.52/1.00  ------ Instantiation
% 3.52/1.00  
% 3.52/1.00  inst_num_of_clauses:                    0
% 3.52/1.00  inst_num_in_passive:                    0
% 3.52/1.00  inst_num_in_active:                     0
% 3.52/1.00  inst_num_in_unprocessed:                0
% 3.52/1.00  inst_num_of_loops:                      0
% 3.52/1.00  inst_num_of_learning_restarts:          0
% 3.52/1.00  inst_num_moves_active_passive:          0
% 3.52/1.00  inst_lit_activity:                      0
% 3.52/1.00  inst_lit_activity_moves:                0
% 3.52/1.00  inst_num_tautologies:                   0
% 3.52/1.00  inst_num_prop_implied:                  0
% 3.52/1.00  inst_num_existing_simplified:           0
% 3.52/1.00  inst_num_eq_res_simplified:             0
% 3.52/1.00  inst_num_child_elim:                    0
% 3.52/1.00  inst_num_of_dismatching_blockings:      0
% 3.52/1.00  inst_num_of_non_proper_insts:           0
% 3.52/1.00  inst_num_of_duplicates:                 0
% 3.52/1.00  inst_inst_num_from_inst_to_res:         0
% 3.52/1.00  inst_dismatching_checking_time:         0.
% 3.52/1.00  
% 3.52/1.00  ------ Resolution
% 3.52/1.00  
% 3.52/1.00  res_num_of_clauses:                     0
% 3.52/1.00  res_num_in_passive:                     0
% 3.52/1.00  res_num_in_active:                      0
% 3.52/1.00  res_num_of_loops:                       29
% 3.52/1.00  res_forward_subset_subsumed:            0
% 3.52/1.00  res_backward_subset_subsumed:           0
% 3.52/1.00  res_forward_subsumed:                   0
% 3.52/1.00  res_backward_subsumed:                  0
% 3.52/1.00  res_forward_subsumption_resolution:     0
% 3.52/1.00  res_backward_subsumption_resolution:    0
% 3.52/1.00  res_clause_to_clause_subsumption:       13397
% 3.52/1.00  res_orphan_elimination:                 0
% 3.52/1.00  res_tautology_del:                      0
% 3.52/1.00  res_num_eq_res_simplified:              0
% 3.52/1.00  res_num_sel_changes:                    0
% 3.52/1.00  res_moves_from_active_to_pass:          0
% 3.52/1.00  
% 3.52/1.00  ------ Superposition
% 3.52/1.00  
% 3.52/1.00  sup_time_total:                         0.
% 3.52/1.00  sup_time_generating:                    0.
% 3.52/1.00  sup_time_sim_full:                      0.
% 3.52/1.00  sup_time_sim_immed:                     0.
% 3.52/1.00  
% 3.52/1.00  sup_num_of_clauses:                     663
% 3.52/1.00  sup_num_in_active:                      50
% 3.52/1.00  sup_num_in_passive:                     613
% 3.52/1.00  sup_num_of_loops:                       50
% 3.52/1.00  sup_fw_superposition:                   1204
% 3.52/1.00  sup_bw_superposition:                   1429
% 3.52/1.00  sup_immediate_simplified:               255
% 3.52/1.00  sup_given_eliminated:                   0
% 3.52/1.00  comparisons_done:                       0
% 3.52/1.00  comparisons_avoided:                    0
% 3.52/1.00  
% 3.52/1.00  ------ Simplifications
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  sim_fw_subset_subsumed:                 0
% 3.52/1.00  sim_bw_subset_subsumed:                 0
% 3.52/1.00  sim_fw_subsumed:                        62
% 3.52/1.00  sim_bw_subsumed:                        20
% 3.52/1.00  sim_fw_subsumption_res:                 0
% 3.52/1.00  sim_bw_subsumption_res:                 0
% 3.52/1.00  sim_tautology_del:                      0
% 3.52/1.00  sim_eq_tautology_del:                   16
% 3.52/1.00  sim_eq_res_simp:                        0
% 3.52/1.00  sim_fw_demodulated:                     114
% 3.52/1.00  sim_bw_demodulated:                     4
% 3.52/1.00  sim_light_normalised:                   69
% 3.52/1.00  sim_joinable_taut:                      0
% 3.52/1.00  sim_joinable_simp:                      0
% 3.52/1.00  sim_ac_normalised:                      0
% 3.52/1.00  sim_smt_subsumption:                    0
% 3.52/1.00  
%------------------------------------------------------------------------------
