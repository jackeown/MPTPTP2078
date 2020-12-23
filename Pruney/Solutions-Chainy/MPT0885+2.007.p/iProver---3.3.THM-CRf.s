%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:26 EST 2020

% Result     : Theorem 23.48s
% Output     : CNFRefutation 23.48s
% Verified   : 
% Statistics : Number of formulae       :   93 (1432 expanded)
%              Number of clauses        :   36 (  92 expanded)
%              Number of leaves         :   20 ( 494 expanded)
%              Depth                    :   16
%              Number of atoms          :   95 (1434 expanded)
%              Number of equality atoms :   94 (1433 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f32,f50])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f36,f46])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f35,f47])).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f34,f48])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f49])).

fof(f61,plain,(
    ! [X2,X0,X1] : k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(definition_unfolding,[],[f41,f50,f52,f50])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
    inference(definition_unfolding,[],[f40,f48,f50,f50])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f26,f50,f50])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(definition_unfolding,[],[f28,f25,f47,f48])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k4_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) ),
    inference(definition_unfolding,[],[f30,f25,f38,f50,f51])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f31,f25,f46,f50])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0) ),
    inference(definition_unfolding,[],[f27,f49,f49])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) ),
    inference(definition_unfolding,[],[f29,f25,f46,f49,f51])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(negated_conjecture,[],[f20])).

fof(f22,plain,(
    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(ennf_transformation,[],[f21])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))
   => k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f23])).

fof(f45,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f24])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,(
    k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f45,f48,f43,f43,f43,f43,f44,f52,f50,f50])).

cnf(c_8,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_24,plain,
    ( k6_enumset1(k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X2_39)) = k2_zfmisc_1(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_6,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,plain,
    ( k6_enumset1(k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X2_39),k4_tarski(X3_39,X1_39),k4_tarski(X3_39,X2_39)) = k2_zfmisc_1(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X3_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_136,plain,
    ( k6_enumset1(k4_tarski(k4_tarski(X0_39,X1_39),X2_39),k4_tarski(k4_tarski(X0_39,X1_39),X2_39),k4_tarski(k4_tarski(X0_39,X1_39),X2_39),k4_tarski(k4_tarski(X0_39,X1_39),X2_39),k4_tarski(k4_tarski(X0_39,X1_39),X2_39),k4_tarski(k4_tarski(X0_39,X1_39),X3_39),k4_tarski(k4_tarski(X0_39,X4_39),X2_39),k4_tarski(k4_tarski(X0_39,X4_39),X3_39)) = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X4_39)),k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X3_39)) ),
    inference(superposition,[status(thm)],[c_24,c_26])).

cnf(c_1,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_31,plain,
    ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X0_39) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_4,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k4_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_28,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39),k4_xboole_0(k6_enumset1(X7_39,X7_39,X7_39,X7_39,X7_39,X7_39,X7_39,X8_39),k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39,X8_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_205,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X5_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39),k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X5_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X5_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) ),
    inference(superposition,[status(thm)],[c_31,c_28])).

cnf(c_0,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_32,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39),k4_xboole_0(k6_enumset1(X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_220,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X5_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39),k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X5_39))) = k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39) ),
    inference(superposition,[status(thm)],[c_28,c_32])).

cnf(c_2,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_30,plain,
    ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39) = k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X0_39,X1_39) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_211,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) = k5_xboole_0(k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X0_39),k4_xboole_0(k6_enumset1(X3_39,X3_39,X3_39,X3_39,X3_39,X4_39,X5_39,X6_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X0_39))) ),
    inference(superposition,[status(thm)],[c_30,c_28])).

cnf(c_215,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39),k4_xboole_0(k6_enumset1(X4_39,X4_39,X4_39,X4_39,X4_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) ),
    inference(superposition,[status(thm)],[c_28,c_32])).

cnf(c_224,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) = k6_enumset1(X1_39,X1_39,X2_39,X0_39,X3_39,X4_39,X5_39,X6_39) ),
    inference(demodulation,[status(thm)],[c_211,c_215])).

cnf(c_229,plain,
    ( k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39) = k6_enumset1(X2_39,X2_39,X0_39,X1_39,X3_39,X4_39,X6_39,X5_39) ),
    inference(demodulation,[status(thm)],[c_205,c_220,c_224])).

cnf(c_210,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) = k5_xboole_0(k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X0_39,X1_39),k4_xboole_0(k6_enumset1(X3_39,X3_39,X3_39,X3_39,X3_39,X4_39,X5_39,X6_39),k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X0_39,X1_39))) ),
    inference(superposition,[status(thm)],[c_30,c_28])).

cnf(c_225,plain,
    ( k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39) = k6_enumset1(X2_39,X2_39,X0_39,X1_39,X3_39,X4_39,X5_39,X6_39) ),
    inference(demodulation,[status(thm)],[c_210,c_215,c_224])).

cnf(c_533,plain,
    ( k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39) = k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X6_39,X5_39) ),
    inference(superposition,[status(thm)],[c_229,c_225])).

cnf(c_3,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_29,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39),k4_xboole_0(k6_enumset1(X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X7_39,X8_39),k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39,X8_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_714,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X7_39,X5_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) ),
    inference(superposition,[status(thm)],[c_30,c_29])).

cnf(c_750,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39),k4_xboole_0(k6_enumset1(X4_39,X4_39,X4_39,X4_39,X4_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39))) ),
    inference(superposition,[status(thm)],[c_29,c_29])).

cnf(c_755,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) ),
    inference(light_normalisation,[status(thm)],[c_750,c_215])).

cnf(c_58,plain,
    ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X0_39) ),
    inference(superposition,[status(thm)],[c_30,c_30])).

cnf(c_719,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X7_39,X7_39,X7_39,X7_39,X7_39,X7_39,X5_39,X6_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) ),
    inference(superposition,[status(thm)],[c_58,c_29])).

cnf(c_771,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X6_39,X7_39,X5_39) ),
    inference(demodulation,[status(thm)],[c_719,c_755])).

cnf(c_776,plain,
    ( k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X6_39,X7_39,X5_39) ),
    inference(demodulation,[status(thm)],[c_714,c_755,c_771])).

cnf(c_9,negated_conjecture,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23,negated_conjecture,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_33267,plain,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_776,c_23])).

cnf(c_34316,plain,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_533,c_33267])).

cnf(c_34326,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_136,c_34316])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:20:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.48/3.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.48/3.50  
% 23.48/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.48/3.50  
% 23.48/3.50  ------  iProver source info
% 23.48/3.50  
% 23.48/3.50  git: date: 2020-06-30 10:37:57 +0100
% 23.48/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.48/3.50  git: non_committed_changes: false
% 23.48/3.50  git: last_make_outside_of_git: false
% 23.48/3.50  
% 23.48/3.50  ------ 
% 23.48/3.50  
% 23.48/3.50  ------ Input Options
% 23.48/3.50  
% 23.48/3.50  --out_options                           all
% 23.48/3.50  --tptp_safe_out                         true
% 23.48/3.50  --problem_path                          ""
% 23.48/3.50  --include_path                          ""
% 23.48/3.50  --clausifier                            res/vclausify_rel
% 23.48/3.50  --clausifier_options                    --mode clausify
% 23.48/3.50  --stdin                                 false
% 23.48/3.50  --stats_out                             all
% 23.48/3.50  
% 23.48/3.50  ------ General Options
% 23.48/3.50  
% 23.48/3.50  --fof                                   false
% 23.48/3.50  --time_out_real                         305.
% 23.48/3.50  --time_out_virtual                      -1.
% 23.48/3.50  --symbol_type_check                     false
% 23.48/3.50  --clausify_out                          false
% 23.48/3.50  --sig_cnt_out                           false
% 23.48/3.50  --trig_cnt_out                          false
% 23.48/3.50  --trig_cnt_out_tolerance                1.
% 23.48/3.50  --trig_cnt_out_sk_spl                   false
% 23.48/3.50  --abstr_cl_out                          false
% 23.48/3.50  
% 23.48/3.50  ------ Global Options
% 23.48/3.50  
% 23.48/3.50  --schedule                              default
% 23.48/3.50  --add_important_lit                     false
% 23.48/3.50  --prop_solver_per_cl                    1000
% 23.48/3.50  --min_unsat_core                        false
% 23.48/3.50  --soft_assumptions                      false
% 23.48/3.50  --soft_lemma_size                       3
% 23.48/3.50  --prop_impl_unit_size                   0
% 23.48/3.50  --prop_impl_unit                        []
% 23.48/3.50  --share_sel_clauses                     true
% 23.48/3.50  --reset_solvers                         false
% 23.48/3.50  --bc_imp_inh                            [conj_cone]
% 23.48/3.50  --conj_cone_tolerance                   3.
% 23.48/3.50  --extra_neg_conj                        none
% 23.48/3.50  --large_theory_mode                     true
% 23.48/3.50  --prolific_symb_bound                   200
% 23.48/3.50  --lt_threshold                          2000
% 23.48/3.50  --clause_weak_htbl                      true
% 23.48/3.50  --gc_record_bc_elim                     false
% 23.48/3.50  
% 23.48/3.50  ------ Preprocessing Options
% 23.48/3.50  
% 23.48/3.50  --preprocessing_flag                    true
% 23.48/3.50  --time_out_prep_mult                    0.1
% 23.48/3.50  --splitting_mode                        input
% 23.48/3.50  --splitting_grd                         true
% 23.48/3.50  --splitting_cvd                         false
% 23.48/3.50  --splitting_cvd_svl                     false
% 23.48/3.50  --splitting_nvd                         32
% 23.48/3.50  --sub_typing                            true
% 23.48/3.50  --prep_gs_sim                           true
% 23.48/3.50  --prep_unflatten                        true
% 23.48/3.50  --prep_res_sim                          true
% 23.48/3.50  --prep_upred                            true
% 23.48/3.50  --prep_sem_filter                       exhaustive
% 23.48/3.50  --prep_sem_filter_out                   false
% 23.48/3.50  --pred_elim                             true
% 23.48/3.50  --res_sim_input                         true
% 23.48/3.50  --eq_ax_congr_red                       true
% 23.48/3.50  --pure_diseq_elim                       true
% 23.48/3.50  --brand_transform                       false
% 23.48/3.50  --non_eq_to_eq                          false
% 23.48/3.50  --prep_def_merge                        true
% 23.48/3.50  --prep_def_merge_prop_impl              false
% 23.48/3.50  --prep_def_merge_mbd                    true
% 23.48/3.50  --prep_def_merge_tr_red                 false
% 23.48/3.50  --prep_def_merge_tr_cl                  false
% 23.48/3.50  --smt_preprocessing                     true
% 23.48/3.50  --smt_ac_axioms                         fast
% 23.48/3.50  --preprocessed_out                      false
% 23.48/3.50  --preprocessed_stats                    false
% 23.48/3.50  
% 23.48/3.50  ------ Abstraction refinement Options
% 23.48/3.50  
% 23.48/3.50  --abstr_ref                             []
% 23.48/3.50  --abstr_ref_prep                        false
% 23.48/3.50  --abstr_ref_until_sat                   false
% 23.48/3.50  --abstr_ref_sig_restrict                funpre
% 23.48/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.48/3.50  --abstr_ref_under                       []
% 23.48/3.50  
% 23.48/3.50  ------ SAT Options
% 23.48/3.50  
% 23.48/3.50  --sat_mode                              false
% 23.48/3.50  --sat_fm_restart_options                ""
% 23.48/3.50  --sat_gr_def                            false
% 23.48/3.50  --sat_epr_types                         true
% 23.48/3.50  --sat_non_cyclic_types                  false
% 23.48/3.50  --sat_finite_models                     false
% 23.48/3.50  --sat_fm_lemmas                         false
% 23.48/3.50  --sat_fm_prep                           false
% 23.48/3.50  --sat_fm_uc_incr                        true
% 23.48/3.50  --sat_out_model                         small
% 23.48/3.50  --sat_out_clauses                       false
% 23.48/3.50  
% 23.48/3.50  ------ QBF Options
% 23.48/3.50  
% 23.48/3.50  --qbf_mode                              false
% 23.48/3.50  --qbf_elim_univ                         false
% 23.48/3.50  --qbf_dom_inst                          none
% 23.48/3.50  --qbf_dom_pre_inst                      false
% 23.48/3.50  --qbf_sk_in                             false
% 23.48/3.50  --qbf_pred_elim                         true
% 23.48/3.50  --qbf_split                             512
% 23.48/3.50  
% 23.48/3.50  ------ BMC1 Options
% 23.48/3.50  
% 23.48/3.50  --bmc1_incremental                      false
% 23.48/3.50  --bmc1_axioms                           reachable_all
% 23.48/3.50  --bmc1_min_bound                        0
% 23.48/3.50  --bmc1_max_bound                        -1
% 23.48/3.50  --bmc1_max_bound_default                -1
% 23.48/3.50  --bmc1_symbol_reachability              true
% 23.48/3.50  --bmc1_property_lemmas                  false
% 23.48/3.50  --bmc1_k_induction                      false
% 23.48/3.50  --bmc1_non_equiv_states                 false
% 23.48/3.50  --bmc1_deadlock                         false
% 23.48/3.50  --bmc1_ucm                              false
% 23.48/3.50  --bmc1_add_unsat_core                   none
% 23.48/3.50  --bmc1_unsat_core_children              false
% 23.48/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.48/3.50  --bmc1_out_stat                         full
% 23.48/3.50  --bmc1_ground_init                      false
% 23.48/3.50  --bmc1_pre_inst_next_state              false
% 23.48/3.50  --bmc1_pre_inst_state                   false
% 23.48/3.50  --bmc1_pre_inst_reach_state             false
% 23.48/3.50  --bmc1_out_unsat_core                   false
% 23.48/3.50  --bmc1_aig_witness_out                  false
% 23.48/3.50  --bmc1_verbose                          false
% 23.48/3.50  --bmc1_dump_clauses_tptp                false
% 23.48/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.48/3.50  --bmc1_dump_file                        -
% 23.48/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.48/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.48/3.50  --bmc1_ucm_extend_mode                  1
% 23.48/3.50  --bmc1_ucm_init_mode                    2
% 23.48/3.50  --bmc1_ucm_cone_mode                    none
% 23.48/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.48/3.50  --bmc1_ucm_relax_model                  4
% 23.48/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.48/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.48/3.50  --bmc1_ucm_layered_model                none
% 23.48/3.50  --bmc1_ucm_max_lemma_size               10
% 23.48/3.50  
% 23.48/3.50  ------ AIG Options
% 23.48/3.50  
% 23.48/3.50  --aig_mode                              false
% 23.48/3.50  
% 23.48/3.50  ------ Instantiation Options
% 23.48/3.50  
% 23.48/3.50  --instantiation_flag                    true
% 23.48/3.50  --inst_sos_flag                         false
% 23.48/3.50  --inst_sos_phase                        true
% 23.48/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.48/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.48/3.50  --inst_lit_sel_side                     num_symb
% 23.48/3.50  --inst_solver_per_active                1400
% 23.48/3.50  --inst_solver_calls_frac                1.
% 23.48/3.50  --inst_passive_queue_type               priority_queues
% 23.48/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.48/3.50  --inst_passive_queues_freq              [25;2]
% 23.48/3.50  --inst_dismatching                      true
% 23.48/3.50  --inst_eager_unprocessed_to_passive     true
% 23.48/3.50  --inst_prop_sim_given                   true
% 23.48/3.50  --inst_prop_sim_new                     false
% 23.48/3.50  --inst_subs_new                         false
% 23.48/3.50  --inst_eq_res_simp                      false
% 23.48/3.50  --inst_subs_given                       false
% 23.48/3.50  --inst_orphan_elimination               true
% 23.48/3.50  --inst_learning_loop_flag               true
% 23.48/3.50  --inst_learning_start                   3000
% 23.48/3.50  --inst_learning_factor                  2
% 23.48/3.50  --inst_start_prop_sim_after_learn       3
% 23.48/3.50  --inst_sel_renew                        solver
% 23.48/3.50  --inst_lit_activity_flag                true
% 23.48/3.50  --inst_restr_to_given                   false
% 23.48/3.50  --inst_activity_threshold               500
% 23.48/3.50  --inst_out_proof                        true
% 23.48/3.50  
% 23.48/3.50  ------ Resolution Options
% 23.48/3.50  
% 23.48/3.50  --resolution_flag                       true
% 23.48/3.50  --res_lit_sel                           adaptive
% 23.48/3.50  --res_lit_sel_side                      none
% 23.48/3.50  --res_ordering                          kbo
% 23.48/3.50  --res_to_prop_solver                    active
% 23.48/3.50  --res_prop_simpl_new                    false
% 23.48/3.50  --res_prop_simpl_given                  true
% 23.48/3.50  --res_passive_queue_type                priority_queues
% 23.48/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.48/3.50  --res_passive_queues_freq               [15;5]
% 23.48/3.50  --res_forward_subs                      full
% 23.48/3.50  --res_backward_subs                     full
% 23.48/3.50  --res_forward_subs_resolution           true
% 23.48/3.50  --res_backward_subs_resolution          true
% 23.48/3.50  --res_orphan_elimination                true
% 23.48/3.50  --res_time_limit                        2.
% 23.48/3.50  --res_out_proof                         true
% 23.48/3.50  
% 23.48/3.50  ------ Superposition Options
% 23.48/3.50  
% 23.48/3.50  --superposition_flag                    true
% 23.48/3.50  --sup_passive_queue_type                priority_queues
% 23.48/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.48/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.48/3.50  --demod_completeness_check              fast
% 23.48/3.50  --demod_use_ground                      true
% 23.48/3.50  --sup_to_prop_solver                    passive
% 23.48/3.50  --sup_prop_simpl_new                    true
% 23.48/3.50  --sup_prop_simpl_given                  true
% 23.48/3.50  --sup_fun_splitting                     false
% 23.48/3.50  --sup_smt_interval                      50000
% 23.48/3.50  
% 23.48/3.50  ------ Superposition Simplification Setup
% 23.48/3.50  
% 23.48/3.50  --sup_indices_passive                   []
% 23.48/3.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.48/3.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.48/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.48/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.48/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.48/3.50  --sup_full_bw                           [BwDemod]
% 23.48/3.50  --sup_immed_triv                        [TrivRules]
% 23.48/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.48/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.48/3.50  --sup_immed_bw_main                     []
% 23.48/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.48/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.48/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.48/3.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.48/3.50  
% 23.48/3.50  ------ Combination Options
% 23.48/3.50  
% 23.48/3.50  --comb_res_mult                         3
% 23.48/3.50  --comb_sup_mult                         2
% 23.48/3.50  --comb_inst_mult                        10
% 23.48/3.50  
% 23.48/3.50  ------ Debug Options
% 23.48/3.50  
% 23.48/3.50  --dbg_backtrace                         false
% 23.48/3.50  --dbg_dump_prop_clauses                 false
% 23.48/3.50  --dbg_dump_prop_clauses_file            -
% 23.48/3.50  --dbg_out_stat                          false
% 23.48/3.50  ------ Parsing...
% 23.48/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.48/3.50  
% 23.48/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 23.48/3.50  
% 23.48/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.48/3.50  
% 23.48/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.48/3.50  ------ Proving...
% 23.48/3.50  ------ Problem Properties 
% 23.48/3.50  
% 23.48/3.50  
% 23.48/3.50  clauses                                 10
% 23.48/3.50  conjectures                             1
% 23.48/3.50  EPR                                     0
% 23.48/3.50  Horn                                    10
% 23.48/3.50  unary                                   10
% 23.48/3.50  binary                                  0
% 23.48/3.50  lits                                    10
% 23.48/3.50  lits eq                                 10
% 23.48/3.50  fd_pure                                 0
% 23.48/3.50  fd_pseudo                               0
% 23.48/3.50  fd_cond                                 0
% 23.48/3.50  fd_pseudo_cond                          0
% 23.48/3.50  AC symbols                              0
% 23.48/3.50  
% 23.48/3.50  ------ Schedule UEQ
% 23.48/3.50  
% 23.48/3.50  ------ pure equality problem: resolution off 
% 23.48/3.50  
% 23.48/3.50  ------ Option_UEQ Time Limit: Unbounded
% 23.48/3.50  
% 23.48/3.50  
% 23.48/3.50  ------ 
% 23.48/3.50  Current options:
% 23.48/3.50  ------ 
% 23.48/3.50  
% 23.48/3.50  ------ Input Options
% 23.48/3.50  
% 23.48/3.50  --out_options                           all
% 23.48/3.50  --tptp_safe_out                         true
% 23.48/3.50  --problem_path                          ""
% 23.48/3.50  --include_path                          ""
% 23.48/3.50  --clausifier                            res/vclausify_rel
% 23.48/3.50  --clausifier_options                    --mode clausify
% 23.48/3.50  --stdin                                 false
% 23.48/3.50  --stats_out                             all
% 23.48/3.50  
% 23.48/3.50  ------ General Options
% 23.48/3.50  
% 23.48/3.50  --fof                                   false
% 23.48/3.50  --time_out_real                         305.
% 23.48/3.50  --time_out_virtual                      -1.
% 23.48/3.50  --symbol_type_check                     false
% 23.48/3.50  --clausify_out                          false
% 23.48/3.50  --sig_cnt_out                           false
% 23.48/3.50  --trig_cnt_out                          false
% 23.48/3.50  --trig_cnt_out_tolerance                1.
% 23.48/3.50  --trig_cnt_out_sk_spl                   false
% 23.48/3.50  --abstr_cl_out                          false
% 23.48/3.50  
% 23.48/3.50  ------ Global Options
% 23.48/3.50  
% 23.48/3.50  --schedule                              default
% 23.48/3.50  --add_important_lit                     false
% 23.48/3.50  --prop_solver_per_cl                    1000
% 23.48/3.50  --min_unsat_core                        false
% 23.48/3.50  --soft_assumptions                      false
% 23.48/3.50  --soft_lemma_size                       3
% 23.48/3.50  --prop_impl_unit_size                   0
% 23.48/3.50  --prop_impl_unit                        []
% 23.48/3.50  --share_sel_clauses                     true
% 23.48/3.50  --reset_solvers                         false
% 23.48/3.50  --bc_imp_inh                            [conj_cone]
% 23.48/3.50  --conj_cone_tolerance                   3.
% 23.48/3.50  --extra_neg_conj                        none
% 23.48/3.50  --large_theory_mode                     true
% 23.48/3.50  --prolific_symb_bound                   200
% 23.48/3.50  --lt_threshold                          2000
% 23.48/3.50  --clause_weak_htbl                      true
% 23.48/3.50  --gc_record_bc_elim                     false
% 23.48/3.50  
% 23.48/3.50  ------ Preprocessing Options
% 23.48/3.50  
% 23.48/3.50  --preprocessing_flag                    true
% 23.48/3.50  --time_out_prep_mult                    0.1
% 23.48/3.50  --splitting_mode                        input
% 23.48/3.50  --splitting_grd                         true
% 23.48/3.50  --splitting_cvd                         false
% 23.48/3.50  --splitting_cvd_svl                     false
% 23.48/3.50  --splitting_nvd                         32
% 23.48/3.50  --sub_typing                            true
% 23.48/3.50  --prep_gs_sim                           true
% 23.48/3.50  --prep_unflatten                        true
% 23.48/3.50  --prep_res_sim                          true
% 23.48/3.50  --prep_upred                            true
% 23.48/3.50  --prep_sem_filter                       exhaustive
% 23.48/3.50  --prep_sem_filter_out                   false
% 23.48/3.50  --pred_elim                             true
% 23.48/3.50  --res_sim_input                         true
% 23.48/3.50  --eq_ax_congr_red                       true
% 23.48/3.50  --pure_diseq_elim                       true
% 23.48/3.50  --brand_transform                       false
% 23.48/3.50  --non_eq_to_eq                          false
% 23.48/3.50  --prep_def_merge                        true
% 23.48/3.50  --prep_def_merge_prop_impl              false
% 23.48/3.50  --prep_def_merge_mbd                    true
% 23.48/3.50  --prep_def_merge_tr_red                 false
% 23.48/3.50  --prep_def_merge_tr_cl                  false
% 23.48/3.50  --smt_preprocessing                     true
% 23.48/3.50  --smt_ac_axioms                         fast
% 23.48/3.50  --preprocessed_out                      false
% 23.48/3.50  --preprocessed_stats                    false
% 23.48/3.50  
% 23.48/3.50  ------ Abstraction refinement Options
% 23.48/3.50  
% 23.48/3.50  --abstr_ref                             []
% 23.48/3.50  --abstr_ref_prep                        false
% 23.48/3.50  --abstr_ref_until_sat                   false
% 23.48/3.50  --abstr_ref_sig_restrict                funpre
% 23.48/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.48/3.50  --abstr_ref_under                       []
% 23.48/3.50  
% 23.48/3.50  ------ SAT Options
% 23.48/3.50  
% 23.48/3.50  --sat_mode                              false
% 23.48/3.50  --sat_fm_restart_options                ""
% 23.48/3.50  --sat_gr_def                            false
% 23.48/3.50  --sat_epr_types                         true
% 23.48/3.50  --sat_non_cyclic_types                  false
% 23.48/3.50  --sat_finite_models                     false
% 23.48/3.50  --sat_fm_lemmas                         false
% 23.48/3.50  --sat_fm_prep                           false
% 23.48/3.50  --sat_fm_uc_incr                        true
% 23.48/3.50  --sat_out_model                         small
% 23.48/3.50  --sat_out_clauses                       false
% 23.48/3.50  
% 23.48/3.50  ------ QBF Options
% 23.48/3.50  
% 23.48/3.50  --qbf_mode                              false
% 23.48/3.50  --qbf_elim_univ                         false
% 23.48/3.50  --qbf_dom_inst                          none
% 23.48/3.50  --qbf_dom_pre_inst                      false
% 23.48/3.50  --qbf_sk_in                             false
% 23.48/3.50  --qbf_pred_elim                         true
% 23.48/3.50  --qbf_split                             512
% 23.48/3.50  
% 23.48/3.50  ------ BMC1 Options
% 23.48/3.50  
% 23.48/3.50  --bmc1_incremental                      false
% 23.48/3.50  --bmc1_axioms                           reachable_all
% 23.48/3.50  --bmc1_min_bound                        0
% 23.48/3.50  --bmc1_max_bound                        -1
% 23.48/3.50  --bmc1_max_bound_default                -1
% 23.48/3.50  --bmc1_symbol_reachability              true
% 23.48/3.50  --bmc1_property_lemmas                  false
% 23.48/3.50  --bmc1_k_induction                      false
% 23.48/3.50  --bmc1_non_equiv_states                 false
% 23.48/3.50  --bmc1_deadlock                         false
% 23.48/3.50  --bmc1_ucm                              false
% 23.48/3.50  --bmc1_add_unsat_core                   none
% 23.48/3.50  --bmc1_unsat_core_children              false
% 23.48/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.48/3.50  --bmc1_out_stat                         full
% 23.48/3.50  --bmc1_ground_init                      false
% 23.48/3.50  --bmc1_pre_inst_next_state              false
% 23.48/3.50  --bmc1_pre_inst_state                   false
% 23.48/3.50  --bmc1_pre_inst_reach_state             false
% 23.48/3.50  --bmc1_out_unsat_core                   false
% 23.48/3.50  --bmc1_aig_witness_out                  false
% 23.48/3.50  --bmc1_verbose                          false
% 23.48/3.50  --bmc1_dump_clauses_tptp                false
% 23.48/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.48/3.50  --bmc1_dump_file                        -
% 23.48/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.48/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.48/3.50  --bmc1_ucm_extend_mode                  1
% 23.48/3.50  --bmc1_ucm_init_mode                    2
% 23.48/3.50  --bmc1_ucm_cone_mode                    none
% 23.48/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.48/3.50  --bmc1_ucm_relax_model                  4
% 23.48/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.48/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.48/3.50  --bmc1_ucm_layered_model                none
% 23.48/3.50  --bmc1_ucm_max_lemma_size               10
% 23.48/3.50  
% 23.48/3.50  ------ AIG Options
% 23.48/3.50  
% 23.48/3.50  --aig_mode                              false
% 23.48/3.50  
% 23.48/3.50  ------ Instantiation Options
% 23.48/3.50  
% 23.48/3.50  --instantiation_flag                    false
% 23.48/3.50  --inst_sos_flag                         false
% 23.48/3.50  --inst_sos_phase                        true
% 23.48/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.48/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.48/3.50  --inst_lit_sel_side                     num_symb
% 23.48/3.50  --inst_solver_per_active                1400
% 23.48/3.50  --inst_solver_calls_frac                1.
% 23.48/3.50  --inst_passive_queue_type               priority_queues
% 23.48/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.48/3.50  --inst_passive_queues_freq              [25;2]
% 23.48/3.50  --inst_dismatching                      true
% 23.48/3.50  --inst_eager_unprocessed_to_passive     true
% 23.48/3.50  --inst_prop_sim_given                   true
% 23.48/3.50  --inst_prop_sim_new                     false
% 23.48/3.50  --inst_subs_new                         false
% 23.48/3.50  --inst_eq_res_simp                      false
% 23.48/3.50  --inst_subs_given                       false
% 23.48/3.50  --inst_orphan_elimination               true
% 23.48/3.50  --inst_learning_loop_flag               true
% 23.48/3.50  --inst_learning_start                   3000
% 23.48/3.50  --inst_learning_factor                  2
% 23.48/3.50  --inst_start_prop_sim_after_learn       3
% 23.48/3.50  --inst_sel_renew                        solver
% 23.48/3.50  --inst_lit_activity_flag                true
% 23.48/3.50  --inst_restr_to_given                   false
% 23.48/3.50  --inst_activity_threshold               500
% 23.48/3.50  --inst_out_proof                        true
% 23.48/3.50  
% 23.48/3.50  ------ Resolution Options
% 23.48/3.50  
% 23.48/3.50  --resolution_flag                       false
% 23.48/3.50  --res_lit_sel                           adaptive
% 23.48/3.50  --res_lit_sel_side                      none
% 23.48/3.50  --res_ordering                          kbo
% 23.48/3.50  --res_to_prop_solver                    active
% 23.48/3.50  --res_prop_simpl_new                    false
% 23.48/3.50  --res_prop_simpl_given                  true
% 23.48/3.50  --res_passive_queue_type                priority_queues
% 23.48/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.48/3.50  --res_passive_queues_freq               [15;5]
% 23.48/3.50  --res_forward_subs                      full
% 23.48/3.50  --res_backward_subs                     full
% 23.48/3.50  --res_forward_subs_resolution           true
% 23.48/3.50  --res_backward_subs_resolution          true
% 23.48/3.50  --res_orphan_elimination                true
% 23.48/3.50  --res_time_limit                        2.
% 23.48/3.50  --res_out_proof                         true
% 23.48/3.50  
% 23.48/3.50  ------ Superposition Options
% 23.48/3.50  
% 23.48/3.50  --superposition_flag                    true
% 23.48/3.50  --sup_passive_queue_type                priority_queues
% 23.48/3.50  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.48/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.48/3.50  --demod_completeness_check              fast
% 23.48/3.50  --demod_use_ground                      true
% 23.48/3.50  --sup_to_prop_solver                    active
% 23.48/3.50  --sup_prop_simpl_new                    false
% 23.48/3.50  --sup_prop_simpl_given                  false
% 23.48/3.50  --sup_fun_splitting                     true
% 23.48/3.50  --sup_smt_interval                      10000
% 23.48/3.50  
% 23.48/3.50  ------ Superposition Simplification Setup
% 23.48/3.50  
% 23.48/3.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.48/3.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.48/3.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.48/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.48/3.50  --sup_full_triv                         [TrivRules]
% 23.48/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.48/3.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.48/3.50  --sup_immed_triv                        [TrivRules]
% 23.48/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.48/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.48/3.50  --sup_immed_bw_main                     []
% 23.48/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.48/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.48/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.48/3.50  --sup_input_bw                          [BwDemod;BwSubsumption]
% 23.48/3.50  
% 23.48/3.50  ------ Combination Options
% 23.48/3.50  
% 23.48/3.50  --comb_res_mult                         1
% 23.48/3.50  --comb_sup_mult                         1
% 23.48/3.50  --comb_inst_mult                        1000000
% 23.48/3.50  
% 23.48/3.50  ------ Debug Options
% 23.48/3.50  
% 23.48/3.50  --dbg_backtrace                         false
% 23.48/3.50  --dbg_dump_prop_clauses                 false
% 23.48/3.50  --dbg_dump_prop_clauses_file            -
% 23.48/3.50  --dbg_out_stat                          false
% 23.48/3.50  
% 23.48/3.50  
% 23.48/3.50  
% 23.48/3.50  
% 23.48/3.50  ------ Proving...
% 23.48/3.50  
% 23.48/3.50  
% 23.48/3.50  % SZS status Theorem for theBenchmark.p
% 23.48/3.50  
% 23.48/3.50   Resolution empty clause
% 23.48/3.50  
% 23.48/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.48/3.50  
% 23.48/3.50  fof(f17,axiom,(
% 23.48/3.50    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 23.48/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.50  
% 23.48/3.50  fof(f41,plain,(
% 23.48/3.50    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 23.48/3.50    inference(cnf_transformation,[],[f17])).
% 23.48/3.50  
% 23.48/3.50  fof(f8,axiom,(
% 23.48/3.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 23.48/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.50  
% 23.48/3.50  fof(f32,plain,(
% 23.48/3.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 23.48/3.50    inference(cnf_transformation,[],[f8])).
% 23.48/3.50  
% 23.48/3.50  fof(f52,plain,(
% 23.48/3.50    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 23.48/3.50    inference(definition_unfolding,[],[f32,f50])).
% 23.48/3.50  
% 23.48/3.50  fof(f9,axiom,(
% 23.48/3.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 23.48/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.50  
% 23.48/3.50  fof(f33,plain,(
% 23.48/3.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 23.48/3.50    inference(cnf_transformation,[],[f9])).
% 23.48/3.50  
% 23.48/3.50  fof(f10,axiom,(
% 23.48/3.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 23.48/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.50  
% 23.48/3.50  fof(f34,plain,(
% 23.48/3.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 23.48/3.50    inference(cnf_transformation,[],[f10])).
% 23.48/3.50  
% 23.48/3.50  fof(f11,axiom,(
% 23.48/3.50    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 23.48/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.50  
% 23.48/3.50  fof(f35,plain,(
% 23.48/3.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 23.48/3.50    inference(cnf_transformation,[],[f11])).
% 23.48/3.50  
% 23.48/3.50  fof(f12,axiom,(
% 23.48/3.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 23.48/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.50  
% 23.48/3.50  fof(f36,plain,(
% 23.48/3.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 23.48/3.50    inference(cnf_transformation,[],[f12])).
% 23.48/3.50  
% 23.48/3.50  fof(f13,axiom,(
% 23.48/3.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 23.48/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.50  
% 23.48/3.50  fof(f37,plain,(
% 23.48/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 23.48/3.50    inference(cnf_transformation,[],[f13])).
% 23.48/3.50  
% 23.48/3.50  fof(f14,axiom,(
% 23.48/3.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 23.48/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.50  
% 23.48/3.50  fof(f38,plain,(
% 23.48/3.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 23.48/3.50    inference(cnf_transformation,[],[f14])).
% 23.48/3.50  
% 23.48/3.50  fof(f46,plain,(
% 23.48/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 23.48/3.50    inference(definition_unfolding,[],[f37,f38])).
% 23.48/3.50  
% 23.48/3.50  fof(f47,plain,(
% 23.48/3.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 23.48/3.50    inference(definition_unfolding,[],[f36,f46])).
% 23.48/3.50  
% 23.48/3.50  fof(f48,plain,(
% 23.48/3.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 23.48/3.50    inference(definition_unfolding,[],[f35,f47])).
% 23.48/3.50  
% 23.48/3.50  fof(f49,plain,(
% 23.48/3.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 23.48/3.50    inference(definition_unfolding,[],[f34,f48])).
% 23.48/3.50  
% 23.48/3.50  fof(f50,plain,(
% 23.48/3.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 23.48/3.50    inference(definition_unfolding,[],[f33,f49])).
% 23.48/3.50  
% 23.48/3.50  fof(f61,plain,(
% 23.48/3.50    ( ! [X2,X0,X1] : (k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 23.48/3.50    inference(definition_unfolding,[],[f41,f50,f52,f50])).
% 23.48/3.50  
% 23.48/3.50  fof(f16,axiom,(
% 23.48/3.50    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 23.48/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.50  
% 23.48/3.50  fof(f40,plain,(
% 23.48/3.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 23.48/3.50    inference(cnf_transformation,[],[f16])).
% 23.48/3.50  
% 23.48/3.50  fof(f59,plain,(
% 23.48/3.50    ( ! [X2,X0,X3,X1] : (k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) )),
% 23.48/3.50    inference(definition_unfolding,[],[f40,f48,f50,f50])).
% 23.48/3.50  
% 23.48/3.50  fof(f2,axiom,(
% 23.48/3.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 23.48/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.50  
% 23.48/3.50  fof(f26,plain,(
% 23.48/3.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 23.48/3.50    inference(cnf_transformation,[],[f2])).
% 23.48/3.50  
% 23.48/3.50  fof(f54,plain,(
% 23.48/3.50    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 23.48/3.50    inference(definition_unfolding,[],[f26,f50,f50])).
% 23.48/3.50  
% 23.48/3.50  fof(f6,axiom,(
% 23.48/3.50    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 23.48/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.50  
% 23.48/3.50  fof(f30,plain,(
% 23.48/3.50    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 23.48/3.50    inference(cnf_transformation,[],[f6])).
% 23.48/3.50  
% 23.48/3.50  fof(f4,axiom,(
% 23.48/3.50    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 23.48/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.50  
% 23.48/3.50  fof(f28,plain,(
% 23.48/3.50    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 23.48/3.50    inference(cnf_transformation,[],[f4])).
% 23.48/3.50  
% 23.48/3.50  fof(f1,axiom,(
% 23.48/3.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 23.48/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.50  
% 23.48/3.50  fof(f25,plain,(
% 23.48/3.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 23.48/3.50    inference(cnf_transformation,[],[f1])).
% 23.48/3.50  
% 23.48/3.50  fof(f51,plain,(
% 23.48/3.50    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 23.48/3.50    inference(definition_unfolding,[],[f28,f25,f47,f48])).
% 23.48/3.50  
% 23.48/3.50  fof(f57,plain,(
% 23.48/3.50    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k4_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) )),
% 23.48/3.50    inference(definition_unfolding,[],[f30,f25,f38,f50,f51])).
% 23.48/3.50  
% 23.48/3.50  fof(f7,axiom,(
% 23.48/3.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 23.48/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.50  
% 23.48/3.50  fof(f31,plain,(
% 23.48/3.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 23.48/3.50    inference(cnf_transformation,[],[f7])).
% 23.48/3.50  
% 23.48/3.50  fof(f53,plain,(
% 23.48/3.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 23.48/3.50    inference(definition_unfolding,[],[f31,f25,f46,f50])).
% 23.48/3.50  
% 23.48/3.50  fof(f3,axiom,(
% 23.48/3.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 23.48/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.50  
% 23.48/3.50  fof(f27,plain,(
% 23.48/3.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 23.48/3.50    inference(cnf_transformation,[],[f3])).
% 23.48/3.50  
% 23.48/3.50  fof(f55,plain,(
% 23.48/3.50    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) )),
% 23.48/3.50    inference(definition_unfolding,[],[f27,f49,f49])).
% 23.48/3.50  
% 23.48/3.50  fof(f5,axiom,(
% 23.48/3.50    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 23.48/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.50  
% 23.48/3.50  fof(f29,plain,(
% 23.48/3.50    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 23.48/3.50    inference(cnf_transformation,[],[f5])).
% 23.48/3.50  
% 23.48/3.50  fof(f56,plain,(
% 23.48/3.50    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) )),
% 23.48/3.50    inference(definition_unfolding,[],[f29,f25,f46,f49,f51])).
% 23.48/3.50  
% 23.48/3.50  fof(f20,conjecture,(
% 23.48/3.50    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))),
% 23.48/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.50  
% 23.48/3.50  fof(f21,negated_conjecture,(
% 23.48/3.50    ~! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))),
% 23.48/3.50    inference(negated_conjecture,[],[f20])).
% 23.48/3.50  
% 23.48/3.50  fof(f22,plain,(
% 23.48/3.50    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))),
% 23.48/3.50    inference(ennf_transformation,[],[f21])).
% 23.48/3.50  
% 23.48/3.50  fof(f23,plain,(
% 23.48/3.50    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) => k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 23.48/3.50    introduced(choice_axiom,[])).
% 23.48/3.50  
% 23.48/3.50  fof(f24,plain,(
% 23.48/3.50    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 23.48/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f23])).
% 23.48/3.50  
% 23.48/3.50  fof(f45,plain,(
% 23.48/3.50    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 23.48/3.50    inference(cnf_transformation,[],[f24])).
% 23.48/3.50  
% 23.48/3.50  fof(f18,axiom,(
% 23.48/3.50    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 23.48/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.50  
% 23.48/3.50  fof(f43,plain,(
% 23.48/3.50    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 23.48/3.50    inference(cnf_transformation,[],[f18])).
% 23.48/3.50  
% 23.48/3.50  fof(f19,axiom,(
% 23.48/3.50    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 23.48/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.48/3.50  
% 23.48/3.50  fof(f44,plain,(
% 23.48/3.50    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 23.48/3.50    inference(cnf_transformation,[],[f19])).
% 23.48/3.50  
% 23.48/3.50  fof(f62,plain,(
% 23.48/3.50    k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 23.48/3.50    inference(definition_unfolding,[],[f45,f48,f43,f43,f43,f43,f44,f52,f50,f50])).
% 23.48/3.50  
% 23.48/3.50  cnf(c_8,plain,
% 23.48/3.50      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
% 23.48/3.50      inference(cnf_transformation,[],[f61]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_24,plain,
% 23.48/3.50      ( k6_enumset1(k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X2_39)) = k2_zfmisc_1(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39)) ),
% 23.48/3.50      inference(subtyping,[status(esa)],[c_8]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_6,plain,
% 23.48/3.50      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
% 23.48/3.50      inference(cnf_transformation,[],[f59]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_26,plain,
% 23.48/3.50      ( k6_enumset1(k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X2_39),k4_tarski(X3_39,X1_39),k4_tarski(X3_39,X2_39)) = k2_zfmisc_1(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X3_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39)) ),
% 23.48/3.50      inference(subtyping,[status(esa)],[c_6]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_136,plain,
% 23.48/3.50      ( k6_enumset1(k4_tarski(k4_tarski(X0_39,X1_39),X2_39),k4_tarski(k4_tarski(X0_39,X1_39),X2_39),k4_tarski(k4_tarski(X0_39,X1_39),X2_39),k4_tarski(k4_tarski(X0_39,X1_39),X2_39),k4_tarski(k4_tarski(X0_39,X1_39),X2_39),k4_tarski(k4_tarski(X0_39,X1_39),X3_39),k4_tarski(k4_tarski(X0_39,X4_39),X2_39),k4_tarski(k4_tarski(X0_39,X4_39),X3_39)) = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X4_39)),k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X3_39)) ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_24,c_26]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_1,plain,
% 23.48/3.50      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 23.48/3.50      inference(cnf_transformation,[],[f54]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_31,plain,
% 23.48/3.50      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X0_39) ),
% 23.48/3.50      inference(subtyping,[status(esa)],[c_1]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_4,plain,
% 23.48/3.50      ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k4_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) ),
% 23.48/3.50      inference(cnf_transformation,[],[f57]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_28,plain,
% 23.48/3.50      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39),k4_xboole_0(k6_enumset1(X7_39,X7_39,X7_39,X7_39,X7_39,X7_39,X7_39,X8_39),k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39,X8_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) ),
% 23.48/3.50      inference(subtyping,[status(esa)],[c_4]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_205,plain,
% 23.48/3.50      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X5_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39),k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X5_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X5_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_31,c_28]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_0,plain,
% 23.48/3.50      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 23.48/3.50      inference(cnf_transformation,[],[f53]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_32,plain,
% 23.48/3.50      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39),k4_xboole_0(k6_enumset1(X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) ),
% 23.48/3.50      inference(subtyping,[status(esa)],[c_0]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_220,plain,
% 23.48/3.50      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X5_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39),k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X5_39))) = k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39) ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_28,c_32]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_2,plain,
% 23.48/3.50      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X0,X1) ),
% 23.48/3.50      inference(cnf_transformation,[],[f55]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_30,plain,
% 23.48/3.50      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39) = k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X0_39,X1_39) ),
% 23.48/3.50      inference(subtyping,[status(esa)],[c_2]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_211,plain,
% 23.48/3.50      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) = k5_xboole_0(k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X0_39),k4_xboole_0(k6_enumset1(X3_39,X3_39,X3_39,X3_39,X3_39,X4_39,X5_39,X6_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X0_39))) ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_30,c_28]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_215,plain,
% 23.48/3.50      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39),k4_xboole_0(k6_enumset1(X4_39,X4_39,X4_39,X4_39,X4_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_28,c_32]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_224,plain,
% 23.48/3.50      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) = k6_enumset1(X1_39,X1_39,X2_39,X0_39,X3_39,X4_39,X5_39,X6_39) ),
% 23.48/3.50      inference(demodulation,[status(thm)],[c_211,c_215]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_229,plain,
% 23.48/3.50      ( k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39) = k6_enumset1(X2_39,X2_39,X0_39,X1_39,X3_39,X4_39,X6_39,X5_39) ),
% 23.48/3.50      inference(demodulation,[status(thm)],[c_205,c_220,c_224]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_210,plain,
% 23.48/3.50      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) = k5_xboole_0(k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X0_39,X1_39),k4_xboole_0(k6_enumset1(X3_39,X3_39,X3_39,X3_39,X3_39,X4_39,X5_39,X6_39),k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X0_39,X1_39))) ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_30,c_28]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_225,plain,
% 23.48/3.50      ( k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39) = k6_enumset1(X2_39,X2_39,X0_39,X1_39,X3_39,X4_39,X5_39,X6_39) ),
% 23.48/3.50      inference(demodulation,[status(thm)],[c_210,c_215,c_224]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_533,plain,
% 23.48/3.50      ( k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39) = k6_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X6_39,X5_39) ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_229,c_225]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_3,plain,
% 23.48/3.50      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) ),
% 23.48/3.50      inference(cnf_transformation,[],[f56]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_29,plain,
% 23.48/3.50      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39),k4_xboole_0(k6_enumset1(X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X7_39,X8_39),k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39,X8_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) ),
% 23.48/3.50      inference(subtyping,[status(esa)],[c_3]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_714,plain,
% 23.48/3.50      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X6_39,X6_39,X6_39,X6_39,X6_39,X6_39,X7_39,X5_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_30,c_29]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_750,plain,
% 23.48/3.50      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39),k4_xboole_0(k6_enumset1(X4_39,X4_39,X4_39,X4_39,X4_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39))) ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_29,c_29]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_755,plain,
% 23.48/3.50      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) ),
% 23.48/3.50      inference(light_normalisation,[status(thm)],[c_750,c_215]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_58,plain,
% 23.48/3.50      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39) = k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39,X0_39) ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_30,c_30]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_719,plain,
% 23.48/3.50      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39))) = k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X7_39,X7_39,X7_39,X7_39,X7_39,X7_39,X5_39,X6_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_58,c_29]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_771,plain,
% 23.48/3.50      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X6_39,X7_39,X5_39) ),
% 23.48/3.50      inference(demodulation,[status(thm)],[c_719,c_755]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_776,plain,
% 23.48/3.50      ( k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X6_39,X7_39,X5_39) ),
% 23.48/3.50      inference(demodulation,[status(thm)],[c_714,c_755,c_771]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_9,negated_conjecture,
% 23.48/3.50      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 23.48/3.50      inference(cnf_transformation,[],[f62]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_23,negated_conjecture,
% 23.48/3.50      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 23.48/3.50      inference(subtyping,[status(esa)],[c_9]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_33267,plain,
% 23.48/3.50      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 23.48/3.50      inference(demodulation,[status(thm)],[c_776,c_23]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_34316,plain,
% 23.48/3.50      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_533,c_33267]) ).
% 23.48/3.50  
% 23.48/3.50  cnf(c_34326,plain,
% 23.48/3.50      ( $false ),
% 23.48/3.50      inference(superposition,[status(thm)],[c_136,c_34316]) ).
% 23.48/3.50  
% 23.48/3.50  
% 23.48/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.48/3.50  
% 23.48/3.50  ------                               Statistics
% 23.48/3.50  
% 23.48/3.50  ------ General
% 23.48/3.50  
% 23.48/3.50  abstr_ref_over_cycles:                  0
% 23.48/3.50  abstr_ref_under_cycles:                 0
% 23.48/3.50  gc_basic_clause_elim:                   0
% 23.48/3.50  forced_gc_time:                         0
% 23.48/3.50  parsing_time:                           0.01
% 23.48/3.50  unif_index_cands_time:                  0.
% 23.48/3.50  unif_index_add_time:                    0.
% 23.48/3.50  orderings_time:                         0.
% 23.48/3.50  out_proof_time:                         0.008
% 23.48/3.50  total_time:                             2.809
% 23.48/3.50  num_of_symbols:                         44
% 23.48/3.50  num_of_terms:                           53397
% 23.48/3.50  
% 23.48/3.50  ------ Preprocessing
% 23.48/3.50  
% 23.48/3.50  num_of_splits:                          0
% 23.48/3.50  num_of_split_atoms:                     0
% 23.48/3.50  num_of_reused_defs:                     0
% 23.48/3.50  num_eq_ax_congr_red:                    0
% 23.48/3.50  num_of_sem_filtered_clauses:            0
% 23.48/3.50  num_of_subtypes:                        2
% 23.48/3.50  monotx_restored_types:                  0
% 23.48/3.50  sat_num_of_epr_types:                   0
% 23.48/3.50  sat_num_of_non_cyclic_types:            0
% 23.48/3.50  sat_guarded_non_collapsed_types:        0
% 23.48/3.50  num_pure_diseq_elim:                    0
% 23.48/3.50  simp_replaced_by:                       0
% 23.48/3.50  res_preprocessed:                       29
% 23.48/3.50  prep_upred:                             0
% 23.48/3.50  prep_unflattend:                        0
% 23.48/3.50  smt_new_axioms:                         0
% 23.48/3.50  pred_elim_cands:                        0
% 23.48/3.50  pred_elim:                              0
% 23.48/3.50  pred_elim_cl:                           0
% 23.48/3.50  pred_elim_cycles:                       0
% 23.48/3.50  merged_defs:                            0
% 23.48/3.50  merged_defs_ncl:                        0
% 23.48/3.50  bin_hyper_res:                          0
% 23.48/3.50  prep_cycles:                            2
% 23.48/3.50  pred_elim_time:                         0.
% 23.48/3.50  splitting_time:                         0.
% 23.48/3.50  sem_filter_time:                        0.
% 23.48/3.50  monotx_time:                            0.
% 23.48/3.50  subtype_inf_time:                       0.001
% 23.48/3.50  
% 23.48/3.50  ------ Problem properties
% 23.48/3.50  
% 23.48/3.50  clauses:                                10
% 23.48/3.50  conjectures:                            1
% 23.48/3.50  epr:                                    0
% 23.48/3.50  horn:                                   10
% 23.48/3.50  ground:                                 1
% 23.48/3.50  unary:                                  10
% 23.48/3.50  binary:                                 0
% 23.48/3.50  lits:                                   10
% 23.48/3.50  lits_eq:                                10
% 23.48/3.50  fd_pure:                                0
% 23.48/3.50  fd_pseudo:                              0
% 23.48/3.50  fd_cond:                                0
% 23.48/3.50  fd_pseudo_cond:                         0
% 23.48/3.50  ac_symbols:                             0
% 23.48/3.50  
% 23.48/3.50  ------ Propositional Solver
% 23.48/3.50  
% 23.48/3.50  prop_solver_calls:                      13
% 23.48/3.50  prop_fast_solver_calls:                 96
% 23.48/3.50  smt_solver_calls:                       0
% 23.48/3.50  smt_fast_solver_calls:                  0
% 23.48/3.50  prop_num_of_clauses:                    318
% 23.48/3.50  prop_preprocess_simplified:             636
% 23.48/3.50  prop_fo_subsumed:                       0
% 23.48/3.50  prop_solver_time:                       0.
% 23.48/3.50  smt_solver_time:                        0.
% 23.48/3.50  smt_fast_solver_time:                   0.
% 23.48/3.50  prop_fast_solver_time:                  0.
% 23.48/3.50  prop_unsat_core_time:                   0.
% 23.48/3.50  
% 23.48/3.50  ------ QBF
% 23.48/3.50  
% 23.48/3.50  qbf_q_res:                              0
% 23.48/3.50  qbf_num_tautologies:                    0
% 23.48/3.50  qbf_prep_cycles:                        0
% 23.48/3.50  
% 23.48/3.50  ------ BMC1
% 23.48/3.50  
% 23.48/3.50  bmc1_current_bound:                     -1
% 23.48/3.50  bmc1_last_solved_bound:                 -1
% 23.48/3.50  bmc1_unsat_core_size:                   -1
% 23.48/3.50  bmc1_unsat_core_parents_size:           -1
% 23.48/3.50  bmc1_merge_next_fun:                    0
% 23.48/3.50  bmc1_unsat_core_clauses_time:           0.
% 23.48/3.50  
% 23.48/3.50  ------ Instantiation
% 23.48/3.50  
% 23.48/3.50  inst_num_of_clauses:                    0
% 23.48/3.50  inst_num_in_passive:                    0
% 23.48/3.50  inst_num_in_active:                     0
% 23.48/3.50  inst_num_in_unprocessed:                0
% 23.48/3.50  inst_num_of_loops:                      0
% 23.48/3.50  inst_num_of_learning_restarts:          0
% 23.48/3.50  inst_num_moves_active_passive:          0
% 23.48/3.50  inst_lit_activity:                      0
% 23.48/3.50  inst_lit_activity_moves:                0
% 23.48/3.50  inst_num_tautologies:                   0
% 23.48/3.50  inst_num_prop_implied:                  0
% 23.48/3.50  inst_num_existing_simplified:           0
% 23.48/3.50  inst_num_eq_res_simplified:             0
% 23.48/3.50  inst_num_child_elim:                    0
% 23.48/3.50  inst_num_of_dismatching_blockings:      0
% 23.48/3.50  inst_num_of_non_proper_insts:           0
% 23.48/3.50  inst_num_of_duplicates:                 0
% 23.48/3.50  inst_inst_num_from_inst_to_res:         0
% 23.48/3.50  inst_dismatching_checking_time:         0.
% 23.48/3.50  
% 23.48/3.50  ------ Resolution
% 23.48/3.50  
% 23.48/3.50  res_num_of_clauses:                     0
% 23.48/3.50  res_num_in_passive:                     0
% 23.48/3.50  res_num_in_active:                      0
% 23.48/3.50  res_num_of_loops:                       31
% 23.48/3.50  res_forward_subset_subsumed:            0
% 23.48/3.50  res_backward_subset_subsumed:           0
% 23.48/3.50  res_forward_subsumed:                   0
% 23.48/3.50  res_backward_subsumed:                  0
% 23.48/3.50  res_forward_subsumption_resolution:     0
% 23.48/3.50  res_backward_subsumption_resolution:    0
% 23.48/3.50  res_clause_to_clause_subsumption:       343312
% 23.48/3.50  res_orphan_elimination:                 0
% 23.48/3.50  res_tautology_del:                      0
% 23.48/3.50  res_num_eq_res_simplified:              0
% 23.48/3.50  res_num_sel_changes:                    0
% 23.48/3.50  res_moves_from_active_to_pass:          0
% 23.48/3.50  
% 23.48/3.50  ------ Superposition
% 23.48/3.50  
% 23.48/3.50  sup_time_total:                         0.
% 23.48/3.50  sup_time_generating:                    0.
% 23.48/3.50  sup_time_sim_full:                      0.
% 23.48/3.50  sup_time_sim_immed:                     0.
% 23.48/3.50  
% 23.48/3.50  sup_num_of_clauses:                     5837
% 23.48/3.50  sup_num_in_active:                      264
% 23.48/3.50  sup_num_in_passive:                     5573
% 23.48/3.50  sup_num_of_loops:                       271
% 23.48/3.50  sup_fw_superposition:                   19443
% 23.48/3.50  sup_bw_superposition:                   13593
% 23.48/3.50  sup_immediate_simplified:               1594
% 23.48/3.50  sup_given_eliminated:                   0
% 23.48/3.50  comparisons_done:                       0
% 23.48/3.50  comparisons_avoided:                    0
% 23.48/3.50  
% 23.48/3.50  ------ Simplifications
% 23.48/3.50  
% 23.48/3.50  
% 23.48/3.50  sim_fw_subset_subsumed:                 0
% 23.48/3.50  sim_bw_subset_subsumed:                 0
% 23.48/3.50  sim_fw_subsumed:                        297
% 23.48/3.50  sim_bw_subsumed:                        129
% 23.48/3.50  sim_fw_subsumption_res:                 0
% 23.48/3.50  sim_bw_subsumption_res:                 0
% 23.48/3.50  sim_tautology_del:                      0
% 23.48/3.50  sim_eq_tautology_del:                   64
% 23.48/3.50  sim_eq_res_simp:                        0
% 23.48/3.50  sim_fw_demodulated:                     829
% 23.48/3.50  sim_bw_demodulated:                     12
% 23.48/3.50  sim_light_normalised:                   385
% 23.48/3.50  sim_joinable_taut:                      0
% 23.48/3.50  sim_joinable_simp:                      0
% 23.48/3.50  sim_ac_normalised:                      0
% 23.48/3.50  sim_smt_subsumption:                    0
% 23.48/3.50  
%------------------------------------------------------------------------------
