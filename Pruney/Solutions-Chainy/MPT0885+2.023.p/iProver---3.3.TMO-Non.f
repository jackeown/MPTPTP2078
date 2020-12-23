%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:29 EST 2020

% Result     : Timeout 59.26s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   86 (1102 expanded)
%              Number of clauses        :   34 (  57 expanded)
%              Number of leaves         :   21 ( 376 expanded)
%              Depth                    :   17
%              Number of atoms          :  110 (1128 expanded)
%              Number of equality atoms :  109 (1127 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f29,f40])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f28,f41])).

fof(f43,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f27,f42])).

fof(f50,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1) ),
    inference(definition_unfolding,[],[f32,f43,f43])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(cnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8))) ),
    inference(definition_unfolding,[],[f22,f45,f31,f44])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f44])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f43])).

fof(f47,plain,(
    ! [X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f25,f44])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8))) = k3_tarski(k6_enumset1(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))) ),
    inference(definition_unfolding,[],[f23,f46,f45,f47])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))) ),
    inference(definition_unfolding,[],[f24,f45,f40,f44])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(negated_conjecture,[],[f17])).

fof(f19,plain,(
    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(ennf_transformation,[],[f18])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))
   => k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f20])).

fof(f39,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f21])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f54,plain,(
    k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f39,f42,f37,f37,f37,f37,f38,f47,f44,f44])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
    inference(definition_unfolding,[],[f34,f42,f44,f44])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X2,X0,X1] : k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(definition_unfolding,[],[f35,f44,f47,f44])).

cnf(c_2,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_730,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8))) ),
    inference(superposition,[status(thm)],[c_2,c_1])).

cnf(c_100671,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))) ),
    inference(superposition,[status(thm)],[c_2,c_730])).

cnf(c_0,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_622,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))) = k6_enumset1(X0,X0,X0,X0,X2,X1,X3,X4) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_101239,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3))) = k6_enumset1(X0,X0,X0,X0,X2,X1,X3,X4) ),
    inference(superposition,[status(thm)],[c_730,c_622])).

cnf(c_27345,plain,
    ( k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X2,X1,X3,X4) ),
    inference(superposition,[status(thm)],[c_622,c_0])).

cnf(c_100703,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X3),k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X3),k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X3),k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X3),k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X3),k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X3),k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X3),k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))) ),
    inference(superposition,[status(thm)],[c_27345,c_730])).

cnf(c_101235,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(superposition,[status(thm)],[c_730,c_0])).

cnf(c_101476,plain,
    ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))) = k6_enumset1(X0,X0,X0,X2,X1,X3,X4,X5) ),
    inference(demodulation,[status(thm)],[c_100703,c_101235])).

cnf(c_101526,plain,
    ( k6_enumset1(X0,X0,X0,X0,X1,X0,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X3) ),
    inference(demodulation,[status(thm)],[c_100671,c_101239,c_101476])).

cnf(c_105366,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X3) ),
    inference(superposition,[status(thm)],[c_101526,c_27345])).

cnf(c_6,negated_conjecture,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_109083,plain,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_105366,c_6])).

cnf(c_18,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_154,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != X1 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1458,plain,
    ( X0 != k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | X0 = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_154])).

cnf(c_5983,plain,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1458])).

cnf(c_3,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3673,plain,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) = k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_22,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_73,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != X0
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != X1
    | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k2_zfmisc_1(X1,X0) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_699,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != X0
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))
    | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),X0) ),
    inference(instantiation,[status(thm)],[c_73])).

cnf(c_1247,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))
    | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_699])).

cnf(c_5,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_322,plain,
    ( k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) = k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_88,plain,
    ( X0 != X1
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != X1
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = X0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_174,plain,
    ( X0 != k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = X0
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_88])).

cnf(c_321,plain,
    ( k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) != k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))
    | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_174])).

cnf(c_17,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_195,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_86,plain,
    ( k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_109083,c_5983,c_3673,c_1247,c_322,c_321,c_195,c_86])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 59.26/7.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.26/7.99  
% 59.26/7.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.26/7.99  
% 59.26/7.99  ------  iProver source info
% 59.26/7.99  
% 59.26/7.99  git: date: 2020-06-30 10:37:57 +0100
% 59.26/7.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.26/7.99  git: non_committed_changes: false
% 59.26/7.99  git: last_make_outside_of_git: false
% 59.26/7.99  
% 59.26/7.99  ------ 
% 59.26/7.99  ------ Parsing...
% 59.26/7.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.26/7.99  
% 59.26/7.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 59.26/7.99  
% 59.26/7.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.26/7.99  
% 59.26/7.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 59.26/7.99  ------ Proving...
% 59.26/7.99  ------ Problem Properties 
% 59.26/7.99  
% 59.26/7.99  
% 59.26/7.99  clauses                                 7
% 59.26/7.99  conjectures                             1
% 59.26/7.99  EPR                                     0
% 59.26/7.99  Horn                                    7
% 59.26/7.99  unary                                   7
% 59.26/7.99  binary                                  0
% 59.26/7.99  lits                                    7
% 59.26/7.99  lits eq                                 7
% 59.26/7.99  fd_pure                                 0
% 59.26/7.99  fd_pseudo                               0
% 59.26/7.99  fd_cond                                 0
% 59.26/7.99  fd_pseudo_cond                          0
% 59.26/7.99  AC symbols                              0
% 59.26/7.99  
% 59.26/7.99  ------ Input Options Time Limit: Unbounded
% 59.26/7.99  
% 59.26/7.99  
% 59.26/7.99  ------ 
% 59.26/7.99  Current options:
% 59.26/7.99  ------ 
% 59.26/7.99  
% 59.26/7.99  
% 59.26/7.99  
% 59.26/7.99  
% 59.26/7.99  ------ Proving...
% 59.26/7.99  
% 59.26/7.99  
% 59.26/7.99  % SZS status Theorem for theBenchmark.p
% 59.26/7.99  
% 59.26/7.99  % SZS output start CNFRefutation for theBenchmark.p
% 59.26/7.99  
% 59.26/7.99  fof(f11,axiom,(
% 59.26/7.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 59.26/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.99  
% 59.26/7.99  fof(f32,plain,(
% 59.26/7.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 59.26/7.99    inference(cnf_transformation,[],[f11])).
% 59.26/7.99  
% 59.26/7.99  fof(f6,axiom,(
% 59.26/7.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 59.26/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.99  
% 59.26/7.99  fof(f27,plain,(
% 59.26/7.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 59.26/7.99    inference(cnf_transformation,[],[f6])).
% 59.26/7.99  
% 59.26/7.99  fof(f7,axiom,(
% 59.26/7.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 59.26/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.99  
% 59.26/7.99  fof(f28,plain,(
% 59.26/7.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 59.26/7.99    inference(cnf_transformation,[],[f7])).
% 59.26/7.99  
% 59.26/7.99  fof(f8,axiom,(
% 59.26/7.99    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 59.26/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.99  
% 59.26/7.99  fof(f29,plain,(
% 59.26/7.99    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 59.26/7.99    inference(cnf_transformation,[],[f8])).
% 59.26/7.99  
% 59.26/7.99  fof(f9,axiom,(
% 59.26/7.99    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 59.26/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.99  
% 59.26/7.99  fof(f30,plain,(
% 59.26/7.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 59.26/7.99    inference(cnf_transformation,[],[f9])).
% 59.26/7.99  
% 59.26/7.99  fof(f10,axiom,(
% 59.26/7.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 59.26/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.99  
% 59.26/7.99  fof(f31,plain,(
% 59.26/7.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 59.26/7.99    inference(cnf_transformation,[],[f10])).
% 59.26/7.99  
% 59.26/7.99  fof(f40,plain,(
% 59.26/7.99    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 59.26/7.99    inference(definition_unfolding,[],[f30,f31])).
% 59.26/7.99  
% 59.26/7.99  fof(f41,plain,(
% 59.26/7.99    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 59.26/7.99    inference(definition_unfolding,[],[f29,f40])).
% 59.26/7.99  
% 59.26/7.99  fof(f42,plain,(
% 59.26/7.99    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 59.26/7.99    inference(definition_unfolding,[],[f28,f41])).
% 59.26/7.99  
% 59.26/7.99  fof(f43,plain,(
% 59.26/7.99    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 59.26/7.99    inference(definition_unfolding,[],[f27,f42])).
% 59.26/7.99  
% 59.26/7.99  fof(f50,plain,(
% 59.26/7.99    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1)) )),
% 59.26/7.99    inference(definition_unfolding,[],[f32,f43,f43])).
% 59.26/7.99  
% 59.26/7.99  fof(f2,axiom,(
% 59.26/7.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 59.26/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.99  
% 59.26/7.99  fof(f23,plain,(
% 59.26/7.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))) )),
% 59.26/7.99    inference(cnf_transformation,[],[f2])).
% 59.26/7.99  
% 59.26/7.99  fof(f1,axiom,(
% 59.26/7.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))),
% 59.26/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.99  
% 59.26/7.99  fof(f22,plain,(
% 59.26/7.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) )),
% 59.26/7.99    inference(cnf_transformation,[],[f1])).
% 59.26/7.99  
% 59.26/7.99  fof(f46,plain,(
% 59.26/7.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8)))) )),
% 59.26/7.99    inference(definition_unfolding,[],[f22,f45,f31,f44])).
% 59.26/7.99  
% 59.26/7.99  fof(f12,axiom,(
% 59.26/7.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 59.26/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.99  
% 59.26/7.99  fof(f33,plain,(
% 59.26/7.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 59.26/7.99    inference(cnf_transformation,[],[f12])).
% 59.26/7.99  
% 59.26/7.99  fof(f45,plain,(
% 59.26/7.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 59.26/7.99    inference(definition_unfolding,[],[f33,f44])).
% 59.26/7.99  
% 59.26/7.99  fof(f4,axiom,(
% 59.26/7.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 59.26/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.99  
% 59.26/7.99  fof(f25,plain,(
% 59.26/7.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 59.26/7.99    inference(cnf_transformation,[],[f4])).
% 59.26/7.99  
% 59.26/7.99  fof(f5,axiom,(
% 59.26/7.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 59.26/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.99  
% 59.26/7.99  fof(f26,plain,(
% 59.26/7.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 59.26/7.99    inference(cnf_transformation,[],[f5])).
% 59.26/7.99  
% 59.26/7.99  fof(f44,plain,(
% 59.26/7.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 59.26/7.99    inference(definition_unfolding,[],[f26,f43])).
% 59.26/7.99  
% 59.26/7.99  fof(f47,plain,(
% 59.26/7.99    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 59.26/7.99    inference(definition_unfolding,[],[f25,f44])).
% 59.26/7.99  
% 59.26/7.99  fof(f49,plain,(
% 59.26/7.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8))) = k3_tarski(k6_enumset1(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8)))) )),
% 59.26/7.99    inference(definition_unfolding,[],[f23,f46,f45,f47])).
% 59.26/7.99  
% 59.26/7.99  fof(f3,axiom,(
% 59.26/7.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 59.26/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.99  
% 59.26/7.99  fof(f24,plain,(
% 59.26/7.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 59.26/7.99    inference(cnf_transformation,[],[f3])).
% 59.26/7.99  
% 59.26/7.99  fof(f48,plain,(
% 59.26/7.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)))) )),
% 59.26/7.99    inference(definition_unfolding,[],[f24,f45,f40,f44])).
% 59.26/7.99  
% 59.26/7.99  fof(f17,conjecture,(
% 59.26/7.99    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))),
% 59.26/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.99  
% 59.26/7.99  fof(f18,negated_conjecture,(
% 59.26/7.99    ~! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))),
% 59.26/7.99    inference(negated_conjecture,[],[f17])).
% 59.26/7.99  
% 59.26/7.99  fof(f19,plain,(
% 59.26/7.99    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))),
% 59.26/7.99    inference(ennf_transformation,[],[f18])).
% 59.26/7.99  
% 59.26/7.99  fof(f20,plain,(
% 59.26/7.99    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) => k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 59.26/7.99    introduced(choice_axiom,[])).
% 59.26/7.99  
% 59.26/7.99  fof(f21,plain,(
% 59.26/7.99    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 59.26/7.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f20])).
% 59.26/7.99  
% 59.26/7.99  fof(f39,plain,(
% 59.26/7.99    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 59.26/7.99    inference(cnf_transformation,[],[f21])).
% 59.26/7.99  
% 59.26/7.99  fof(f15,axiom,(
% 59.26/7.99    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 59.26/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.99  
% 59.26/7.99  fof(f37,plain,(
% 59.26/7.99    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 59.26/7.99    inference(cnf_transformation,[],[f15])).
% 59.26/7.99  
% 59.26/7.99  fof(f16,axiom,(
% 59.26/7.99    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 59.26/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.99  
% 59.26/7.99  fof(f38,plain,(
% 59.26/7.99    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 59.26/7.99    inference(cnf_transformation,[],[f16])).
% 59.26/7.99  
% 59.26/7.99  fof(f54,plain,(
% 59.26/7.99    k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 59.26/7.99    inference(definition_unfolding,[],[f39,f42,f37,f37,f37,f37,f38,f47,f44,f44])).
% 59.26/7.99  
% 59.26/7.99  fof(f13,axiom,(
% 59.26/7.99    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 59.26/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.99  
% 59.26/7.99  fof(f34,plain,(
% 59.26/7.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 59.26/7.99    inference(cnf_transformation,[],[f13])).
% 59.26/7.99  
% 59.26/7.99  fof(f51,plain,(
% 59.26/7.99    ( ! [X2,X0,X3,X1] : (k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) )),
% 59.26/7.99    inference(definition_unfolding,[],[f34,f42,f44,f44])).
% 59.26/7.99  
% 59.26/7.99  fof(f14,axiom,(
% 59.26/7.99    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 59.26/7.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.26/7.99  
% 59.26/7.99  fof(f35,plain,(
% 59.26/7.99    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 59.26/7.99    inference(cnf_transformation,[],[f14])).
% 59.26/7.99  
% 59.26/7.99  fof(f53,plain,(
% 59.26/7.99    ( ! [X2,X0,X1] : (k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 59.26/7.99    inference(definition_unfolding,[],[f35,f44,f47,f44])).
% 59.26/7.99  
% 59.26/7.99  cnf(c_2,plain,
% 59.26/7.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1) ),
% 59.26/7.99      inference(cnf_transformation,[],[f50]) ).
% 59.26/7.99  
% 59.26/7.99  cnf(c_1,plain,
% 59.26/7.99      ( k3_tarski(k6_enumset1(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8))) ),
% 59.26/7.99      inference(cnf_transformation,[],[f49]) ).
% 59.26/7.99  
% 59.26/7.99  cnf(c_730,plain,
% 59.26/7.99      ( k3_tarski(k6_enumset1(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8))) ),
% 59.26/7.99      inference(superposition,[status(thm)],[c_2,c_1]) ).
% 59.26/7.99  
% 59.26/7.99  cnf(c_100671,plain,
% 59.26/7.99      ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))) ),
% 59.26/7.99      inference(superposition,[status(thm)],[c_2,c_730]) ).
% 59.26/7.99  
% 59.26/7.99  cnf(c_0,plain,
% 59.26/7.99      ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 59.26/7.99      inference(cnf_transformation,[],[f48]) ).
% 59.26/7.99  
% 59.26/7.99  cnf(c_622,plain,
% 59.26/7.99      ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))) = k6_enumset1(X0,X0,X0,X0,X2,X1,X3,X4) ),
% 59.26/7.99      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 59.26/7.99  
% 59.26/7.99  cnf(c_101239,plain,
% 59.26/7.99      ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3))) = k6_enumset1(X0,X0,X0,X0,X2,X1,X3,X4) ),
% 59.26/7.99      inference(superposition,[status(thm)],[c_730,c_622]) ).
% 59.26/7.99  
% 59.26/7.99  cnf(c_27345,plain,
% 59.26/7.99      ( k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X2,X1,X3,X4) ),
% 59.26/7.99      inference(superposition,[status(thm)],[c_622,c_0]) ).
% 59.26/7.99  
% 59.26/7.99  cnf(c_100703,plain,
% 59.26/7.99      ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X3),k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X3),k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X3),k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X3),k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X3),k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X3),k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X3),k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))) ),
% 59.26/7.99      inference(superposition,[status(thm)],[c_27345,c_730]) ).
% 59.26/7.99  
% 59.26/7.99  cnf(c_101235,plain,
% 59.26/7.99      ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 59.26/7.99      inference(superposition,[status(thm)],[c_730,c_0]) ).
% 59.26/7.99  
% 59.26/7.99  cnf(c_101476,plain,
% 59.26/7.99      ( k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))) = k6_enumset1(X0,X0,X0,X2,X1,X3,X4,X5) ),
% 59.26/7.99      inference(demodulation,[status(thm)],[c_100703,c_101235]) ).
% 59.26/7.99  
% 59.26/7.99  cnf(c_101526,plain,
% 59.26/7.99      ( k6_enumset1(X0,X0,X0,X0,X1,X0,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X3) ),
% 59.26/7.99      inference(demodulation,[status(thm)],[c_100671,c_101239,c_101476]) ).
% 59.26/7.99  
% 59.26/7.99  cnf(c_105366,plain,
% 59.26/7.99      ( k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X3) ),
% 59.26/7.99      inference(superposition,[status(thm)],[c_101526,c_27345]) ).
% 59.26/7.99  
% 59.26/7.99  cnf(c_6,negated_conjecture,
% 59.26/7.99      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 59.26/7.99      inference(cnf_transformation,[],[f54]) ).
% 59.26/7.99  
% 59.26/7.99  cnf(c_109083,plain,
% 59.26/7.99      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 59.26/7.99      inference(demodulation,[status(thm)],[c_105366,c_6]) ).
% 59.26/7.99  
% 59.26/7.99  cnf(c_18,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 59.26/7.99  
% 59.26/7.99  cnf(c_154,plain,
% 59.26/7.99      ( X0 != X1
% 59.26/7.99      | X0 = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 59.26/7.99      | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != X1 ),
% 59.26/7.99      inference(instantiation,[status(thm)],[c_18]) ).
% 59.26/7.99  
% 59.26/7.99  cnf(c_1458,plain,
% 59.26/7.99      ( X0 != k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 59.26/7.99      | X0 = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 59.26/7.99      | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 59.26/7.99      inference(instantiation,[status(thm)],[c_154]) ).
% 59.26/7.99  
% 59.26/7.99  cnf(c_5983,plain,
% 59.26/7.99      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 59.26/7.99      | k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 59.26/7.99      | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 59.26/7.99      inference(instantiation,[status(thm)],[c_1458]) ).
% 59.26/7.99  
% 59.26/7.99  cnf(c_3,plain,
% 59.26/7.99      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
% 59.26/7.99      inference(cnf_transformation,[],[f51]) ).
% 59.26/7.99  
% 59.26/7.99  cnf(c_3673,plain,
% 59.26/7.99      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) = k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 59.26/7.99      inference(instantiation,[status(thm)],[c_3]) ).
% 59.26/7.99  
% 59.26/7.99  cnf(c_22,plain,
% 59.26/7.99      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 59.26/7.99      theory(equality) ).
% 59.26/7.99  
% 59.26/7.99  cnf(c_73,plain,
% 59.26/8.00      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != X0
% 59.26/8.00      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != X1
% 59.26/8.00      | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k2_zfmisc_1(X1,X0) ),
% 59.26/8.00      inference(instantiation,[status(thm)],[c_22]) ).
% 59.26/8.00  
% 59.26/8.00  cnf(c_699,plain,
% 59.26/8.00      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != X0
% 59.26/8.00      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))
% 59.26/8.00      | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),X0) ),
% 59.26/8.00      inference(instantiation,[status(thm)],[c_73]) ).
% 59.26/8.00  
% 59.26/8.00  cnf(c_1247,plain,
% 59.26/8.00      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 59.26/8.00      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))
% 59.26/8.00      | k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 59.26/8.00      inference(instantiation,[status(thm)],[c_699]) ).
% 59.26/8.00  
% 59.26/8.00  cnf(c_5,plain,
% 59.26/8.00      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
% 59.26/8.00      inference(cnf_transformation,[],[f53]) ).
% 59.26/8.00  
% 59.26/8.00  cnf(c_322,plain,
% 59.26/8.00      ( k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) = k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 59.26/8.00      inference(instantiation,[status(thm)],[c_5]) ).
% 59.26/8.00  
% 59.26/8.00  cnf(c_88,plain,
% 59.26/8.00      ( X0 != X1
% 59.26/8.00      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != X1
% 59.26/8.00      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = X0 ),
% 59.26/8.00      inference(instantiation,[status(thm)],[c_18]) ).
% 59.26/8.00  
% 59.26/8.00  cnf(c_174,plain,
% 59.26/8.00      ( X0 != k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
% 59.26/8.00      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = X0
% 59.26/8.00      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 59.26/8.00      inference(instantiation,[status(thm)],[c_88]) ).
% 59.26/8.00  
% 59.26/8.00  cnf(c_321,plain,
% 59.26/8.00      ( k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) != k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
% 59.26/8.00      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k6_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))
% 59.26/8.00      | k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 59.26/8.00      inference(instantiation,[status(thm)],[c_174]) ).
% 59.26/8.00  
% 59.26/8.00  cnf(c_17,plain,( X0 = X0 ),theory(equality) ).
% 59.26/8.00  
% 59.26/8.00  cnf(c_195,plain,
% 59.26/8.00      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
% 59.26/8.00      inference(instantiation,[status(thm)],[c_17]) ).
% 59.26/8.00  
% 59.26/8.00  cnf(c_86,plain,
% 59.26/8.00      ( k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 59.26/8.00      inference(instantiation,[status(thm)],[c_17]) ).
% 59.26/8.00  
% 59.26/8.00  cnf(contradiction,plain,
% 59.26/8.00      ( $false ),
% 59.26/8.00      inference(minisat,
% 59.26/8.00                [status(thm)],
% 59.26/8.00                [c_109083,c_5983,c_3673,c_1247,c_322,c_321,c_195,c_86]) ).
% 59.26/8.00  
% 59.26/8.00  
% 59.26/8.00  % SZS output end CNFRefutation for theBenchmark.p
% 59.26/8.00  
% 59.26/8.00  ------                               Statistics
% 59.26/8.00  
% 59.26/8.00  ------ Selected
% 59.26/8.00  
% 59.26/8.00  total_time:                             7.118
% 59.26/8.00  
%------------------------------------------------------------------------------
