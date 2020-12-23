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
% DateTime   : Thu Dec  3 11:58:23 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 384 expanded)
%              Number of clauses        :   21 (  27 expanded)
%              Number of leaves         :   17 ( 129 expanded)
%              Depth                    :   15
%              Number of atoms          :   71 ( 386 expanded)
%              Number of equality atoms :   70 ( 385 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f31,f42])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f30,f43])).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f29,f44])).

fof(f47,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f28,f45])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
    inference(definition_unfolding,[],[f36,f44,f47,f47])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1) ),
    inference(definition_unfolding,[],[f34,f45,f45])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f26,f23,f43,f45])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0) ),
    inference(definition_unfolding,[],[f24,f45,f45])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) ),
    inference(negated_conjecture,[],[f18])).

fof(f20,plain,(
    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) ),
    inference(ennf_transformation,[],[f19])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))
   => k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f20,f21])).

fof(f41,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f22])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f27,f47])).

fof(f56,plain,(
    k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f41,f44,f39,f39,f39,f39,f40,f47,f48,f47])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X2,X0,X1] : k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(definition_unfolding,[],[f38,f47,f47,f48])).

cnf(c_4,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_23,plain,
    ( k6_enumset1(k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X2_39),k4_tarski(X3_39,X1_39),k4_tarski(X3_39,X2_39)) = k2_zfmisc_1(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X3_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_25,plain,
    ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39) = k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X2_39,X1_39) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_0,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_27,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_149,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X7_39,X6_39) ),
    inference(superposition,[status(thm)],[c_25,c_27])).

cnf(c_513,plain,
    ( k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X7_39,X6_39) ),
    inference(superposition,[status(thm)],[c_149,c_27])).

cnf(c_1,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_26,plain,
    ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39) = k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X0_39,X1_39) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_151,plain,
    ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X7_39,X5_39,X6_39) ),
    inference(superposition,[status(thm)],[c_26,c_27])).

cnf(c_621,plain,
    ( k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X6_39,X7_39,X5_39) ),
    inference(superposition,[status(thm)],[c_27,c_151])).

cnf(c_7,negated_conjecture,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_20,negated_conjecture,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_666,plain,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_621,c_20])).

cnf(c_779,plain,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_513,c_666])).

cnf(c_781,plain,
    ( k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_23,c_779])).

cnf(c_5,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_22,plain,
    ( k6_enumset1(k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X2_39,X1_39)) = k2_zfmisc_1(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X2_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_782,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_781,c_22])).

cnf(c_783,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_782])).

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
% 0.12/0.34  % DateTime   : Tue Dec  1 21:07:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.67/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.04  
% 2.67/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.67/1.04  
% 2.67/1.04  ------  iProver source info
% 2.67/1.04  
% 2.67/1.04  git: date: 2020-06-30 10:37:57 +0100
% 2.67/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.67/1.04  git: non_committed_changes: false
% 2.67/1.04  git: last_make_outside_of_git: false
% 2.67/1.04  
% 2.67/1.04  ------ 
% 2.67/1.04  
% 2.67/1.04  ------ Input Options
% 2.67/1.04  
% 2.67/1.04  --out_options                           all
% 2.67/1.04  --tptp_safe_out                         true
% 2.67/1.04  --problem_path                          ""
% 2.67/1.04  --include_path                          ""
% 2.67/1.04  --clausifier                            res/vclausify_rel
% 2.67/1.04  --clausifier_options                    --mode clausify
% 2.67/1.04  --stdin                                 false
% 2.67/1.04  --stats_out                             all
% 2.67/1.04  
% 2.67/1.04  ------ General Options
% 2.67/1.04  
% 2.67/1.04  --fof                                   false
% 2.67/1.04  --time_out_real                         305.
% 2.67/1.04  --time_out_virtual                      -1.
% 2.67/1.04  --symbol_type_check                     false
% 2.67/1.04  --clausify_out                          false
% 2.67/1.04  --sig_cnt_out                           false
% 2.67/1.04  --trig_cnt_out                          false
% 2.67/1.04  --trig_cnt_out_tolerance                1.
% 2.67/1.04  --trig_cnt_out_sk_spl                   false
% 2.67/1.04  --abstr_cl_out                          false
% 2.67/1.04  
% 2.67/1.04  ------ Global Options
% 2.67/1.04  
% 2.67/1.04  --schedule                              default
% 2.67/1.04  --add_important_lit                     false
% 2.67/1.04  --prop_solver_per_cl                    1000
% 2.67/1.04  --min_unsat_core                        false
% 2.67/1.04  --soft_assumptions                      false
% 2.67/1.04  --soft_lemma_size                       3
% 2.67/1.04  --prop_impl_unit_size                   0
% 2.67/1.04  --prop_impl_unit                        []
% 2.67/1.04  --share_sel_clauses                     true
% 2.67/1.04  --reset_solvers                         false
% 2.67/1.04  --bc_imp_inh                            [conj_cone]
% 2.67/1.04  --conj_cone_tolerance                   3.
% 2.67/1.04  --extra_neg_conj                        none
% 2.67/1.04  --large_theory_mode                     true
% 2.67/1.04  --prolific_symb_bound                   200
% 2.67/1.04  --lt_threshold                          2000
% 2.67/1.04  --clause_weak_htbl                      true
% 2.67/1.04  --gc_record_bc_elim                     false
% 2.67/1.04  
% 2.67/1.04  ------ Preprocessing Options
% 2.67/1.04  
% 2.67/1.04  --preprocessing_flag                    true
% 2.67/1.04  --time_out_prep_mult                    0.1
% 2.67/1.04  --splitting_mode                        input
% 2.67/1.04  --splitting_grd                         true
% 2.67/1.04  --splitting_cvd                         false
% 2.67/1.04  --splitting_cvd_svl                     false
% 2.67/1.04  --splitting_nvd                         32
% 2.67/1.04  --sub_typing                            true
% 2.67/1.04  --prep_gs_sim                           true
% 2.67/1.04  --prep_unflatten                        true
% 2.67/1.04  --prep_res_sim                          true
% 2.67/1.04  --prep_upred                            true
% 2.67/1.04  --prep_sem_filter                       exhaustive
% 2.67/1.04  --prep_sem_filter_out                   false
% 2.67/1.04  --pred_elim                             true
% 2.67/1.04  --res_sim_input                         true
% 2.67/1.04  --eq_ax_congr_red                       true
% 2.67/1.04  --pure_diseq_elim                       true
% 2.67/1.04  --brand_transform                       false
% 2.67/1.04  --non_eq_to_eq                          false
% 2.67/1.04  --prep_def_merge                        true
% 2.67/1.04  --prep_def_merge_prop_impl              false
% 2.67/1.04  --prep_def_merge_mbd                    true
% 2.67/1.04  --prep_def_merge_tr_red                 false
% 2.67/1.04  --prep_def_merge_tr_cl                  false
% 2.67/1.04  --smt_preprocessing                     true
% 2.67/1.04  --smt_ac_axioms                         fast
% 2.67/1.04  --preprocessed_out                      false
% 2.67/1.04  --preprocessed_stats                    false
% 2.67/1.04  
% 2.67/1.04  ------ Abstraction refinement Options
% 2.67/1.04  
% 2.67/1.04  --abstr_ref                             []
% 2.67/1.04  --abstr_ref_prep                        false
% 2.67/1.04  --abstr_ref_until_sat                   false
% 2.67/1.04  --abstr_ref_sig_restrict                funpre
% 2.67/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/1.04  --abstr_ref_under                       []
% 2.67/1.04  
% 2.67/1.04  ------ SAT Options
% 2.67/1.04  
% 2.67/1.04  --sat_mode                              false
% 2.67/1.04  --sat_fm_restart_options                ""
% 2.67/1.04  --sat_gr_def                            false
% 2.67/1.04  --sat_epr_types                         true
% 2.67/1.04  --sat_non_cyclic_types                  false
% 2.67/1.04  --sat_finite_models                     false
% 2.67/1.04  --sat_fm_lemmas                         false
% 2.67/1.04  --sat_fm_prep                           false
% 2.67/1.04  --sat_fm_uc_incr                        true
% 2.67/1.04  --sat_out_model                         small
% 2.67/1.04  --sat_out_clauses                       false
% 2.67/1.04  
% 2.67/1.04  ------ QBF Options
% 2.67/1.04  
% 2.67/1.04  --qbf_mode                              false
% 2.67/1.04  --qbf_elim_univ                         false
% 2.67/1.04  --qbf_dom_inst                          none
% 2.67/1.04  --qbf_dom_pre_inst                      false
% 2.67/1.04  --qbf_sk_in                             false
% 2.67/1.04  --qbf_pred_elim                         true
% 2.67/1.04  --qbf_split                             512
% 2.67/1.04  
% 2.67/1.04  ------ BMC1 Options
% 2.67/1.04  
% 2.67/1.04  --bmc1_incremental                      false
% 2.67/1.04  --bmc1_axioms                           reachable_all
% 2.67/1.04  --bmc1_min_bound                        0
% 2.67/1.04  --bmc1_max_bound                        -1
% 2.67/1.04  --bmc1_max_bound_default                -1
% 2.67/1.04  --bmc1_symbol_reachability              true
% 2.67/1.04  --bmc1_property_lemmas                  false
% 2.67/1.04  --bmc1_k_induction                      false
% 2.67/1.04  --bmc1_non_equiv_states                 false
% 2.67/1.04  --bmc1_deadlock                         false
% 2.67/1.04  --bmc1_ucm                              false
% 2.67/1.04  --bmc1_add_unsat_core                   none
% 2.67/1.04  --bmc1_unsat_core_children              false
% 2.67/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/1.04  --bmc1_out_stat                         full
% 2.67/1.04  --bmc1_ground_init                      false
% 2.67/1.04  --bmc1_pre_inst_next_state              false
% 2.67/1.04  --bmc1_pre_inst_state                   false
% 2.67/1.04  --bmc1_pre_inst_reach_state             false
% 2.67/1.04  --bmc1_out_unsat_core                   false
% 2.67/1.04  --bmc1_aig_witness_out                  false
% 2.67/1.04  --bmc1_verbose                          false
% 2.67/1.04  --bmc1_dump_clauses_tptp                false
% 2.67/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.67/1.04  --bmc1_dump_file                        -
% 2.67/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.67/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.67/1.04  --bmc1_ucm_extend_mode                  1
% 2.67/1.04  --bmc1_ucm_init_mode                    2
% 2.67/1.04  --bmc1_ucm_cone_mode                    none
% 2.67/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.67/1.04  --bmc1_ucm_relax_model                  4
% 2.67/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.67/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/1.04  --bmc1_ucm_layered_model                none
% 2.67/1.04  --bmc1_ucm_max_lemma_size               10
% 2.67/1.04  
% 2.67/1.04  ------ AIG Options
% 2.67/1.04  
% 2.67/1.04  --aig_mode                              false
% 2.67/1.04  
% 2.67/1.04  ------ Instantiation Options
% 2.67/1.04  
% 2.67/1.04  --instantiation_flag                    true
% 2.67/1.04  --inst_sos_flag                         false
% 2.67/1.04  --inst_sos_phase                        true
% 2.67/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/1.04  --inst_lit_sel_side                     num_symb
% 2.67/1.04  --inst_solver_per_active                1400
% 2.67/1.04  --inst_solver_calls_frac                1.
% 2.67/1.04  --inst_passive_queue_type               priority_queues
% 2.67/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/1.04  --inst_passive_queues_freq              [25;2]
% 2.67/1.04  --inst_dismatching                      true
% 2.67/1.04  --inst_eager_unprocessed_to_passive     true
% 2.67/1.04  --inst_prop_sim_given                   true
% 2.67/1.04  --inst_prop_sim_new                     false
% 2.67/1.04  --inst_subs_new                         false
% 2.67/1.04  --inst_eq_res_simp                      false
% 2.67/1.04  --inst_subs_given                       false
% 2.67/1.04  --inst_orphan_elimination               true
% 2.67/1.04  --inst_learning_loop_flag               true
% 2.67/1.04  --inst_learning_start                   3000
% 2.67/1.04  --inst_learning_factor                  2
% 2.67/1.04  --inst_start_prop_sim_after_learn       3
% 2.67/1.04  --inst_sel_renew                        solver
% 2.67/1.04  --inst_lit_activity_flag                true
% 2.67/1.04  --inst_restr_to_given                   false
% 2.67/1.04  --inst_activity_threshold               500
% 2.67/1.04  --inst_out_proof                        true
% 2.67/1.04  
% 2.67/1.04  ------ Resolution Options
% 2.67/1.04  
% 2.67/1.04  --resolution_flag                       true
% 2.67/1.04  --res_lit_sel                           adaptive
% 2.67/1.04  --res_lit_sel_side                      none
% 2.67/1.04  --res_ordering                          kbo
% 2.67/1.04  --res_to_prop_solver                    active
% 2.67/1.04  --res_prop_simpl_new                    false
% 2.67/1.04  --res_prop_simpl_given                  true
% 2.67/1.04  --res_passive_queue_type                priority_queues
% 2.67/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/1.04  --res_passive_queues_freq               [15;5]
% 2.67/1.04  --res_forward_subs                      full
% 2.67/1.04  --res_backward_subs                     full
% 2.67/1.04  --res_forward_subs_resolution           true
% 2.67/1.04  --res_backward_subs_resolution          true
% 2.67/1.04  --res_orphan_elimination                true
% 2.67/1.04  --res_time_limit                        2.
% 2.67/1.04  --res_out_proof                         true
% 2.67/1.04  
% 2.67/1.04  ------ Superposition Options
% 2.67/1.04  
% 2.67/1.04  --superposition_flag                    true
% 2.67/1.04  --sup_passive_queue_type                priority_queues
% 2.67/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.67/1.04  --demod_completeness_check              fast
% 2.67/1.04  --demod_use_ground                      true
% 2.67/1.04  --sup_to_prop_solver                    passive
% 2.67/1.04  --sup_prop_simpl_new                    true
% 2.67/1.04  --sup_prop_simpl_given                  true
% 2.67/1.04  --sup_fun_splitting                     false
% 2.67/1.04  --sup_smt_interval                      50000
% 2.67/1.04  
% 2.67/1.04  ------ Superposition Simplification Setup
% 2.67/1.04  
% 2.67/1.04  --sup_indices_passive                   []
% 2.67/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.04  --sup_full_bw                           [BwDemod]
% 2.67/1.04  --sup_immed_triv                        [TrivRules]
% 2.67/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.04  --sup_immed_bw_main                     []
% 2.67/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.04  
% 2.67/1.04  ------ Combination Options
% 2.67/1.04  
% 2.67/1.04  --comb_res_mult                         3
% 2.67/1.04  --comb_sup_mult                         2
% 2.67/1.04  --comb_inst_mult                        10
% 2.67/1.04  
% 2.67/1.04  ------ Debug Options
% 2.67/1.04  
% 2.67/1.04  --dbg_backtrace                         false
% 2.67/1.04  --dbg_dump_prop_clauses                 false
% 2.67/1.04  --dbg_dump_prop_clauses_file            -
% 2.67/1.04  --dbg_out_stat                          false
% 2.67/1.04  ------ Parsing...
% 2.67/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.67/1.04  
% 2.67/1.04  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.67/1.04  
% 2.67/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.67/1.04  
% 2.67/1.04  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.67/1.04  ------ Proving...
% 2.67/1.04  ------ Problem Properties 
% 2.67/1.04  
% 2.67/1.04  
% 2.67/1.04  clauses                                 8
% 2.67/1.04  conjectures                             1
% 2.67/1.04  EPR                                     0
% 2.67/1.04  Horn                                    8
% 2.67/1.04  unary                                   8
% 2.67/1.04  binary                                  0
% 2.67/1.04  lits                                    8
% 2.67/1.04  lits eq                                 8
% 2.67/1.04  fd_pure                                 0
% 2.67/1.04  fd_pseudo                               0
% 2.67/1.04  fd_cond                                 0
% 2.67/1.04  fd_pseudo_cond                          0
% 2.67/1.04  AC symbols                              0
% 2.67/1.04  
% 2.67/1.04  ------ Schedule UEQ
% 2.67/1.04  
% 2.67/1.04  ------ pure equality problem: resolution off 
% 2.67/1.04  
% 2.67/1.04  ------ Option_UEQ Time Limit: Unbounded
% 2.67/1.04  
% 2.67/1.04  
% 2.67/1.04  ------ 
% 2.67/1.04  Current options:
% 2.67/1.04  ------ 
% 2.67/1.04  
% 2.67/1.04  ------ Input Options
% 2.67/1.04  
% 2.67/1.04  --out_options                           all
% 2.67/1.04  --tptp_safe_out                         true
% 2.67/1.04  --problem_path                          ""
% 2.67/1.04  --include_path                          ""
% 2.67/1.04  --clausifier                            res/vclausify_rel
% 2.67/1.04  --clausifier_options                    --mode clausify
% 2.67/1.04  --stdin                                 false
% 2.67/1.04  --stats_out                             all
% 2.67/1.04  
% 2.67/1.04  ------ General Options
% 2.67/1.04  
% 2.67/1.04  --fof                                   false
% 2.67/1.04  --time_out_real                         305.
% 2.67/1.04  --time_out_virtual                      -1.
% 2.67/1.04  --symbol_type_check                     false
% 2.67/1.04  --clausify_out                          false
% 2.67/1.04  --sig_cnt_out                           false
% 2.67/1.04  --trig_cnt_out                          false
% 2.67/1.04  --trig_cnt_out_tolerance                1.
% 2.67/1.04  --trig_cnt_out_sk_spl                   false
% 2.67/1.04  --abstr_cl_out                          false
% 2.67/1.04  
% 2.67/1.04  ------ Global Options
% 2.67/1.04  
% 2.67/1.04  --schedule                              default
% 2.67/1.04  --add_important_lit                     false
% 2.67/1.04  --prop_solver_per_cl                    1000
% 2.67/1.04  --min_unsat_core                        false
% 2.67/1.04  --soft_assumptions                      false
% 2.67/1.04  --soft_lemma_size                       3
% 2.67/1.04  --prop_impl_unit_size                   0
% 2.67/1.04  --prop_impl_unit                        []
% 2.67/1.04  --share_sel_clauses                     true
% 2.67/1.04  --reset_solvers                         false
% 2.67/1.04  --bc_imp_inh                            [conj_cone]
% 2.67/1.04  --conj_cone_tolerance                   3.
% 2.67/1.04  --extra_neg_conj                        none
% 2.67/1.04  --large_theory_mode                     true
% 2.67/1.04  --prolific_symb_bound                   200
% 2.67/1.04  --lt_threshold                          2000
% 2.67/1.04  --clause_weak_htbl                      true
% 2.67/1.04  --gc_record_bc_elim                     false
% 2.67/1.04  
% 2.67/1.04  ------ Preprocessing Options
% 2.67/1.04  
% 2.67/1.04  --preprocessing_flag                    true
% 2.67/1.04  --time_out_prep_mult                    0.1
% 2.67/1.04  --splitting_mode                        input
% 2.67/1.04  --splitting_grd                         true
% 2.67/1.04  --splitting_cvd                         false
% 2.67/1.04  --splitting_cvd_svl                     false
% 2.67/1.04  --splitting_nvd                         32
% 2.67/1.04  --sub_typing                            true
% 2.67/1.04  --prep_gs_sim                           true
% 2.67/1.04  --prep_unflatten                        true
% 2.67/1.04  --prep_res_sim                          true
% 2.67/1.04  --prep_upred                            true
% 2.67/1.04  --prep_sem_filter                       exhaustive
% 2.67/1.04  --prep_sem_filter_out                   false
% 2.67/1.04  --pred_elim                             true
% 2.67/1.04  --res_sim_input                         true
% 2.67/1.04  --eq_ax_congr_red                       true
% 2.67/1.04  --pure_diseq_elim                       true
% 2.67/1.04  --brand_transform                       false
% 2.67/1.04  --non_eq_to_eq                          false
% 2.67/1.04  --prep_def_merge                        true
% 2.67/1.04  --prep_def_merge_prop_impl              false
% 2.67/1.04  --prep_def_merge_mbd                    true
% 2.67/1.04  --prep_def_merge_tr_red                 false
% 2.67/1.04  --prep_def_merge_tr_cl                  false
% 2.67/1.04  --smt_preprocessing                     true
% 2.67/1.04  --smt_ac_axioms                         fast
% 2.67/1.04  --preprocessed_out                      false
% 2.67/1.04  --preprocessed_stats                    false
% 2.67/1.04  
% 2.67/1.04  ------ Abstraction refinement Options
% 2.67/1.04  
% 2.67/1.04  --abstr_ref                             []
% 2.67/1.04  --abstr_ref_prep                        false
% 2.67/1.04  --abstr_ref_until_sat                   false
% 2.67/1.04  --abstr_ref_sig_restrict                funpre
% 2.67/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/1.04  --abstr_ref_under                       []
% 2.67/1.04  
% 2.67/1.04  ------ SAT Options
% 2.67/1.04  
% 2.67/1.04  --sat_mode                              false
% 2.67/1.04  --sat_fm_restart_options                ""
% 2.67/1.04  --sat_gr_def                            false
% 2.67/1.04  --sat_epr_types                         true
% 2.67/1.04  --sat_non_cyclic_types                  false
% 2.67/1.04  --sat_finite_models                     false
% 2.67/1.04  --sat_fm_lemmas                         false
% 2.67/1.04  --sat_fm_prep                           false
% 2.67/1.04  --sat_fm_uc_incr                        true
% 2.67/1.04  --sat_out_model                         small
% 2.67/1.04  --sat_out_clauses                       false
% 2.67/1.04  
% 2.67/1.04  ------ QBF Options
% 2.67/1.04  
% 2.67/1.04  --qbf_mode                              false
% 2.67/1.04  --qbf_elim_univ                         false
% 2.67/1.04  --qbf_dom_inst                          none
% 2.67/1.04  --qbf_dom_pre_inst                      false
% 2.67/1.04  --qbf_sk_in                             false
% 2.67/1.04  --qbf_pred_elim                         true
% 2.67/1.04  --qbf_split                             512
% 2.67/1.04  
% 2.67/1.04  ------ BMC1 Options
% 2.67/1.04  
% 2.67/1.04  --bmc1_incremental                      false
% 2.67/1.04  --bmc1_axioms                           reachable_all
% 2.67/1.04  --bmc1_min_bound                        0
% 2.67/1.04  --bmc1_max_bound                        -1
% 2.67/1.04  --bmc1_max_bound_default                -1
% 2.67/1.04  --bmc1_symbol_reachability              true
% 2.67/1.04  --bmc1_property_lemmas                  false
% 2.67/1.04  --bmc1_k_induction                      false
% 2.67/1.04  --bmc1_non_equiv_states                 false
% 2.67/1.04  --bmc1_deadlock                         false
% 2.67/1.04  --bmc1_ucm                              false
% 2.67/1.04  --bmc1_add_unsat_core                   none
% 2.67/1.04  --bmc1_unsat_core_children              false
% 2.67/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/1.04  --bmc1_out_stat                         full
% 2.67/1.04  --bmc1_ground_init                      false
% 2.67/1.04  --bmc1_pre_inst_next_state              false
% 2.67/1.04  --bmc1_pre_inst_state                   false
% 2.67/1.04  --bmc1_pre_inst_reach_state             false
% 2.67/1.04  --bmc1_out_unsat_core                   false
% 2.67/1.04  --bmc1_aig_witness_out                  false
% 2.67/1.04  --bmc1_verbose                          false
% 2.67/1.04  --bmc1_dump_clauses_tptp                false
% 2.67/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.67/1.04  --bmc1_dump_file                        -
% 2.67/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.67/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.67/1.04  --bmc1_ucm_extend_mode                  1
% 2.67/1.04  --bmc1_ucm_init_mode                    2
% 2.67/1.04  --bmc1_ucm_cone_mode                    none
% 2.67/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.67/1.04  --bmc1_ucm_relax_model                  4
% 2.67/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.67/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/1.04  --bmc1_ucm_layered_model                none
% 2.67/1.04  --bmc1_ucm_max_lemma_size               10
% 2.67/1.04  
% 2.67/1.04  ------ AIG Options
% 2.67/1.04  
% 2.67/1.04  --aig_mode                              false
% 2.67/1.04  
% 2.67/1.04  ------ Instantiation Options
% 2.67/1.04  
% 2.67/1.04  --instantiation_flag                    false
% 2.67/1.04  --inst_sos_flag                         false
% 2.67/1.04  --inst_sos_phase                        true
% 2.67/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/1.04  --inst_lit_sel_side                     num_symb
% 2.67/1.04  --inst_solver_per_active                1400
% 2.67/1.04  --inst_solver_calls_frac                1.
% 2.67/1.04  --inst_passive_queue_type               priority_queues
% 2.67/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/1.04  --inst_passive_queues_freq              [25;2]
% 2.67/1.04  --inst_dismatching                      true
% 2.67/1.04  --inst_eager_unprocessed_to_passive     true
% 2.67/1.04  --inst_prop_sim_given                   true
% 2.67/1.04  --inst_prop_sim_new                     false
% 2.67/1.04  --inst_subs_new                         false
% 2.67/1.04  --inst_eq_res_simp                      false
% 2.67/1.04  --inst_subs_given                       false
% 2.67/1.04  --inst_orphan_elimination               true
% 2.67/1.04  --inst_learning_loop_flag               true
% 2.67/1.04  --inst_learning_start                   3000
% 2.67/1.04  --inst_learning_factor                  2
% 2.67/1.04  --inst_start_prop_sim_after_learn       3
% 2.67/1.04  --inst_sel_renew                        solver
% 2.67/1.04  --inst_lit_activity_flag                true
% 2.67/1.04  --inst_restr_to_given                   false
% 2.67/1.04  --inst_activity_threshold               500
% 2.67/1.04  --inst_out_proof                        true
% 2.67/1.04  
% 2.67/1.04  ------ Resolution Options
% 2.67/1.04  
% 2.67/1.04  --resolution_flag                       false
% 2.67/1.04  --res_lit_sel                           adaptive
% 2.67/1.04  --res_lit_sel_side                      none
% 2.67/1.04  --res_ordering                          kbo
% 2.67/1.04  --res_to_prop_solver                    active
% 2.67/1.04  --res_prop_simpl_new                    false
% 2.67/1.04  --res_prop_simpl_given                  true
% 2.67/1.04  --res_passive_queue_type                priority_queues
% 2.67/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/1.04  --res_passive_queues_freq               [15;5]
% 2.67/1.04  --res_forward_subs                      full
% 2.67/1.04  --res_backward_subs                     full
% 2.67/1.04  --res_forward_subs_resolution           true
% 2.67/1.04  --res_backward_subs_resolution          true
% 2.67/1.04  --res_orphan_elimination                true
% 2.67/1.04  --res_time_limit                        2.
% 2.67/1.04  --res_out_proof                         true
% 2.67/1.04  
% 2.67/1.04  ------ Superposition Options
% 2.67/1.04  
% 2.67/1.04  --superposition_flag                    true
% 2.67/1.04  --sup_passive_queue_type                priority_queues
% 2.67/1.04  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.67/1.04  --demod_completeness_check              fast
% 2.67/1.04  --demod_use_ground                      true
% 2.67/1.04  --sup_to_prop_solver                    active
% 2.67/1.04  --sup_prop_simpl_new                    false
% 2.67/1.04  --sup_prop_simpl_given                  false
% 2.67/1.04  --sup_fun_splitting                     true
% 2.67/1.04  --sup_smt_interval                      10000
% 2.67/1.04  
% 2.67/1.04  ------ Superposition Simplification Setup
% 2.67/1.04  
% 2.67/1.04  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.67/1.04  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.67/1.04  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.04  --sup_full_triv                         [TrivRules]
% 2.67/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.67/1.04  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.67/1.04  --sup_immed_triv                        [TrivRules]
% 2.67/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/1.04  --sup_immed_bw_main                     []
% 2.67/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.67/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/1.04  --sup_input_bw                          [BwDemod;BwSubsumption]
% 2.67/1.04  
% 2.67/1.04  ------ Combination Options
% 2.67/1.04  
% 2.67/1.04  --comb_res_mult                         1
% 2.67/1.04  --comb_sup_mult                         1
% 2.67/1.04  --comb_inst_mult                        1000000
% 2.67/1.04  
% 2.67/1.04  ------ Debug Options
% 2.67/1.04  
% 2.67/1.04  --dbg_backtrace                         false
% 2.67/1.04  --dbg_dump_prop_clauses                 false
% 2.67/1.04  --dbg_dump_prop_clauses_file            -
% 2.67/1.04  --dbg_out_stat                          false
% 2.67/1.04  
% 2.67/1.04  
% 2.67/1.04  
% 2.67/1.04  
% 2.67/1.04  ------ Proving...
% 2.67/1.04  
% 2.67/1.04  
% 2.67/1.04  % SZS status Theorem for theBenchmark.p
% 2.67/1.04  
% 2.67/1.04   Resolution empty clause
% 2.67/1.04  
% 2.67/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 2.67/1.04  
% 2.67/1.04  fof(f14,axiom,(
% 2.67/1.04    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 2.67/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.04  
% 2.67/1.04  fof(f36,plain,(
% 2.67/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 2.67/1.04    inference(cnf_transformation,[],[f14])).
% 2.67/1.04  
% 2.67/1.04  fof(f6,axiom,(
% 2.67/1.04    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.67/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.04  
% 2.67/1.04  fof(f28,plain,(
% 2.67/1.04    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.67/1.04    inference(cnf_transformation,[],[f6])).
% 2.67/1.04  
% 2.67/1.04  fof(f7,axiom,(
% 2.67/1.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.67/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.04  
% 2.67/1.04  fof(f29,plain,(
% 2.67/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.67/1.04    inference(cnf_transformation,[],[f7])).
% 2.67/1.04  
% 2.67/1.04  fof(f8,axiom,(
% 2.67/1.04    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.67/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.04  
% 2.67/1.04  fof(f30,plain,(
% 2.67/1.04    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.67/1.04    inference(cnf_transformation,[],[f8])).
% 2.67/1.04  
% 2.67/1.04  fof(f9,axiom,(
% 2.67/1.04    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.67/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.04  
% 2.67/1.04  fof(f31,plain,(
% 2.67/1.04    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.67/1.04    inference(cnf_transformation,[],[f9])).
% 2.67/1.04  
% 2.67/1.04  fof(f10,axiom,(
% 2.67/1.04    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.67/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.04  
% 2.67/1.04  fof(f32,plain,(
% 2.67/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.67/1.04    inference(cnf_transformation,[],[f10])).
% 2.67/1.04  
% 2.67/1.04  fof(f11,axiom,(
% 2.67/1.04    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.67/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.04  
% 2.67/1.04  fof(f33,plain,(
% 2.67/1.04    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.67/1.04    inference(cnf_transformation,[],[f11])).
% 2.67/1.04  
% 2.67/1.04  fof(f42,plain,(
% 2.67/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.67/1.04    inference(definition_unfolding,[],[f32,f33])).
% 2.67/1.04  
% 2.67/1.04  fof(f43,plain,(
% 2.67/1.04    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.67/1.04    inference(definition_unfolding,[],[f31,f42])).
% 2.67/1.04  
% 2.67/1.04  fof(f44,plain,(
% 2.67/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.67/1.04    inference(definition_unfolding,[],[f30,f43])).
% 2.67/1.04  
% 2.67/1.04  fof(f45,plain,(
% 2.67/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.67/1.04    inference(definition_unfolding,[],[f29,f44])).
% 2.67/1.04  
% 2.67/1.04  fof(f47,plain,(
% 2.67/1.04    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.67/1.04    inference(definition_unfolding,[],[f28,f45])).
% 2.67/1.04  
% 2.67/1.04  fof(f53,plain,(
% 2.67/1.04    ( ! [X2,X0,X3,X1] : (k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) )),
% 2.67/1.04    inference(definition_unfolding,[],[f36,f44,f47,f47])).
% 2.67/1.04  
% 2.67/1.04  fof(f12,axiom,(
% 2.67/1.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 2.67/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.04  
% 2.67/1.04  fof(f34,plain,(
% 2.67/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 2.67/1.04    inference(cnf_transformation,[],[f12])).
% 2.67/1.04  
% 2.67/1.04  fof(f51,plain,(
% 2.67/1.04    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1)) )),
% 2.67/1.04    inference(definition_unfolding,[],[f34,f45,f45])).
% 2.67/1.04  
% 2.67/1.04  fof(f4,axiom,(
% 2.67/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 2.67/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.04  
% 2.67/1.04  fof(f26,plain,(
% 2.67/1.04    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 2.67/1.04    inference(cnf_transformation,[],[f4])).
% 2.67/1.04  
% 2.67/1.04  fof(f1,axiom,(
% 2.67/1.04    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.67/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.04  
% 2.67/1.04  fof(f23,plain,(
% 2.67/1.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.67/1.04    inference(cnf_transformation,[],[f1])).
% 2.67/1.04  
% 2.67/1.04  fof(f49,plain,(
% 2.67/1.04    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 2.67/1.04    inference(definition_unfolding,[],[f26,f23,f43,f45])).
% 2.67/1.04  
% 2.67/1.04  fof(f2,axiom,(
% 2.67/1.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 2.67/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.04  
% 2.67/1.04  fof(f24,plain,(
% 2.67/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 2.67/1.04    inference(cnf_transformation,[],[f2])).
% 2.67/1.04  
% 2.67/1.04  fof(f50,plain,(
% 2.67/1.04    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) )),
% 2.67/1.04    inference(definition_unfolding,[],[f24,f45,f45])).
% 2.67/1.04  
% 2.67/1.04  fof(f18,conjecture,(
% 2.67/1.04    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 2.67/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.04  
% 2.67/1.04  fof(f19,negated_conjecture,(
% 2.67/1.04    ~! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 2.67/1.04    inference(negated_conjecture,[],[f18])).
% 2.67/1.04  
% 2.67/1.04  fof(f20,plain,(
% 2.67/1.04    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 2.67/1.04    inference(ennf_transformation,[],[f19])).
% 2.67/1.04  
% 2.67/1.04  fof(f21,plain,(
% 2.67/1.04    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) => k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 2.67/1.04    introduced(choice_axiom,[])).
% 2.67/1.04  
% 2.67/1.04  fof(f22,plain,(
% 2.67/1.04    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 2.67/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f20,f21])).
% 2.67/1.04  
% 2.67/1.04  fof(f41,plain,(
% 2.67/1.04    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 2.67/1.04    inference(cnf_transformation,[],[f22])).
% 2.67/1.04  
% 2.67/1.04  fof(f16,axiom,(
% 2.67/1.04    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 2.67/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.04  
% 2.67/1.04  fof(f39,plain,(
% 2.67/1.04    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 2.67/1.04    inference(cnf_transformation,[],[f16])).
% 2.67/1.04  
% 2.67/1.04  fof(f17,axiom,(
% 2.67/1.04    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 2.67/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.04  
% 2.67/1.04  fof(f40,plain,(
% 2.67/1.04    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 2.67/1.04    inference(cnf_transformation,[],[f17])).
% 2.67/1.04  
% 2.67/1.04  fof(f5,axiom,(
% 2.67/1.04    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.67/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.04  
% 2.67/1.04  fof(f27,plain,(
% 2.67/1.04    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.67/1.04    inference(cnf_transformation,[],[f5])).
% 2.67/1.04  
% 2.67/1.04  fof(f48,plain,(
% 2.67/1.04    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 2.67/1.04    inference(definition_unfolding,[],[f27,f47])).
% 2.67/1.04  
% 2.67/1.04  fof(f56,plain,(
% 2.67/1.04    k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 2.67/1.04    inference(definition_unfolding,[],[f41,f44,f39,f39,f39,f39,f40,f47,f48,f47])).
% 2.67/1.04  
% 2.67/1.04  fof(f15,axiom,(
% 2.67/1.04    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 2.67/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.04  
% 2.67/1.04  fof(f38,plain,(
% 2.67/1.04    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 2.67/1.04    inference(cnf_transformation,[],[f15])).
% 2.67/1.04  
% 2.67/1.04  fof(f54,plain,(
% 2.67/1.04    ( ! [X2,X0,X1] : (k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) )),
% 2.67/1.04    inference(definition_unfolding,[],[f38,f47,f47,f48])).
% 2.67/1.04  
% 2.67/1.04  cnf(c_4,plain,
% 2.67/1.04      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
% 2.67/1.04      inference(cnf_transformation,[],[f53]) ).
% 2.67/1.04  
% 2.67/1.04  cnf(c_23,plain,
% 2.67/1.04      ( k6_enumset1(k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X2_39),k4_tarski(X3_39,X1_39),k4_tarski(X3_39,X2_39)) = k2_zfmisc_1(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X3_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X2_39)) ),
% 2.67/1.04      inference(subtyping,[status(esa)],[c_4]) ).
% 2.67/1.04  
% 2.67/1.04  cnf(c_2,plain,
% 2.67/1.04      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1) ),
% 2.67/1.04      inference(cnf_transformation,[],[f51]) ).
% 2.67/1.04  
% 2.67/1.04  cnf(c_25,plain,
% 2.67/1.04      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39) = k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X2_39,X1_39) ),
% 2.67/1.04      inference(subtyping,[status(esa)],[c_2]) ).
% 2.67/1.04  
% 2.67/1.04  cnf(c_0,plain,
% 2.67/1.04      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 2.67/1.04      inference(cnf_transformation,[],[f49]) ).
% 2.67/1.04  
% 2.67/1.04  cnf(c_27,plain,
% 2.67/1.04      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) ),
% 2.67/1.04      inference(subtyping,[status(esa)],[c_0]) ).
% 2.67/1.04  
% 2.67/1.04  cnf(c_149,plain,
% 2.67/1.04      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X7_39,X6_39) ),
% 2.67/1.04      inference(superposition,[status(thm)],[c_25,c_27]) ).
% 2.67/1.04  
% 2.67/1.04  cnf(c_513,plain,
% 2.67/1.04      ( k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X7_39,X6_39) ),
% 2.67/1.04      inference(superposition,[status(thm)],[c_149,c_27]) ).
% 2.67/1.04  
% 2.67/1.04  cnf(c_1,plain,
% 2.67/1.04      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X0,X1) ),
% 2.67/1.04      inference(cnf_transformation,[],[f50]) ).
% 2.67/1.04  
% 2.67/1.04  cnf(c_26,plain,
% 2.67/1.04      ( k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39) = k6_enumset1(X2_39,X2_39,X2_39,X2_39,X2_39,X2_39,X0_39,X1_39) ),
% 2.67/1.04      inference(subtyping,[status(esa)],[c_1]) ).
% 2.67/1.04  
% 2.67/1.04  cnf(c_151,plain,
% 2.67/1.04      ( k5_xboole_0(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39),k4_xboole_0(k6_enumset1(X5_39,X5_39,X5_39,X5_39,X5_39,X5_39,X6_39,X7_39),k6_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39,X4_39))) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X7_39,X5_39,X6_39) ),
% 2.67/1.04      inference(superposition,[status(thm)],[c_26,c_27]) ).
% 2.67/1.04  
% 2.67/1.04  cnf(c_621,plain,
% 2.67/1.04      ( k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39,X7_39) = k6_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X6_39,X7_39,X5_39) ),
% 2.67/1.04      inference(superposition,[status(thm)],[c_27,c_151]) ).
% 2.67/1.04  
% 2.67/1.04  cnf(c_7,negated_conjecture,
% 2.67/1.04      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 2.67/1.04      inference(cnf_transformation,[],[f56]) ).
% 2.67/1.04  
% 2.67/1.04  cnf(c_20,negated_conjecture,
% 2.67/1.04      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 2.67/1.04      inference(subtyping,[status(esa)],[c_7]) ).
% 2.67/1.04  
% 2.67/1.04  cnf(c_666,plain,
% 2.67/1.04      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 2.67/1.04      inference(demodulation,[status(thm)],[c_621,c_20]) ).
% 2.67/1.04  
% 2.67/1.04  cnf(c_779,plain,
% 2.67/1.04      ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 2.67/1.04      inference(superposition,[status(thm)],[c_513,c_666]) ).
% 2.67/1.04  
% 2.67/1.04  cnf(c_781,plain,
% 2.67/1.04      ( k2_zfmisc_1(k6_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 2.67/1.04      inference(superposition,[status(thm)],[c_23,c_779]) ).
% 2.67/1.04  
% 2.67/1.04  cnf(c_5,plain,
% 2.67/1.04      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
% 2.67/1.04      inference(cnf_transformation,[],[f54]) ).
% 2.67/1.04  
% 2.67/1.04  cnf(c_22,plain,
% 2.67/1.04      ( k6_enumset1(k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X1_39),k4_tarski(X2_39,X1_39)) = k2_zfmisc_1(k6_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X0_39,X2_39),k6_enumset1(X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39,X1_39)) ),
% 2.67/1.04      inference(subtyping,[status(esa)],[c_5]) ).
% 2.67/1.04  
% 2.67/1.04  cnf(c_782,plain,
% 2.67/1.04      ( k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 2.67/1.04      inference(demodulation,[status(thm)],[c_781,c_22]) ).
% 2.67/1.04  
% 2.67/1.04  cnf(c_783,plain,
% 2.67/1.04      ( $false ),
% 2.67/1.04      inference(equality_resolution_simp,[status(thm)],[c_782]) ).
% 2.67/1.04  
% 2.67/1.04  
% 2.67/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 2.67/1.04  
% 2.67/1.04  ------                               Statistics
% 2.67/1.04  
% 2.67/1.04  ------ General
% 2.67/1.04  
% 2.67/1.04  abstr_ref_over_cycles:                  0
% 2.67/1.04  abstr_ref_under_cycles:                 0
% 2.67/1.04  gc_basic_clause_elim:                   0
% 2.67/1.04  forced_gc_time:                         0
% 2.67/1.04  parsing_time:                           0.008
% 2.67/1.04  unif_index_cands_time:                  0.
% 2.67/1.04  unif_index_add_time:                    0.
% 2.67/1.04  orderings_time:                         0.
% 2.67/1.04  out_proof_time:                         0.024
% 2.67/1.04  total_time:                             0.093
% 2.67/1.04  num_of_symbols:                         44
% 2.67/1.04  num_of_terms:                           1142
% 2.67/1.04  
% 2.67/1.04  ------ Preprocessing
% 2.67/1.04  
% 2.67/1.04  num_of_splits:                          0
% 2.67/1.04  num_of_split_atoms:                     0
% 2.67/1.04  num_of_reused_defs:                     0
% 2.67/1.04  num_eq_ax_congr_red:                    0
% 2.67/1.04  num_of_sem_filtered_clauses:            0
% 2.67/1.04  num_of_subtypes:                        2
% 2.67/1.04  monotx_restored_types:                  0
% 2.67/1.04  sat_num_of_epr_types:                   0
% 2.67/1.04  sat_num_of_non_cyclic_types:            0
% 2.67/1.04  sat_guarded_non_collapsed_types:        0
% 2.67/1.04  num_pure_diseq_elim:                    0
% 2.67/1.04  simp_replaced_by:                       0
% 2.67/1.04  res_preprocessed:                       25
% 2.67/1.04  prep_upred:                             0
% 2.67/1.04  prep_unflattend:                        0
% 2.67/1.04  smt_new_axioms:                         0
% 2.67/1.04  pred_elim_cands:                        0
% 2.67/1.04  pred_elim:                              0
% 2.67/1.04  pred_elim_cl:                           0
% 2.67/1.04  pred_elim_cycles:                       0
% 2.67/1.04  merged_defs:                            0
% 2.67/1.04  merged_defs_ncl:                        0
% 2.67/1.04  bin_hyper_res:                          0
% 2.67/1.04  prep_cycles:                            2
% 2.67/1.04  pred_elim_time:                         0.
% 2.67/1.04  splitting_time:                         0.
% 2.67/1.04  sem_filter_time:                        0.
% 2.67/1.04  monotx_time:                            0.
% 2.67/1.04  subtype_inf_time:                       0.
% 2.67/1.04  
% 2.67/1.04  ------ Problem properties
% 2.67/1.04  
% 2.67/1.04  clauses:                                8
% 2.67/1.04  conjectures:                            1
% 2.67/1.04  epr:                                    0
% 2.67/1.04  horn:                                   8
% 2.67/1.04  ground:                                 1
% 2.67/1.04  unary:                                  8
% 2.67/1.04  binary:                                 0
% 2.67/1.04  lits:                                   8
% 2.67/1.04  lits_eq:                                8
% 2.67/1.04  fd_pure:                                0
% 2.67/1.04  fd_pseudo:                              0
% 2.67/1.04  fd_cond:                                0
% 2.67/1.04  fd_pseudo_cond:                         0
% 2.67/1.04  ac_symbols:                             0
% 2.67/1.04  
% 2.67/1.04  ------ Propositional Solver
% 2.67/1.04  
% 2.67/1.04  prop_solver_calls:                      13
% 2.67/1.04  prop_fast_solver_calls:                 88
% 2.67/1.04  smt_solver_calls:                       0
% 2.67/1.04  smt_fast_solver_calls:                  0
% 2.67/1.04  prop_num_of_clauses:                    69
% 2.67/1.04  prop_preprocess_simplified:             347
% 2.67/1.04  prop_fo_subsumed:                       0
% 2.67/1.04  prop_solver_time:                       0.
% 2.67/1.04  smt_solver_time:                        0.
% 2.67/1.04  smt_fast_solver_time:                   0.
% 2.67/1.04  prop_fast_solver_time:                  0.
% 2.67/1.04  prop_unsat_core_time:                   0.
% 2.67/1.04  
% 2.67/1.04  ------ QBF
% 2.67/1.04  
% 2.67/1.04  qbf_q_res:                              0
% 2.67/1.04  qbf_num_tautologies:                    0
% 2.67/1.04  qbf_prep_cycles:                        0
% 2.67/1.04  
% 2.67/1.04  ------ BMC1
% 2.67/1.04  
% 2.67/1.04  bmc1_current_bound:                     -1
% 2.67/1.04  bmc1_last_solved_bound:                 -1
% 2.67/1.04  bmc1_unsat_core_size:                   -1
% 2.67/1.04  bmc1_unsat_core_parents_size:           -1
% 2.67/1.04  bmc1_merge_next_fun:                    0
% 2.67/1.04  bmc1_unsat_core_clauses_time:           0.
% 2.67/1.04  
% 2.67/1.04  ------ Instantiation
% 2.67/1.04  
% 2.67/1.04  inst_num_of_clauses:                    0
% 2.67/1.04  inst_num_in_passive:                    0
% 2.67/1.04  inst_num_in_active:                     0
% 2.67/1.04  inst_num_in_unprocessed:                0
% 2.67/1.04  inst_num_of_loops:                      0
% 2.67/1.04  inst_num_of_learning_restarts:          0
% 2.67/1.04  inst_num_moves_active_passive:          0
% 2.67/1.04  inst_lit_activity:                      0
% 2.67/1.04  inst_lit_activity_moves:                0
% 2.67/1.04  inst_num_tautologies:                   0
% 2.67/1.04  inst_num_prop_implied:                  0
% 2.67/1.04  inst_num_existing_simplified:           0
% 2.67/1.04  inst_num_eq_res_simplified:             0
% 2.67/1.04  inst_num_child_elim:                    0
% 2.67/1.04  inst_num_of_dismatching_blockings:      0
% 2.67/1.04  inst_num_of_non_proper_insts:           0
% 2.67/1.04  inst_num_of_duplicates:                 0
% 2.67/1.04  inst_inst_num_from_inst_to_res:         0
% 2.67/1.04  inst_dismatching_checking_time:         0.
% 2.67/1.04  
% 2.67/1.04  ------ Resolution
% 2.67/1.04  
% 2.67/1.04  res_num_of_clauses:                     0
% 2.67/1.04  res_num_in_passive:                     0
% 2.67/1.04  res_num_in_active:                      0
% 2.67/1.04  res_num_of_loops:                       27
% 2.67/1.04  res_forward_subset_subsumed:            0
% 2.67/1.04  res_backward_subset_subsumed:           0
% 2.67/1.04  res_forward_subsumed:                   0
% 2.67/1.04  res_backward_subsumed:                  0
% 2.67/1.04  res_forward_subsumption_resolution:     0
% 2.67/1.04  res_backward_subsumption_resolution:    0
% 2.67/1.04  res_clause_to_clause_subsumption:       1341
% 2.67/1.04  res_orphan_elimination:                 0
% 2.67/1.04  res_tautology_del:                      0
% 2.67/1.04  res_num_eq_res_simplified:              0
% 2.67/1.04  res_num_sel_changes:                    0
% 2.67/1.04  res_moves_from_active_to_pass:          0
% 2.67/1.04  
% 2.67/1.04  ------ Superposition
% 2.67/1.04  
% 2.67/1.04  sup_time_total:                         0.
% 2.67/1.04  sup_time_generating:                    0.
% 2.67/1.04  sup_time_sim_full:                      0.
% 2.67/1.04  sup_time_sim_immed:                     0.
% 2.67/1.04  
% 2.67/1.04  sup_num_of_clauses:                     145
% 2.67/1.04  sup_num_in_active:                      31
% 2.67/1.04  sup_num_in_passive:                     114
% 2.67/1.04  sup_num_of_loops:                       32
% 2.67/1.04  sup_fw_superposition:                   431
% 2.67/1.04  sup_bw_superposition:                   295
% 2.67/1.04  sup_immediate_simplified:               9
% 2.67/1.04  sup_given_eliminated:                   0
% 2.67/1.04  comparisons_done:                       0
% 2.67/1.04  comparisons_avoided:                    0
% 2.67/1.04  
% 2.67/1.04  ------ Simplifications
% 2.67/1.04  
% 2.67/1.04  
% 2.67/1.04  sim_fw_subset_subsumed:                 0
% 2.67/1.04  sim_bw_subset_subsumed:                 0
% 2.67/1.04  sim_fw_subsumed:                        1
% 2.67/1.04  sim_bw_subsumed:                        6
% 2.67/1.04  sim_fw_subsumption_res:                 0
% 2.67/1.04  sim_bw_subsumption_res:                 0
% 2.67/1.04  sim_tautology_del:                      0
% 2.67/1.04  sim_eq_tautology_del:                   1
% 2.67/1.04  sim_eq_res_simp:                        0
% 2.67/1.04  sim_fw_demodulated:                     1
% 2.67/1.04  sim_bw_demodulated:                     1
% 2.67/1.04  sim_light_normalised:                   3
% 2.67/1.04  sim_joinable_taut:                      0
% 2.67/1.04  sim_joinable_simp:                      0
% 2.67/1.04  sim_ac_normalised:                      0
% 2.67/1.04  sim_smt_subsumption:                    0
% 2.67/1.04  
%------------------------------------------------------------------------------
