%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:21 EST 2020

% Result     : Theorem 15.41s
% Output     : CNFRefutation 15.41s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 653 expanded)
%              Number of clauses        :   28 (  56 expanded)
%              Number of leaves         :   15 ( 227 expanded)
%              Depth                    :   14
%              Number of atoms          :   73 ( 656 expanded)
%              Number of equality atoms :   72 ( 655 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f34])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f36,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f23,f34])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3))) ),
    inference(definition_unfolding,[],[f21,f35,f25,f36])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) ),
    inference(definition_unfolding,[],[f20,f35,f34,f34])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f19,f35,f35])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)) ),
    inference(definition_unfolding,[],[f28,f34,f34])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(definition_unfolding,[],[f30,f34,f34,f36])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X3,X4))) ),
    inference(definition_unfolding,[],[f22,f35,f34,f25])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X3))) ),
    inference(definition_unfolding,[],[f26,f37])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) ),
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) ),
    inference(ennf_transformation,[],[f15])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))
   => k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f17])).

fof(f33,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f33,f31,f31,f31,f31,f32,f34,f36,f34])).

cnf(c_2,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_0,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_630,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) = k2_enumset1(X2,X3,X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_1])).

cnf(c_7653,plain,
    ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X1,X1,X2,X0) ),
    inference(superposition,[status(thm)],[c_2,c_630])).

cnf(c_4,plain,
    ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X3),k2_enumset1(X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_7915,plain,
    ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k2_enumset1(X2,X2,X2,X0),k2_enumset1(X1,X1,X1,X1)) ),
    inference(superposition,[status(thm)],[c_7653,c_4])).

cnf(c_5,plain,
    ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X2),k2_enumset1(X1,X1,X1,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_12813,plain,
    ( k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) = k2_zfmisc_1(k2_enumset1(X1,X1,X1,X0),k2_enumset1(X2,X2,X2,X2)) ),
    inference(superposition,[status(thm)],[c_7915,c_5])).

cnf(c_670,plain,
    ( k2_enumset1(X0,X1,X2,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_3,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_752,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2))) = k2_enumset1(X0,X1,X2,X2) ),
    inference(superposition,[status(thm)],[c_670,c_3])).

cnf(c_769,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X2,X3,X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(superposition,[status(thm)],[c_670,c_3])).

cnf(c_43485,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X3))))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(superposition,[status(thm)],[c_752,c_769])).

cnf(c_671,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X3))) = k2_enumset1(X1,X2,X3,X0) ),
    inference(superposition,[status(thm)],[c_2,c_1])).

cnf(c_43610,plain,
    ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X0,X1) ),
    inference(demodulation,[status(thm)],[c_43485,c_671])).

cnf(c_46661,plain,
    ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X2),k4_tarski(X3,X1)) = k2_zfmisc_1(k2_enumset1(X3,X3,X3,X0),k2_enumset1(X1,X1,X1,X2)) ),
    inference(superposition,[status(thm)],[c_43610,c_4])).

cnf(c_32377,plain,
    ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    inference(superposition,[status(thm)],[c_671,c_3])).

cnf(c_765,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X1,X2,X2),k2_enumset1(X0,X1,X2,X2),k2_enumset1(X0,X1,X2,X2),k2_enumset1(X3,X3,X3,X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(superposition,[status(thm)],[c_670,c_2])).

cnf(c_42567,plain,
    ( k3_tarski(k2_enumset1(k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2))),k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2))),k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2))),k2_enumset1(X3,X3,X3,X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(superposition,[status(thm)],[c_752,c_765])).

cnf(c_716,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3))) = k2_enumset1(X3,X0,X1,X2) ),
    inference(superposition,[status(thm)],[c_3,c_1])).

cnf(c_42734,plain,
    ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
    inference(demodulation,[status(thm)],[c_42567,c_671,c_716])).

cnf(c_44290,plain,
    ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X1,X2) ),
    inference(superposition,[status(thm)],[c_32377,c_42734])).

cnf(c_7,negated_conjecture,
    ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_50501,plain,
    ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_44290,c_7])).

cnf(c_55246,plain,
    ( k2_zfmisc_1(k2_enumset1(k4_tarski(sK1,sK2),k4_tarski(sK1,sK2),k4_tarski(sK1,sK2),k4_tarski(sK0,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_46661,c_50501])).

cnf(c_55252,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK0),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_55246,c_5])).

cnf(c_55441,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_12813,c_55252])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:00:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.41/2.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.41/2.48  
% 15.41/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.41/2.48  
% 15.41/2.48  ------  iProver source info
% 15.41/2.48  
% 15.41/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.41/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.41/2.48  git: non_committed_changes: false
% 15.41/2.48  git: last_make_outside_of_git: false
% 15.41/2.48  
% 15.41/2.48  ------ 
% 15.41/2.48  ------ Parsing...
% 15.41/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.41/2.48  
% 15.41/2.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 15.41/2.48  
% 15.41/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.41/2.48  
% 15.41/2.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.41/2.48  ------ Proving...
% 15.41/2.48  ------ Problem Properties 
% 15.41/2.48  
% 15.41/2.48  
% 15.41/2.48  clauses                                 8
% 15.41/2.48  conjectures                             1
% 15.41/2.48  EPR                                     0
% 15.41/2.48  Horn                                    8
% 15.41/2.48  unary                                   8
% 15.41/2.48  binary                                  0
% 15.41/2.48  lits                                    8
% 15.41/2.48  lits eq                                 8
% 15.41/2.48  fd_pure                                 0
% 15.41/2.48  fd_pseudo                               0
% 15.41/2.48  fd_cond                                 0
% 15.41/2.48  fd_pseudo_cond                          0
% 15.41/2.48  AC symbols                              0
% 15.41/2.48  
% 15.41/2.48  ------ Input Options Time Limit: Unbounded
% 15.41/2.48  
% 15.41/2.48  
% 15.41/2.48  
% 15.41/2.48  
% 15.41/2.48  ------ Preprocessing...
% 15.41/2.48  
% 15.41/2.48  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 15.41/2.48  Current options:
% 15.41/2.48  ------ 
% 15.41/2.48  
% 15.41/2.48  
% 15.41/2.48  
% 15.41/2.48  
% 15.41/2.48  ------ Proving...
% 15.41/2.48  
% 15.41/2.48  
% 15.41/2.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.41/2.48  
% 15.41/2.48  ------ Proving...
% 15.41/2.48  
% 15.41/2.48  
% 15.41/2.48  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.41/2.48  
% 15.41/2.48  ------ Proving...
% 15.41/2.48  
% 15.41/2.48  
% 15.41/2.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.41/2.48  
% 15.41/2.48  ------ Proving...
% 15.41/2.48  
% 15.41/2.48  
% 15.41/2.48  ------ Preprocessing...
% 15.41/2.48  
% 15.41/2.48  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.41/2.48  
% 15.41/2.48  ------ Proving...
% 15.41/2.48  
% 15.41/2.48  
% 15.41/2.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.41/2.48  
% 15.41/2.48  ------ Proving...
% 15.41/2.48  
% 15.41/2.48  
% 15.41/2.48  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.41/2.48  
% 15.41/2.48  ------ Proving...
% 15.41/2.48  
% 15.41/2.48  
% 15.41/2.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.41/2.48  
% 15.41/2.48  ------ Proving...
% 15.41/2.48  
% 15.41/2.48  
% 15.41/2.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.41/2.48  
% 15.41/2.48  ------ Proving...
% 15.41/2.48  
% 15.41/2.48  
% 15.41/2.48  % SZS status Theorem for theBenchmark.p
% 15.41/2.48  
% 15.41/2.48   Resolution empty clause
% 15.41/2.48  
% 15.41/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.41/2.48  
% 15.41/2.48  fof(f3,axiom,(
% 15.41/2.48    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 15.41/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.48  
% 15.41/2.48  fof(f21,plain,(
% 15.41/2.48    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 15.41/2.48    inference(cnf_transformation,[],[f3])).
% 15.41/2.48  
% 15.41/2.48  fof(f9,axiom,(
% 15.41/2.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 15.41/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.48  
% 15.41/2.48  fof(f27,plain,(
% 15.41/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 15.41/2.48    inference(cnf_transformation,[],[f9])).
% 15.41/2.48  
% 15.41/2.48  fof(f35,plain,(
% 15.41/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 15.41/2.48    inference(definition_unfolding,[],[f27,f34])).
% 15.41/2.48  
% 15.41/2.48  fof(f5,axiom,(
% 15.41/2.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.41/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.48  
% 15.41/2.48  fof(f23,plain,(
% 15.41/2.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.41/2.48    inference(cnf_transformation,[],[f5])).
% 15.41/2.48  
% 15.41/2.48  fof(f6,axiom,(
% 15.41/2.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 15.41/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.48  
% 15.41/2.48  fof(f24,plain,(
% 15.41/2.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 15.41/2.48    inference(cnf_transformation,[],[f6])).
% 15.41/2.48  
% 15.41/2.48  fof(f7,axiom,(
% 15.41/2.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 15.41/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.48  
% 15.41/2.48  fof(f25,plain,(
% 15.41/2.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 15.41/2.48    inference(cnf_transformation,[],[f7])).
% 15.41/2.48  
% 15.41/2.48  fof(f34,plain,(
% 15.41/2.48    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.41/2.48    inference(definition_unfolding,[],[f24,f25])).
% 15.41/2.48  
% 15.41/2.48  fof(f36,plain,(
% 15.41/2.48    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 15.41/2.48    inference(definition_unfolding,[],[f23,f34])).
% 15.41/2.48  
% 15.41/2.48  fof(f40,plain,(
% 15.41/2.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)))) )),
% 15.41/2.48    inference(definition_unfolding,[],[f21,f35,f25,f36])).
% 15.41/2.48  
% 15.41/2.48  fof(f2,axiom,(
% 15.41/2.48    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 15.41/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.48  
% 15.41/2.48  fof(f20,plain,(
% 15.41/2.48    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 15.41/2.48    inference(cnf_transformation,[],[f2])).
% 15.41/2.48  
% 15.41/2.48  fof(f38,plain,(
% 15.41/2.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)))) )),
% 15.41/2.48    inference(definition_unfolding,[],[f20,f35,f34,f34])).
% 15.41/2.48  
% 15.41/2.48  fof(f1,axiom,(
% 15.41/2.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 15.41/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.48  
% 15.41/2.48  fof(f19,plain,(
% 15.41/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 15.41/2.48    inference(cnf_transformation,[],[f1])).
% 15.41/2.48  
% 15.41/2.48  fof(f39,plain,(
% 15.41/2.48    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0))) )),
% 15.41/2.48    inference(definition_unfolding,[],[f19,f35,f35])).
% 15.41/2.48  
% 15.41/2.48  fof(f10,axiom,(
% 15.41/2.48    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 15.41/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.48  
% 15.41/2.48  fof(f28,plain,(
% 15.41/2.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 15.41/2.48    inference(cnf_transformation,[],[f10])).
% 15.41/2.48  
% 15.41/2.48  fof(f42,plain,(
% 15.41/2.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) )),
% 15.41/2.48    inference(definition_unfolding,[],[f28,f34,f34])).
% 15.41/2.48  
% 15.41/2.48  fof(f11,axiom,(
% 15.41/2.48    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 15.41/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.48  
% 15.41/2.48  fof(f30,plain,(
% 15.41/2.48    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 15.41/2.48    inference(cnf_transformation,[],[f11])).
% 15.41/2.48  
% 15.41/2.48  fof(f43,plain,(
% 15.41/2.48    ( ! [X2,X0,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2))) )),
% 15.41/2.48    inference(definition_unfolding,[],[f30,f34,f34,f36])).
% 15.41/2.48  
% 15.41/2.48  fof(f8,axiom,(
% 15.41/2.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 15.41/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.48  
% 15.41/2.48  fof(f26,plain,(
% 15.41/2.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 15.41/2.48    inference(cnf_transformation,[],[f8])).
% 15.41/2.48  
% 15.41/2.48  fof(f4,axiom,(
% 15.41/2.48    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 15.41/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.48  
% 15.41/2.48  fof(f22,plain,(
% 15.41/2.48    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 15.41/2.48    inference(cnf_transformation,[],[f4])).
% 15.41/2.48  
% 15.41/2.48  fof(f37,plain,(
% 15.41/2.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X3,X4)))) )),
% 15.41/2.48    inference(definition_unfolding,[],[f22,f35,f34,f25])).
% 15.41/2.48  
% 15.41/2.48  fof(f41,plain,(
% 15.41/2.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X3)))) )),
% 15.41/2.48    inference(definition_unfolding,[],[f26,f37])).
% 15.41/2.48  
% 15.41/2.48  fof(f14,conjecture,(
% 15.41/2.48    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 15.41/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.48  
% 15.41/2.48  fof(f15,negated_conjecture,(
% 15.41/2.48    ~! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 15.41/2.48    inference(negated_conjecture,[],[f14])).
% 15.41/2.48  
% 15.41/2.48  fof(f16,plain,(
% 15.41/2.48    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 15.41/2.48    inference(ennf_transformation,[],[f15])).
% 15.41/2.48  
% 15.41/2.48  fof(f17,plain,(
% 15.41/2.48    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) => k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 15.41/2.48    introduced(choice_axiom,[])).
% 15.41/2.48  
% 15.41/2.48  fof(f18,plain,(
% 15.41/2.48    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 15.41/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f17])).
% 15.41/2.48  
% 15.41/2.48  fof(f33,plain,(
% 15.41/2.48    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 15.41/2.48    inference(cnf_transformation,[],[f18])).
% 15.41/2.48  
% 15.41/2.48  fof(f12,axiom,(
% 15.41/2.48    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 15.41/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.48  
% 15.41/2.48  fof(f31,plain,(
% 15.41/2.48    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 15.41/2.48    inference(cnf_transformation,[],[f12])).
% 15.41/2.48  
% 15.41/2.48  fof(f13,axiom,(
% 15.41/2.48    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 15.41/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.48  
% 15.41/2.48  fof(f32,plain,(
% 15.41/2.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 15.41/2.48    inference(cnf_transformation,[],[f13])).
% 15.41/2.48  
% 15.41/2.48  fof(f45,plain,(
% 15.41/2.48    k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4))),
% 15.41/2.48    inference(definition_unfolding,[],[f33,f31,f31,f31,f31,f32,f34,f36,f34])).
% 15.41/2.48  
% 15.41/2.48  cnf(c_2,plain,
% 15.41/2.48      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3))) = k2_enumset1(X0,X1,X2,X3) ),
% 15.41/2.48      inference(cnf_transformation,[],[f40]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_0,plain,
% 15.41/2.48      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) = k2_enumset1(X0,X1,X2,X3) ),
% 15.41/2.48      inference(cnf_transformation,[],[f38]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_1,plain,
% 15.41/2.48      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
% 15.41/2.48      inference(cnf_transformation,[],[f39]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_630,plain,
% 15.41/2.48      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) = k2_enumset1(X2,X3,X0,X1) ),
% 15.41/2.48      inference(superposition,[status(thm)],[c_0,c_1]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_7653,plain,
% 15.41/2.48      ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X1,X1,X2,X0) ),
% 15.41/2.48      inference(superposition,[status(thm)],[c_2,c_630]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_4,plain,
% 15.41/2.48      ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X3),k2_enumset1(X1,X1,X1,X2)) ),
% 15.41/2.48      inference(cnf_transformation,[],[f42]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_7915,plain,
% 15.41/2.48      ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k2_enumset1(X2,X2,X2,X0),k2_enumset1(X1,X1,X1,X1)) ),
% 15.41/2.48      inference(superposition,[status(thm)],[c_7653,c_4]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_5,plain,
% 15.41/2.48      ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X2),k2_enumset1(X1,X1,X1,X1)) ),
% 15.41/2.48      inference(cnf_transformation,[],[f43]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_12813,plain,
% 15.41/2.48      ( k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) = k2_zfmisc_1(k2_enumset1(X1,X1,X1,X0),k2_enumset1(X2,X2,X2,X2)) ),
% 15.41/2.48      inference(superposition,[status(thm)],[c_7915,c_5]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_670,plain,
% 15.41/2.48      ( k2_enumset1(X0,X1,X2,X2) = k2_enumset1(X0,X0,X1,X2) ),
% 15.41/2.48      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_3,plain,
% 15.41/2.48      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X3))) = k2_enumset1(X0,X1,X2,X3) ),
% 15.41/2.48      inference(cnf_transformation,[],[f41]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_752,plain,
% 15.41/2.48      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2))) = k2_enumset1(X0,X1,X2,X2) ),
% 15.41/2.48      inference(superposition,[status(thm)],[c_670,c_3]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_769,plain,
% 15.41/2.48      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X2,X3,X3))) = k2_enumset1(X0,X1,X2,X3) ),
% 15.41/2.48      inference(superposition,[status(thm)],[c_670,c_3]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_43485,plain,
% 15.41/2.48      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X3))))) = k2_enumset1(X0,X1,X2,X3) ),
% 15.41/2.48      inference(superposition,[status(thm)],[c_752,c_769]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_671,plain,
% 15.41/2.48      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X3))) = k2_enumset1(X1,X2,X3,X0) ),
% 15.41/2.48      inference(superposition,[status(thm)],[c_2,c_1]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_43610,plain,
% 15.41/2.48      ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X0,X1) ),
% 15.41/2.48      inference(demodulation,[status(thm)],[c_43485,c_671]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_46661,plain,
% 15.41/2.48      ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X2),k4_tarski(X3,X1)) = k2_zfmisc_1(k2_enumset1(X3,X3,X3,X0),k2_enumset1(X1,X1,X1,X2)) ),
% 15.41/2.48      inference(superposition,[status(thm)],[c_43610,c_4]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_32377,plain,
% 15.41/2.48      ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
% 15.41/2.48      inference(superposition,[status(thm)],[c_671,c_3]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_765,plain,
% 15.41/2.48      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X1,X2,X2),k2_enumset1(X0,X1,X2,X2),k2_enumset1(X0,X1,X2,X2),k2_enumset1(X3,X3,X3,X3))) = k2_enumset1(X0,X1,X2,X3) ),
% 15.41/2.48      inference(superposition,[status(thm)],[c_670,c_2]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_42567,plain,
% 15.41/2.48      ( k3_tarski(k2_enumset1(k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2))),k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2))),k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2))),k2_enumset1(X3,X3,X3,X3))) = k2_enumset1(X0,X1,X2,X3) ),
% 15.41/2.48      inference(superposition,[status(thm)],[c_752,c_765]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_716,plain,
% 15.41/2.48      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3))) = k2_enumset1(X3,X0,X1,X2) ),
% 15.41/2.48      inference(superposition,[status(thm)],[c_3,c_1]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_42734,plain,
% 15.41/2.48      ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
% 15.41/2.48      inference(demodulation,[status(thm)],[c_42567,c_671,c_716]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_44290,plain,
% 15.41/2.48      ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X1,X2) ),
% 15.41/2.48      inference(superposition,[status(thm)],[c_32377,c_42734]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_7,negated_conjecture,
% 15.41/2.48      ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 15.41/2.48      inference(cnf_transformation,[],[f45]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_50501,plain,
% 15.41/2.48      ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 15.41/2.48      inference(demodulation,[status(thm)],[c_44290,c_7]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_55246,plain,
% 15.41/2.48      ( k2_zfmisc_1(k2_enumset1(k4_tarski(sK1,sK2),k4_tarski(sK1,sK2),k4_tarski(sK1,sK2),k4_tarski(sK0,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 15.41/2.48      inference(superposition,[status(thm)],[c_46661,c_50501]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_55252,plain,
% 15.41/2.48      ( k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK0),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 15.41/2.48      inference(demodulation,[status(thm)],[c_55246,c_5]) ).
% 15.41/2.48  
% 15.41/2.48  cnf(c_55441,plain,
% 15.41/2.48      ( $false ),
% 15.41/2.48      inference(superposition,[status(thm)],[c_12813,c_55252]) ).
% 15.41/2.48  
% 15.41/2.48  
% 15.41/2.48  % SZS output end CNFRefutation for theBenchmark.p
% 15.41/2.48  
% 15.41/2.48  ------                               Statistics
% 15.41/2.48  
% 15.41/2.48  ------ Selected
% 15.41/2.48  
% 15.41/2.48  total_time:                             1.755
% 15.41/2.48  
%------------------------------------------------------------------------------
