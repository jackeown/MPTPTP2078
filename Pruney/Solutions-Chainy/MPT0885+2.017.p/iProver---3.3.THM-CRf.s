%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:28 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :   77 (3147 expanded)
%              Number of clauses        :   34 ( 214 expanded)
%              Number of leaves         :   15 (1113 expanded)
%              Depth                    :   21
%              Number of atoms          :   79 (3155 expanded)
%              Number of equality atoms :   78 (3154 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f23,f34])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) ),
    inference(definition_unfolding,[],[f29,f34,f37,f34])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)) ),
    inference(definition_unfolding,[],[f28,f34,f34])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f34])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X3,X4))) ),
    inference(definition_unfolding,[],[f21,f35,f34,f25])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X3))) ),
    inference(definition_unfolding,[],[f26,f36])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) ),
    inference(definition_unfolding,[],[f20,f35,f34,f34])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X3,X4))) = k3_tarski(k2_enumset1(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X0,X1,X2,X3),k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X4,X4,X4))) ),
    inference(definition_unfolding,[],[f22,f35,f37,f36])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f19,f35,f35])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(ennf_transformation,[],[f15])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))
   => k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f17])).

fof(f33,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f33,f31,f31,f31,f31,f32,f37,f34,f34])).

cnf(c_6,plain,
    ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4,plain,
    ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X3),k2_enumset1(X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_40,plain,
    ( k2_enumset1(k4_tarski(k4_tarski(X0,X1),X2),k4_tarski(k4_tarski(X0,X1),X3),k4_tarski(k4_tarski(X0,X4),X2),k4_tarski(k4_tarski(X0,X4),X3)) = k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X4)),k2_enumset1(X2,X2,X2,X3)) ),
    inference(superposition,[status(thm)],[c_6,c_4])).

cnf(c_3,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_0,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_159,plain,
    ( k2_enumset1(X0,X1,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_236,plain,
    ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X2,X1),k4_tarski(X2,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X2),k2_enumset1(X1,X1,X1,X1)) ),
    inference(superposition,[status(thm)],[c_159,c_4])).

cnf(c_2,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X0,X1,X2,X3),k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X4,X4,X4))) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X3,X4))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_260,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X1,k4_tarski(X2,X3),k4_tarski(X2,X3)),k2_enumset1(X0,X1,k4_tarski(X2,X3),k4_tarski(X2,X3)),k2_enumset1(X0,X1,k4_tarski(X2,X3),k4_tarski(X2,X3)),k2_enumset1(k4_tarski(X2,X3),k4_tarski(X2,X3),k4_tarski(X2,X3),k4_tarski(X2,X3)))) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)))) ),
    inference(superposition,[status(thm)],[c_236,c_2])).

cnf(c_136,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X4)))) = k2_enumset1(X0,X1,k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_212,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X1,X2,X2),k2_enumset1(X0,X1,X2,X2),k2_enumset1(X0,X1,X2,X2),k2_enumset1(X2,X2,X2,X2))) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X1,X2))) ),
    inference(superposition,[status(thm)],[c_2,c_2])).

cnf(c_214,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X1,X2,X2),k2_enumset1(X0,X1,X2,X2),k2_enumset1(X0,X1,X2,X2),k2_enumset1(X2,X2,X2,X2))) = k2_enumset1(X0,X0,X1,X2) ),
    inference(demodulation,[status(thm)],[c_212,c_3])).

cnf(c_282,plain,
    ( k2_enumset1(X0,X1,k4_tarski(X2,X3),k4_tarski(X2,X3)) = k2_enumset1(X0,X0,X1,k4_tarski(X2,X3)) ),
    inference(demodulation,[status(thm)],[c_260,c_136,c_214])).

cnf(c_295,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X1,k4_tarski(X2,X3)),k2_enumset1(X0,X0,X1,k4_tarski(X2,X3)),k2_enumset1(X0,X0,X1,k4_tarski(X2,X3)),k2_enumset1(X4,X4,X4,X4))) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(k4_tarski(X2,X3),k4_tarski(X2,X3),k4_tarski(X2,X3),X4))) ),
    inference(superposition,[status(thm)],[c_282,c_2])).

cnf(c_1,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_138,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) = k2_enumset1(X2,X3,X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_1])).

cnf(c_213,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(superposition,[status(thm)],[c_2,c_3])).

cnf(c_337,plain,
    ( k2_enumset1(k4_tarski(X0,X1),X2,X3,X4) = k2_enumset1(X3,X4,k4_tarski(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_295,c_138,c_213])).

cnf(c_380,plain,
    ( k2_enumset1(X0,X1,k4_tarski(X2,X3),k4_tarski(X2,X3)) = k2_enumset1(k4_tarski(X2,X3),X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_337,c_159])).

cnf(c_504,plain,
    ( k2_enumset1(X0,X0,X1,k4_tarski(X2,X3)) = k2_enumset1(k4_tarski(X2,X3),X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_380,c_282])).

cnf(c_495,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(k4_tarski(X2,X3),k4_tarski(X2,X3),k4_tarski(X2,X3),X4))) = k3_tarski(k2_enumset1(k2_enumset1(k4_tarski(X2,X3),X0,X0,X1),k2_enumset1(k4_tarski(X2,X3),X0,X0,X1),k2_enumset1(k4_tarski(X2,X3),X0,X0,X1),k2_enumset1(X4,X4,X4,X4))) ),
    inference(superposition,[status(thm)],[c_380,c_2])).

cnf(c_231,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X1,X1,X2),k2_enumset1(X0,X1,X1,X2),k2_enumset1(X0,X1,X1,X2),k2_enumset1(X3,X3,X3,X3))) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X3))) ),
    inference(superposition,[status(thm)],[c_159,c_2])).

cnf(c_238,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X1,X1,X2),k2_enumset1(X0,X1,X1,X2),k2_enumset1(X0,X1,X1,X2),k2_enumset1(X3,X3,X3,X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(light_normalisation,[status(thm)],[c_231,c_3])).

cnf(c_549,plain,
    ( k2_enumset1(k4_tarski(X0,X1),X2,X3,X4) = k2_enumset1(k4_tarski(X0,X1),X4,X2,X3) ),
    inference(demodulation,[status(thm)],[c_495,c_138,c_238])).

cnf(c_1218,plain,
    ( k2_enumset1(k4_tarski(X0,X1),X2,X3,X3) = k2_enumset1(X3,X3,X2,k4_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_504,c_549])).

cnf(c_2012,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(k4_tarski(X0,X1),X2,X3,X3),k2_enumset1(k4_tarski(X0,X1),X2,X3,X3),k2_enumset1(k4_tarski(X0,X1),X2,X3,X3),k2_enumset1(X4,X4,X4,X4))) = k3_tarski(k2_enumset1(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X3,X3,X3,X3),k2_enumset1(X3,X3,X3,X3),k2_enumset1(X2,X2,k4_tarski(X0,X1),X4))) ),
    inference(superposition,[status(thm)],[c_1218,c_2])).

cnf(c_209,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X0,X1,X2,X2),k2_enumset1(X0,X1,X2,X2),k2_enumset1(X0,X1,X2,X2),k2_enumset1(X3,X3,X3,X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_2070,plain,
    ( k2_enumset1(X0,X1,k4_tarski(X2,X3),X4) = k2_enumset1(k4_tarski(X2,X3),X1,X0,X4) ),
    inference(demodulation,[status(thm)],[c_2012,c_3,c_209])).

cnf(c_1210,plain,
    ( k2_enumset1(k4_tarski(X0,X1),X2,X3,X4) = k2_enumset1(X4,X2,k4_tarski(X0,X1),X3) ),
    inference(superposition,[status(thm)],[c_337,c_549])).

cnf(c_2326,plain,
    ( k2_enumset1(k4_tarski(X0,X1),X2,X3,X4) = k2_enumset1(k4_tarski(X0,X1),X2,X4,X3) ),
    inference(superposition,[status(thm)],[c_2070,c_1210])).

cnf(c_7,negated_conjecture,
    ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1198,plain,
    ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_549,c_7])).

cnf(c_12262,plain,
    ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_2326,c_1198])).

cnf(c_12689,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_40,c_12262])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.20/0.34  % DateTime   : Tue Dec  1 09:39:00 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 3.84/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/0.99  
% 3.84/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.84/0.99  
% 3.84/0.99  ------  iProver source info
% 3.84/0.99  
% 3.84/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.84/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.84/0.99  git: non_committed_changes: false
% 3.84/0.99  git: last_make_outside_of_git: false
% 3.84/0.99  
% 3.84/0.99  ------ 
% 3.84/0.99  
% 3.84/0.99  ------ Input Options
% 3.84/0.99  
% 3.84/0.99  --out_options                           all
% 3.84/0.99  --tptp_safe_out                         true
% 3.84/0.99  --problem_path                          ""
% 3.84/0.99  --include_path                          ""
% 3.84/0.99  --clausifier                            res/vclausify_rel
% 3.84/0.99  --clausifier_options                    --mode clausify
% 3.84/0.99  --stdin                                 false
% 3.84/0.99  --stats_out                             all
% 3.84/0.99  
% 3.84/0.99  ------ General Options
% 3.84/0.99  
% 3.84/0.99  --fof                                   false
% 3.84/0.99  --time_out_real                         305.
% 3.84/0.99  --time_out_virtual                      -1.
% 3.84/0.99  --symbol_type_check                     false
% 3.84/0.99  --clausify_out                          false
% 3.84/0.99  --sig_cnt_out                           false
% 3.84/0.99  --trig_cnt_out                          false
% 3.84/0.99  --trig_cnt_out_tolerance                1.
% 3.84/0.99  --trig_cnt_out_sk_spl                   false
% 3.84/0.99  --abstr_cl_out                          false
% 3.84/0.99  
% 3.84/0.99  ------ Global Options
% 3.84/0.99  
% 3.84/0.99  --schedule                              default
% 3.84/0.99  --add_important_lit                     false
% 3.84/0.99  --prop_solver_per_cl                    1000
% 3.84/0.99  --min_unsat_core                        false
% 3.84/0.99  --soft_assumptions                      false
% 3.84/0.99  --soft_lemma_size                       3
% 3.84/0.99  --prop_impl_unit_size                   0
% 3.84/0.99  --prop_impl_unit                        []
% 3.84/0.99  --share_sel_clauses                     true
% 3.84/0.99  --reset_solvers                         false
% 3.84/0.99  --bc_imp_inh                            [conj_cone]
% 3.84/0.99  --conj_cone_tolerance                   3.
% 3.84/0.99  --extra_neg_conj                        none
% 3.84/0.99  --large_theory_mode                     true
% 3.84/0.99  --prolific_symb_bound                   200
% 3.84/0.99  --lt_threshold                          2000
% 3.84/0.99  --clause_weak_htbl                      true
% 3.84/0.99  --gc_record_bc_elim                     false
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing Options
% 3.84/0.99  
% 3.84/0.99  --preprocessing_flag                    true
% 3.84/0.99  --time_out_prep_mult                    0.1
% 3.84/0.99  --splitting_mode                        input
% 3.84/0.99  --splitting_grd                         true
% 3.84/0.99  --splitting_cvd                         false
% 3.84/0.99  --splitting_cvd_svl                     false
% 3.84/0.99  --splitting_nvd                         32
% 3.84/0.99  --sub_typing                            true
% 3.84/0.99  --prep_gs_sim                           true
% 3.84/0.99  --prep_unflatten                        true
% 3.84/0.99  --prep_res_sim                          true
% 3.84/0.99  --prep_upred                            true
% 3.84/0.99  --prep_sem_filter                       exhaustive
% 3.84/0.99  --prep_sem_filter_out                   false
% 3.84/0.99  --pred_elim                             true
% 3.84/0.99  --res_sim_input                         true
% 3.84/0.99  --eq_ax_congr_red                       true
% 3.84/0.99  --pure_diseq_elim                       true
% 3.84/0.99  --brand_transform                       false
% 3.84/0.99  --non_eq_to_eq                          false
% 3.84/0.99  --prep_def_merge                        true
% 3.84/0.99  --prep_def_merge_prop_impl              false
% 3.84/0.99  --prep_def_merge_mbd                    true
% 3.84/0.99  --prep_def_merge_tr_red                 false
% 3.84/0.99  --prep_def_merge_tr_cl                  false
% 3.84/0.99  --smt_preprocessing                     true
% 3.84/0.99  --smt_ac_axioms                         fast
% 3.84/0.99  --preprocessed_out                      false
% 3.84/0.99  --preprocessed_stats                    false
% 3.84/0.99  
% 3.84/0.99  ------ Abstraction refinement Options
% 3.84/0.99  
% 3.84/0.99  --abstr_ref                             []
% 3.84/0.99  --abstr_ref_prep                        false
% 3.84/0.99  --abstr_ref_until_sat                   false
% 3.84/0.99  --abstr_ref_sig_restrict                funpre
% 3.84/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/0.99  --abstr_ref_under                       []
% 3.84/0.99  
% 3.84/0.99  ------ SAT Options
% 3.84/0.99  
% 3.84/0.99  --sat_mode                              false
% 3.84/0.99  --sat_fm_restart_options                ""
% 3.84/0.99  --sat_gr_def                            false
% 3.84/0.99  --sat_epr_types                         true
% 3.84/0.99  --sat_non_cyclic_types                  false
% 3.84/0.99  --sat_finite_models                     false
% 3.84/0.99  --sat_fm_lemmas                         false
% 3.84/0.99  --sat_fm_prep                           false
% 3.84/0.99  --sat_fm_uc_incr                        true
% 3.84/0.99  --sat_out_model                         small
% 3.84/0.99  --sat_out_clauses                       false
% 3.84/0.99  
% 3.84/0.99  ------ QBF Options
% 3.84/0.99  
% 3.84/0.99  --qbf_mode                              false
% 3.84/0.99  --qbf_elim_univ                         false
% 3.84/0.99  --qbf_dom_inst                          none
% 3.84/0.99  --qbf_dom_pre_inst                      false
% 3.84/0.99  --qbf_sk_in                             false
% 3.84/0.99  --qbf_pred_elim                         true
% 3.84/0.99  --qbf_split                             512
% 3.84/0.99  
% 3.84/0.99  ------ BMC1 Options
% 3.84/0.99  
% 3.84/0.99  --bmc1_incremental                      false
% 3.84/0.99  --bmc1_axioms                           reachable_all
% 3.84/0.99  --bmc1_min_bound                        0
% 3.84/0.99  --bmc1_max_bound                        -1
% 3.84/0.99  --bmc1_max_bound_default                -1
% 3.84/0.99  --bmc1_symbol_reachability              true
% 3.84/0.99  --bmc1_property_lemmas                  false
% 3.84/0.99  --bmc1_k_induction                      false
% 3.84/0.99  --bmc1_non_equiv_states                 false
% 3.84/0.99  --bmc1_deadlock                         false
% 3.84/0.99  --bmc1_ucm                              false
% 3.84/0.99  --bmc1_add_unsat_core                   none
% 3.84/0.99  --bmc1_unsat_core_children              false
% 3.84/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/0.99  --bmc1_out_stat                         full
% 3.84/0.99  --bmc1_ground_init                      false
% 3.84/0.99  --bmc1_pre_inst_next_state              false
% 3.84/0.99  --bmc1_pre_inst_state                   false
% 3.84/0.99  --bmc1_pre_inst_reach_state             false
% 3.84/0.99  --bmc1_out_unsat_core                   false
% 3.84/0.99  --bmc1_aig_witness_out                  false
% 3.84/0.99  --bmc1_verbose                          false
% 3.84/0.99  --bmc1_dump_clauses_tptp                false
% 3.84/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.84/0.99  --bmc1_dump_file                        -
% 3.84/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.84/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.84/0.99  --bmc1_ucm_extend_mode                  1
% 3.84/0.99  --bmc1_ucm_init_mode                    2
% 3.84/0.99  --bmc1_ucm_cone_mode                    none
% 3.84/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.84/0.99  --bmc1_ucm_relax_model                  4
% 3.84/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.84/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/0.99  --bmc1_ucm_layered_model                none
% 3.84/0.99  --bmc1_ucm_max_lemma_size               10
% 3.84/0.99  
% 3.84/0.99  ------ AIG Options
% 3.84/0.99  
% 3.84/0.99  --aig_mode                              false
% 3.84/0.99  
% 3.84/0.99  ------ Instantiation Options
% 3.84/0.99  
% 3.84/0.99  --instantiation_flag                    true
% 3.84/0.99  --inst_sos_flag                         false
% 3.84/0.99  --inst_sos_phase                        true
% 3.84/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/0.99  --inst_lit_sel_side                     num_symb
% 3.84/0.99  --inst_solver_per_active                1400
% 3.84/0.99  --inst_solver_calls_frac                1.
% 3.84/0.99  --inst_passive_queue_type               priority_queues
% 3.84/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/0.99  --inst_passive_queues_freq              [25;2]
% 3.84/0.99  --inst_dismatching                      true
% 3.84/0.99  --inst_eager_unprocessed_to_passive     true
% 3.84/0.99  --inst_prop_sim_given                   true
% 3.84/0.99  --inst_prop_sim_new                     false
% 3.84/0.99  --inst_subs_new                         false
% 3.84/0.99  --inst_eq_res_simp                      false
% 3.84/0.99  --inst_subs_given                       false
% 3.84/0.99  --inst_orphan_elimination               true
% 3.84/0.99  --inst_learning_loop_flag               true
% 3.84/0.99  --inst_learning_start                   3000
% 3.84/0.99  --inst_learning_factor                  2
% 3.84/0.99  --inst_start_prop_sim_after_learn       3
% 3.84/0.99  --inst_sel_renew                        solver
% 3.84/0.99  --inst_lit_activity_flag                true
% 3.84/0.99  --inst_restr_to_given                   false
% 3.84/0.99  --inst_activity_threshold               500
% 3.84/0.99  --inst_out_proof                        true
% 3.84/0.99  
% 3.84/0.99  ------ Resolution Options
% 3.84/0.99  
% 3.84/0.99  --resolution_flag                       true
% 3.84/0.99  --res_lit_sel                           adaptive
% 3.84/0.99  --res_lit_sel_side                      none
% 3.84/0.99  --res_ordering                          kbo
% 3.84/0.99  --res_to_prop_solver                    active
% 3.84/0.99  --res_prop_simpl_new                    false
% 3.84/0.99  --res_prop_simpl_given                  true
% 3.84/0.99  --res_passive_queue_type                priority_queues
% 3.84/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/0.99  --res_passive_queues_freq               [15;5]
% 3.84/0.99  --res_forward_subs                      full
% 3.84/0.99  --res_backward_subs                     full
% 3.84/0.99  --res_forward_subs_resolution           true
% 3.84/0.99  --res_backward_subs_resolution          true
% 3.84/0.99  --res_orphan_elimination                true
% 3.84/0.99  --res_time_limit                        2.
% 3.84/0.99  --res_out_proof                         true
% 3.84/0.99  
% 3.84/0.99  ------ Superposition Options
% 3.84/0.99  
% 3.84/0.99  --superposition_flag                    true
% 3.84/0.99  --sup_passive_queue_type                priority_queues
% 3.84/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.84/0.99  --demod_completeness_check              fast
% 3.84/0.99  --demod_use_ground                      true
% 3.84/0.99  --sup_to_prop_solver                    passive
% 3.84/0.99  --sup_prop_simpl_new                    true
% 3.84/0.99  --sup_prop_simpl_given                  true
% 3.84/0.99  --sup_fun_splitting                     false
% 3.84/0.99  --sup_smt_interval                      50000
% 3.84/0.99  
% 3.84/0.99  ------ Superposition Simplification Setup
% 3.84/0.99  
% 3.84/0.99  --sup_indices_passive                   []
% 3.84/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.99  --sup_full_bw                           [BwDemod]
% 3.84/0.99  --sup_immed_triv                        [TrivRules]
% 3.84/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.99  --sup_immed_bw_main                     []
% 3.84/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/0.99  
% 3.84/0.99  ------ Combination Options
% 3.84/0.99  
% 3.84/0.99  --comb_res_mult                         3
% 3.84/0.99  --comb_sup_mult                         2
% 3.84/0.99  --comb_inst_mult                        10
% 3.84/0.99  
% 3.84/0.99  ------ Debug Options
% 3.84/0.99  
% 3.84/0.99  --dbg_backtrace                         false
% 3.84/0.99  --dbg_dump_prop_clauses                 false
% 3.84/0.99  --dbg_dump_prop_clauses_file            -
% 3.84/0.99  --dbg_out_stat                          false
% 3.84/0.99  ------ Parsing...
% 3.84/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.84/0.99  ------ Proving...
% 3.84/0.99  ------ Problem Properties 
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  clauses                                 8
% 3.84/0.99  conjectures                             1
% 3.84/0.99  EPR                                     0
% 3.84/0.99  Horn                                    8
% 3.84/0.99  unary                                   8
% 3.84/0.99  binary                                  0
% 3.84/0.99  lits                                    8
% 3.84/0.99  lits eq                                 8
% 3.84/0.99  fd_pure                                 0
% 3.84/0.99  fd_pseudo                               0
% 3.84/0.99  fd_cond                                 0
% 3.84/0.99  fd_pseudo_cond                          0
% 3.84/0.99  AC symbols                              0
% 3.84/0.99  
% 3.84/0.99  ------ Schedule UEQ
% 3.84/0.99  
% 3.84/0.99  ------ pure equality problem: resolution off 
% 3.84/0.99  
% 3.84/0.99  ------ Option_UEQ Time Limit: Unbounded
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  ------ 
% 3.84/0.99  Current options:
% 3.84/0.99  ------ 
% 3.84/0.99  
% 3.84/0.99  ------ Input Options
% 3.84/0.99  
% 3.84/0.99  --out_options                           all
% 3.84/0.99  --tptp_safe_out                         true
% 3.84/0.99  --problem_path                          ""
% 3.84/0.99  --include_path                          ""
% 3.84/0.99  --clausifier                            res/vclausify_rel
% 3.84/0.99  --clausifier_options                    --mode clausify
% 3.84/0.99  --stdin                                 false
% 3.84/0.99  --stats_out                             all
% 3.84/0.99  
% 3.84/0.99  ------ General Options
% 3.84/0.99  
% 3.84/0.99  --fof                                   false
% 3.84/0.99  --time_out_real                         305.
% 3.84/0.99  --time_out_virtual                      -1.
% 3.84/0.99  --symbol_type_check                     false
% 3.84/0.99  --clausify_out                          false
% 3.84/0.99  --sig_cnt_out                           false
% 3.84/0.99  --trig_cnt_out                          false
% 3.84/0.99  --trig_cnt_out_tolerance                1.
% 3.84/0.99  --trig_cnt_out_sk_spl                   false
% 3.84/0.99  --abstr_cl_out                          false
% 3.84/0.99  
% 3.84/0.99  ------ Global Options
% 3.84/0.99  
% 3.84/0.99  --schedule                              default
% 3.84/0.99  --add_important_lit                     false
% 3.84/0.99  --prop_solver_per_cl                    1000
% 3.84/0.99  --min_unsat_core                        false
% 3.84/0.99  --soft_assumptions                      false
% 3.84/0.99  --soft_lemma_size                       3
% 3.84/0.99  --prop_impl_unit_size                   0
% 3.84/0.99  --prop_impl_unit                        []
% 3.84/0.99  --share_sel_clauses                     true
% 3.84/0.99  --reset_solvers                         false
% 3.84/0.99  --bc_imp_inh                            [conj_cone]
% 3.84/0.99  --conj_cone_tolerance                   3.
% 3.84/0.99  --extra_neg_conj                        none
% 3.84/0.99  --large_theory_mode                     true
% 3.84/0.99  --prolific_symb_bound                   200
% 3.84/0.99  --lt_threshold                          2000
% 3.84/0.99  --clause_weak_htbl                      true
% 3.84/0.99  --gc_record_bc_elim                     false
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing Options
% 3.84/0.99  
% 3.84/0.99  --preprocessing_flag                    true
% 3.84/0.99  --time_out_prep_mult                    0.1
% 3.84/0.99  --splitting_mode                        input
% 3.84/0.99  --splitting_grd                         true
% 3.84/0.99  --splitting_cvd                         false
% 3.84/0.99  --splitting_cvd_svl                     false
% 3.84/0.99  --splitting_nvd                         32
% 3.84/0.99  --sub_typing                            true
% 3.84/0.99  --prep_gs_sim                           true
% 3.84/0.99  --prep_unflatten                        true
% 3.84/0.99  --prep_res_sim                          true
% 3.84/0.99  --prep_upred                            true
% 3.84/0.99  --prep_sem_filter                       exhaustive
% 3.84/0.99  --prep_sem_filter_out                   false
% 3.84/0.99  --pred_elim                             true
% 3.84/0.99  --res_sim_input                         true
% 3.84/0.99  --eq_ax_congr_red                       true
% 3.84/0.99  --pure_diseq_elim                       true
% 3.84/0.99  --brand_transform                       false
% 3.84/0.99  --non_eq_to_eq                          false
% 3.84/0.99  --prep_def_merge                        true
% 3.84/0.99  --prep_def_merge_prop_impl              false
% 3.84/0.99  --prep_def_merge_mbd                    true
% 3.84/0.99  --prep_def_merge_tr_red                 false
% 3.84/0.99  --prep_def_merge_tr_cl                  false
% 3.84/0.99  --smt_preprocessing                     true
% 3.84/0.99  --smt_ac_axioms                         fast
% 3.84/0.99  --preprocessed_out                      false
% 3.84/0.99  --preprocessed_stats                    false
% 3.84/0.99  
% 3.84/0.99  ------ Abstraction refinement Options
% 3.84/0.99  
% 3.84/0.99  --abstr_ref                             []
% 3.84/0.99  --abstr_ref_prep                        false
% 3.84/0.99  --abstr_ref_until_sat                   false
% 3.84/0.99  --abstr_ref_sig_restrict                funpre
% 3.84/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/0.99  --abstr_ref_under                       []
% 3.84/0.99  
% 3.84/0.99  ------ SAT Options
% 3.84/0.99  
% 3.84/0.99  --sat_mode                              false
% 3.84/0.99  --sat_fm_restart_options                ""
% 3.84/0.99  --sat_gr_def                            false
% 3.84/0.99  --sat_epr_types                         true
% 3.84/0.99  --sat_non_cyclic_types                  false
% 3.84/0.99  --sat_finite_models                     false
% 3.84/0.99  --sat_fm_lemmas                         false
% 3.84/0.99  --sat_fm_prep                           false
% 3.84/0.99  --sat_fm_uc_incr                        true
% 3.84/0.99  --sat_out_model                         small
% 3.84/0.99  --sat_out_clauses                       false
% 3.84/0.99  
% 3.84/0.99  ------ QBF Options
% 3.84/0.99  
% 3.84/0.99  --qbf_mode                              false
% 3.84/0.99  --qbf_elim_univ                         false
% 3.84/0.99  --qbf_dom_inst                          none
% 3.84/0.99  --qbf_dom_pre_inst                      false
% 3.84/0.99  --qbf_sk_in                             false
% 3.84/0.99  --qbf_pred_elim                         true
% 3.84/0.99  --qbf_split                             512
% 3.84/0.99  
% 3.84/0.99  ------ BMC1 Options
% 3.84/0.99  
% 3.84/0.99  --bmc1_incremental                      false
% 3.84/0.99  --bmc1_axioms                           reachable_all
% 3.84/0.99  --bmc1_min_bound                        0
% 3.84/0.99  --bmc1_max_bound                        -1
% 3.84/0.99  --bmc1_max_bound_default                -1
% 3.84/0.99  --bmc1_symbol_reachability              true
% 3.84/0.99  --bmc1_property_lemmas                  false
% 3.84/0.99  --bmc1_k_induction                      false
% 3.84/0.99  --bmc1_non_equiv_states                 false
% 3.84/0.99  --bmc1_deadlock                         false
% 3.84/0.99  --bmc1_ucm                              false
% 3.84/0.99  --bmc1_add_unsat_core                   none
% 3.84/0.99  --bmc1_unsat_core_children              false
% 3.84/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/0.99  --bmc1_out_stat                         full
% 3.84/0.99  --bmc1_ground_init                      false
% 3.84/0.99  --bmc1_pre_inst_next_state              false
% 3.84/0.99  --bmc1_pre_inst_state                   false
% 3.84/0.99  --bmc1_pre_inst_reach_state             false
% 3.84/0.99  --bmc1_out_unsat_core                   false
% 3.84/0.99  --bmc1_aig_witness_out                  false
% 3.84/0.99  --bmc1_verbose                          false
% 3.84/0.99  --bmc1_dump_clauses_tptp                false
% 3.84/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.84/0.99  --bmc1_dump_file                        -
% 3.84/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.84/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.84/0.99  --bmc1_ucm_extend_mode                  1
% 3.84/0.99  --bmc1_ucm_init_mode                    2
% 3.84/0.99  --bmc1_ucm_cone_mode                    none
% 3.84/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.84/0.99  --bmc1_ucm_relax_model                  4
% 3.84/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.84/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/0.99  --bmc1_ucm_layered_model                none
% 3.84/0.99  --bmc1_ucm_max_lemma_size               10
% 3.84/0.99  
% 3.84/0.99  ------ AIG Options
% 3.84/0.99  
% 3.84/0.99  --aig_mode                              false
% 3.84/0.99  
% 3.84/0.99  ------ Instantiation Options
% 3.84/0.99  
% 3.84/0.99  --instantiation_flag                    false
% 3.84/0.99  --inst_sos_flag                         false
% 3.84/0.99  --inst_sos_phase                        true
% 3.84/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/0.99  --inst_lit_sel_side                     num_symb
% 3.84/0.99  --inst_solver_per_active                1400
% 3.84/0.99  --inst_solver_calls_frac                1.
% 3.84/0.99  --inst_passive_queue_type               priority_queues
% 3.84/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/0.99  --inst_passive_queues_freq              [25;2]
% 3.84/0.99  --inst_dismatching                      true
% 3.84/0.99  --inst_eager_unprocessed_to_passive     true
% 3.84/0.99  --inst_prop_sim_given                   true
% 3.84/0.99  --inst_prop_sim_new                     false
% 3.84/0.99  --inst_subs_new                         false
% 3.84/0.99  --inst_eq_res_simp                      false
% 3.84/0.99  --inst_subs_given                       false
% 3.84/0.99  --inst_orphan_elimination               true
% 3.84/0.99  --inst_learning_loop_flag               true
% 3.84/0.99  --inst_learning_start                   3000
% 3.84/0.99  --inst_learning_factor                  2
% 3.84/0.99  --inst_start_prop_sim_after_learn       3
% 3.84/0.99  --inst_sel_renew                        solver
% 3.84/0.99  --inst_lit_activity_flag                true
% 3.84/0.99  --inst_restr_to_given                   false
% 3.84/0.99  --inst_activity_threshold               500
% 3.84/0.99  --inst_out_proof                        true
% 3.84/0.99  
% 3.84/0.99  ------ Resolution Options
% 3.84/0.99  
% 3.84/0.99  --resolution_flag                       false
% 3.84/0.99  --res_lit_sel                           adaptive
% 3.84/0.99  --res_lit_sel_side                      none
% 3.84/0.99  --res_ordering                          kbo
% 3.84/0.99  --res_to_prop_solver                    active
% 3.84/0.99  --res_prop_simpl_new                    false
% 3.84/0.99  --res_prop_simpl_given                  true
% 3.84/0.99  --res_passive_queue_type                priority_queues
% 3.84/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/0.99  --res_passive_queues_freq               [15;5]
% 3.84/0.99  --res_forward_subs                      full
% 3.84/0.99  --res_backward_subs                     full
% 3.84/0.99  --res_forward_subs_resolution           true
% 3.84/0.99  --res_backward_subs_resolution          true
% 3.84/0.99  --res_orphan_elimination                true
% 3.84/0.99  --res_time_limit                        2.
% 3.84/0.99  --res_out_proof                         true
% 3.84/0.99  
% 3.84/0.99  ------ Superposition Options
% 3.84/0.99  
% 3.84/0.99  --superposition_flag                    true
% 3.84/0.99  --sup_passive_queue_type                priority_queues
% 3.84/0.99  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.84/0.99  --demod_completeness_check              fast
% 3.84/0.99  --demod_use_ground                      true
% 3.84/0.99  --sup_to_prop_solver                    active
% 3.84/0.99  --sup_prop_simpl_new                    false
% 3.84/0.99  --sup_prop_simpl_given                  false
% 3.84/0.99  --sup_fun_splitting                     true
% 3.84/0.99  --sup_smt_interval                      10000
% 3.84/0.99  
% 3.84/0.99  ------ Superposition Simplification Setup
% 3.84/0.99  
% 3.84/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.84/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.84/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.99  --sup_full_triv                         [TrivRules]
% 3.84/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.84/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.84/0.99  --sup_immed_triv                        [TrivRules]
% 3.84/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/0.99  --sup_immed_bw_main                     []
% 3.84/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.84/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/0.99  --sup_input_bw                          [BwDemod;BwSubsumption]
% 3.84/0.99  
% 3.84/0.99  ------ Combination Options
% 3.84/0.99  
% 3.84/0.99  --comb_res_mult                         1
% 3.84/0.99  --comb_sup_mult                         1
% 3.84/0.99  --comb_inst_mult                        1000000
% 3.84/0.99  
% 3.84/0.99  ------ Debug Options
% 3.84/0.99  
% 3.84/0.99  --dbg_backtrace                         false
% 3.84/0.99  --dbg_dump_prop_clauses                 false
% 3.84/0.99  --dbg_dump_prop_clauses_file            -
% 3.84/0.99  --dbg_out_stat                          false
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  ------ Proving...
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  % SZS status Theorem for theBenchmark.p
% 3.84/0.99  
% 3.84/0.99   Resolution empty clause
% 3.84/0.99  
% 3.84/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.84/0.99  
% 3.84/0.99  fof(f11,axiom,(
% 3.84/0.99    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f29,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 3.84/0.99    inference(cnf_transformation,[],[f11])).
% 3.84/0.99  
% 3.84/0.99  fof(f5,axiom,(
% 3.84/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f23,plain,(
% 3.84/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f5])).
% 3.84/0.99  
% 3.84/0.99  fof(f37,plain,(
% 3.84/0.99    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.84/0.99    inference(definition_unfolding,[],[f23,f34])).
% 3.84/0.99  
% 3.84/0.99  fof(f6,axiom,(
% 3.84/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f24,plain,(
% 3.84/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f6])).
% 3.84/0.99  
% 3.84/0.99  fof(f7,axiom,(
% 3.84/0.99    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f25,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f7])).
% 3.84/0.99  
% 3.84/0.99  fof(f34,plain,(
% 3.84/0.99    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.84/0.99    inference(definition_unfolding,[],[f24,f25])).
% 3.84/0.99  
% 3.84/0.99  fof(f44,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2))) )),
% 3.84/0.99    inference(definition_unfolding,[],[f29,f34,f37,f34])).
% 3.84/0.99  
% 3.84/0.99  fof(f10,axiom,(
% 3.84/0.99    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f28,plain,(
% 3.84/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 3.84/0.99    inference(cnf_transformation,[],[f10])).
% 3.84/0.99  
% 3.84/0.99  fof(f42,plain,(
% 3.84/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) )),
% 3.84/0.99    inference(definition_unfolding,[],[f28,f34,f34])).
% 3.84/0.99  
% 3.84/0.99  fof(f8,axiom,(
% 3.84/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f26,plain,(
% 3.84/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f8])).
% 3.84/0.99  
% 3.84/0.99  fof(f3,axiom,(
% 3.84/0.99    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f21,plain,(
% 3.84/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f3])).
% 3.84/0.99  
% 3.84/0.99  fof(f9,axiom,(
% 3.84/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f27,plain,(
% 3.84/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.84/0.99    inference(cnf_transformation,[],[f9])).
% 3.84/0.99  
% 3.84/0.99  fof(f35,plain,(
% 3.84/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 3.84/0.99    inference(definition_unfolding,[],[f27,f34])).
% 3.84/0.99  
% 3.84/0.99  fof(f36,plain,(
% 3.84/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X3,X4)))) )),
% 3.84/0.99    inference(definition_unfolding,[],[f21,f35,f34,f25])).
% 3.84/0.99  
% 3.84/0.99  fof(f41,plain,(
% 3.84/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X3)))) )),
% 3.84/0.99    inference(definition_unfolding,[],[f26,f36])).
% 3.84/0.99  
% 3.84/0.99  fof(f2,axiom,(
% 3.84/0.99    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f20,plain,(
% 3.84/0.99    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f2])).
% 3.84/0.99  
% 3.84/0.99  fof(f38,plain,(
% 3.84/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)))) )),
% 3.84/0.99    inference(definition_unfolding,[],[f20,f35,f34,f34])).
% 3.84/0.99  
% 3.84/0.99  fof(f4,axiom,(
% 3.84/0.99    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f22,plain,(
% 3.84/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f4])).
% 3.84/0.99  
% 3.84/0.99  fof(f40,plain,(
% 3.84/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X3,X4))) = k3_tarski(k2_enumset1(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X0,X1,X2,X3),k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X4,X4,X4)))) )),
% 3.84/0.99    inference(definition_unfolding,[],[f22,f35,f37,f36])).
% 3.84/0.99  
% 3.84/0.99  fof(f1,axiom,(
% 3.84/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f19,plain,(
% 3.84/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f1])).
% 3.84/0.99  
% 3.84/0.99  fof(f39,plain,(
% 3.84/0.99    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0))) )),
% 3.84/0.99    inference(definition_unfolding,[],[f19,f35,f35])).
% 3.84/0.99  
% 3.84/0.99  fof(f14,conjecture,(
% 3.84/0.99    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f15,negated_conjecture,(
% 3.84/0.99    ~! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))),
% 3.84/0.99    inference(negated_conjecture,[],[f14])).
% 3.84/0.99  
% 3.84/0.99  fof(f16,plain,(
% 3.84/0.99    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))),
% 3.84/0.99    inference(ennf_transformation,[],[f15])).
% 3.84/0.99  
% 3.84/0.99  fof(f17,plain,(
% 3.84/0.99    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) => k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f18,plain,(
% 3.84/0.99    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 3.84/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f17])).
% 3.84/0.99  
% 3.84/0.99  fof(f33,plain,(
% 3.84/0.99    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 3.84/0.99    inference(cnf_transformation,[],[f18])).
% 3.84/0.99  
% 3.84/0.99  fof(f12,axiom,(
% 3.84/0.99    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f31,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f12])).
% 3.84/0.99  
% 3.84/0.99  fof(f13,axiom,(
% 3.84/0.99    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f32,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f13])).
% 3.84/0.99  
% 3.84/0.99  fof(f45,plain,(
% 3.84/0.99    k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4))),
% 3.84/0.99    inference(definition_unfolding,[],[f33,f31,f31,f31,f31,f32,f37,f34,f34])).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6,plain,
% 3.84/0.99      ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) ),
% 3.84/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4,plain,
% 3.84/0.99      ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X3),k2_enumset1(X1,X1,X1,X2)) ),
% 3.84/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_40,plain,
% 3.84/0.99      ( k2_enumset1(k4_tarski(k4_tarski(X0,X1),X2),k4_tarski(k4_tarski(X0,X1),X3),k4_tarski(k4_tarski(X0,X4),X2),k4_tarski(k4_tarski(X0,X4),X3)) = k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X4)),k2_enumset1(X2,X2,X2,X3)) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_6,c_4]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3,plain,
% 3.84/0.99      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X3))) = k2_enumset1(X0,X1,X2,X3) ),
% 3.84/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_0,plain,
% 3.84/0.99      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) = k2_enumset1(X0,X1,X2,X3) ),
% 3.84/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_159,plain,
% 3.84/0.99      ( k2_enumset1(X0,X1,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_236,plain,
% 3.84/0.99      ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X2,X1),k4_tarski(X2,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X2),k2_enumset1(X1,X1,X1,X1)) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_159,c_4]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2,plain,
% 3.84/0.99      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X0,X1,X2,X3),k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X4,X4,X4))) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X3,X4))) ),
% 3.84/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_260,plain,
% 3.84/0.99      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X1,k4_tarski(X2,X3),k4_tarski(X2,X3)),k2_enumset1(X0,X1,k4_tarski(X2,X3),k4_tarski(X2,X3)),k2_enumset1(X0,X1,k4_tarski(X2,X3),k4_tarski(X2,X3)),k2_enumset1(k4_tarski(X2,X3),k4_tarski(X2,X3),k4_tarski(X2,X3),k4_tarski(X2,X3)))) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)))) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_236,c_2]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_136,plain,
% 3.84/0.99      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X4)))) = k2_enumset1(X0,X1,k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_212,plain,
% 3.84/0.99      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X1,X2,X2),k2_enumset1(X0,X1,X2,X2),k2_enumset1(X0,X1,X2,X2),k2_enumset1(X2,X2,X2,X2))) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X1,X2))) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_2,c_2]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_214,plain,
% 3.84/0.99      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X1,X2,X2),k2_enumset1(X0,X1,X2,X2),k2_enumset1(X0,X1,X2,X2),k2_enumset1(X2,X2,X2,X2))) = k2_enumset1(X0,X0,X1,X2) ),
% 3.84/0.99      inference(demodulation,[status(thm)],[c_212,c_3]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_282,plain,
% 3.84/0.99      ( k2_enumset1(X0,X1,k4_tarski(X2,X3),k4_tarski(X2,X3)) = k2_enumset1(X0,X0,X1,k4_tarski(X2,X3)) ),
% 3.84/0.99      inference(demodulation,[status(thm)],[c_260,c_136,c_214]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_295,plain,
% 3.84/0.99      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X1,k4_tarski(X2,X3)),k2_enumset1(X0,X0,X1,k4_tarski(X2,X3)),k2_enumset1(X0,X0,X1,k4_tarski(X2,X3)),k2_enumset1(X4,X4,X4,X4))) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(k4_tarski(X2,X3),k4_tarski(X2,X3),k4_tarski(X2,X3),X4))) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_282,c_2]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1,plain,
% 3.84/0.99      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
% 3.84/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_138,plain,
% 3.84/0.99      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) = k2_enumset1(X2,X3,X0,X1) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_0,c_1]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_213,plain,
% 3.84/0.99      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3))) = k2_enumset1(X0,X1,X2,X3) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_2,c_3]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_337,plain,
% 3.84/0.99      ( k2_enumset1(k4_tarski(X0,X1),X2,X3,X4) = k2_enumset1(X3,X4,k4_tarski(X0,X1),X2) ),
% 3.84/0.99      inference(demodulation,[status(thm)],[c_295,c_138,c_213]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_380,plain,
% 3.84/0.99      ( k2_enumset1(X0,X1,k4_tarski(X2,X3),k4_tarski(X2,X3)) = k2_enumset1(k4_tarski(X2,X3),X0,X0,X1) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_337,c_159]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_504,plain,
% 3.84/0.99      ( k2_enumset1(X0,X0,X1,k4_tarski(X2,X3)) = k2_enumset1(k4_tarski(X2,X3),X0,X0,X1) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_380,c_282]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_495,plain,
% 3.84/0.99      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(k4_tarski(X2,X3),k4_tarski(X2,X3),k4_tarski(X2,X3),X4))) = k3_tarski(k2_enumset1(k2_enumset1(k4_tarski(X2,X3),X0,X0,X1),k2_enumset1(k4_tarski(X2,X3),X0,X0,X1),k2_enumset1(k4_tarski(X2,X3),X0,X0,X1),k2_enumset1(X4,X4,X4,X4))) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_380,c_2]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_231,plain,
% 3.84/0.99      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X1,X1,X2),k2_enumset1(X0,X1,X1,X2),k2_enumset1(X0,X1,X1,X2),k2_enumset1(X3,X3,X3,X3))) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X3))) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_159,c_2]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_238,plain,
% 3.84/0.99      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X1,X1,X2),k2_enumset1(X0,X1,X1,X2),k2_enumset1(X0,X1,X1,X2),k2_enumset1(X3,X3,X3,X3))) = k2_enumset1(X0,X1,X2,X3) ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_231,c_3]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_549,plain,
% 3.84/0.99      ( k2_enumset1(k4_tarski(X0,X1),X2,X3,X4) = k2_enumset1(k4_tarski(X0,X1),X4,X2,X3) ),
% 3.84/0.99      inference(demodulation,[status(thm)],[c_495,c_138,c_238]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1218,plain,
% 3.84/0.99      ( k2_enumset1(k4_tarski(X0,X1),X2,X3,X3) = k2_enumset1(X3,X3,X2,k4_tarski(X0,X1)) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_504,c_549]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2012,plain,
% 3.84/0.99      ( k3_tarski(k2_enumset1(k2_enumset1(k4_tarski(X0,X1),X2,X3,X3),k2_enumset1(k4_tarski(X0,X1),X2,X3,X3),k2_enumset1(k4_tarski(X0,X1),X2,X3,X3),k2_enumset1(X4,X4,X4,X4))) = k3_tarski(k2_enumset1(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X3,X3,X3,X3),k2_enumset1(X3,X3,X3,X3),k2_enumset1(X2,X2,k4_tarski(X0,X1),X4))) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1218,c_2]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_209,plain,
% 3.84/0.99      ( k3_tarski(k2_enumset1(k2_enumset1(X0,X1,X2,X2),k2_enumset1(X0,X1,X2,X2),k2_enumset1(X0,X1,X2,X2),k2_enumset1(X3,X3,X3,X3))) = k2_enumset1(X0,X1,X2,X3) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2070,plain,
% 3.84/0.99      ( k2_enumset1(X0,X1,k4_tarski(X2,X3),X4) = k2_enumset1(k4_tarski(X2,X3),X1,X0,X4) ),
% 3.84/0.99      inference(demodulation,[status(thm)],[c_2012,c_3,c_209]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1210,plain,
% 3.84/0.99      ( k2_enumset1(k4_tarski(X0,X1),X2,X3,X4) = k2_enumset1(X4,X2,k4_tarski(X0,X1),X3) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_337,c_549]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2326,plain,
% 3.84/0.99      ( k2_enumset1(k4_tarski(X0,X1),X2,X3,X4) = k2_enumset1(k4_tarski(X0,X1),X2,X4,X3) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_2070,c_1210]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7,negated_conjecture,
% 3.84/0.99      ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 3.84/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1198,plain,
% 3.84/0.99      ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 3.84/0.99      inference(demodulation,[status(thm)],[c_549,c_7]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_12262,plain,
% 3.84/0.99      ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 3.84/0.99      inference(demodulation,[status(thm)],[c_2326,c_1198]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_12689,plain,
% 3.84/0.99      ( $false ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_40,c_12262]) ).
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.84/0.99  
% 3.84/0.99  ------                               Statistics
% 3.84/0.99  
% 3.84/0.99  ------ General
% 3.84/0.99  
% 3.84/0.99  abstr_ref_over_cycles:                  0
% 3.84/0.99  abstr_ref_under_cycles:                 0
% 3.84/0.99  gc_basic_clause_elim:                   0
% 3.84/0.99  forced_gc_time:                         0
% 3.84/0.99  parsing_time:                           0.013
% 3.84/0.99  unif_index_cands_time:                  0.
% 3.84/0.99  unif_index_add_time:                    0.
% 3.84/0.99  orderings_time:                         0.
% 3.84/0.99  out_proof_time:                         0.008
% 3.84/0.99  total_time:                             0.489
% 3.84/0.99  num_of_symbols:                         40
% 3.84/0.99  num_of_terms:                           7443
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing
% 3.84/0.99  
% 3.84/0.99  num_of_splits:                          0
% 3.84/0.99  num_of_split_atoms:                     0
% 3.84/0.99  num_of_reused_defs:                     0
% 3.84/0.99  num_eq_ax_congr_red:                    0
% 3.84/0.99  num_of_sem_filtered_clauses:            0
% 3.84/0.99  num_of_subtypes:                        1
% 3.84/0.99  monotx_restored_types:                  0
% 3.84/0.99  sat_num_of_epr_types:                   0
% 3.84/0.99  sat_num_of_non_cyclic_types:            0
% 3.84/0.99  sat_guarded_non_collapsed_types:        0
% 3.84/0.99  num_pure_diseq_elim:                    0
% 3.84/0.99  simp_replaced_by:                       0
% 3.84/0.99  res_preprocessed:                       22
% 3.84/0.99  prep_upred:                             0
% 3.84/0.99  prep_unflattend:                        0
% 3.84/0.99  smt_new_axioms:                         0
% 3.84/0.99  pred_elim_cands:                        0
% 3.84/0.99  pred_elim:                              0
% 3.84/0.99  pred_elim_cl:                           0
% 3.84/0.99  pred_elim_cycles:                       0
% 3.84/0.99  merged_defs:                            0
% 3.84/0.99  merged_defs_ncl:                        0
% 3.84/0.99  bin_hyper_res:                          0
% 3.84/0.99  prep_cycles:                            2
% 3.84/0.99  pred_elim_time:                         0.
% 3.84/0.99  splitting_time:                         0.
% 3.84/0.99  sem_filter_time:                        0.
% 3.84/0.99  monotx_time:                            0.
% 3.84/0.99  subtype_inf_time:                       0.
% 3.84/0.99  
% 3.84/0.99  ------ Problem properties
% 3.84/0.99  
% 3.84/0.99  clauses:                                8
% 3.84/0.99  conjectures:                            1
% 3.84/0.99  epr:                                    0
% 3.84/0.99  horn:                                   8
% 3.84/0.99  ground:                                 1
% 3.84/0.99  unary:                                  8
% 3.84/0.99  binary:                                 0
% 3.84/0.99  lits:                                   8
% 3.84/0.99  lits_eq:                                8
% 3.84/0.99  fd_pure:                                0
% 3.84/0.99  fd_pseudo:                              0
% 3.84/0.99  fd_cond:                                0
% 3.84/0.99  fd_pseudo_cond:                         0
% 3.84/0.99  ac_symbols:                             0
% 3.84/0.99  
% 3.84/0.99  ------ Propositional Solver
% 3.84/0.99  
% 3.84/0.99  prop_solver_calls:                      13
% 3.84/0.99  prop_fast_solver_calls:                 66
% 3.84/0.99  smt_solver_calls:                       0
% 3.84/0.99  smt_fast_solver_calls:                  0
% 3.84/0.99  prop_num_of_clauses:                    120
% 3.84/0.99  prop_preprocess_simplified:             350
% 3.84/0.99  prop_fo_subsumed:                       0
% 3.84/0.99  prop_solver_time:                       0.
% 3.84/0.99  smt_solver_time:                        0.
% 3.84/0.99  smt_fast_solver_time:                   0.
% 3.84/0.99  prop_fast_solver_time:                  0.
% 3.84/0.99  prop_unsat_core_time:                   0.
% 3.84/0.99  
% 3.84/0.99  ------ QBF
% 3.84/0.99  
% 3.84/0.99  qbf_q_res:                              0
% 3.84/0.99  qbf_num_tautologies:                    0
% 3.84/0.99  qbf_prep_cycles:                        0
% 3.84/0.99  
% 3.84/0.99  ------ BMC1
% 3.84/0.99  
% 3.84/0.99  bmc1_current_bound:                     -1
% 3.84/0.99  bmc1_last_solved_bound:                 -1
% 3.84/0.99  bmc1_unsat_core_size:                   -1
% 3.84/0.99  bmc1_unsat_core_parents_size:           -1
% 3.84/0.99  bmc1_merge_next_fun:                    0
% 3.84/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.84/0.99  
% 3.84/0.99  ------ Instantiation
% 3.84/0.99  
% 3.84/0.99  inst_num_of_clauses:                    0
% 3.84/0.99  inst_num_in_passive:                    0
% 3.84/0.99  inst_num_in_active:                     0
% 3.84/0.99  inst_num_in_unprocessed:                0
% 3.84/0.99  inst_num_of_loops:                      0
% 3.84/0.99  inst_num_of_learning_restarts:          0
% 3.84/0.99  inst_num_moves_active_passive:          0
% 3.84/0.99  inst_lit_activity:                      0
% 3.84/0.99  inst_lit_activity_moves:                0
% 3.84/0.99  inst_num_tautologies:                   0
% 3.84/0.99  inst_num_prop_implied:                  0
% 3.84/0.99  inst_num_existing_simplified:           0
% 3.84/0.99  inst_num_eq_res_simplified:             0
% 3.84/0.99  inst_num_child_elim:                    0
% 3.84/0.99  inst_num_of_dismatching_blockings:      0
% 3.84/0.99  inst_num_of_non_proper_insts:           0
% 3.84/0.99  inst_num_of_duplicates:                 0
% 3.84/0.99  inst_inst_num_from_inst_to_res:         0
% 3.84/0.99  inst_dismatching_checking_time:         0.
% 3.84/0.99  
% 3.84/0.99  ------ Resolution
% 3.84/0.99  
% 3.84/0.99  res_num_of_clauses:                     0
% 3.84/0.99  res_num_in_passive:                     0
% 3.84/0.99  res_num_in_active:                      0
% 3.84/0.99  res_num_of_loops:                       24
% 3.84/0.99  res_forward_subset_subsumed:            0
% 3.84/0.99  res_backward_subset_subsumed:           0
% 3.84/0.99  res_forward_subsumed:                   0
% 3.84/0.99  res_backward_subsumed:                  0
% 3.84/0.99  res_forward_subsumption_resolution:     0
% 3.84/0.99  res_backward_subsumption_resolution:    0
% 3.84/0.99  res_clause_to_clause_subsumption:       21462
% 3.84/0.99  res_orphan_elimination:                 0
% 3.84/0.99  res_tautology_del:                      0
% 3.84/0.99  res_num_eq_res_simplified:              0
% 3.84/0.99  res_num_sel_changes:                    0
% 3.84/0.99  res_moves_from_active_to_pass:          0
% 3.84/0.99  
% 3.84/0.99  ------ Superposition
% 3.84/0.99  
% 3.84/0.99  sup_time_total:                         0.
% 3.84/0.99  sup_time_generating:                    0.
% 3.84/0.99  sup_time_sim_full:                      0.
% 3.84/0.99  sup_time_sim_immed:                     0.
% 3.84/0.99  
% 3.84/0.99  sup_num_of_clauses:                     1020
% 3.84/0.99  sup_num_in_active:                      76
% 3.84/0.99  sup_num_in_passive:                     944
% 3.84/0.99  sup_num_of_loops:                       80
% 3.84/0.99  sup_fw_superposition:                   5295
% 3.84/0.99  sup_bw_superposition:                   7166
% 3.84/0.99  sup_immediate_simplified:               349
% 3.84/0.99  sup_given_eliminated:                   0
% 3.84/0.99  comparisons_done:                       0
% 3.84/0.99  comparisons_avoided:                    0
% 3.84/0.99  
% 3.84/0.99  ------ Simplifications
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  sim_fw_subset_subsumed:                 0
% 3.84/0.99  sim_bw_subset_subsumed:                 0
% 3.84/0.99  sim_fw_subsumed:                        175
% 3.84/0.99  sim_bw_subsumed:                        35
% 3.84/0.99  sim_fw_subsumption_res:                 0
% 3.84/0.99  sim_bw_subsumption_res:                 0
% 3.84/0.99  sim_tautology_del:                      0
% 3.84/0.99  sim_eq_tautology_del:                   29
% 3.84/0.99  sim_eq_res_simp:                        0
% 3.84/0.99  sim_fw_demodulated:                     109
% 3.84/0.99  sim_bw_demodulated:                     4
% 3.84/0.99  sim_light_normalised:                   62
% 3.84/0.99  sim_joinable_taut:                      0
% 3.84/0.99  sim_joinable_simp:                      0
% 3.84/0.99  sim_ac_normalised:                      0
% 3.84/0.99  sim_smt_subsumption:                    0
% 3.84/0.99  
%------------------------------------------------------------------------------
