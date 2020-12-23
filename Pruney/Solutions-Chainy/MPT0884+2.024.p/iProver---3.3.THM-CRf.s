%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:22 EST 2020

% Result     : Theorem 31.81s
% Output     : CNFRefutation 31.81s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 234 expanded)
%              Number of clauses        :   30 (  36 expanded)
%              Number of leaves         :   17 (  86 expanded)
%              Depth                    :   12
%              Number of atoms          :   94 ( 260 expanded)
%              Number of equality atoms :   93 ( 259 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f24])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X0),k1_enumset1(X1,X1,X0),k1_enumset1(X2,X2,X0))) ),
    inference(definition_unfolding,[],[f20,f34,f24,f24])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) ),
    inference(definition_unfolding,[],[f19,f34,f24,f24])).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) ),
    inference(definition_unfolding,[],[f25,f35])).

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

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4))) ),
    inference(definition_unfolding,[],[f21,f34,f24])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) ),
    inference(definition_unfolding,[],[f26,f35,f36])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f45,plain,(
    k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f33,f35,f31,f31,f31,f31,f32,f24,f38,f24])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3)),k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3)),k1_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3)))) = k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) ),
    inference(definition_unfolding,[],[f28,f35,f24,f24])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)) ),
    inference(definition_unfolding,[],[f30,f24,f24,f38])).

cnf(c_0,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X1))) = k1_enumset1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_36,plain,
    ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_1])).

cnf(c_211,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X1))) = k1_enumset1(X0,X1,X2) ),
    inference(superposition,[status(thm)],[c_36,c_1])).

cnf(c_2,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_192,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X1))) = k1_enumset1(X1,X0,X2) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_1121,plain,
    ( k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(superposition,[status(thm)],[c_211,c_192])).

cnf(c_100033,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X2,X1,X3))) ),
    inference(superposition,[status(thm)],[c_1121,c_2])).

cnf(c_100746,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X2),k1_enumset1(X0,X0,X2),k1_enumset1(X1,X1,X3))) ),
    inference(superposition,[status(thm)],[c_100033,c_2])).

cnf(c_6,negated_conjecture,
    ( k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_102182,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_100746,c_6])).

cnf(c_18,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_126,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4))
    | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != X1 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_795,plain,
    ( X0 != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4))
    | X0 = k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4))
    | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_126])).

cnf(c_2515,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4))
    | k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)))) != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4))
    | k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)))) = k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_3,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X3,X1),k4_tarski(X3,X1),k4_tarski(X3,X2)))) = k2_zfmisc_1(k1_enumset1(X0,X0,X3),k1_enumset1(X1,X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1734,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)))) = k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_22,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_61,plain,
    ( k1_enumset1(sK3,sK3,sK4) != X0
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) != X1
    | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k2_zfmisc_1(X1,X0) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_386,plain,
    ( k1_enumset1(sK3,sK3,sK4) != X0
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) != k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))
    | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),X0) ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_745,plain,
    ( k1_enumset1(sK3,sK3,sK4) != k1_enumset1(sK3,sK3,sK4)
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) != k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))
    | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_386])).

cnf(c_4,plain,
    ( k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k1_enumset1(X0,X0,X2),k1_enumset1(X1,X1,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_279,plain,
    ( k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)) = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_76,plain,
    ( X0 != X1
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) != X1
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) = X0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_144,plain,
    ( X0 != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) = X0
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_278,plain,
    ( k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)) != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_144])).

cnf(c_17,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_155,plain,
    ( k1_enumset1(sK3,sK3,sK4) = k1_enumset1(sK3,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_74,plain,
    ( k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_102182,c_2515,c_1734,c_745,c_279,c_278,c_155,c_74])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n009.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 14:54:41 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 31.81/4.43  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.81/4.43  
% 31.81/4.43  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.81/4.43  
% 31.81/4.43  ------  iProver source info
% 31.81/4.43  
% 31.81/4.43  git: date: 2020-06-30 10:37:57 +0100
% 31.81/4.43  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.81/4.43  git: non_committed_changes: false
% 31.81/4.43  git: last_make_outside_of_git: false
% 31.81/4.43  
% 31.81/4.43  ------ 
% 31.81/4.43  ------ Parsing...
% 31.81/4.43  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.81/4.43  
% 31.81/4.43  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 31.81/4.43  
% 31.81/4.43  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.81/4.43  
% 31.81/4.43  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.81/4.43  ------ Proving...
% 31.81/4.43  ------ Problem Properties 
% 31.81/4.43  
% 31.81/4.43  
% 31.81/4.43  clauses                                 7
% 31.81/4.43  conjectures                             1
% 31.81/4.43  EPR                                     0
% 31.81/4.43  Horn                                    7
% 31.81/4.43  unary                                   7
% 31.81/4.43  binary                                  0
% 31.81/4.43  lits                                    7
% 31.81/4.43  lits eq                                 7
% 31.81/4.43  fd_pure                                 0
% 31.81/4.43  fd_pseudo                               0
% 31.81/4.43  fd_cond                                 0
% 31.81/4.43  fd_pseudo_cond                          0
% 31.81/4.43  AC symbols                              0
% 31.81/4.43  
% 31.81/4.43  ------ Input Options Time Limit: Unbounded
% 31.81/4.43  
% 31.81/4.43  
% 31.81/4.43  ------ 
% 31.81/4.43  Current options:
% 31.81/4.43  ------ 
% 31.81/4.43  
% 31.81/4.43  
% 31.81/4.43  
% 31.81/4.43  
% 31.81/4.43  ------ Proving...
% 31.81/4.43  
% 31.81/4.43  
% 31.81/4.43  % SZS status Theorem for theBenchmark.p
% 31.81/4.43  
% 31.81/4.43  % SZS output start CNFRefutation for theBenchmark.p
% 31.81/4.43  
% 31.81/4.43  fof(f2,axiom,(
% 31.81/4.43    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 31.81/4.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.81/4.43  
% 31.81/4.43  fof(f20,plain,(
% 31.81/4.43    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)) )),
% 31.81/4.43    inference(cnf_transformation,[],[f2])).
% 31.81/4.43  
% 31.81/4.43  fof(f9,axiom,(
% 31.81/4.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 31.81/4.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.81/4.43  
% 31.81/4.43  fof(f27,plain,(
% 31.81/4.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 31.81/4.43    inference(cnf_transformation,[],[f9])).
% 31.81/4.43  
% 31.81/4.43  fof(f34,plain,(
% 31.81/4.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 31.81/4.43    inference(definition_unfolding,[],[f27,f24])).
% 31.81/4.43  
% 31.81/4.43  fof(f6,axiom,(
% 31.81/4.43    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 31.81/4.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.81/4.43  
% 31.81/4.43  fof(f24,plain,(
% 31.81/4.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 31.81/4.43    inference(cnf_transformation,[],[f6])).
% 31.81/4.43  
% 31.81/4.43  fof(f39,plain,(
% 31.81/4.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X0),k1_enumset1(X1,X1,X0),k1_enumset1(X2,X2,X0)))) )),
% 31.81/4.43    inference(definition_unfolding,[],[f20,f34,f24,f24])).
% 31.81/4.43  
% 31.81/4.43  fof(f7,axiom,(
% 31.81/4.43    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 31.81/4.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.81/4.43  
% 31.81/4.43  fof(f25,plain,(
% 31.81/4.43    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 31.81/4.43    inference(cnf_transformation,[],[f7])).
% 31.81/4.43  
% 31.81/4.43  fof(f1,axiom,(
% 31.81/4.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 31.81/4.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.81/4.43  
% 31.81/4.43  fof(f19,plain,(
% 31.81/4.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 31.81/4.43    inference(cnf_transformation,[],[f1])).
% 31.81/4.43  
% 31.81/4.43  fof(f35,plain,(
% 31.81/4.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)))) )),
% 31.81/4.43    inference(definition_unfolding,[],[f19,f34,f24,f24])).
% 31.81/4.43  
% 31.81/4.43  fof(f40,plain,(
% 31.81/4.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)))) )),
% 31.81/4.43    inference(definition_unfolding,[],[f25,f35])).
% 31.81/4.43  
% 31.81/4.43  fof(f8,axiom,(
% 31.81/4.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 31.81/4.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.81/4.43  
% 31.81/4.43  fof(f26,plain,(
% 31.81/4.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 31.81/4.43    inference(cnf_transformation,[],[f8])).
% 31.81/4.43  
% 31.81/4.43  fof(f3,axiom,(
% 31.81/4.43    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 31.81/4.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.81/4.43  
% 31.81/4.43  fof(f21,plain,(
% 31.81/4.43    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 31.81/4.43    inference(cnf_transformation,[],[f3])).
% 31.81/4.43  
% 31.81/4.43  fof(f36,plain,(
% 31.81/4.43    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4)))) )),
% 31.81/4.43    inference(definition_unfolding,[],[f21,f34,f24])).
% 31.81/4.43  
% 31.81/4.43  fof(f41,plain,(
% 31.81/4.43    ( ! [X2,X0,X3,X1] : (k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)))) )),
% 31.81/4.43    inference(definition_unfolding,[],[f26,f35,f36])).
% 31.81/4.43  
% 31.81/4.43  fof(f14,conjecture,(
% 31.81/4.43    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 31.81/4.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.81/4.43  
% 31.81/4.43  fof(f15,negated_conjecture,(
% 31.81/4.43    ~! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 31.81/4.43    inference(negated_conjecture,[],[f14])).
% 31.81/4.43  
% 31.81/4.43  fof(f16,plain,(
% 31.81/4.43    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 31.81/4.43    inference(ennf_transformation,[],[f15])).
% 31.81/4.43  
% 31.81/4.43  fof(f17,plain,(
% 31.81/4.43    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) => k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 31.81/4.43    introduced(choice_axiom,[])).
% 31.81/4.43  
% 31.81/4.43  fof(f18,plain,(
% 31.81/4.43    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 31.81/4.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f17])).
% 31.81/4.43  
% 31.81/4.43  fof(f33,plain,(
% 31.81/4.43    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 31.81/4.43    inference(cnf_transformation,[],[f18])).
% 31.81/4.43  
% 31.81/4.43  fof(f12,axiom,(
% 31.81/4.43    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 31.81/4.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.81/4.43  
% 31.81/4.43  fof(f31,plain,(
% 31.81/4.43    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 31.81/4.43    inference(cnf_transformation,[],[f12])).
% 31.81/4.43  
% 31.81/4.43  fof(f13,axiom,(
% 31.81/4.43    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 31.81/4.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.81/4.43  
% 31.81/4.43  fof(f32,plain,(
% 31.81/4.43    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 31.81/4.43    inference(cnf_transformation,[],[f13])).
% 31.81/4.43  
% 31.81/4.43  fof(f5,axiom,(
% 31.81/4.43    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 31.81/4.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.81/4.43  
% 31.81/4.43  fof(f23,plain,(
% 31.81/4.43    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 31.81/4.43    inference(cnf_transformation,[],[f5])).
% 31.81/4.43  
% 31.81/4.43  fof(f38,plain,(
% 31.81/4.43    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 31.81/4.43    inference(definition_unfolding,[],[f23,f24])).
% 31.81/4.43  
% 31.81/4.43  fof(f45,plain,(
% 31.81/4.43    k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4))),
% 31.81/4.43    inference(definition_unfolding,[],[f33,f35,f31,f31,f31,f31,f32,f24,f38,f24])).
% 31.81/4.43  
% 31.81/4.43  fof(f10,axiom,(
% 31.81/4.43    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 31.81/4.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.81/4.43  
% 31.81/4.43  fof(f28,plain,(
% 31.81/4.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 31.81/4.43    inference(cnf_transformation,[],[f10])).
% 31.81/4.43  
% 31.81/4.43  fof(f42,plain,(
% 31.81/4.43    ( ! [X2,X0,X3,X1] : (k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3)),k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3)),k1_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3)))) = k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) )),
% 31.81/4.43    inference(definition_unfolding,[],[f28,f35,f24,f24])).
% 31.81/4.43  
% 31.81/4.43  fof(f11,axiom,(
% 31.81/4.43    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 31.81/4.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.81/4.43  
% 31.81/4.43  fof(f30,plain,(
% 31.81/4.43    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 31.81/4.43    inference(cnf_transformation,[],[f11])).
% 31.81/4.43  
% 31.81/4.43  fof(f43,plain,(
% 31.81/4.43    ( ! [X2,X0,X1] : (k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) )),
% 31.81/4.43    inference(definition_unfolding,[],[f30,f24,f24,f38])).
% 31.81/4.43  
% 31.81/4.43  cnf(c_0,plain,
% 31.81/4.43      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X1))) = k1_enumset1(X1,X0,X2) ),
% 31.81/4.43      inference(cnf_transformation,[],[f39]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_1,plain,
% 31.81/4.43      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
% 31.81/4.43      inference(cnf_transformation,[],[f40]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_36,plain,
% 31.81/4.43      ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X0,X1) ),
% 31.81/4.43      inference(superposition,[status(thm)],[c_0,c_1]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_211,plain,
% 31.81/4.43      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X1))) = k1_enumset1(X0,X1,X2) ),
% 31.81/4.43      inference(superposition,[status(thm)],[c_36,c_1]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_2,plain,
% 31.81/4.43      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) ),
% 31.81/4.43      inference(cnf_transformation,[],[f41]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_192,plain,
% 31.81/4.43      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X1))) = k1_enumset1(X1,X0,X2) ),
% 31.81/4.43      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_1121,plain,
% 31.81/4.43      ( k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
% 31.81/4.43      inference(superposition,[status(thm)],[c_211,c_192]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_100033,plain,
% 31.81/4.43      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X2,X1,X3))) ),
% 31.81/4.43      inference(superposition,[status(thm)],[c_1121,c_2]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_100746,plain,
% 31.81/4.43      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X2),k1_enumset1(X0,X0,X2),k1_enumset1(X1,X1,X3))) ),
% 31.81/4.43      inference(superposition,[status(thm)],[c_100033,c_2]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_6,negated_conjecture,
% 31.81/4.43      ( k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
% 31.81/4.43      inference(cnf_transformation,[],[f45]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_102182,plain,
% 31.81/4.43      ( k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
% 31.81/4.43      inference(superposition,[status(thm)],[c_100746,c_6]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_18,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_126,plain,
% 31.81/4.43      ( X0 != X1
% 31.81/4.43      | X0 = k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4))
% 31.81/4.43      | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != X1 ),
% 31.81/4.43      inference(instantiation,[status(thm)],[c_18]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_795,plain,
% 31.81/4.43      ( X0 != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4))
% 31.81/4.43      | X0 = k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4))
% 31.81/4.43      | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
% 31.81/4.43      inference(instantiation,[status(thm)],[c_126]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_2515,plain,
% 31.81/4.43      ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4))
% 31.81/4.43      | k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)))) != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4))
% 31.81/4.43      | k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)))) = k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
% 31.81/4.43      inference(instantiation,[status(thm)],[c_795]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_3,plain,
% 31.81/4.43      ( k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X3,X1),k4_tarski(X3,X1),k4_tarski(X3,X2)))) = k2_zfmisc_1(k1_enumset1(X0,X0,X3),k1_enumset1(X1,X1,X2)) ),
% 31.81/4.43      inference(cnf_transformation,[],[f42]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_1734,plain,
% 31.81/4.43      ( k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)))) = k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
% 31.81/4.43      inference(instantiation,[status(thm)],[c_3]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_22,plain,
% 31.81/4.43      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 31.81/4.43      theory(equality) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_61,plain,
% 31.81/4.43      ( k1_enumset1(sK3,sK3,sK4) != X0
% 31.81/4.43      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) != X1
% 31.81/4.43      | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k2_zfmisc_1(X1,X0) ),
% 31.81/4.43      inference(instantiation,[status(thm)],[c_22]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_386,plain,
% 31.81/4.43      ( k1_enumset1(sK3,sK3,sK4) != X0
% 31.81/4.43      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) != k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))
% 31.81/4.43      | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),X0) ),
% 31.81/4.43      inference(instantiation,[status(thm)],[c_61]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_745,plain,
% 31.81/4.43      ( k1_enumset1(sK3,sK3,sK4) != k1_enumset1(sK3,sK3,sK4)
% 31.81/4.43      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) != k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))
% 31.81/4.43      | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
% 31.81/4.43      inference(instantiation,[status(thm)],[c_386]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_4,plain,
% 31.81/4.43      ( k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k1_enumset1(X0,X0,X2),k1_enumset1(X1,X1,X1)) ),
% 31.81/4.43      inference(cnf_transformation,[],[f43]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_279,plain,
% 31.81/4.43      ( k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)) = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) ),
% 31.81/4.43      inference(instantiation,[status(thm)],[c_4]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_76,plain,
% 31.81/4.43      ( X0 != X1
% 31.81/4.43      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) != X1
% 31.81/4.43      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) = X0 ),
% 31.81/4.43      inference(instantiation,[status(thm)],[c_18]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_144,plain,
% 31.81/4.43      ( X0 != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))
% 31.81/4.43      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) = X0
% 31.81/4.43      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) ),
% 31.81/4.43      inference(instantiation,[status(thm)],[c_76]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_278,plain,
% 31.81/4.43      ( k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)) != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))
% 31.81/4.43      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))
% 31.81/4.43      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) ),
% 31.81/4.43      inference(instantiation,[status(thm)],[c_144]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_17,plain,( X0 = X0 ),theory(equality) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_155,plain,
% 31.81/4.43      ( k1_enumset1(sK3,sK3,sK4) = k1_enumset1(sK3,sK3,sK4) ),
% 31.81/4.43      inference(instantiation,[status(thm)],[c_17]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(c_74,plain,
% 31.81/4.43      ( k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) ),
% 31.81/4.43      inference(instantiation,[status(thm)],[c_17]) ).
% 31.81/4.43  
% 31.81/4.43  cnf(contradiction,plain,
% 31.81/4.43      ( $false ),
% 31.81/4.43      inference(minisat,
% 31.81/4.43                [status(thm)],
% 31.81/4.43                [c_102182,c_2515,c_1734,c_745,c_279,c_278,c_155,c_74]) ).
% 31.81/4.43  
% 31.81/4.43  
% 31.81/4.43  % SZS output end CNFRefutation for theBenchmark.p
% 31.81/4.43  
% 31.81/4.43  ------                               Statistics
% 31.81/4.43  
% 31.81/4.43  ------ Selected
% 31.81/4.43  
% 31.81/4.43  total_time:                             3.716
% 31.81/4.43  
%------------------------------------------------------------------------------
