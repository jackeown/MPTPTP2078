%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:22 EST 2020

% Result     : Theorem 43.66s
% Output     : CNFRefutation 43.66s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 226 expanded)
%              Number of clauses        :   16 (  21 expanded)
%              Number of leaves         :   14 (  84 expanded)
%              Depth                    :   13
%              Number of atoms          :   57 ( 227 expanded)
%              Number of equality atoms :   56 ( 226 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f28,f26])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) ),
    inference(definition_unfolding,[],[f19,f33,f26,f26])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3)),k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3)),k1_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3)))) = k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) ),
    inference(definition_unfolding,[],[f29,f34,f26,f26])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) ),
    inference(definition_unfolding,[],[f22,f33,f26,f36])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) ),
    inference(definition_unfolding,[],[f27,f34])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X0),k1_enumset1(X1,X1,X0),k1_enumset1(X2,X2,X0))) ),
    inference(definition_unfolding,[],[f21,f33,f26,f26])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4))) ),
    inference(definition_unfolding,[],[f20,f33,f26])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4))) ),
    inference(definition_unfolding,[],[f24,f33,f26,f35])).

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

fof(f32,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f32,f34,f30,f30,f30,f30,f31,f26,f36,f26])).

cnf(c_5,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X3,X1),k4_tarski(X3,X1),k4_tarski(X3,X2)))) = k2_zfmisc_1(k1_enumset1(X0,X0,X3),k1_enumset1(X1,X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_295,plain,
    ( k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k1_enumset1(X0,X0,X2),k1_enumset1(X1,X1,X1)) ),
    inference(superposition,[status(thm)],[c_5,c_1])).

cnf(c_4,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_0,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X1))) = k1_enumset1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_82,plain,
    ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_426,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X1))) = k1_enumset1(X0,X1,X2) ),
    inference(superposition,[status(thm)],[c_82,c_4])).

cnf(c_3,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_189,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X1))) = k1_enumset1(X1,X0,X2) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_2156,plain,
    ( k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(superposition,[status(thm)],[c_426,c_189])).

cnf(c_111764,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X3,X2,X4))) ),
    inference(superposition,[status(thm)],[c_2156,c_3])).

cnf(c_116243,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X3),k1_enumset1(X0,X1,X3),k1_enumset1(X2,X2,X4))) ),
    inference(superposition,[status(thm)],[c_111764,c_3])).

cnf(c_6,negated_conjecture,
    ( k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_121466,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_116243,c_6])).

cnf(c_125310,plain,
    ( k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_5,c_121466])).

cnf(c_125785,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_295,c_125310])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 43.66/5.95  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.66/5.95  
% 43.66/5.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.66/5.95  
% 43.66/5.95  ------  iProver source info
% 43.66/5.95  
% 43.66/5.95  git: date: 2020-06-30 10:37:57 +0100
% 43.66/5.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.66/5.95  git: non_committed_changes: false
% 43.66/5.95  git: last_make_outside_of_git: false
% 43.66/5.95  
% 43.66/5.95  ------ 
% 43.66/5.95  ------ Parsing...
% 43.66/5.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.66/5.95  
% 43.66/5.95  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 43.66/5.95  
% 43.66/5.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.66/5.95  
% 43.66/5.95  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 43.66/5.95  ------ Proving...
% 43.66/5.95  ------ Problem Properties 
% 43.66/5.95  
% 43.66/5.95  
% 43.66/5.95  clauses                                 7
% 43.66/5.95  conjectures                             1
% 43.66/5.95  EPR                                     0
% 43.66/5.95  Horn                                    7
% 43.66/5.95  unary                                   7
% 43.66/5.95  binary                                  0
% 43.66/5.95  lits                                    7
% 43.66/5.95  lits eq                                 7
% 43.66/5.95  fd_pure                                 0
% 43.66/5.95  fd_pseudo                               0
% 43.66/5.95  fd_cond                                 0
% 43.66/5.95  fd_pseudo_cond                          0
% 43.66/5.95  AC symbols                              0
% 43.66/5.95  
% 43.66/5.95  ------ Input Options Time Limit: Unbounded
% 43.66/5.95  
% 43.66/5.95  
% 43.66/5.95  ------ 
% 43.66/5.95  Current options:
% 43.66/5.95  ------ 
% 43.66/5.95  
% 43.66/5.95  
% 43.66/5.95  
% 43.66/5.95  
% 43.66/5.95  ------ Proving...
% 43.66/5.95  
% 43.66/5.95  
% 43.66/5.95  % SZS status Theorem for theBenchmark.p
% 43.66/5.95  
% 43.66/5.95   Resolution empty clause
% 43.66/5.95  
% 43.66/5.95  % SZS output start CNFRefutation for theBenchmark.p
% 43.66/5.95  
% 43.66/5.95  fof(f11,axiom,(
% 43.66/5.95    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 43.66/5.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.66/5.95  
% 43.66/5.95  fof(f29,plain,(
% 43.66/5.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 43.66/5.95    inference(cnf_transformation,[],[f11])).
% 43.66/5.95  
% 43.66/5.95  fof(f1,axiom,(
% 43.66/5.95    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 43.66/5.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.66/5.95  
% 43.66/5.95  fof(f19,plain,(
% 43.66/5.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 43.66/5.95    inference(cnf_transformation,[],[f1])).
% 43.66/5.95  
% 43.66/5.95  fof(f10,axiom,(
% 43.66/5.95    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 43.66/5.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.66/5.95  
% 43.66/5.95  fof(f28,plain,(
% 43.66/5.95    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 43.66/5.95    inference(cnf_transformation,[],[f10])).
% 43.66/5.95  
% 43.66/5.95  fof(f33,plain,(
% 43.66/5.95    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 43.66/5.95    inference(definition_unfolding,[],[f28,f26])).
% 43.66/5.95  
% 43.66/5.95  fof(f34,plain,(
% 43.66/5.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)))) )),
% 43.66/5.95    inference(definition_unfolding,[],[f19,f33,f26,f26])).
% 43.66/5.95  
% 43.66/5.95  fof(f8,axiom,(
% 43.66/5.95    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 43.66/5.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.66/5.95  
% 43.66/5.95  fof(f26,plain,(
% 43.66/5.95    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 43.66/5.95    inference(cnf_transformation,[],[f8])).
% 43.66/5.95  
% 43.66/5.95  fof(f42,plain,(
% 43.66/5.95    ( ! [X2,X0,X3,X1] : (k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3)),k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3)),k1_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3)))) = k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) )),
% 43.66/5.95    inference(definition_unfolding,[],[f29,f34,f26,f26])).
% 43.66/5.95  
% 43.66/5.95  fof(f4,axiom,(
% 43.66/5.95    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2)),
% 43.66/5.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.66/5.95  
% 43.66/5.95  fof(f22,plain,(
% 43.66/5.95    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2)) )),
% 43.66/5.95    inference(cnf_transformation,[],[f4])).
% 43.66/5.95  
% 43.66/5.95  fof(f7,axiom,(
% 43.66/5.95    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 43.66/5.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.66/5.95  
% 43.66/5.95  fof(f25,plain,(
% 43.66/5.95    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 43.66/5.95    inference(cnf_transformation,[],[f7])).
% 43.66/5.95  
% 43.66/5.95  fof(f36,plain,(
% 43.66/5.95    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 43.66/5.95    inference(definition_unfolding,[],[f25,f26])).
% 43.66/5.95  
% 43.66/5.95  fof(f38,plain,(
% 43.66/5.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)))) )),
% 43.66/5.95    inference(definition_unfolding,[],[f22,f33,f26,f36])).
% 43.66/5.95  
% 43.66/5.95  fof(f9,axiom,(
% 43.66/5.95    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 43.66/5.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.66/5.95  
% 43.66/5.95  fof(f27,plain,(
% 43.66/5.95    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 43.66/5.95    inference(cnf_transformation,[],[f9])).
% 43.66/5.95  
% 43.66/5.95  fof(f41,plain,(
% 43.66/5.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)))) )),
% 43.66/5.95    inference(definition_unfolding,[],[f27,f34])).
% 43.66/5.95  
% 43.66/5.95  fof(f3,axiom,(
% 43.66/5.95    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 43.66/5.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.66/5.95  
% 43.66/5.95  fof(f21,plain,(
% 43.66/5.95    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)) )),
% 43.66/5.95    inference(cnf_transformation,[],[f3])).
% 43.66/5.95  
% 43.66/5.95  fof(f37,plain,(
% 43.66/5.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X0),k1_enumset1(X1,X1,X0),k1_enumset1(X2,X2,X0)))) )),
% 43.66/5.95    inference(definition_unfolding,[],[f21,f33,f26,f26])).
% 43.66/5.95  
% 43.66/5.95  fof(f6,axiom,(
% 43.66/5.95    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 43.66/5.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.66/5.95  
% 43.66/5.95  fof(f24,plain,(
% 43.66/5.95    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 43.66/5.95    inference(cnf_transformation,[],[f6])).
% 43.66/5.95  
% 43.66/5.95  fof(f2,axiom,(
% 43.66/5.95    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 43.66/5.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.66/5.95  
% 43.66/5.95  fof(f20,plain,(
% 43.66/5.95    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 43.66/5.95    inference(cnf_transformation,[],[f2])).
% 43.66/5.95  
% 43.66/5.95  fof(f35,plain,(
% 43.66/5.95    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4)))) )),
% 43.66/5.95    inference(definition_unfolding,[],[f20,f33,f26])).
% 43.66/5.95  
% 43.66/5.95  fof(f40,plain,(
% 43.66/5.95    ( ! [X4,X2,X0,X3,X1] : (k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4)))) )),
% 43.66/5.95    inference(definition_unfolding,[],[f24,f33,f26,f35])).
% 43.66/5.95  
% 43.66/5.95  fof(f14,conjecture,(
% 43.66/5.95    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 43.66/5.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.66/5.95  
% 43.66/5.95  fof(f15,negated_conjecture,(
% 43.66/5.95    ~! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 43.66/5.95    inference(negated_conjecture,[],[f14])).
% 43.66/5.95  
% 43.66/5.95  fof(f16,plain,(
% 43.66/5.95    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 43.66/5.95    inference(ennf_transformation,[],[f15])).
% 43.66/5.95  
% 43.66/5.95  fof(f17,plain,(
% 43.66/5.95    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) => k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 43.66/5.95    introduced(choice_axiom,[])).
% 43.66/5.95  
% 43.66/5.95  fof(f18,plain,(
% 43.66/5.95    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 43.66/5.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f17])).
% 43.66/5.95  
% 43.66/5.95  fof(f32,plain,(
% 43.66/5.95    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 43.66/5.95    inference(cnf_transformation,[],[f18])).
% 43.66/5.95  
% 43.66/5.95  fof(f12,axiom,(
% 43.66/5.95    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 43.66/5.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.66/5.95  
% 43.66/5.95  fof(f30,plain,(
% 43.66/5.95    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 43.66/5.95    inference(cnf_transformation,[],[f12])).
% 43.66/5.95  
% 43.66/5.95  fof(f13,axiom,(
% 43.66/5.95    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 43.66/5.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.66/5.95  
% 43.66/5.95  fof(f31,plain,(
% 43.66/5.95    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 43.66/5.95    inference(cnf_transformation,[],[f13])).
% 43.66/5.95  
% 43.66/5.95  fof(f43,plain,(
% 43.66/5.95    k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4))),
% 43.66/5.95    inference(definition_unfolding,[],[f32,f34,f30,f30,f30,f30,f31,f26,f36,f26])).
% 43.66/5.95  
% 43.66/5.95  cnf(c_5,plain,
% 43.66/5.95      ( k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X3,X1),k4_tarski(X3,X1),k4_tarski(X3,X2)))) = k2_zfmisc_1(k1_enumset1(X0,X0,X3),k1_enumset1(X1,X1,X2)) ),
% 43.66/5.95      inference(cnf_transformation,[],[f42]) ).
% 43.66/5.95  
% 43.66/5.95  cnf(c_1,plain,
% 43.66/5.95      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) = k1_enumset1(X0,X1,X2) ),
% 43.66/5.95      inference(cnf_transformation,[],[f38]) ).
% 43.66/5.95  
% 43.66/5.95  cnf(c_295,plain,
% 43.66/5.95      ( k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k1_enumset1(X0,X0,X2),k1_enumset1(X1,X1,X1)) ),
% 43.66/5.95      inference(superposition,[status(thm)],[c_5,c_1]) ).
% 43.66/5.95  
% 43.66/5.95  cnf(c_4,plain,
% 43.66/5.95      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
% 43.66/5.95      inference(cnf_transformation,[],[f41]) ).
% 43.66/5.95  
% 43.66/5.95  cnf(c_0,plain,
% 43.66/5.95      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X1))) = k1_enumset1(X1,X0,X2) ),
% 43.66/5.95      inference(cnf_transformation,[],[f37]) ).
% 43.66/5.95  
% 43.66/5.95  cnf(c_82,plain,
% 43.66/5.95      ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X0,X1) ),
% 43.66/5.95      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 43.66/5.95  
% 43.66/5.95  cnf(c_426,plain,
% 43.66/5.95      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X1))) = k1_enumset1(X0,X1,X2) ),
% 43.66/5.95      inference(superposition,[status(thm)],[c_82,c_4]) ).
% 43.66/5.95  
% 43.66/5.95  cnf(c_3,plain,
% 43.66/5.95      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4))) ),
% 43.66/5.95      inference(cnf_transformation,[],[f40]) ).
% 43.66/5.95  
% 43.66/5.95  cnf(c_189,plain,
% 43.66/5.95      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X1))) = k1_enumset1(X1,X0,X2) ),
% 43.66/5.95      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 43.66/5.95  
% 43.66/5.95  cnf(c_2156,plain,
% 43.66/5.95      ( k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
% 43.66/5.95      inference(superposition,[status(thm)],[c_426,c_189]) ).
% 43.66/5.95  
% 43.66/5.95  cnf(c_111764,plain,
% 43.66/5.95      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X3,X2,X4))) ),
% 43.66/5.95      inference(superposition,[status(thm)],[c_2156,c_3]) ).
% 43.66/5.95  
% 43.66/5.95  cnf(c_116243,plain,
% 43.66/5.95      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X4))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X3),k1_enumset1(X0,X1,X3),k1_enumset1(X2,X2,X4))) ),
% 43.66/5.95      inference(superposition,[status(thm)],[c_111764,c_3]) ).
% 43.66/5.95  
% 43.66/5.95  cnf(c_6,negated_conjecture,
% 43.66/5.95      ( k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
% 43.66/5.95      inference(cnf_transformation,[],[f43]) ).
% 43.66/5.95  
% 43.66/5.95  cnf(c_121466,plain,
% 43.66/5.95      ( k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
% 43.66/5.95      inference(superposition,[status(thm)],[c_116243,c_6]) ).
% 43.66/5.95  
% 43.66/5.95  cnf(c_125310,plain,
% 43.66/5.95      ( k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
% 43.66/5.95      inference(superposition,[status(thm)],[c_5,c_121466]) ).
% 43.66/5.95  
% 43.66/5.95  cnf(c_125785,plain,
% 43.66/5.95      ( $false ),
% 43.66/5.95      inference(superposition,[status(thm)],[c_295,c_125310]) ).
% 43.66/5.95  
% 43.66/5.95  
% 43.66/5.95  % SZS output end CNFRefutation for theBenchmark.p
% 43.66/5.95  
% 43.66/5.95  ------                               Statistics
% 43.66/5.95  
% 43.66/5.95  ------ Selected
% 43.66/5.95  
% 43.66/5.95  total_time:                             5.259
% 43.66/5.95  
%------------------------------------------------------------------------------
