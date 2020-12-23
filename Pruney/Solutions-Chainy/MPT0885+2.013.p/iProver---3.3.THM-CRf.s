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
% DateTime   : Thu Dec  3 11:58:27 EST 2020

% Result     : Theorem 11.53s
% Output     : CNFRefutation 11.53s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 864 expanded)
%              Number of clauses        :   35 (  89 expanded)
%              Number of leaves         :   14 ( 289 expanded)
%              Depth                    :   17
%              Number of atoms          :   77 ( 866 expanded)
%              Number of equality atoms :   76 ( 865 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f22,f32])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X3)) ),
    inference(definition_unfolding,[],[f26,f24,f33,f33])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f21,f33])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X4,X4,X4,X4,X4)) ),
    inference(definition_unfolding,[],[f20,f24,f34])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X3,X4)) ),
    inference(definition_unfolding,[],[f19,f33,f32])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f18,f33,f33])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f25,f33])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(ennf_transformation,[],[f14])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))
   => k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).

fof(f31,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,(
    k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f31,f24,f29,f29,f29,f29,f30,f34,f33,f33])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X2,X0,X1] : k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(definition_unfolding,[],[f27,f33,f34,f33])).

cnf(c_4,plain,
    ( k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X3),k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3,plain,
    ( k2_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X4,X4,X4,X4,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1,plain,
    ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_52,plain,
    ( k3_enumset1(X0,X1,X2,X2,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(superposition,[status(thm)],[c_3,c_1])).

cnf(c_63,plain,
    ( k2_xboole_0(k3_enumset1(X0,X1,X2,X2,X2),k3_enumset1(X3,X3,X3,X3,X3)) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(superposition,[status(thm)],[c_52,c_3])).

cnf(c_2,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_40,plain,
    ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X3,X4)) = k3_enumset1(X1,X0,X2,X3,X4) ),
    inference(superposition,[status(thm)],[c_2,c_1])).

cnf(c_70,plain,
    ( k2_xboole_0(k3_enumset1(X0,X0,X1,X1,X1),k3_enumset1(X2,X2,X2,X3,X4)) = k3_enumset1(X1,X0,X2,X3,X4) ),
    inference(superposition,[status(thm)],[c_52,c_40])).

cnf(c_2993,plain,
    ( k2_xboole_0(k2_xboole_0(k3_enumset1(X0,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1)),k3_enumset1(X2,X2,X2,X3,X4)) = k3_enumset1(X1,X0,X2,X3,X4) ),
    inference(superposition,[status(thm)],[c_63,c_70])).

cnf(c_66,plain,
    ( k3_enumset1(X0,X1,X2,X2,X2) = k3_enumset1(X1,X1,X1,X0,X2) ),
    inference(superposition,[status(thm)],[c_3,c_40])).

cnf(c_174,plain,
    ( k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X1,X1,X1,X0,X2) ),
    inference(superposition,[status(thm)],[c_66,c_52])).

cnf(c_274,plain,
    ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X3,X4)) = k3_enumset1(X0,X1,X3,X2,X4) ),
    inference(superposition,[status(thm)],[c_174,c_1])).

cnf(c_42,plain,
    ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(X0,X1,X3,X3,X2) ),
    inference(superposition,[status(thm)],[c_2,c_1])).

cnf(c_2286,plain,
    ( k2_xboole_0(k3_enumset1(X0,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X2)) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X2,X2,X2,X2,X1)) ),
    inference(superposition,[status(thm)],[c_63,c_42])).

cnf(c_0,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_31,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_36,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_31,c_0])).

cnf(c_44,plain,
    ( k2_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X3,X3,X3,X3,X4)) = k3_enumset1(X3,X4,X0,X1,X2) ),
    inference(superposition,[status(thm)],[c_1,c_36])).

cnf(c_461,plain,
    ( k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X3,X3,X0,X1,X2) ),
    inference(superposition,[status(thm)],[c_44,c_3])).

cnf(c_53,plain,
    ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X2,X3,X4)) = k3_enumset1(X1,X2,X3,X4,X0) ),
    inference(superposition,[status(thm)],[c_3,c_36])).

cnf(c_1450,plain,
    ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X2,X3,X4)) = k3_enumset1(X4,X1,X2,X3,X0) ),
    inference(superposition,[status(thm)],[c_461,c_53])).

cnf(c_311,plain,
    ( k2_xboole_0(k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)),k3_enumset1(X3,X3,X3,X3,X3)) = k3_enumset1(X0,X2,X2,X1,X3) ),
    inference(superposition,[status(thm)],[c_42,c_3])).

cnf(c_77,plain,
    ( k2_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X3,X3,X3,X3,X4)) = k3_enumset1(X4,X3,X0,X1,X2) ),
    inference(superposition,[status(thm)],[c_40,c_36])).

cnf(c_313,plain,
    ( k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X3,X2,X2,X1,X0) ),
    inference(demodulation,[status(thm)],[c_311,c_53,c_77])).

cnf(c_666,plain,
    ( k3_enumset1(X0,X1,X1,X1,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_313,c_2])).

cnf(c_56,plain,
    ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2)) = k3_enumset1(X0,X1,X1,X1,X2) ),
    inference(superposition,[status(thm)],[c_52,c_3])).

cnf(c_1720,plain,
    ( k2_xboole_0(k3_enumset1(X0,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X2)) = k3_enumset1(X0,X1,X1,X1,X2) ),
    inference(superposition,[status(thm)],[c_666,c_56])).

cnf(c_2320,plain,
    ( k2_xboole_0(k3_enumset1(X0,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X2)) = k3_enumset1(X1,X2,X2,X2,X0) ),
    inference(demodulation,[status(thm)],[c_2286,c_1450,c_1720])).

cnf(c_3060,plain,
    ( k3_enumset1(X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X3,X2,X4) ),
    inference(demodulation,[status(thm)],[c_2993,c_274,c_2320])).

cnf(c_7,negated_conjecture,
    ( k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_44087,plain,
    ( k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_3060,c_7])).

cnf(c_44640,plain,
    ( k2_zfmisc_1(k3_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_4,c_44087])).

cnf(c_6,plain,
    ( k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_44641,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_44640,c_6])).

cnf(c_44642,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_44641])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:14:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 11.53/1.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.53/1.97  
% 11.53/1.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.53/1.97  
% 11.53/1.97  ------  iProver source info
% 11.53/1.97  
% 11.53/1.97  git: date: 2020-06-30 10:37:57 +0100
% 11.53/1.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.53/1.97  git: non_committed_changes: false
% 11.53/1.97  git: last_make_outside_of_git: false
% 11.53/1.97  
% 11.53/1.97  ------ 
% 11.53/1.97  
% 11.53/1.97  ------ Input Options
% 11.53/1.97  
% 11.53/1.97  --out_options                           all
% 11.53/1.97  --tptp_safe_out                         true
% 11.53/1.97  --problem_path                          ""
% 11.53/1.97  --include_path                          ""
% 11.53/1.97  --clausifier                            res/vclausify_rel
% 11.53/1.97  --clausifier_options                    --mode clausify
% 11.53/1.97  --stdin                                 false
% 11.53/1.97  --stats_out                             all
% 11.53/1.97  
% 11.53/1.97  ------ General Options
% 11.53/1.97  
% 11.53/1.97  --fof                                   false
% 11.53/1.97  --time_out_real                         305.
% 11.53/1.97  --time_out_virtual                      -1.
% 11.53/1.97  --symbol_type_check                     false
% 11.53/1.97  --clausify_out                          false
% 11.53/1.97  --sig_cnt_out                           false
% 11.53/1.97  --trig_cnt_out                          false
% 11.53/1.97  --trig_cnt_out_tolerance                1.
% 11.53/1.97  --trig_cnt_out_sk_spl                   false
% 11.53/1.97  --abstr_cl_out                          false
% 11.53/1.97  
% 11.53/1.97  ------ Global Options
% 11.53/1.97  
% 11.53/1.97  --schedule                              default
% 11.53/1.97  --add_important_lit                     false
% 11.53/1.97  --prop_solver_per_cl                    1000
% 11.53/1.97  --min_unsat_core                        false
% 11.53/1.97  --soft_assumptions                      false
% 11.53/1.97  --soft_lemma_size                       3
% 11.53/1.97  --prop_impl_unit_size                   0
% 11.53/1.97  --prop_impl_unit                        []
% 11.53/1.97  --share_sel_clauses                     true
% 11.53/1.97  --reset_solvers                         false
% 11.53/1.97  --bc_imp_inh                            [conj_cone]
% 11.53/1.97  --conj_cone_tolerance                   3.
% 11.53/1.97  --extra_neg_conj                        none
% 11.53/1.97  --large_theory_mode                     true
% 11.53/1.97  --prolific_symb_bound                   200
% 11.53/1.97  --lt_threshold                          2000
% 11.53/1.97  --clause_weak_htbl                      true
% 11.53/1.97  --gc_record_bc_elim                     false
% 11.53/1.97  
% 11.53/1.97  ------ Preprocessing Options
% 11.53/1.97  
% 11.53/1.97  --preprocessing_flag                    true
% 11.53/1.97  --time_out_prep_mult                    0.1
% 11.53/1.97  --splitting_mode                        input
% 11.53/1.97  --splitting_grd                         true
% 11.53/1.97  --splitting_cvd                         false
% 11.53/1.97  --splitting_cvd_svl                     false
% 11.53/1.97  --splitting_nvd                         32
% 11.53/1.97  --sub_typing                            true
% 11.53/1.97  --prep_gs_sim                           true
% 11.53/1.97  --prep_unflatten                        true
% 11.53/1.97  --prep_res_sim                          true
% 11.53/1.97  --prep_upred                            true
% 11.53/1.97  --prep_sem_filter                       exhaustive
% 11.53/1.97  --prep_sem_filter_out                   false
% 11.53/1.97  --pred_elim                             true
% 11.53/1.97  --res_sim_input                         true
% 11.53/1.97  --eq_ax_congr_red                       true
% 11.53/1.97  --pure_diseq_elim                       true
% 11.53/1.97  --brand_transform                       false
% 11.53/1.97  --non_eq_to_eq                          false
% 11.53/1.97  --prep_def_merge                        true
% 11.53/1.97  --prep_def_merge_prop_impl              false
% 11.53/1.97  --prep_def_merge_mbd                    true
% 11.53/1.97  --prep_def_merge_tr_red                 false
% 11.53/1.97  --prep_def_merge_tr_cl                  false
% 11.53/1.97  --smt_preprocessing                     true
% 11.53/1.97  --smt_ac_axioms                         fast
% 11.53/1.97  --preprocessed_out                      false
% 11.53/1.97  --preprocessed_stats                    false
% 11.53/1.97  
% 11.53/1.97  ------ Abstraction refinement Options
% 11.53/1.97  
% 11.53/1.97  --abstr_ref                             []
% 11.53/1.97  --abstr_ref_prep                        false
% 11.53/1.97  --abstr_ref_until_sat                   false
% 11.53/1.97  --abstr_ref_sig_restrict                funpre
% 11.53/1.97  --abstr_ref_af_restrict_to_split_sk     false
% 11.53/1.97  --abstr_ref_under                       []
% 11.53/1.97  
% 11.53/1.97  ------ SAT Options
% 11.53/1.97  
% 11.53/1.97  --sat_mode                              false
% 11.53/1.97  --sat_fm_restart_options                ""
% 11.53/1.97  --sat_gr_def                            false
% 11.53/1.97  --sat_epr_types                         true
% 11.53/1.97  --sat_non_cyclic_types                  false
% 11.53/1.97  --sat_finite_models                     false
% 11.53/1.97  --sat_fm_lemmas                         false
% 11.53/1.97  --sat_fm_prep                           false
% 11.53/1.97  --sat_fm_uc_incr                        true
% 11.53/1.97  --sat_out_model                         small
% 11.53/1.97  --sat_out_clauses                       false
% 11.53/1.97  
% 11.53/1.97  ------ QBF Options
% 11.53/1.97  
% 11.53/1.97  --qbf_mode                              false
% 11.53/1.97  --qbf_elim_univ                         false
% 11.53/1.97  --qbf_dom_inst                          none
% 11.53/1.97  --qbf_dom_pre_inst                      false
% 11.53/1.97  --qbf_sk_in                             false
% 11.53/1.97  --qbf_pred_elim                         true
% 11.53/1.97  --qbf_split                             512
% 11.53/1.97  
% 11.53/1.97  ------ BMC1 Options
% 11.53/1.97  
% 11.53/1.97  --bmc1_incremental                      false
% 11.53/1.97  --bmc1_axioms                           reachable_all
% 11.53/1.97  --bmc1_min_bound                        0
% 11.53/1.97  --bmc1_max_bound                        -1
% 11.53/1.97  --bmc1_max_bound_default                -1
% 11.53/1.97  --bmc1_symbol_reachability              true
% 11.53/1.97  --bmc1_property_lemmas                  false
% 11.53/1.97  --bmc1_k_induction                      false
% 11.53/1.97  --bmc1_non_equiv_states                 false
% 11.53/1.97  --bmc1_deadlock                         false
% 11.53/1.97  --bmc1_ucm                              false
% 11.53/1.97  --bmc1_add_unsat_core                   none
% 11.53/1.97  --bmc1_unsat_core_children              false
% 11.53/1.97  --bmc1_unsat_core_extrapolate_axioms    false
% 11.53/1.97  --bmc1_out_stat                         full
% 11.53/1.97  --bmc1_ground_init                      false
% 11.53/1.97  --bmc1_pre_inst_next_state              false
% 11.53/1.97  --bmc1_pre_inst_state                   false
% 11.53/1.97  --bmc1_pre_inst_reach_state             false
% 11.53/1.97  --bmc1_out_unsat_core                   false
% 11.53/1.97  --bmc1_aig_witness_out                  false
% 11.53/1.97  --bmc1_verbose                          false
% 11.53/1.97  --bmc1_dump_clauses_tptp                false
% 11.53/1.97  --bmc1_dump_unsat_core_tptp             false
% 11.53/1.97  --bmc1_dump_file                        -
% 11.53/1.97  --bmc1_ucm_expand_uc_limit              128
% 11.53/1.97  --bmc1_ucm_n_expand_iterations          6
% 11.53/1.97  --bmc1_ucm_extend_mode                  1
% 11.53/1.97  --bmc1_ucm_init_mode                    2
% 11.53/1.97  --bmc1_ucm_cone_mode                    none
% 11.53/1.97  --bmc1_ucm_reduced_relation_type        0
% 11.53/1.97  --bmc1_ucm_relax_model                  4
% 11.53/1.97  --bmc1_ucm_full_tr_after_sat            true
% 11.53/1.97  --bmc1_ucm_expand_neg_assumptions       false
% 11.53/1.97  --bmc1_ucm_layered_model                none
% 11.53/1.97  --bmc1_ucm_max_lemma_size               10
% 11.53/1.97  
% 11.53/1.97  ------ AIG Options
% 11.53/1.97  
% 11.53/1.97  --aig_mode                              false
% 11.53/1.97  
% 11.53/1.97  ------ Instantiation Options
% 11.53/1.97  
% 11.53/1.97  --instantiation_flag                    true
% 11.53/1.97  --inst_sos_flag                         false
% 11.53/1.97  --inst_sos_phase                        true
% 11.53/1.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.53/1.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.53/1.97  --inst_lit_sel_side                     num_symb
% 11.53/1.97  --inst_solver_per_active                1400
% 11.53/1.97  --inst_solver_calls_frac                1.
% 11.53/1.97  --inst_passive_queue_type               priority_queues
% 11.53/1.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.53/1.97  --inst_passive_queues_freq              [25;2]
% 11.53/1.97  --inst_dismatching                      true
% 11.53/1.97  --inst_eager_unprocessed_to_passive     true
% 11.53/1.97  --inst_prop_sim_given                   true
% 11.53/1.97  --inst_prop_sim_new                     false
% 11.53/1.97  --inst_subs_new                         false
% 11.53/1.97  --inst_eq_res_simp                      false
% 11.53/1.97  --inst_subs_given                       false
% 11.53/1.97  --inst_orphan_elimination               true
% 11.53/1.97  --inst_learning_loop_flag               true
% 11.53/1.97  --inst_learning_start                   3000
% 11.53/1.97  --inst_learning_factor                  2
% 11.53/1.97  --inst_start_prop_sim_after_learn       3
% 11.53/1.97  --inst_sel_renew                        solver
% 11.53/1.97  --inst_lit_activity_flag                true
% 11.53/1.97  --inst_restr_to_given                   false
% 11.53/1.97  --inst_activity_threshold               500
% 11.53/1.97  --inst_out_proof                        true
% 11.53/1.97  
% 11.53/1.97  ------ Resolution Options
% 11.53/1.97  
% 11.53/1.97  --resolution_flag                       true
% 11.53/1.97  --res_lit_sel                           adaptive
% 11.53/1.97  --res_lit_sel_side                      none
% 11.53/1.97  --res_ordering                          kbo
% 11.53/1.97  --res_to_prop_solver                    active
% 11.53/1.97  --res_prop_simpl_new                    false
% 11.53/1.97  --res_prop_simpl_given                  true
% 11.53/1.97  --res_passive_queue_type                priority_queues
% 11.53/1.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.53/1.97  --res_passive_queues_freq               [15;5]
% 11.53/1.97  --res_forward_subs                      full
% 11.53/1.97  --res_backward_subs                     full
% 11.53/1.97  --res_forward_subs_resolution           true
% 11.53/1.97  --res_backward_subs_resolution          true
% 11.53/1.97  --res_orphan_elimination                true
% 11.53/1.97  --res_time_limit                        2.
% 11.53/1.97  --res_out_proof                         true
% 11.53/1.97  
% 11.53/1.97  ------ Superposition Options
% 11.53/1.97  
% 11.53/1.97  --superposition_flag                    true
% 11.53/1.97  --sup_passive_queue_type                priority_queues
% 11.53/1.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.53/1.97  --sup_passive_queues_freq               [8;1;4]
% 11.53/1.97  --demod_completeness_check              fast
% 11.53/1.97  --demod_use_ground                      true
% 11.53/1.97  --sup_to_prop_solver                    passive
% 11.53/1.97  --sup_prop_simpl_new                    true
% 11.53/1.97  --sup_prop_simpl_given                  true
% 11.53/1.97  --sup_fun_splitting                     false
% 11.53/1.97  --sup_smt_interval                      50000
% 11.53/1.97  
% 11.53/1.97  ------ Superposition Simplification Setup
% 11.53/1.97  
% 11.53/1.97  --sup_indices_passive                   []
% 11.53/1.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.53/1.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.53/1.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.53/1.97  --sup_full_triv                         [TrivRules;PropSubs]
% 11.53/1.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.53/1.97  --sup_full_bw                           [BwDemod]
% 11.53/1.97  --sup_immed_triv                        [TrivRules]
% 11.53/1.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/1.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.53/1.97  --sup_immed_bw_main                     []
% 11.53/1.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.53/1.97  --sup_input_triv                        [Unflattening;TrivRules]
% 11.53/1.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.53/1.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.53/1.97  
% 11.53/1.97  ------ Combination Options
% 11.53/1.97  
% 11.53/1.97  --comb_res_mult                         3
% 11.53/1.97  --comb_sup_mult                         2
% 11.53/1.97  --comb_inst_mult                        10
% 11.53/1.97  
% 11.53/1.97  ------ Debug Options
% 11.53/1.97  
% 11.53/1.97  --dbg_backtrace                         false
% 11.53/1.97  --dbg_dump_prop_clauses                 false
% 11.53/1.97  --dbg_dump_prop_clauses_file            -
% 11.53/1.97  --dbg_out_stat                          false
% 11.53/1.97  ------ Parsing...
% 11.53/1.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.53/1.97  
% 11.53/1.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 11.53/1.97  
% 11.53/1.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.53/1.97  
% 11.53/1.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.53/1.97  ------ Proving...
% 11.53/1.97  ------ Problem Properties 
% 11.53/1.97  
% 11.53/1.97  
% 11.53/1.97  clauses                                 8
% 11.53/1.97  conjectures                             1
% 11.53/1.97  EPR                                     0
% 11.53/1.97  Horn                                    8
% 11.53/1.97  unary                                   8
% 11.53/1.97  binary                                  0
% 11.53/1.97  lits                                    8
% 11.53/1.97  lits eq                                 8
% 11.53/1.97  fd_pure                                 0
% 11.53/1.97  fd_pseudo                               0
% 11.53/1.97  fd_cond                                 0
% 11.53/1.97  fd_pseudo_cond                          0
% 11.53/1.97  AC symbols                              0
% 11.53/1.97  
% 11.53/1.97  ------ Schedule UEQ
% 11.53/1.97  
% 11.53/1.97  ------ pure equality problem: resolution off 
% 11.53/1.97  
% 11.53/1.97  ------ Option_UEQ Time Limit: Unbounded
% 11.53/1.97  
% 11.53/1.97  
% 11.53/1.97  ------ 
% 11.53/1.97  Current options:
% 11.53/1.97  ------ 
% 11.53/1.97  
% 11.53/1.97  ------ Input Options
% 11.53/1.97  
% 11.53/1.97  --out_options                           all
% 11.53/1.97  --tptp_safe_out                         true
% 11.53/1.97  --problem_path                          ""
% 11.53/1.97  --include_path                          ""
% 11.53/1.97  --clausifier                            res/vclausify_rel
% 11.53/1.97  --clausifier_options                    --mode clausify
% 11.53/1.97  --stdin                                 false
% 11.53/1.97  --stats_out                             all
% 11.53/1.97  
% 11.53/1.97  ------ General Options
% 11.53/1.97  
% 11.53/1.97  --fof                                   false
% 11.53/1.97  --time_out_real                         305.
% 11.53/1.97  --time_out_virtual                      -1.
% 11.53/1.97  --symbol_type_check                     false
% 11.53/1.97  --clausify_out                          false
% 11.53/1.97  --sig_cnt_out                           false
% 11.53/1.97  --trig_cnt_out                          false
% 11.53/1.97  --trig_cnt_out_tolerance                1.
% 11.53/1.97  --trig_cnt_out_sk_spl                   false
% 11.53/1.97  --abstr_cl_out                          false
% 11.53/1.97  
% 11.53/1.97  ------ Global Options
% 11.53/1.97  
% 11.53/1.97  --schedule                              default
% 11.53/1.97  --add_important_lit                     false
% 11.53/1.97  --prop_solver_per_cl                    1000
% 11.53/1.97  --min_unsat_core                        false
% 11.53/1.97  --soft_assumptions                      false
% 11.53/1.97  --soft_lemma_size                       3
% 11.53/1.97  --prop_impl_unit_size                   0
% 11.53/1.97  --prop_impl_unit                        []
% 11.53/1.97  --share_sel_clauses                     true
% 11.53/1.97  --reset_solvers                         false
% 11.53/1.97  --bc_imp_inh                            [conj_cone]
% 11.53/1.97  --conj_cone_tolerance                   3.
% 11.53/1.97  --extra_neg_conj                        none
% 11.53/1.97  --large_theory_mode                     true
% 11.53/1.97  --prolific_symb_bound                   200
% 11.53/1.97  --lt_threshold                          2000
% 11.53/1.97  --clause_weak_htbl                      true
% 11.53/1.97  --gc_record_bc_elim                     false
% 11.53/1.97  
% 11.53/1.97  ------ Preprocessing Options
% 11.53/1.97  
% 11.53/1.97  --preprocessing_flag                    true
% 11.53/1.97  --time_out_prep_mult                    0.1
% 11.53/1.97  --splitting_mode                        input
% 11.53/1.97  --splitting_grd                         true
% 11.53/1.97  --splitting_cvd                         false
% 11.53/1.97  --splitting_cvd_svl                     false
% 11.53/1.97  --splitting_nvd                         32
% 11.53/1.97  --sub_typing                            true
% 11.53/1.97  --prep_gs_sim                           true
% 11.53/1.97  --prep_unflatten                        true
% 11.53/1.97  --prep_res_sim                          true
% 11.53/1.97  --prep_upred                            true
% 11.53/1.97  --prep_sem_filter                       exhaustive
% 11.53/1.97  --prep_sem_filter_out                   false
% 11.53/1.97  --pred_elim                             true
% 11.53/1.97  --res_sim_input                         true
% 11.53/1.97  --eq_ax_congr_red                       true
% 11.53/1.97  --pure_diseq_elim                       true
% 11.53/1.97  --brand_transform                       false
% 11.53/1.97  --non_eq_to_eq                          false
% 11.53/1.97  --prep_def_merge                        true
% 11.53/1.97  --prep_def_merge_prop_impl              false
% 11.53/1.97  --prep_def_merge_mbd                    true
% 11.53/1.97  --prep_def_merge_tr_red                 false
% 11.53/1.97  --prep_def_merge_tr_cl                  false
% 11.53/1.97  --smt_preprocessing                     true
% 11.53/1.97  --smt_ac_axioms                         fast
% 11.53/1.97  --preprocessed_out                      false
% 11.53/1.97  --preprocessed_stats                    false
% 11.53/1.97  
% 11.53/1.97  ------ Abstraction refinement Options
% 11.53/1.97  
% 11.53/1.97  --abstr_ref                             []
% 11.53/1.97  --abstr_ref_prep                        false
% 11.53/1.97  --abstr_ref_until_sat                   false
% 11.53/1.97  --abstr_ref_sig_restrict                funpre
% 11.53/1.97  --abstr_ref_af_restrict_to_split_sk     false
% 11.53/1.97  --abstr_ref_under                       []
% 11.53/1.97  
% 11.53/1.97  ------ SAT Options
% 11.53/1.97  
% 11.53/1.97  --sat_mode                              false
% 11.53/1.97  --sat_fm_restart_options                ""
% 11.53/1.97  --sat_gr_def                            false
% 11.53/1.97  --sat_epr_types                         true
% 11.53/1.97  --sat_non_cyclic_types                  false
% 11.53/1.97  --sat_finite_models                     false
% 11.53/1.97  --sat_fm_lemmas                         false
% 11.53/1.97  --sat_fm_prep                           false
% 11.53/1.97  --sat_fm_uc_incr                        true
% 11.53/1.97  --sat_out_model                         small
% 11.53/1.97  --sat_out_clauses                       false
% 11.53/1.97  
% 11.53/1.97  ------ QBF Options
% 11.53/1.97  
% 11.53/1.97  --qbf_mode                              false
% 11.53/1.97  --qbf_elim_univ                         false
% 11.53/1.97  --qbf_dom_inst                          none
% 11.53/1.97  --qbf_dom_pre_inst                      false
% 11.53/1.97  --qbf_sk_in                             false
% 11.53/1.97  --qbf_pred_elim                         true
% 11.53/1.97  --qbf_split                             512
% 11.53/1.97  
% 11.53/1.97  ------ BMC1 Options
% 11.53/1.97  
% 11.53/1.97  --bmc1_incremental                      false
% 11.53/1.97  --bmc1_axioms                           reachable_all
% 11.53/1.97  --bmc1_min_bound                        0
% 11.53/1.97  --bmc1_max_bound                        -1
% 11.53/1.97  --bmc1_max_bound_default                -1
% 11.53/1.97  --bmc1_symbol_reachability              true
% 11.53/1.97  --bmc1_property_lemmas                  false
% 11.53/1.98  --bmc1_k_induction                      false
% 11.53/1.98  --bmc1_non_equiv_states                 false
% 11.53/1.98  --bmc1_deadlock                         false
% 11.53/1.98  --bmc1_ucm                              false
% 11.53/1.98  --bmc1_add_unsat_core                   none
% 11.53/1.98  --bmc1_unsat_core_children              false
% 11.53/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.53/1.98  --bmc1_out_stat                         full
% 11.53/1.98  --bmc1_ground_init                      false
% 11.53/1.98  --bmc1_pre_inst_next_state              false
% 11.53/1.98  --bmc1_pre_inst_state                   false
% 11.53/1.98  --bmc1_pre_inst_reach_state             false
% 11.53/1.98  --bmc1_out_unsat_core                   false
% 11.53/1.98  --bmc1_aig_witness_out                  false
% 11.53/1.98  --bmc1_verbose                          false
% 11.53/1.98  --bmc1_dump_clauses_tptp                false
% 11.53/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.53/1.98  --bmc1_dump_file                        -
% 11.53/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.53/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.53/1.98  --bmc1_ucm_extend_mode                  1
% 11.53/1.98  --bmc1_ucm_init_mode                    2
% 11.53/1.98  --bmc1_ucm_cone_mode                    none
% 11.53/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.53/1.98  --bmc1_ucm_relax_model                  4
% 11.53/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.53/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.53/1.98  --bmc1_ucm_layered_model                none
% 11.53/1.98  --bmc1_ucm_max_lemma_size               10
% 11.53/1.98  
% 11.53/1.98  ------ AIG Options
% 11.53/1.98  
% 11.53/1.98  --aig_mode                              false
% 11.53/1.98  
% 11.53/1.98  ------ Instantiation Options
% 11.53/1.98  
% 11.53/1.98  --instantiation_flag                    false
% 11.53/1.98  --inst_sos_flag                         false
% 11.53/1.98  --inst_sos_phase                        true
% 11.53/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.53/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.53/1.98  --inst_lit_sel_side                     num_symb
% 11.53/1.98  --inst_solver_per_active                1400
% 11.53/1.98  --inst_solver_calls_frac                1.
% 11.53/1.98  --inst_passive_queue_type               priority_queues
% 11.53/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.53/1.98  --inst_passive_queues_freq              [25;2]
% 11.53/1.98  --inst_dismatching                      true
% 11.53/1.98  --inst_eager_unprocessed_to_passive     true
% 11.53/1.98  --inst_prop_sim_given                   true
% 11.53/1.98  --inst_prop_sim_new                     false
% 11.53/1.98  --inst_subs_new                         false
% 11.53/1.98  --inst_eq_res_simp                      false
% 11.53/1.98  --inst_subs_given                       false
% 11.53/1.98  --inst_orphan_elimination               true
% 11.53/1.98  --inst_learning_loop_flag               true
% 11.53/1.98  --inst_learning_start                   3000
% 11.53/1.98  --inst_learning_factor                  2
% 11.53/1.98  --inst_start_prop_sim_after_learn       3
% 11.53/1.98  --inst_sel_renew                        solver
% 11.53/1.98  --inst_lit_activity_flag                true
% 11.53/1.98  --inst_restr_to_given                   false
% 11.53/1.98  --inst_activity_threshold               500
% 11.53/1.98  --inst_out_proof                        true
% 11.53/1.98  
% 11.53/1.98  ------ Resolution Options
% 11.53/1.98  
% 11.53/1.98  --resolution_flag                       false
% 11.53/1.98  --res_lit_sel                           adaptive
% 11.53/1.98  --res_lit_sel_side                      none
% 11.53/1.98  --res_ordering                          kbo
% 11.53/1.98  --res_to_prop_solver                    active
% 11.53/1.98  --res_prop_simpl_new                    false
% 11.53/1.98  --res_prop_simpl_given                  true
% 11.53/1.98  --res_passive_queue_type                priority_queues
% 11.53/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.53/1.98  --res_passive_queues_freq               [15;5]
% 11.53/1.98  --res_forward_subs                      full
% 11.53/1.98  --res_backward_subs                     full
% 11.53/1.98  --res_forward_subs_resolution           true
% 11.53/1.98  --res_backward_subs_resolution          true
% 11.53/1.98  --res_orphan_elimination                true
% 11.53/1.98  --res_time_limit                        2.
% 11.53/1.98  --res_out_proof                         true
% 11.53/1.98  
% 11.53/1.98  ------ Superposition Options
% 11.53/1.98  
% 11.53/1.98  --superposition_flag                    true
% 11.53/1.98  --sup_passive_queue_type                priority_queues
% 11.53/1.98  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.53/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.53/1.98  --demod_completeness_check              fast
% 11.53/1.98  --demod_use_ground                      true
% 11.53/1.98  --sup_to_prop_solver                    active
% 11.53/1.98  --sup_prop_simpl_new                    false
% 11.53/1.98  --sup_prop_simpl_given                  false
% 11.53/1.98  --sup_fun_splitting                     true
% 11.53/1.98  --sup_smt_interval                      10000
% 11.53/1.98  
% 11.53/1.98  ------ Superposition Simplification Setup
% 11.53/1.98  
% 11.53/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.53/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.53/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.53/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.53/1.98  --sup_full_triv                         [TrivRules]
% 11.53/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.53/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.53/1.98  --sup_immed_triv                        [TrivRules]
% 11.53/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/1.98  --sup_immed_bw_main                     []
% 11.53/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.53/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.53/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/1.98  --sup_input_bw                          [BwDemod;BwSubsumption]
% 11.53/1.98  
% 11.53/1.98  ------ Combination Options
% 11.53/1.98  
% 11.53/1.98  --comb_res_mult                         1
% 11.53/1.98  --comb_sup_mult                         1
% 11.53/1.98  --comb_inst_mult                        1000000
% 11.53/1.98  
% 11.53/1.98  ------ Debug Options
% 11.53/1.98  
% 11.53/1.98  --dbg_backtrace                         false
% 11.53/1.98  --dbg_dump_prop_clauses                 false
% 11.53/1.98  --dbg_dump_prop_clauses_file            -
% 11.53/1.98  --dbg_out_stat                          false
% 11.53/1.98  
% 11.53/1.98  
% 11.53/1.98  
% 11.53/1.98  
% 11.53/1.98  ------ Proving...
% 11.53/1.98  
% 11.53/1.98  
% 11.53/1.98  % SZS status Theorem for theBenchmark.p
% 11.53/1.98  
% 11.53/1.98   Resolution empty clause
% 11.53/1.98  
% 11.53/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.53/1.98  
% 11.53/1.98  fof(f9,axiom,(
% 11.53/1.98    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f26,plain,(
% 11.53/1.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 11.53/1.98    inference(cnf_transformation,[],[f9])).
% 11.53/1.98  
% 11.53/1.98  fof(f5,axiom,(
% 11.53/1.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f22,plain,(
% 11.53/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.53/1.98    inference(cnf_transformation,[],[f5])).
% 11.53/1.98  
% 11.53/1.98  fof(f6,axiom,(
% 11.53/1.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f23,plain,(
% 11.53/1.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.53/1.98    inference(cnf_transformation,[],[f6])).
% 11.53/1.98  
% 11.53/1.98  fof(f7,axiom,(
% 11.53/1.98    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f24,plain,(
% 11.53/1.98    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 11.53/1.98    inference(cnf_transformation,[],[f7])).
% 11.53/1.98  
% 11.53/1.98  fof(f32,plain,(
% 11.53/1.98    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 11.53/1.98    inference(definition_unfolding,[],[f23,f24])).
% 11.53/1.98  
% 11.53/1.98  fof(f33,plain,(
% 11.53/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 11.53/1.98    inference(definition_unfolding,[],[f22,f32])).
% 11.53/1.98  
% 11.53/1.98  fof(f39,plain,(
% 11.53/1.98    ( ! [X2,X0,X3,X1] : (k3_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X3))) )),
% 11.53/1.98    inference(definition_unfolding,[],[f26,f24,f33,f33])).
% 11.53/1.98  
% 11.53/1.98  fof(f3,axiom,(
% 11.53/1.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f20,plain,(
% 11.53/1.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 11.53/1.98    inference(cnf_transformation,[],[f3])).
% 11.53/1.98  
% 11.53/1.98  fof(f4,axiom,(
% 11.53/1.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f21,plain,(
% 11.53/1.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.53/1.98    inference(cnf_transformation,[],[f4])).
% 11.53/1.98  
% 11.53/1.98  fof(f34,plain,(
% 11.53/1.98    ( ! [X0] : (k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 11.53/1.98    inference(definition_unfolding,[],[f21,f33])).
% 11.53/1.98  
% 11.53/1.98  fof(f38,plain,(
% 11.53/1.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X4,X4,X4,X4,X4))) )),
% 11.53/1.98    inference(definition_unfolding,[],[f20,f24,f34])).
% 11.53/1.98  
% 11.53/1.98  fof(f2,axiom,(
% 11.53/1.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f19,plain,(
% 11.53/1.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 11.53/1.98    inference(cnf_transformation,[],[f2])).
% 11.53/1.98  
% 11.53/1.98  fof(f36,plain,(
% 11.53/1.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X3,X4))) )),
% 11.53/1.98    inference(definition_unfolding,[],[f19,f33,f32])).
% 11.53/1.98  
% 11.53/1.98  fof(f1,axiom,(
% 11.53/1.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f18,plain,(
% 11.53/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 11.53/1.98    inference(cnf_transformation,[],[f1])).
% 11.53/1.98  
% 11.53/1.98  fof(f37,plain,(
% 11.53/1.98    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 11.53/1.98    inference(definition_unfolding,[],[f18,f33,f33])).
% 11.53/1.98  
% 11.53/1.98  fof(f8,axiom,(
% 11.53/1.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f25,plain,(
% 11.53/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.53/1.98    inference(cnf_transformation,[],[f8])).
% 11.53/1.98  
% 11.53/1.98  fof(f35,plain,(
% 11.53/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 11.53/1.98    inference(definition_unfolding,[],[f25,f33])).
% 11.53/1.98  
% 11.53/1.98  fof(f13,conjecture,(
% 11.53/1.98    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f14,negated_conjecture,(
% 11.53/1.98    ~! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))),
% 11.53/1.98    inference(negated_conjecture,[],[f13])).
% 11.53/1.98  
% 11.53/1.98  fof(f15,plain,(
% 11.53/1.98    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))),
% 11.53/1.98    inference(ennf_transformation,[],[f14])).
% 11.53/1.98  
% 11.53/1.98  fof(f16,plain,(
% 11.53/1.98    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) => k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 11.53/1.98    introduced(choice_axiom,[])).
% 11.53/1.98  
% 11.53/1.98  fof(f17,plain,(
% 11.53/1.98    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 11.53/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).
% 11.53/1.98  
% 11.53/1.98  fof(f31,plain,(
% 11.53/1.98    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 11.53/1.98    inference(cnf_transformation,[],[f17])).
% 11.53/1.98  
% 11.53/1.98  fof(f11,axiom,(
% 11.53/1.98    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f29,plain,(
% 11.53/1.98    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 11.53/1.98    inference(cnf_transformation,[],[f11])).
% 11.53/1.98  
% 11.53/1.98  fof(f12,axiom,(
% 11.53/1.98    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f30,plain,(
% 11.53/1.98    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 11.53/1.98    inference(cnf_transformation,[],[f12])).
% 11.53/1.98  
% 11.53/1.98  fof(f42,plain,(
% 11.53/1.98    k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4))),
% 11.53/1.98    inference(definition_unfolding,[],[f31,f24,f29,f29,f29,f29,f30,f34,f33,f33])).
% 11.53/1.98  
% 11.53/1.98  fof(f10,axiom,(
% 11.53/1.98    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 11.53/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.98  
% 11.53/1.98  fof(f27,plain,(
% 11.53/1.98    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 11.53/1.98    inference(cnf_transformation,[],[f10])).
% 11.53/1.98  
% 11.53/1.98  fof(f41,plain,(
% 11.53/1.98    ( ! [X2,X0,X1] : (k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2))) )),
% 11.53/1.98    inference(definition_unfolding,[],[f27,f33,f34,f33])).
% 11.53/1.98  
% 11.53/1.98  cnf(c_4,plain,
% 11.53/1.98      ( k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X3),k3_enumset1(X1,X1,X1,X1,X2)) ),
% 11.53/1.98      inference(cnf_transformation,[],[f39]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_3,plain,
% 11.53/1.98      ( k2_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X4,X4,X4,X4,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 11.53/1.98      inference(cnf_transformation,[],[f38]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_1,plain,
% 11.53/1.98      ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 11.53/1.98      inference(cnf_transformation,[],[f36]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_52,plain,
% 11.53/1.98      ( k3_enumset1(X0,X1,X2,X2,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_3,c_1]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_63,plain,
% 11.53/1.98      ( k2_xboole_0(k3_enumset1(X0,X1,X2,X2,X2),k3_enumset1(X3,X3,X3,X3,X3)) = k3_enumset1(X0,X0,X1,X2,X3) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_52,c_3]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_2,plain,
% 11.53/1.98      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 11.53/1.98      inference(cnf_transformation,[],[f37]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_40,plain,
% 11.53/1.98      ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X3,X4)) = k3_enumset1(X1,X0,X2,X3,X4) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_2,c_1]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_70,plain,
% 11.53/1.98      ( k2_xboole_0(k3_enumset1(X0,X0,X1,X1,X1),k3_enumset1(X2,X2,X2,X3,X4)) = k3_enumset1(X1,X0,X2,X3,X4) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_52,c_40]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_2993,plain,
% 11.53/1.98      ( k2_xboole_0(k2_xboole_0(k3_enumset1(X0,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1)),k3_enumset1(X2,X2,X2,X3,X4)) = k3_enumset1(X1,X0,X2,X3,X4) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_63,c_70]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_66,plain,
% 11.53/1.98      ( k3_enumset1(X0,X1,X2,X2,X2) = k3_enumset1(X1,X1,X1,X0,X2) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_3,c_40]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_174,plain,
% 11.53/1.98      ( k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X1,X1,X1,X0,X2) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_66,c_52]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_274,plain,
% 11.53/1.98      ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X3,X4)) = k3_enumset1(X0,X1,X3,X2,X4) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_174,c_1]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_42,plain,
% 11.53/1.98      ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X3)) = k3_enumset1(X0,X1,X3,X3,X2) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_2,c_1]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_2286,plain,
% 11.53/1.98      ( k2_xboole_0(k3_enumset1(X0,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X2)) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X2,X2,X2,X2,X1)) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_63,c_42]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_0,plain,
% 11.53/1.98      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k2_xboole_0(X0,X1) ),
% 11.53/1.98      inference(cnf_transformation,[],[f35]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_31,plain,
% 11.53/1.98      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k2_xboole_0(X1,X0) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_36,plain,
% 11.53/1.98      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_31,c_0]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_44,plain,
% 11.53/1.98      ( k2_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X3,X3,X3,X3,X4)) = k3_enumset1(X3,X4,X0,X1,X2) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_1,c_36]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_461,plain,
% 11.53/1.98      ( k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X3,X3,X0,X1,X2) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_44,c_3]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_53,plain,
% 11.53/1.98      ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X2,X3,X4)) = k3_enumset1(X1,X2,X3,X4,X0) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_3,c_36]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_1450,plain,
% 11.53/1.98      ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X2,X3,X4)) = k3_enumset1(X4,X1,X2,X3,X0) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_461,c_53]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_311,plain,
% 11.53/1.98      ( k2_xboole_0(k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)),k3_enumset1(X3,X3,X3,X3,X3)) = k3_enumset1(X0,X2,X2,X1,X3) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_42,c_3]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_77,plain,
% 11.53/1.98      ( k2_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X3,X3,X3,X3,X4)) = k3_enumset1(X4,X3,X0,X1,X2) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_40,c_36]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_313,plain,
% 11.53/1.98      ( k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X3,X2,X2,X1,X0) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_311,c_53,c_77]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_666,plain,
% 11.53/1.98      ( k3_enumset1(X0,X1,X1,X1,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_313,c_2]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_56,plain,
% 11.53/1.98      ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X2)) = k3_enumset1(X0,X1,X1,X1,X2) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_52,c_3]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_1720,plain,
% 11.53/1.98      ( k2_xboole_0(k3_enumset1(X0,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X2)) = k3_enumset1(X0,X1,X1,X1,X2) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_666,c_56]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_2320,plain,
% 11.53/1.98      ( k2_xboole_0(k3_enumset1(X0,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X2)) = k3_enumset1(X1,X2,X2,X2,X0) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_2286,c_1450,c_1720]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_3060,plain,
% 11.53/1.98      ( k3_enumset1(X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X3,X2,X4) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_2993,c_274,c_2320]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_7,negated_conjecture,
% 11.53/1.98      ( k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) ),
% 11.53/1.98      inference(cnf_transformation,[],[f42]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_44087,plain,
% 11.53/1.98      ( k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_3060,c_7]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_44640,plain,
% 11.53/1.98      ( k2_zfmisc_1(k3_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) ),
% 11.53/1.98      inference(superposition,[status(thm)],[c_4,c_44087]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_6,plain,
% 11.53/1.98      ( k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)) ),
% 11.53/1.98      inference(cnf_transformation,[],[f41]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_44641,plain,
% 11.53/1.98      ( k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)),k3_enumset1(sK3,sK3,sK3,sK3,sK4)) ),
% 11.53/1.98      inference(demodulation,[status(thm)],[c_44640,c_6]) ).
% 11.53/1.98  
% 11.53/1.98  cnf(c_44642,plain,
% 11.53/1.98      ( $false ),
% 11.53/1.98      inference(equality_resolution_simp,[status(thm)],[c_44641]) ).
% 11.53/1.98  
% 11.53/1.98  
% 11.53/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.53/1.98  
% 11.53/1.98  ------                               Statistics
% 11.53/1.98  
% 11.53/1.98  ------ General
% 11.53/1.98  
% 11.53/1.98  abstr_ref_over_cycles:                  0
% 11.53/1.98  abstr_ref_under_cycles:                 0
% 11.53/1.98  gc_basic_clause_elim:                   0
% 11.53/1.98  forced_gc_time:                         0
% 11.53/1.98  parsing_time:                           0.007
% 11.53/1.98  unif_index_cands_time:                  0.
% 11.53/1.98  unif_index_add_time:                    0.
% 11.53/1.98  orderings_time:                         0.
% 11.53/1.98  out_proof_time:                         0.006
% 11.53/1.98  total_time:                             1.361
% 11.53/1.98  num_of_symbols:                         41
% 11.53/1.98  num_of_terms:                           13707
% 11.53/1.98  
% 11.53/1.98  ------ Preprocessing
% 11.53/1.98  
% 11.53/1.98  num_of_splits:                          0
% 11.53/1.98  num_of_split_atoms:                     0
% 11.53/1.98  num_of_reused_defs:                     0
% 11.53/1.98  num_eq_ax_congr_red:                    0
% 11.53/1.98  num_of_sem_filtered_clauses:            0
% 11.53/1.98  num_of_subtypes:                        1
% 11.53/1.98  monotx_restored_types:                  0
% 11.53/1.98  sat_num_of_epr_types:                   0
% 11.53/1.98  sat_num_of_non_cyclic_types:            0
% 11.53/1.98  sat_guarded_non_collapsed_types:        0
% 11.53/1.98  num_pure_diseq_elim:                    0
% 11.53/1.98  simp_replaced_by:                       0
% 11.53/1.98  res_preprocessed:                       23
% 11.53/1.98  prep_upred:                             0
% 11.53/1.98  prep_unflattend:                        0
% 11.53/1.98  smt_new_axioms:                         0
% 11.53/1.98  pred_elim_cands:                        0
% 11.53/1.98  pred_elim:                              0
% 11.53/1.98  pred_elim_cl:                           0
% 11.53/1.98  pred_elim_cycles:                       0
% 11.53/1.98  merged_defs:                            0
% 11.53/1.98  merged_defs_ncl:                        0
% 11.53/1.98  bin_hyper_res:                          0
% 11.53/1.98  prep_cycles:                            2
% 11.53/1.98  pred_elim_time:                         0.
% 11.53/1.98  splitting_time:                         0.
% 11.53/1.98  sem_filter_time:                        0.
% 11.53/1.98  monotx_time:                            0.
% 11.53/1.98  subtype_inf_time:                       0.
% 11.53/1.98  
% 11.53/1.98  ------ Problem properties
% 11.53/1.98  
% 11.53/1.98  clauses:                                8
% 11.53/1.98  conjectures:                            1
% 11.53/1.98  epr:                                    0
% 11.53/1.98  horn:                                   8
% 11.53/1.98  ground:                                 1
% 11.53/1.98  unary:                                  8
% 11.53/1.98  binary:                                 0
% 11.53/1.98  lits:                                   8
% 11.53/1.98  lits_eq:                                8
% 11.53/1.98  fd_pure:                                0
% 11.53/1.98  fd_pseudo:                              0
% 11.53/1.98  fd_cond:                                0
% 11.53/1.98  fd_pseudo_cond:                         0
% 11.53/1.98  ac_symbols:                             0
% 11.53/1.98  
% 11.53/1.98  ------ Propositional Solver
% 11.53/1.98  
% 11.53/1.98  prop_solver_calls:                      13
% 11.53/1.98  prop_fast_solver_calls:                 74
% 11.53/1.98  smt_solver_calls:                       0
% 11.53/1.98  smt_fast_solver_calls:                  0
% 11.53/1.98  prop_num_of_clauses:                    232
% 11.53/1.98  prop_preprocess_simplified:             513
% 11.53/1.98  prop_fo_subsumed:                       0
% 11.53/1.98  prop_solver_time:                       0.
% 11.53/1.98  smt_solver_time:                        0.
% 11.53/1.98  smt_fast_solver_time:                   0.
% 11.53/1.98  prop_fast_solver_time:                  0.
% 11.53/1.98  prop_unsat_core_time:                   0.
% 11.53/1.98  
% 11.53/1.98  ------ QBF
% 11.53/1.98  
% 11.53/1.98  qbf_q_res:                              0
% 11.53/1.98  qbf_num_tautologies:                    0
% 11.53/1.98  qbf_prep_cycles:                        0
% 11.53/1.98  
% 11.53/1.98  ------ BMC1
% 11.53/1.98  
% 11.53/1.98  bmc1_current_bound:                     -1
% 11.53/1.98  bmc1_last_solved_bound:                 -1
% 11.53/1.98  bmc1_unsat_core_size:                   -1
% 11.53/1.98  bmc1_unsat_core_parents_size:           -1
% 11.53/1.98  bmc1_merge_next_fun:                    0
% 11.53/1.98  bmc1_unsat_core_clauses_time:           0.
% 11.53/1.98  
% 11.53/1.98  ------ Instantiation
% 11.53/1.98  
% 11.53/1.98  inst_num_of_clauses:                    0
% 11.53/1.98  inst_num_in_passive:                    0
% 11.53/1.98  inst_num_in_active:                     0
% 11.53/1.98  inst_num_in_unprocessed:                0
% 11.53/1.98  inst_num_of_loops:                      0
% 11.53/1.98  inst_num_of_learning_restarts:          0
% 11.53/1.98  inst_num_moves_active_passive:          0
% 11.53/1.98  inst_lit_activity:                      0
% 11.53/1.98  inst_lit_activity_moves:                0
% 11.53/1.98  inst_num_tautologies:                   0
% 11.53/1.98  inst_num_prop_implied:                  0
% 11.53/1.98  inst_num_existing_simplified:           0
% 11.53/1.98  inst_num_eq_res_simplified:             0
% 11.53/1.98  inst_num_child_elim:                    0
% 11.53/1.98  inst_num_of_dismatching_blockings:      0
% 11.53/1.98  inst_num_of_non_proper_insts:           0
% 11.53/1.98  inst_num_of_duplicates:                 0
% 11.53/1.98  inst_inst_num_from_inst_to_res:         0
% 11.53/1.98  inst_dismatching_checking_time:         0.
% 11.53/1.98  
% 11.53/1.98  ------ Resolution
% 11.53/1.98  
% 11.53/1.98  res_num_of_clauses:                     0
% 11.53/1.98  res_num_in_passive:                     0
% 11.53/1.98  res_num_in_active:                      0
% 11.53/1.98  res_num_of_loops:                       25
% 11.53/1.98  res_forward_subset_subsumed:            0
% 11.53/1.98  res_backward_subset_subsumed:           0
% 11.53/1.98  res_forward_subsumed:                   0
% 11.53/1.98  res_backward_subsumed:                  0
% 11.53/1.98  res_forward_subsumption_resolution:     0
% 11.53/1.98  res_backward_subsumption_resolution:    0
% 11.53/1.98  res_clause_to_clause_subsumption:       212551
% 11.53/1.98  res_orphan_elimination:                 0
% 11.53/1.98  res_tautology_del:                      0
% 11.53/1.98  res_num_eq_res_simplified:              0
% 11.53/1.98  res_num_sel_changes:                    0
% 11.53/1.98  res_moves_from_active_to_pass:          0
% 11.53/1.98  
% 11.53/1.98  ------ Superposition
% 11.53/1.98  
% 11.53/1.98  sup_time_total:                         0.
% 11.53/1.98  sup_time_generating:                    0.
% 11.53/1.98  sup_time_sim_full:                      0.
% 11.53/1.98  sup_time_sim_immed:                     0.
% 11.53/1.98  
% 11.53/1.98  sup_num_of_clauses:                     3380
% 11.53/1.98  sup_num_in_active:                      199
% 11.53/1.98  sup_num_in_passive:                     3181
% 11.53/1.98  sup_num_of_loops:                       210
% 11.53/1.98  sup_fw_superposition:                   21740
% 11.53/1.98  sup_bw_superposition:                   22383
% 11.53/1.98  sup_immediate_simplified:               777
% 11.53/1.98  sup_given_eliminated:                   0
% 11.53/1.98  comparisons_done:                       0
% 11.53/1.98  comparisons_avoided:                    0
% 11.53/1.98  
% 11.53/1.98  ------ Simplifications
% 11.53/1.98  
% 11.53/1.98  
% 11.53/1.98  sim_fw_subset_subsumed:                 0
% 11.53/1.98  sim_bw_subset_subsumed:                 0
% 11.53/1.98  sim_fw_subsumed:                        275
% 11.53/1.98  sim_bw_subsumed:                        73
% 11.53/1.98  sim_fw_subsumption_res:                 0
% 11.53/1.98  sim_bw_subsumption_res:                 0
% 11.53/1.98  sim_tautology_del:                      0
% 11.53/1.98  sim_eq_tautology_del:                   19
% 11.53/1.98  sim_eq_res_simp:                        0
% 11.53/1.98  sim_fw_demodulated:                     418
% 11.53/1.98  sim_bw_demodulated:                     1
% 11.53/1.98  sim_light_normalised:                   64
% 11.53/1.98  sim_joinable_taut:                      0
% 11.53/1.98  sim_joinable_simp:                      0
% 11.53/1.98  sim_ac_normalised:                      0
% 11.53/1.98  sim_smt_subsumption:                    0
% 11.53/1.98  
%------------------------------------------------------------------------------
