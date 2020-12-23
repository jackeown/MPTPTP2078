%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:28 EST 2020

% Result     : Theorem 31.45s
% Output     : CNFRefutation 31.45s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f25,f22])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X0),k1_enumset1(X1,X1,X0),k1_enumset1(X2,X2,X0))) ),
    inference(definition_unfolding,[],[f19,f32,f22,f22])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) ),
    inference(definition_unfolding,[],[f18,f32,f22,f22])).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) ),
    inference(definition_unfolding,[],[f23,f33])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4))) ),
    inference(definition_unfolding,[],[f20,f32,f22])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) ),
    inference(definition_unfolding,[],[f24,f33,f34])).

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

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f42,plain,(
    k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f31,f33,f29,f29,f29,f29,f30,f35,f22,f22])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3)),k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3)),k1_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3)))) = k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) ),
    inference(definition_unfolding,[],[f26,f33,f22,f22])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)) ),
    inference(definition_unfolding,[],[f27,f22,f35,f22])).

cnf(c_0,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X1))) = k1_enumset1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_36,plain,
    ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_1])).

cnf(c_209,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X1))) = k1_enumset1(X0,X1,X2) ),
    inference(superposition,[status(thm)],[c_36,c_1])).

cnf(c_2,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_190,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X1))) = k1_enumset1(X1,X0,X2) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_1126,plain,
    ( k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(superposition,[status(thm)],[c_209,c_190])).

cnf(c_102700,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X2,X1,X3))) ),
    inference(superposition,[status(thm)],[c_1126,c_2])).

cnf(c_103413,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X2),k1_enumset1(X0,X0,X2),k1_enumset1(X1,X1,X3))) ),
    inference(superposition,[status(thm)],[c_102700,c_2])).

cnf(c_6,negated_conjecture,
    ( k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_104863,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_103413,c_6])).

cnf(c_18,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_126,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)),k1_enumset1(sK3,sK3,sK4))
    | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) != X1 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_802,plain,
    ( X0 != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k1_enumset1(sK3,sK3,sK4))
    | X0 = k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)),k1_enumset1(sK3,sK3,sK4))
    | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_126])).

cnf(c_5638,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k1_enumset1(sK3,sK3,sK4))
    | k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)))) != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k1_enumset1(sK3,sK3,sK4))
    | k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)))) = k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_3,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X3,X1),k4_tarski(X3,X1),k4_tarski(X3,X2)))) = k2_zfmisc_1(k1_enumset1(X0,X0,X3),k1_enumset1(X1,X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1796,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)))) = k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_22,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_61,plain,
    ( k1_enumset1(sK3,sK3,sK4) != X0
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) != X1
    | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) = k2_zfmisc_1(X1,X0) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_384,plain,
    ( k1_enumset1(sK3,sK3,sK4) != X0
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) != k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))
    | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) = k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),X0) ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_664,plain,
    ( k1_enumset1(sK3,sK3,sK4) != k1_enumset1(sK3,sK3,sK4)
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) != k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))
    | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) = k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_384])).

cnf(c_5,plain,
    ( k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_277,plain,
    ( k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_76,plain,
    ( X0 != X1
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) != X1
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) = X0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_144,plain,
    ( X0 != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) = X0
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_276,plain,
    ( k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) = k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_144])).

cnf(c_17,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_153,plain,
    ( k1_enumset1(sK3,sK3,sK4) = k1_enumset1(sK3,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_74,plain,
    ( k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_104863,c_5638,c_1796,c_664,c_277,c_276,c_153,c_74])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:16:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 31.45/4.43  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.45/4.43  
% 31.45/4.43  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.45/4.43  
% 31.45/4.43  ------  iProver source info
% 31.45/4.43  
% 31.45/4.43  git: date: 2020-06-30 10:37:57 +0100
% 31.45/4.43  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.45/4.43  git: non_committed_changes: false
% 31.45/4.43  git: last_make_outside_of_git: false
% 31.45/4.43  
% 31.45/4.43  ------ 
% 31.45/4.43  ------ Parsing...
% 31.45/4.43  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.45/4.43  
% 31.45/4.43  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 31.45/4.43  
% 31.45/4.43  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.45/4.43  
% 31.45/4.43  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 31.45/4.43  ------ Proving...
% 31.45/4.43  ------ Problem Properties 
% 31.45/4.43  
% 31.45/4.43  
% 31.45/4.43  clauses                                 7
% 31.45/4.43  conjectures                             1
% 31.45/4.43  EPR                                     0
% 31.45/4.43  Horn                                    7
% 31.45/4.43  unary                                   7
% 31.45/4.43  binary                                  0
% 31.45/4.43  lits                                    7
% 31.45/4.43  lits eq                                 7
% 31.45/4.43  fd_pure                                 0
% 31.45/4.43  fd_pseudo                               0
% 31.45/4.43  fd_cond                                 0
% 31.45/4.43  fd_pseudo_cond                          0
% 31.45/4.43  AC symbols                              0
% 31.45/4.43  
% 31.45/4.43  ------ Input Options Time Limit: Unbounded
% 31.45/4.43  
% 31.45/4.43  
% 31.45/4.43  ------ 
% 31.45/4.43  Current options:
% 31.45/4.43  ------ 
% 31.45/4.43  
% 31.45/4.43  
% 31.45/4.43  
% 31.45/4.43  
% 31.45/4.43  ------ Proving...
% 31.45/4.43  
% 31.45/4.43  
% 31.45/4.43  % SZS status Theorem for theBenchmark.p
% 31.45/4.43  
% 31.45/4.43  % SZS output start CNFRefutation for theBenchmark.p
% 31.45/4.43  
% 31.45/4.43  fof(f2,axiom,(
% 31.45/4.43    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 31.45/4.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.43  
% 31.45/4.43  fof(f19,plain,(
% 31.45/4.43    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)) )),
% 31.45/4.43    inference(cnf_transformation,[],[f2])).
% 31.45/4.43  
% 31.45/4.43  fof(f8,axiom,(
% 31.45/4.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 31.45/4.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.43  
% 31.45/4.43  fof(f25,plain,(
% 31.45/4.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 31.45/4.43    inference(cnf_transformation,[],[f8])).
% 31.45/4.43  
% 31.45/4.43  fof(f32,plain,(
% 31.45/4.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 31.45/4.43    inference(definition_unfolding,[],[f25,f22])).
% 31.45/4.43  
% 31.45/4.43  fof(f5,axiom,(
% 31.45/4.43    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 31.45/4.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.43  
% 31.45/4.43  fof(f22,plain,(
% 31.45/4.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 31.45/4.43    inference(cnf_transformation,[],[f5])).
% 31.45/4.43  
% 31.45/4.43  fof(f36,plain,(
% 31.45/4.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X0),k1_enumset1(X1,X1,X0),k1_enumset1(X2,X2,X0)))) )),
% 31.45/4.43    inference(definition_unfolding,[],[f19,f32,f22,f22])).
% 31.45/4.43  
% 31.45/4.43  fof(f6,axiom,(
% 31.45/4.43    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 31.45/4.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.43  
% 31.45/4.43  fof(f23,plain,(
% 31.45/4.43    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 31.45/4.43    inference(cnf_transformation,[],[f6])).
% 31.45/4.43  
% 31.45/4.43  fof(f1,axiom,(
% 31.45/4.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 31.45/4.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.43  
% 31.45/4.43  fof(f18,plain,(
% 31.45/4.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 31.45/4.43    inference(cnf_transformation,[],[f1])).
% 31.45/4.43  
% 31.45/4.43  fof(f33,plain,(
% 31.45/4.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)))) )),
% 31.45/4.43    inference(definition_unfolding,[],[f18,f32,f22,f22])).
% 31.45/4.43  
% 31.45/4.43  fof(f37,plain,(
% 31.45/4.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)))) )),
% 31.45/4.43    inference(definition_unfolding,[],[f23,f33])).
% 31.45/4.43  
% 31.45/4.43  fof(f7,axiom,(
% 31.45/4.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 31.45/4.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.43  
% 31.45/4.43  fof(f24,plain,(
% 31.45/4.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 31.45/4.43    inference(cnf_transformation,[],[f7])).
% 31.45/4.43  
% 31.45/4.43  fof(f3,axiom,(
% 31.45/4.43    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 31.45/4.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.43  
% 31.45/4.43  fof(f20,plain,(
% 31.45/4.43    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 31.45/4.43    inference(cnf_transformation,[],[f3])).
% 31.45/4.43  
% 31.45/4.43  fof(f34,plain,(
% 31.45/4.43    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4)))) )),
% 31.45/4.43    inference(definition_unfolding,[],[f20,f32,f22])).
% 31.45/4.43  
% 31.45/4.43  fof(f38,plain,(
% 31.45/4.43    ( ! [X2,X0,X3,X1] : (k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)))) )),
% 31.45/4.43    inference(definition_unfolding,[],[f24,f33,f34])).
% 31.45/4.43  
% 31.45/4.43  fof(f13,conjecture,(
% 31.45/4.43    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))),
% 31.45/4.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.43  
% 31.45/4.43  fof(f14,negated_conjecture,(
% 31.45/4.43    ~! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))),
% 31.45/4.43    inference(negated_conjecture,[],[f13])).
% 31.45/4.43  
% 31.45/4.43  fof(f15,plain,(
% 31.45/4.43    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))),
% 31.45/4.43    inference(ennf_transformation,[],[f14])).
% 31.45/4.43  
% 31.45/4.43  fof(f16,plain,(
% 31.45/4.43    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) => k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 31.45/4.43    introduced(choice_axiom,[])).
% 31.45/4.43  
% 31.45/4.43  fof(f17,plain,(
% 31.45/4.43    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 31.45/4.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).
% 31.45/4.43  
% 31.45/4.43  fof(f31,plain,(
% 31.45/4.43    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 31.45/4.43    inference(cnf_transformation,[],[f17])).
% 31.45/4.43  
% 31.45/4.43  fof(f11,axiom,(
% 31.45/4.43    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 31.45/4.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.43  
% 31.45/4.43  fof(f29,plain,(
% 31.45/4.43    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 31.45/4.43    inference(cnf_transformation,[],[f11])).
% 31.45/4.43  
% 31.45/4.43  fof(f12,axiom,(
% 31.45/4.43    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 31.45/4.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.43  
% 31.45/4.43  fof(f30,plain,(
% 31.45/4.43    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 31.45/4.43    inference(cnf_transformation,[],[f12])).
% 31.45/4.43  
% 31.45/4.43  fof(f4,axiom,(
% 31.45/4.43    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 31.45/4.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.43  
% 31.45/4.43  fof(f21,plain,(
% 31.45/4.43    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 31.45/4.43    inference(cnf_transformation,[],[f4])).
% 31.45/4.43  
% 31.45/4.43  fof(f35,plain,(
% 31.45/4.43    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 31.45/4.43    inference(definition_unfolding,[],[f21,f22])).
% 31.45/4.43  
% 31.45/4.43  fof(f42,plain,(
% 31.45/4.43    k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)),k1_enumset1(sK3,sK3,sK4))),
% 31.45/4.43    inference(definition_unfolding,[],[f31,f33,f29,f29,f29,f29,f30,f35,f22,f22])).
% 31.45/4.43  
% 31.45/4.43  fof(f9,axiom,(
% 31.45/4.43    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 31.45/4.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.43  
% 31.45/4.43  fof(f26,plain,(
% 31.45/4.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 31.45/4.43    inference(cnf_transformation,[],[f9])).
% 31.45/4.43  
% 31.45/4.43  fof(f39,plain,(
% 31.45/4.43    ( ! [X2,X0,X3,X1] : (k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3)),k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3)),k1_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3)))) = k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) )),
% 31.45/4.43    inference(definition_unfolding,[],[f26,f33,f22,f22])).
% 31.45/4.43  
% 31.45/4.43  fof(f10,axiom,(
% 31.45/4.43    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 31.45/4.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.45/4.43  
% 31.45/4.43  fof(f27,plain,(
% 31.45/4.43    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 31.45/4.43    inference(cnf_transformation,[],[f10])).
% 31.45/4.43  
% 31.45/4.43  fof(f41,plain,(
% 31.45/4.43    ( ! [X2,X0,X1] : (k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) )),
% 31.45/4.43    inference(definition_unfolding,[],[f27,f22,f35,f22])).
% 31.45/4.43  
% 31.45/4.43  cnf(c_0,plain,
% 31.45/4.43      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X1))) = k1_enumset1(X1,X0,X2) ),
% 31.45/4.43      inference(cnf_transformation,[],[f36]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_1,plain,
% 31.45/4.43      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
% 31.45/4.43      inference(cnf_transformation,[],[f37]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_36,plain,
% 31.45/4.43      ( k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X0,X1) ),
% 31.45/4.43      inference(superposition,[status(thm)],[c_0,c_1]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_209,plain,
% 31.45/4.43      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X1))) = k1_enumset1(X0,X1,X2) ),
% 31.45/4.43      inference(superposition,[status(thm)],[c_36,c_1]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_2,plain,
% 31.45/4.43      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) ),
% 31.45/4.43      inference(cnf_transformation,[],[f38]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_190,plain,
% 31.45/4.43      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X1))) = k1_enumset1(X1,X0,X2) ),
% 31.45/4.43      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_1126,plain,
% 31.45/4.43      ( k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
% 31.45/4.43      inference(superposition,[status(thm)],[c_209,c_190]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_102700,plain,
% 31.45/4.43      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X2,X1,X3))) ),
% 31.45/4.43      inference(superposition,[status(thm)],[c_1126,c_2]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_103413,plain,
% 31.45/4.43      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X2),k1_enumset1(X0,X0,X2),k1_enumset1(X1,X1,X3))) ),
% 31.45/4.43      inference(superposition,[status(thm)],[c_102700,c_2]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_6,negated_conjecture,
% 31.45/4.43      ( k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
% 31.45/4.43      inference(cnf_transformation,[],[f42]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_104863,plain,
% 31.45/4.43      ( k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
% 31.45/4.43      inference(superposition,[status(thm)],[c_103413,c_6]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_18,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_126,plain,
% 31.45/4.43      ( X0 != X1
% 31.45/4.43      | X0 = k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)),k1_enumset1(sK3,sK3,sK4))
% 31.45/4.43      | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) != X1 ),
% 31.45/4.43      inference(instantiation,[status(thm)],[c_18]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_802,plain,
% 31.45/4.43      ( X0 != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k1_enumset1(sK3,sK3,sK4))
% 31.45/4.43      | X0 = k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)),k1_enumset1(sK3,sK3,sK4))
% 31.45/4.43      | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
% 31.45/4.43      inference(instantiation,[status(thm)],[c_126]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_5638,plain,
% 31.45/4.43      ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k1_enumset1(sK3,sK3,sK4))
% 31.45/4.43      | k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)))) != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k1_enumset1(sK3,sK3,sK4))
% 31.45/4.43      | k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)))) = k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
% 31.45/4.43      inference(instantiation,[status(thm)],[c_802]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_3,plain,
% 31.45/4.43      ( k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X3,X1),k4_tarski(X3,X1),k4_tarski(X3,X2)))) = k2_zfmisc_1(k1_enumset1(X0,X0,X3),k1_enumset1(X1,X1,X2)) ),
% 31.45/4.43      inference(cnf_transformation,[],[f39]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_1796,plain,
% 31.45/4.43      ( k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)))) = k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
% 31.45/4.43      inference(instantiation,[status(thm)],[c_3]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_22,plain,
% 31.45/4.43      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 31.45/4.43      theory(equality) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_61,plain,
% 31.45/4.43      ( k1_enumset1(sK3,sK3,sK4) != X0
% 31.45/4.43      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) != X1
% 31.45/4.43      | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) = k2_zfmisc_1(X1,X0) ),
% 31.45/4.43      inference(instantiation,[status(thm)],[c_22]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_384,plain,
% 31.45/4.43      ( k1_enumset1(sK3,sK3,sK4) != X0
% 31.45/4.43      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) != k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))
% 31.45/4.43      | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) = k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),X0) ),
% 31.45/4.43      inference(instantiation,[status(thm)],[c_61]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_664,plain,
% 31.45/4.43      ( k1_enumset1(sK3,sK3,sK4) != k1_enumset1(sK3,sK3,sK4)
% 31.45/4.43      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) != k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))
% 31.45/4.43      | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) = k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
% 31.45/4.43      inference(instantiation,[status(thm)],[c_384]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_5,plain,
% 31.45/4.43      ( k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)) ),
% 31.45/4.43      inference(cnf_transformation,[],[f41]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_277,plain,
% 31.45/4.43      ( k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) ),
% 31.45/4.43      inference(instantiation,[status(thm)],[c_5]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_76,plain,
% 31.45/4.43      ( X0 != X1
% 31.45/4.43      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) != X1
% 31.45/4.43      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) = X0 ),
% 31.45/4.43      inference(instantiation,[status(thm)],[c_18]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_144,plain,
% 31.45/4.43      ( X0 != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))
% 31.45/4.43      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) = X0
% 31.45/4.43      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) ),
% 31.45/4.43      inference(instantiation,[status(thm)],[c_76]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_276,plain,
% 31.45/4.43      ( k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2))
% 31.45/4.43      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) = k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))
% 31.45/4.43      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) ),
% 31.45/4.43      inference(instantiation,[status(thm)],[c_144]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_17,plain,( X0 = X0 ),theory(equality) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_153,plain,
% 31.45/4.43      ( k1_enumset1(sK3,sK3,sK4) = k1_enumset1(sK3,sK3,sK4) ),
% 31.45/4.43      inference(instantiation,[status(thm)],[c_17]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(c_74,plain,
% 31.45/4.43      ( k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK2)) ),
% 31.45/4.43      inference(instantiation,[status(thm)],[c_17]) ).
% 31.45/4.43  
% 31.45/4.43  cnf(contradiction,plain,
% 31.45/4.43      ( $false ),
% 31.45/4.43      inference(minisat,
% 31.45/4.43                [status(thm)],
% 31.45/4.43                [c_104863,c_5638,c_1796,c_664,c_277,c_276,c_153,c_74]) ).
% 31.45/4.43  
% 31.45/4.43  
% 31.45/4.43  % SZS output end CNFRefutation for theBenchmark.p
% 31.45/4.43  
% 31.45/4.43  ------                               Statistics
% 31.45/4.43  
% 31.45/4.43  ------ Selected
% 31.45/4.43  
% 31.45/4.43  total_time:                             3.76
% 31.45/4.43  
%------------------------------------------------------------------------------
