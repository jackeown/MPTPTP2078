%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:19 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 166 expanded)
%              Number of clauses        :   28 (  32 expanded)
%              Number of leaves         :   15 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :   86 ( 192 expanded)
%              Number of equality atoms :   85 ( 191 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f37,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f18,f32,f32])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)) ),
    inference(definition_unfolding,[],[f19,f32,f32])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f22,f32])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)) ),
    inference(definition_unfolding,[],[f20,f24,f33])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) ),
    inference(ennf_transformation,[],[f14])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))
   => k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).

fof(f31,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,(
    k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f31,f29,f29,f29,f29,f30,f32,f33,f32])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)) ),
    inference(definition_unfolding,[],[f26,f32,f32])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(definition_unfolding,[],[f28,f32,f32,f33])).

cnf(c_20,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_113,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4))
    | k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != X1 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_912,plain,
    ( X0 != k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4))
    | X0 = k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4))
    | k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_113])).

cnf(c_6016,plain,
    ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4))
    | k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)) = k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4))
    | k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_912])).

cnf(c_2,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1,plain,
    ( k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_66,plain,
    ( k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)) = k2_enumset1(X0,X1,X3,X2) ),
    inference(superposition,[status(thm)],[c_2,c_1])).

cnf(c_805,plain,
    ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(superposition,[status(thm)],[c_66,c_1])).

cnf(c_3,plain,
    ( k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1151,plain,
    ( k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)) = k2_enumset1(X0,X2,X1,X3) ),
    inference(superposition,[status(thm)],[c_805,c_3])).

cnf(c_4706,plain,
    ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(superposition,[status(thm)],[c_1151,c_3])).

cnf(c_7,negated_conjecture,
    ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_4962,plain,
    ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_4706,c_7])).

cnf(c_4,plain,
    ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X3),k2_enumset1(X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2866,plain,
    ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)) = k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_25,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_52,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) != X0
    | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) != X1
    | k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) = k2_zfmisc_1(X1,X0) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_560,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) != X0
    | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))
    | k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) = k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),X0) ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_764,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) != k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))
    | k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) = k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_5,plain,
    ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X2),k2_enumset1(X1,X1,X1,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_336,plain,
    ( k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)) = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_103,plain,
    ( X0 != X1
    | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) != X1
    | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) = X0 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_133,plain,
    ( X0 != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2))
    | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) = X0
    | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_103])).

cnf(c_335,plain,
    ( k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)) != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2))
    | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) = k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))
    | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_19,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_230,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k2_enumset1(sK3,sK3,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_101,plain,
    ( k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6016,c_4962,c_2866,c_764,c_336,c_335,c_230,c_101])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:59:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.75/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/0.98  
% 3.75/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.75/0.98  
% 3.75/0.98  ------  iProver source info
% 3.75/0.98  
% 3.75/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.75/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.75/0.98  git: non_committed_changes: false
% 3.75/0.98  git: last_make_outside_of_git: false
% 3.75/0.98  
% 3.75/0.98  ------ 
% 3.75/0.98  ------ Parsing...
% 3.75/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.75/0.98  ------ Proving...
% 3.75/0.98  ------ Problem Properties 
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  clauses                                 8
% 3.75/0.98  conjectures                             1
% 3.75/0.98  EPR                                     0
% 3.75/0.98  Horn                                    8
% 3.75/0.98  unary                                   8
% 3.75/0.98  binary                                  0
% 3.75/0.98  lits                                    8
% 3.75/0.98  lits eq                                 8
% 3.75/0.98  fd_pure                                 0
% 3.75/0.98  fd_pseudo                               0
% 3.75/0.98  fd_cond                                 0
% 3.75/0.98  fd_pseudo_cond                          0
% 3.75/0.98  AC symbols                              0
% 3.75/0.98  
% 3.75/0.98  ------ Input Options Time Limit: Unbounded
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  ------ 
% 3.75/0.98  Current options:
% 3.75/0.98  ------ 
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  ------ Proving...
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  % SZS status Theorem for theBenchmark.p
% 3.75/0.98  
% 3.75/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.75/0.98  
% 3.75/0.98  fof(f1,axiom,(
% 3.75/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f18,plain,(
% 3.75/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f1])).
% 3.75/0.98  
% 3.75/0.98  fof(f6,axiom,(
% 3.75/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f23,plain,(
% 3.75/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f6])).
% 3.75/0.98  
% 3.75/0.98  fof(f7,axiom,(
% 3.75/0.98    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f24,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f7])).
% 3.75/0.98  
% 3.75/0.98  fof(f32,plain,(
% 3.75/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.75/0.98    inference(definition_unfolding,[],[f23,f24])).
% 3.75/0.98  
% 3.75/0.98  fof(f37,plain,(
% 3.75/0.98    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 3.75/0.98    inference(definition_unfolding,[],[f18,f32,f32])).
% 3.75/0.98  
% 3.75/0.98  fof(f2,axiom,(
% 3.75/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 3.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f19,plain,(
% 3.75/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 3.75/0.98    inference(cnf_transformation,[],[f2])).
% 3.75/0.98  
% 3.75/0.98  fof(f36,plain,(
% 3.75/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) )),
% 3.75/0.98    inference(definition_unfolding,[],[f19,f32,f32])).
% 3.75/0.98  
% 3.75/0.98  fof(f3,axiom,(
% 3.75/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 3.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f20,plain,(
% 3.75/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 3.75/0.98    inference(cnf_transformation,[],[f3])).
% 3.75/0.98  
% 3.75/0.98  fof(f5,axiom,(
% 3.75/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f22,plain,(
% 3.75/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f5])).
% 3.75/0.98  
% 3.75/0.98  fof(f33,plain,(
% 3.75/0.98    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.75/0.98    inference(definition_unfolding,[],[f22,f32])).
% 3.75/0.98  
% 3.75/0.98  fof(f38,plain,(
% 3.75/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3))) )),
% 3.75/0.98    inference(definition_unfolding,[],[f20,f24,f33])).
% 3.75/0.98  
% 3.75/0.98  fof(f13,conjecture,(
% 3.75/0.98    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 3.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f14,negated_conjecture,(
% 3.75/0.98    ~! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 3.75/0.98    inference(negated_conjecture,[],[f13])).
% 3.75/0.98  
% 3.75/0.98  fof(f15,plain,(
% 3.75/0.98    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 3.75/0.98    inference(ennf_transformation,[],[f14])).
% 3.75/0.98  
% 3.75/0.98  fof(f16,plain,(
% 3.75/0.98    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) => k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 3.75/0.98    introduced(choice_axiom,[])).
% 3.75/0.98  
% 3.75/0.98  fof(f17,plain,(
% 3.75/0.98    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 3.75/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).
% 3.75/0.98  
% 3.75/0.98  fof(f31,plain,(
% 3.75/0.98    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 3.75/0.98    inference(cnf_transformation,[],[f17])).
% 3.75/0.98  
% 3.75/0.98  fof(f11,axiom,(
% 3.75/0.98    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 3.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f29,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f11])).
% 3.75/0.98  
% 3.75/0.98  fof(f12,axiom,(
% 3.75/0.98    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 3.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f30,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f12])).
% 3.75/0.98  
% 3.75/0.98  fof(f42,plain,(
% 3.75/0.98    k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4))),
% 3.75/0.98    inference(definition_unfolding,[],[f31,f29,f29,f29,f29,f30,f32,f33,f32])).
% 3.75/0.98  
% 3.75/0.98  fof(f9,axiom,(
% 3.75/0.98    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 3.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f26,plain,(
% 3.75/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 3.75/0.98    inference(cnf_transformation,[],[f9])).
% 3.75/0.98  
% 3.75/0.98  fof(f39,plain,(
% 3.75/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) )),
% 3.75/0.98    inference(definition_unfolding,[],[f26,f32,f32])).
% 3.75/0.98  
% 3.75/0.98  fof(f10,axiom,(
% 3.75/0.98    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f28,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 3.75/0.98    inference(cnf_transformation,[],[f10])).
% 3.75/0.98  
% 3.75/0.98  fof(f40,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2))) )),
% 3.75/0.98    inference(definition_unfolding,[],[f28,f32,f32,f33])).
% 3.75/0.98  
% 3.75/0.98  cnf(c_20,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_113,plain,
% 3.75/0.98      ( X0 != X1
% 3.75/0.98      | X0 = k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4))
% 3.75/0.98      | k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != X1 ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_20]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_912,plain,
% 3.75/0.98      ( X0 != k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4))
% 3.75/0.98      | X0 = k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4))
% 3.75/0.98      | k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_113]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_6016,plain,
% 3.75/0.98      ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4))
% 3.75/0.98      | k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)) = k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4))
% 3.75/0.98      | k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_912]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_2,plain,
% 3.75/0.98      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 3.75/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1,plain,
% 3.75/0.98      ( k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
% 3.75/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_66,plain,
% 3.75/0.98      ( k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)) = k2_enumset1(X0,X1,X3,X2) ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_2,c_1]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_805,plain,
% 3.75/0.98      ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_66,c_1]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_3,plain,
% 3.75/0.98      ( k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)) = k2_enumset1(X0,X1,X2,X3) ),
% 3.75/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1151,plain,
% 3.75/0.98      ( k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)) = k2_enumset1(X0,X2,X1,X3) ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_805,c_3]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_4706,plain,
% 3.75/0.98      ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_1151,c_3]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_7,negated_conjecture,
% 3.75/0.98      ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 3.75/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_4962,plain,
% 3.75/0.98      ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_4706,c_7]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_4,plain,
% 3.75/0.98      ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X3),k2_enumset1(X1,X1,X1,X2)) ),
% 3.75/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_2866,plain,
% 3.75/0.98      ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)) = k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_25,plain,
% 3.75/0.98      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 3.75/0.98      theory(equality) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_52,plain,
% 3.75/0.98      ( k2_enumset1(sK3,sK3,sK3,sK4) != X0
% 3.75/0.98      | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) != X1
% 3.75/0.98      | k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) = k2_zfmisc_1(X1,X0) ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_25]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_560,plain,
% 3.75/0.98      ( k2_enumset1(sK3,sK3,sK3,sK4) != X0
% 3.75/0.98      | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))
% 3.75/0.98      | k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) = k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),X0) ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_52]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_764,plain,
% 3.75/0.98      ( k2_enumset1(sK3,sK3,sK3,sK4) != k2_enumset1(sK3,sK3,sK3,sK4)
% 3.75/0.98      | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))
% 3.75/0.98      | k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) = k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_560]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_5,plain,
% 3.75/0.98      ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X2),k2_enumset1(X1,X1,X1,X1)) ),
% 3.75/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_336,plain,
% 3.75/0.98      ( k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)) = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_103,plain,
% 3.75/0.98      ( X0 != X1
% 3.75/0.98      | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) != X1
% 3.75/0.98      | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) = X0 ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_20]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_133,plain,
% 3.75/0.98      ( X0 != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2))
% 3.75/0.98      | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) = X0
% 3.75/0.98      | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_103]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_335,plain,
% 3.75/0.98      ( k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)) != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2))
% 3.75/0.98      | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) = k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))
% 3.75/0.98      | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_133]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_19,plain,( X0 = X0 ),theory(equality) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_230,plain,
% 3.75/0.98      ( k2_enumset1(sK3,sK3,sK3,sK4) = k2_enumset1(sK3,sK3,sK3,sK4) ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_19]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_101,plain,
% 3.75/0.98      ( k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_19]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(contradiction,plain,
% 3.75/0.98      ( $false ),
% 3.75/0.98      inference(minisat,
% 3.75/0.98                [status(thm)],
% 3.75/0.98                [c_6016,c_4962,c_2866,c_764,c_336,c_335,c_230,c_101]) ).
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.75/0.98  
% 3.75/0.98  ------                               Statistics
% 3.75/0.98  
% 3.75/0.98  ------ Selected
% 3.75/0.98  
% 3.75/0.98  total_time:                             0.298
% 3.75/0.98  
%------------------------------------------------------------------------------
