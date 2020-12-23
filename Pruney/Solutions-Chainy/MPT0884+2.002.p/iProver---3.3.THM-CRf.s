%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:19 EST 2020

% Result     : Theorem 7.88s
% Output     : CNFRefutation 7.88s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 148 expanded)
%              Number of clauses        :   28 (  32 expanded)
%              Number of leaves         :   15 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :   86 ( 174 expanded)
%              Number of equality atoms :   85 ( 173 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f20,f27,f27])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) ),
    inference(definition_unfolding,[],[f21,f27,f27])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f28,f36])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)) ),
    inference(definition_unfolding,[],[f24,f36,f38])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) ),
    inference(negated_conjecture,[],[f15])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) ),
    inference(ennf_transformation,[],[f16])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))
   => k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f18])).

fof(f35,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f19])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,(
    k2_xboole_0(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f35,f36,f33,f33,f33,f33,f34,f27,f38,f27])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3)),k1_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3))) = k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) ),
    inference(definition_unfolding,[],[f30,f36,f27,f27])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)) ),
    inference(definition_unfolding,[],[f32,f27,f27,f38])).

cnf(c_2,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_5,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_63,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)) = k1_enumset1(X0,X2,X1) ),
    inference(superposition,[status(thm)],[c_2,c_5])).

cnf(c_731,plain,
    ( k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(superposition,[status(thm)],[c_63,c_5])).

cnf(c_3,plain,
    ( k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_967,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_enumset1(X3,X3,X3)) ),
    inference(superposition,[status(thm)],[c_731,c_3])).

cnf(c_10957,plain,
    ( k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X0,X2),k1_enumset1(X1,X1,X3)) ),
    inference(superposition,[status(thm)],[c_967,c_3])).

cnf(c_9,negated_conjecture,
    ( k2_xboole_0(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_36414,plain,
    ( k2_xboole_0(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_10957,c_9])).

cnf(c_25,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_116,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4))
    | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != X1 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_885,plain,
    ( X0 != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4))
    | X0 = k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4))
    | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_116])).

cnf(c_5803,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4))
    | k2_xboole_0(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4))) != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4))
    | k2_xboole_0(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4))) = k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_885])).

cnf(c_6,plain,
    ( k2_xboole_0(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X3,X1),k4_tarski(X3,X1),k4_tarski(X3,X2))) = k2_zfmisc_1(k1_enumset1(X0,X0,X3),k1_enumset1(X1,X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2421,plain,
    ( k2_xboole_0(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4))) = k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_30,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_57,plain,
    ( k1_enumset1(sK3,sK3,sK4) != X0
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) != X1
    | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k2_zfmisc_1(X1,X0) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_513,plain,
    ( k1_enumset1(sK3,sK3,sK4) != X0
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) != k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))
    | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),X0) ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_761,plain,
    ( k1_enumset1(sK3,sK3,sK4) != k1_enumset1(sK3,sK3,sK4)
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) != k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))
    | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_513])).

cnf(c_7,plain,
    ( k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k1_enumset1(X0,X0,X2),k1_enumset1(X1,X1,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_323,plain,
    ( k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)) = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_106,plain,
    ( X0 != X1
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) != X1
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) = X0 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_136,plain,
    ( X0 != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) = X0
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_106])).

cnf(c_322,plain,
    ( k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)) != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_24,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_192,plain,
    ( k1_enumset1(sK3,sK3,sK4) = k1_enumset1(sK3,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_104,plain,
    ( k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_36414,c_5803,c_2421,c_761,c_323,c_322,c_192,c_104])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:25:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.88/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.88/1.49  
% 7.88/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.88/1.49  
% 7.88/1.49  ------  iProver source info
% 7.88/1.49  
% 7.88/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.88/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.88/1.49  git: non_committed_changes: false
% 7.88/1.49  git: last_make_outside_of_git: false
% 7.88/1.49  
% 7.88/1.49  ------ 
% 7.88/1.49  ------ Parsing...
% 7.88/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.88/1.49  
% 7.88/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 7.88/1.49  
% 7.88/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.88/1.49  
% 7.88/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.88/1.49  ------ Proving...
% 7.88/1.49  ------ Problem Properties 
% 7.88/1.49  
% 7.88/1.49  
% 7.88/1.49  clauses                                 10
% 7.88/1.49  conjectures                             1
% 7.88/1.49  EPR                                     0
% 7.88/1.49  Horn                                    10
% 7.88/1.49  unary                                   10
% 7.88/1.49  binary                                  0
% 7.88/1.49  lits                                    10
% 7.88/1.49  lits eq                                 10
% 7.88/1.49  fd_pure                                 0
% 7.88/1.49  fd_pseudo                               0
% 7.88/1.49  fd_cond                                 0
% 7.88/1.49  fd_pseudo_cond                          0
% 7.88/1.49  AC symbols                              0
% 7.88/1.49  
% 7.88/1.49  ------ Input Options Time Limit: Unbounded
% 7.88/1.49  
% 7.88/1.49  
% 7.88/1.49  ------ 
% 7.88/1.49  Current options:
% 7.88/1.49  ------ 
% 7.88/1.49  
% 7.88/1.49  
% 7.88/1.49  
% 7.88/1.49  
% 7.88/1.49  ------ Proving...
% 7.88/1.49  
% 7.88/1.49  
% 7.88/1.49  % SZS status Theorem for theBenchmark.p
% 7.88/1.49  
% 7.88/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.88/1.49  
% 7.88/1.49  fof(f1,axiom,(
% 7.88/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f20,plain,(
% 7.88/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f1])).
% 7.88/1.49  
% 7.88/1.49  fof(f8,axiom,(
% 7.88/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f27,plain,(
% 7.88/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f8])).
% 7.88/1.49  
% 7.88/1.49  fof(f41,plain,(
% 7.88/1.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 7.88/1.49    inference(definition_unfolding,[],[f20,f27,f27])).
% 7.88/1.49  
% 7.88/1.49  fof(f9,axiom,(
% 7.88/1.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f28,plain,(
% 7.88/1.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f9])).
% 7.88/1.49  
% 7.88/1.49  fof(f2,axiom,(
% 7.88/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f21,plain,(
% 7.88/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 7.88/1.49    inference(cnf_transformation,[],[f2])).
% 7.88/1.49  
% 7.88/1.49  fof(f36,plain,(
% 7.88/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) )),
% 7.88/1.49    inference(definition_unfolding,[],[f21,f27,f27])).
% 7.88/1.49  
% 7.88/1.49  fof(f44,plain,(
% 7.88/1.49    ( ! [X2,X0,X1] : (k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 7.88/1.49    inference(definition_unfolding,[],[f28,f36])).
% 7.88/1.49  
% 7.88/1.49  fof(f5,axiom,(
% 7.88/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f24,plain,(
% 7.88/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 7.88/1.49    inference(cnf_transformation,[],[f5])).
% 7.88/1.49  
% 7.88/1.49  fof(f7,axiom,(
% 7.88/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f26,plain,(
% 7.88/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f7])).
% 7.88/1.49  
% 7.88/1.49  fof(f38,plain,(
% 7.88/1.49    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 7.88/1.49    inference(definition_unfolding,[],[f26,f27])).
% 7.88/1.49  
% 7.88/1.49  fof(f42,plain,(
% 7.88/1.49    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) )),
% 7.88/1.49    inference(definition_unfolding,[],[f24,f36,f38])).
% 7.88/1.49  
% 7.88/1.49  fof(f15,conjecture,(
% 7.88/1.49    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f16,negated_conjecture,(
% 7.88/1.49    ~! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 7.88/1.49    inference(negated_conjecture,[],[f15])).
% 7.88/1.49  
% 7.88/1.49  fof(f17,plain,(
% 7.88/1.49    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 7.88/1.49    inference(ennf_transformation,[],[f16])).
% 7.88/1.49  
% 7.88/1.49  fof(f18,plain,(
% 7.88/1.49    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) => k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 7.88/1.49    introduced(choice_axiom,[])).
% 7.88/1.49  
% 7.88/1.49  fof(f19,plain,(
% 7.88/1.49    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 7.88/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f18])).
% 7.88/1.49  
% 7.88/1.49  fof(f35,plain,(
% 7.88/1.49    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 7.88/1.49    inference(cnf_transformation,[],[f19])).
% 7.88/1.49  
% 7.88/1.49  fof(f13,axiom,(
% 7.88/1.49    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f33,plain,(
% 7.88/1.49    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f13])).
% 7.88/1.49  
% 7.88/1.49  fof(f14,axiom,(
% 7.88/1.49    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f34,plain,(
% 7.88/1.49    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 7.88/1.49    inference(cnf_transformation,[],[f14])).
% 7.88/1.49  
% 7.88/1.49  fof(f48,plain,(
% 7.88/1.49    k2_xboole_0(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4))),
% 7.88/1.49    inference(definition_unfolding,[],[f35,f36,f33,f33,f33,f33,f34,f27,f38,f27])).
% 7.88/1.49  
% 7.88/1.49  fof(f11,axiom,(
% 7.88/1.49    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f30,plain,(
% 7.88/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 7.88/1.49    inference(cnf_transformation,[],[f11])).
% 7.88/1.49  
% 7.88/1.49  fof(f45,plain,(
% 7.88/1.49    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3)),k1_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3))) = k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) )),
% 7.88/1.49    inference(definition_unfolding,[],[f30,f36,f27,f27])).
% 7.88/1.49  
% 7.88/1.49  fof(f12,axiom,(
% 7.88/1.49    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 7.88/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.49  
% 7.88/1.49  fof(f32,plain,(
% 7.88/1.49    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 7.88/1.49    inference(cnf_transformation,[],[f12])).
% 7.88/1.49  
% 7.88/1.49  fof(f46,plain,(
% 7.88/1.49    ( ! [X2,X0,X1] : (k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) )),
% 7.88/1.49    inference(definition_unfolding,[],[f32,f27,f27,f38])).
% 7.88/1.49  
% 7.88/1.49  cnf(c_2,plain,
% 7.88/1.49      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 7.88/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_5,plain,
% 7.88/1.49      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)) = k1_enumset1(X0,X1,X2) ),
% 7.88/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_63,plain,
% 7.88/1.49      ( k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)) = k1_enumset1(X0,X2,X1) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_2,c_5]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_731,plain,
% 7.88/1.49      ( k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_63,c_5]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_3,plain,
% 7.88/1.49      ( k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) ),
% 7.88/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_967,plain,
% 7.88/1.49      ( k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_enumset1(X3,X3,X3)) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_731,c_3]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_10957,plain,
% 7.88/1.49      ( k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X0,X2),k1_enumset1(X1,X1,X3)) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_967,c_3]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_9,negated_conjecture,
% 7.88/1.49      ( k2_xboole_0(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
% 7.88/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_36414,plain,
% 7.88/1.49      ( k2_xboole_0(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
% 7.88/1.49      inference(superposition,[status(thm)],[c_10957,c_9]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_25,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_116,plain,
% 7.88/1.49      ( X0 != X1
% 7.88/1.49      | X0 = k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4))
% 7.88/1.49      | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != X1 ),
% 7.88/1.49      inference(instantiation,[status(thm)],[c_25]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_885,plain,
% 7.88/1.49      ( X0 != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4))
% 7.88/1.49      | X0 = k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4))
% 7.88/1.49      | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
% 7.88/1.49      inference(instantiation,[status(thm)],[c_116]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_5803,plain,
% 7.88/1.49      ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4))
% 7.88/1.49      | k2_xboole_0(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4))) != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4))
% 7.88/1.49      | k2_xboole_0(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4))) = k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
% 7.88/1.49      inference(instantiation,[status(thm)],[c_885]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_6,plain,
% 7.88/1.49      ( k2_xboole_0(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X3,X1),k4_tarski(X3,X1),k4_tarski(X3,X2))) = k2_zfmisc_1(k1_enumset1(X0,X0,X3),k1_enumset1(X1,X1,X2)) ),
% 7.88/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_2421,plain,
% 7.88/1.49      ( k2_xboole_0(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4))) = k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
% 7.88/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_30,plain,
% 7.88/1.49      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 7.88/1.49      theory(equality) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_57,plain,
% 7.88/1.49      ( k1_enumset1(sK3,sK3,sK4) != X0
% 7.88/1.49      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) != X1
% 7.88/1.49      | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k2_zfmisc_1(X1,X0) ),
% 7.88/1.49      inference(instantiation,[status(thm)],[c_30]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_513,plain,
% 7.88/1.49      ( k1_enumset1(sK3,sK3,sK4) != X0
% 7.88/1.49      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) != k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))
% 7.88/1.49      | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),X0) ),
% 7.88/1.49      inference(instantiation,[status(thm)],[c_57]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_761,plain,
% 7.88/1.49      ( k1_enumset1(sK3,sK3,sK4) != k1_enumset1(sK3,sK3,sK4)
% 7.88/1.49      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) != k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))
% 7.88/1.49      | k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) ),
% 7.88/1.49      inference(instantiation,[status(thm)],[c_513]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_7,plain,
% 7.88/1.49      ( k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k1_enumset1(X0,X0,X2),k1_enumset1(X1,X1,X1)) ),
% 7.88/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_323,plain,
% 7.88/1.49      ( k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)) = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) ),
% 7.88/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_106,plain,
% 7.88/1.49      ( X0 != X1
% 7.88/1.49      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) != X1
% 7.88/1.49      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) = X0 ),
% 7.88/1.49      inference(instantiation,[status(thm)],[c_25]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_136,plain,
% 7.88/1.49      ( X0 != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))
% 7.88/1.49      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) = X0
% 7.88/1.49      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) ),
% 7.88/1.49      inference(instantiation,[status(thm)],[c_106]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_322,plain,
% 7.88/1.49      ( k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)) != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))
% 7.88/1.49      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) = k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2))
% 7.88/1.49      | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) ),
% 7.88/1.49      inference(instantiation,[status(thm)],[c_136]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_24,plain,( X0 = X0 ),theory(equality) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_192,plain,
% 7.88/1.49      ( k1_enumset1(sK3,sK3,sK4) = k1_enumset1(sK3,sK3,sK4) ),
% 7.88/1.49      inference(instantiation,[status(thm)],[c_24]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(c_104,plain,
% 7.88/1.49      ( k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) ),
% 7.88/1.49      inference(instantiation,[status(thm)],[c_24]) ).
% 7.88/1.49  
% 7.88/1.49  cnf(contradiction,plain,
% 7.88/1.49      ( $false ),
% 7.88/1.49      inference(minisat,
% 7.88/1.49                [status(thm)],
% 7.88/1.49                [c_36414,c_5803,c_2421,c_761,c_323,c_322,c_192,c_104]) ).
% 7.88/1.49  
% 7.88/1.49  
% 7.88/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.88/1.49  
% 7.88/1.49  ------                               Statistics
% 7.88/1.49  
% 7.88/1.49  ------ Selected
% 7.88/1.49  
% 7.88/1.49  total_time:                             0.92
% 7.88/1.49  
%------------------------------------------------------------------------------
