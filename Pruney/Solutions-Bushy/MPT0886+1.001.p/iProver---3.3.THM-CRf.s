%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0886+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:20 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   38 (  83 expanded)
%              Number of clauses        :   14 (  20 expanded)
%              Number of leaves         :    9 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :   40 (  85 expanded)
%              Number of equality atoms :   39 (  84 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X3)) ),
    inference(definition_unfolding,[],[f15,f19,f19])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k2_tarski(X4,X5)) = k6_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X0,X2,X5),k3_mcart_1(X0,X3,X5),k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k2_tarski(X4,X5)) = k6_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X0,X2,X5),k3_mcart_1(X0,X3,X5),k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5)) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k2_tarski(X4,X5)) != k6_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X0,X2,X5),k3_mcart_1(X0,X3,X5),k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5)) ),
    inference(ennf_transformation,[],[f9])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k2_tarski(X4,X5)) != k6_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X0,X2,X5),k3_mcart_1(X0,X3,X5),k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) != k6_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK0,sK2,sK5),k3_mcart_1(sK0,sK3,sK5),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK1,sK3,sK4),k3_mcart_1(sK1,sK2,sK5),k3_mcart_1(sK1,sK3,sK5)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) != k6_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK0,sK2,sK5),k3_mcart_1(sK0,sK3,sK5),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK1,sK3,sK4),k3_mcart_1(sK1,sK2,sK5),k3_mcart_1(sK1,sK3,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f10,f11])).

fof(f21,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) != k6_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK0,sK2,sK5),k3_mcart_1(sK0,sK3,sK5),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK1,sK3,sK4),k3_mcart_1(sK1,sK2,sK5),k3_mcart_1(sK1,sK3,sK5)) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)),k2_xboole_0(k2_tarski(X4,X5),k2_tarski(X6,X7))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f20,f19,f19])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f25,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) != k2_xboole_0(k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK3),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK5),k4_tarski(k4_tarski(sK0,sK3),sK5))),k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4)),k2_tarski(k4_tarski(k4_tarski(sK1,sK2),sK5),k4_tarski(k4_tarski(sK1,sK3),sK5)))) ),
    inference(definition_unfolding,[],[f21,f14,f22,f13,f13,f13,f13,f13,f13,f13,f13])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(k4_tarski(X0,X2),k4_tarski(X0,X3)),k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))) ),
    inference(definition_unfolding,[],[f18,f19])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_0,plain,
    ( k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_19,plain,
    ( k2_xboole_0(k2_tarski(X0_39,X1_39),k2_tarski(X2_39,X3_39)) = k2_xboole_0(k2_tarski(X0_39,X2_39),k2_tarski(X1_39,X3_39)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_4,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) != k2_xboole_0(k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK3),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK5),k4_tarski(k4_tarski(sK0,sK3),sK5))),k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4)),k2_tarski(k4_tarski(k4_tarski(sK1,sK2),sK5),k4_tarski(k4_tarski(sK1,sK3),sK5)))) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_15,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) != k2_xboole_0(k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK3),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK5),k4_tarski(k4_tarski(sK0,sK3),sK5))),k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4)),k2_tarski(k4_tarski(k4_tarski(sK1,sK2),sK5),k4_tarski(k4_tarski(sK1,sK3),sK5)))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_50,plain,
    ( k2_xboole_0(k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK5)),k2_tarski(k4_tarski(k4_tarski(sK0,sK3),sK4),k4_tarski(k4_tarski(sK0,sK3),sK5))),k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4)),k2_tarski(k4_tarski(k4_tarski(sK1,sK2),sK5),k4_tarski(k4_tarski(sK1,sK3),sK5)))) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_19,c_15])).

cnf(c_3,plain,
    ( k2_xboole_0(k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)),k2_tarski(k4_tarski(X3,X1),k4_tarski(X3,X2))) = k2_zfmisc_1(k2_tarski(X0,X3),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_16,plain,
    ( k2_xboole_0(k2_tarski(k4_tarski(X0_39,X1_39),k4_tarski(X0_39,X2_39)),k2_tarski(k4_tarski(X3_39,X1_39),k4_tarski(X3_39,X2_39))) = k2_zfmisc_1(k2_tarski(X0_39,X3_39),k2_tarski(X1_39,X2_39)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_51,plain,
    ( k2_xboole_0(k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(sK4,sK5)),k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4)),k2_tarski(k4_tarski(k4_tarski(sK1,sK2),sK5),k4_tarski(k4_tarski(sK1,sK3),sK5)))) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_50,c_16])).

cnf(c_56,plain,
    ( k2_xboole_0(k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(sK4,sK5)),k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK5)),k2_tarski(k4_tarski(k4_tarski(sK1,sK3),sK4),k4_tarski(k4_tarski(sK1,sK3),sK5)))) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_19,c_51])).

cnf(c_2,plain,
    ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_17,plain,
    ( k2_xboole_0(k2_zfmisc_1(X0_38,X1_38),k2_zfmisc_1(X2_38,X1_38)) = k2_zfmisc_1(k2_xboole_0(X0_38,X2_38),X1_38) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_58,plain,
    ( k2_zfmisc_1(k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))),k2_tarski(sK4,sK5)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_56,c_16,c_17])).

cnf(c_59,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_58,c_16])).

cnf(c_60,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_59])).


%------------------------------------------------------------------------------
