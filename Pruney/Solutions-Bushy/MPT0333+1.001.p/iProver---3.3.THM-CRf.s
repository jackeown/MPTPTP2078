%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0333+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:01 EST 2020

% Result     : Theorem 1.35s
% Output     : CNFRefutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   25 (  35 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :   28 (  38 expanded)
%              Number of equality atoms :   27 (  37 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(negated_conjecture,[],[f5])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(ennf_transformation,[],[f6])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))
   => k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).

fof(f16,plain,(
    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k1_tarski(X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f15,f14,f14])).

fof(f20,plain,(
    k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(sK0,sK2)),k1_tarski(k4_tarski(sK0,sK3))),k2_xboole_0(k1_tarski(k4_tarski(sK1,sK2)),k1_tarski(k4_tarski(sK1,sK3)))) != k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(definition_unfolding,[],[f16,f14,f14,f17])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X0,X2))) = k2_zfmisc_1(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) ),
    inference(definition_unfolding,[],[f12,f14,f14])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))
      & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_4,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(sK0,sK2)),k1_tarski(k4_tarski(sK0,sK3))),k2_xboole_0(k1_tarski(k4_tarski(sK1,sK2)),k1_tarski(k4_tarski(sK1,sK3)))) != k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_15,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(sK0,sK2)),k1_tarski(k4_tarski(sK0,sK3))),k2_xboole_0(k1_tarski(k4_tarski(sK1,sK2)),k1_tarski(k4_tarski(sK1,sK3)))) != k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3,plain,
    ( k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X0,X2))) = k2_zfmisc_1(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_16,plain,
    ( k2_xboole_0(k1_tarski(k4_tarski(X0_37,X1_37)),k1_tarski(k4_tarski(X0_37,X2_37))) = k2_zfmisc_1(k1_tarski(X0_37),k2_xboole_0(k1_tarski(X1_37),k1_tarski(X2_37))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1,plain,
    ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_18,plain,
    ( k2_xboole_0(k2_zfmisc_1(X0_36,X1_36),k2_zfmisc_1(X2_36,X1_36)) = k2_zfmisc_1(k2_xboole_0(X0_36,X2_36),X1_36) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_31,plain,
    ( k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) != k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(demodulation,[status(thm)],[c_15,c_16,c_18])).

cnf(c_32,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_31])).


%------------------------------------------------------------------------------
