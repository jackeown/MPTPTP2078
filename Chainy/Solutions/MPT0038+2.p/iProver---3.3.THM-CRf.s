%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0038+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:14 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   21 (  21 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    8
%              Number of atoms          :   22 (  22 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f182,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f47,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f257,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

fof(f65,conjecture,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,negated_conjecture,(
    ~ ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f65])).

fof(f120,plain,(
    ? [X0,X1,X2] : ~ r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f66])).

fof(f177,plain,
    ( ? [X0,X1,X2] : ~ r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))
   => ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK15,sK16),k3_xboole_0(sK15,sK17)),k2_xboole_0(sK16,sK17)) ),
    introduced(choice_axiom,[])).

fof(f178,plain,(
    ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK15,sK16),k3_xboole_0(sK15,sK17)),k2_xboole_0(sK16,sK17)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f120,f177])).

fof(f277,plain,(
    ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK15,sK16),k3_xboole_0(sK15,sK17)),k2_xboole_0(sK16,sK17)) ),
    inference(cnf_transformation,[],[f178])).

fof(f55,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f267,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f182])).

cnf(c_76,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f257])).

cnf(c_3342,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_76])).

cnf(c_4135,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_3342])).

cnf(c_96,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK15,sK16),k3_xboole_0(sK15,sK17)),k2_xboole_0(sK16,sK17)) ),
    inference(cnf_transformation,[],[f277])).

cnf(c_3329,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(sK15,sK16),k3_xboole_0(sK15,sK17)),k2_xboole_0(sK16,sK17)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_96])).

cnf(c_86,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f267])).

cnf(c_3520,plain,
    ( r1_tarski(k3_xboole_0(sK15,k2_xboole_0(sK16,sK17)),k2_xboole_0(sK16,sK17)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3329,c_86])).

cnf(c_5736,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4135,c_3520])).

%------------------------------------------------------------------------------
