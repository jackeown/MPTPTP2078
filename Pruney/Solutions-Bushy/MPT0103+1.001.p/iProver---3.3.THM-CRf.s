%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0103+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:29 EST 2020

% Result     : Theorem 0.55s
% Output     : CNFRefutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   14 (  14 expanded)
%              Number of clauses        :    3 (   3 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    7
%              Number of atoms          :   15 (  15 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,conjecture,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1] : ~ r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f4])).

fof(f6,plain,
    ( ? [X0,X1] : ~ r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))
   => ~ r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f6])).

fof(f10,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) ),
    inference(definition_unfolding,[],[f10,f8])).

cnf(c_0,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_1,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_20,plain,
    ( $false ),
    inference(resolution,[status(thm)],[c_0,c_1])).


%------------------------------------------------------------------------------
