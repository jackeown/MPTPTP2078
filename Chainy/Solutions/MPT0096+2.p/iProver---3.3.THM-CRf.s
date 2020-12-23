%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0096+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:20 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    8
%              Number of atoms          :   17 (  17 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f135,conjecture,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f136,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f135])).

fof(f234,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f136])).

fof(f293,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))
   => ~ r1_xboole_0(k3_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK16)) ),
    introduced(choice_axiom,[])).

fof(f294,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK16)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f234,f293])).

fof(f471,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK15,sK16),k4_xboole_0(sK15,sK16)) ),
    inference(cnf_transformation,[],[f294])).

fof(f87,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f419,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f87])).

fof(f551,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),k4_xboole_0(sK15,sK16)) ),
    inference(definition_unfolding,[],[f471,f419])).

fof(f123,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f458,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_173,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),k4_xboole_0(sK15,sK16)) ),
    inference(cnf_transformation,[],[f551])).

cnf(c_5325,plain,
    ( r1_xboole_0(k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)),k4_xboole_0(sK15,sK16)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_173])).

cnf(c_160,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f458])).

cnf(c_5337,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_160])).

cnf(c_5545,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5325,c_5337])).

%------------------------------------------------------------------------------
