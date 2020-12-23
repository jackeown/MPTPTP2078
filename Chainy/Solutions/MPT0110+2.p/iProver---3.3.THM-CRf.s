%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0110+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:22 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   17 (  19 expanded)
%              Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    8
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48,conjecture,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f48])).

fof(f179,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f49])).

fof(f306,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))
   => ~ r1_xboole_0(k3_xboole_0(sK13,sK14),k5_xboole_0(sK13,sK14)) ),
    introduced(choice_axiom,[])).

fof(f307,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK13,sK14),k5_xboole_0(sK13,sK14)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14])],[f179,f306])).

fof(f394,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK13,sK14),k5_xboole_0(sK13,sK14)) ),
    inference(cnf_transformation,[],[f307])).

fof(f94,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f444,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f94])).

fof(f550,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK13,k4_xboole_0(sK13,sK14)),k5_xboole_0(sK13,sK14)) ),
    inference(definition_unfolding,[],[f394,f444])).

fof(f43,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f389,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f546,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f389,f444])).

cnf(c_79,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(sK13,k4_xboole_0(sK13,sK14)),k5_xboole_0(sK13,sK14)) ),
    inference(cnf_transformation,[],[f550])).

cnf(c_5759,plain,
    ( r1_xboole_0(k4_xboole_0(sK13,k4_xboole_0(sK13,sK14)),k5_xboole_0(sK13,sK14)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_79])).

cnf(c_75,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f546])).

cnf(c_5760,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_75])).

cnf(c_5919,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5759,c_5760])).

%------------------------------------------------------------------------------
