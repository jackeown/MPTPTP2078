%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0122+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:23 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   17 (  19 expanded)
%              Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    8
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,axiom,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f517,plain,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f127])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f353,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f671,plain,(
    ! [X0] : ~ r2_xboole_0(X0,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f517,f353])).

fof(f64,conjecture,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,negated_conjecture,(
    ~ ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f64])).

fof(f206,plain,(
    ? [X0] : r2_xboole_0(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f65])).

fof(f338,plain,
    ( ? [X0] : r2_xboole_0(X0,k1_xboole_0)
   => r2_xboole_0(sK13,k1_xboole_0) ),
    introduced(choice_axiom,[])).

fof(f339,plain,(
    r2_xboole_0(sK13,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f206,f338])).

fof(f450,plain,(
    r2_xboole_0(sK13,k1_xboole_0) ),
    inference(cnf_transformation,[],[f339])).

fof(f616,plain,(
    r2_xboole_0(sK13,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f450,f353])).

cnf(c_169,plain,
    ( ~ r2_xboole_0(X0,o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f671])).

cnf(c_6407,plain,
    ( r2_xboole_0(X0,o_0_0_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_169])).

cnf(c_103,negated_conjecture,
    ( r2_xboole_0(sK13,o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f616])).

cnf(c_6441,plain,
    ( r2_xboole_0(sK13,o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_103])).

cnf(c_6549,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_6407,c_6441])).

%------------------------------------------------------------------------------
