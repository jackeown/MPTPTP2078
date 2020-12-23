%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0069+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:17 EST 2020

% Result     : Theorem 1.39s
% Output     : CNFRefutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   21 (  23 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    7
%              Number of atoms          :   27 (  29 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f338,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f66])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f243,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f431,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f338,f243])).

fof(f102,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f102])).

fof(f375,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f172])).

fof(f104,conjecture,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f105,negated_conjecture,(
    ~ ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f104])).

fof(f174,plain,(
    ? [X0] : r2_xboole_0(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f105])).

fof(f234,plain,
    ( ? [X0] : r2_xboole_0(X0,k1_xboole_0)
   => r2_xboole_0(sK15,k1_xboole_0) ),
    introduced(choice_axiom,[])).

fof(f235,plain,(
    r2_xboole_0(sK15,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f174,f234])).

fof(f377,plain,(
    r2_xboole_0(sK15,k1_xboole_0) ),
    inference(cnf_transformation,[],[f235])).

fof(f450,plain,(
    r2_xboole_0(sK15,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f377,f243])).

cnf(c_100,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f431])).

cnf(c_5381,plain,
    ( r1_tarski(o_0_0_xboole_0,sK15) ),
    inference(instantiation,[status(thm)],[c_100])).

cnf(c_136,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f375])).

cnf(c_4997,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,sK15)
    | ~ r2_xboole_0(sK15,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_138,negated_conjecture,
    ( r2_xboole_0(sK15,o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f450])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5381,c_4997,c_138])).

%------------------------------------------------------------------------------
