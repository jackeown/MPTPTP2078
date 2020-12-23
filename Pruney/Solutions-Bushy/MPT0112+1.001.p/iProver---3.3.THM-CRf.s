%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0112+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:30 EST 2020

% Result     : Theorem 0.59s
% Output     : CNFRefutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   23 (  28 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :   10
%              Number of atoms          :   43 (  55 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ~ ( k4_xboole_0(X1,X0) = k1_xboole_0
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k4_xboole_0(X1,X0) = k1_xboole_0
          & r2_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X1,X0) = k1_xboole_0
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( k4_xboole_0(X1,X0) = k1_xboole_0
        & r2_xboole_0(X0,X1) )
   => ( k4_xboole_0(sK1,sK0) = k1_xboole_0
      & r2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( k4_xboole_0(sK1,sK0) = k1_xboole_0
    & r2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f9])).

fof(f13,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f14,plain,(
    k4_xboole_0(sK1,sK0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

cnf(c_0,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_3,negated_conjecture,
    ( r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_39,plain,
    ( ~ r1_tarski(X0,X1)
    | sK0 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_3])).

cnf(c_40,plain,
    ( ~ r1_tarski(sK1,sK0) ),
    inference(unflattening,[status(thm)],[c_39])).

cnf(c_48,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | sK0 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_40])).

cnf(c_49,plain,
    ( k4_xboole_0(sK1,sK0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_48])).

cnf(c_2,negated_conjecture,
    ( k4_xboole_0(sK1,sK0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_49,c_2])).


%------------------------------------------------------------------------------
