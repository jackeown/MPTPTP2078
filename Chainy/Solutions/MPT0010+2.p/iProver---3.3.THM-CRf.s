%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0010+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:11 EST 2020

% Result     : Theorem 1.05s
% Output     : CNFRefutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   25 (  34 expanded)
%              Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  66 expanded)
%              Number of equality atoms :   19 (  29 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f39,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f187,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f126,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f207,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f187,f126])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f115,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f115])).

fof(f185,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f116])).

fof(f40,conjecture,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,negated_conjecture,(
    ~ ! [X0] :
        ( r1_tarski(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f40])).

fof(f68,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f117,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & r1_tarski(X0,k1_xboole_0) )
   => ( k1_xboole_0 != sK13
      & r1_tarski(sK13,k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f118,plain,
    ( k1_xboole_0 != sK13
    & r1_tarski(sK13,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f68,f117])).

fof(f189,plain,(
    k1_xboole_0 != sK13 ),
    inference(cnf_transformation,[],[f118])).

fof(f208,plain,(
    o_0_0_xboole_0 != sK13 ),
    inference(definition_unfolding,[],[f189,f126])).

fof(f188,plain,(
    r1_tarski(sK13,k1_xboole_0) ),
    inference(cnf_transformation,[],[f118])).

fof(f209,plain,(
    r1_tarski(sK13,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f188,f126])).

cnf(c_66,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f207])).

cnf(c_3058,plain,
    ( r1_tarski(o_0_0_xboole_0,sK13) ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_62,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f185])).

cnf(c_2919,plain,
    ( ~ r1_tarski(sK13,o_0_0_xboole_0)
    | ~ r1_tarski(o_0_0_xboole_0,sK13)
    | o_0_0_xboole_0 = sK13 ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_67,negated_conjecture,
    ( o_0_0_xboole_0 != sK13 ),
    inference(cnf_transformation,[],[f208])).

cnf(c_68,negated_conjecture,
    ( r1_tarski(sK13,o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f209])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3058,c_2919,c_67,c_68])).

%------------------------------------------------------------------------------
