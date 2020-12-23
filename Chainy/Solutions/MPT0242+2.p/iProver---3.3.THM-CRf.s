%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0242+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:29 EST 2020

% Result     : Theorem 7.61s
% Output     : CNFRefutation 7.61s
% Verified   : 
% Statistics : Number of formulae       :   22 (  30 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :    3 (   6 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 (  82 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f336,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f337,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f336])).

fof(f479,plain,(
    ? [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f337])).

fof(f609,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) )
      & ( r2_hidden(X0,X1)
        | r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f479])).

fof(f610,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | ~ r1_tarski(k1_tarski(X0),X1) )
        & ( r2_hidden(X0,X1)
          | r1_tarski(k1_tarski(X0),X1) ) )
   => ( ( ~ r2_hidden(sK33,sK34)
        | ~ r1_tarski(k1_tarski(sK33),sK34) )
      & ( r2_hidden(sK33,sK34)
        | r1_tarski(k1_tarski(sK33),sK34) ) ) ),
    introduced(choice_axiom,[])).

fof(f611,plain,
    ( ( ~ r2_hidden(sK33,sK34)
      | ~ r1_tarski(k1_tarski(sK33),sK34) )
    & ( r2_hidden(sK33,sK34)
      | r1_tarski(k1_tarski(sK33),sK34) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK33,sK34])],[f609,f610])).

fof(f1064,plain,
    ( ~ r2_hidden(sK33,sK34)
    | ~ r1_tarski(k1_tarski(sK33),sK34) ),
    inference(cnf_transformation,[],[f611])).

fof(f294,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f595,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f294])).

fof(f1002,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f595])).

fof(f1063,plain,
    ( r2_hidden(sK33,sK34)
    | r1_tarski(k1_tarski(sK33),sK34) ),
    inference(cnf_transformation,[],[f611])).

fof(f1003,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f595])).

cnf(c_439,negated_conjecture,
    ( ~ r1_tarski(k1_tarski(sK33),sK34)
    | ~ r2_hidden(sK33,sK34) ),
    inference(cnf_transformation,[],[f1064])).

cnf(c_13661,plain,
    ( r1_tarski(k1_tarski(sK33),sK34) != iProver_top
    | r2_hidden(sK33,sK34) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_439])).

cnf(c_379,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f1002])).

cnf(c_13698,plain,
    ( r1_tarski(k1_tarski(X0),X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_440,negated_conjecture,
    ( r1_tarski(k1_tarski(sK33),sK34)
    | r2_hidden(sK33,sK34) ),
    inference(cnf_transformation,[],[f1063])).

cnf(c_13660,plain,
    ( r1_tarski(k1_tarski(sK33),sK34) = iProver_top
    | r2_hidden(sK33,sK34) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_440])).

cnf(c_14137,plain,
    ( r2_hidden(sK33,sK34) = iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_13698,c_13660])).

cnf(c_378,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f1003])).

cnf(c_13699,plain,
    ( r1_tarski(k1_tarski(X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_378])).

cnf(c_14205,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13661,c_14137,c_13699])).

%------------------------------------------------------------------------------
