%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0748+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:51 EST 2020

% Result     : Theorem 31.11s
% Output     : CNFRefutation 31.11s
% Verified   : 
% Statistics : Number of formulae       :   39 (  49 expanded)
%              Number of clauses        :   19 (  19 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    9
%              Number of atoms          :  117 ( 170 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1073,axiom,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( r2_hidden(X2,X1)
    <=> ( v3_ordinal1(X2)
        & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2821,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(nnf_transformation,[],[f1073])).

fof(f2822,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(flattening,[],[f2821])).

fof(f2823,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ( r2_hidden(X2,X1)
            | ~ v3_ordinal1(X2)
            | ~ r2_hidden(X2,X0) )
          & ( ( v3_ordinal1(X2)
              & r2_hidden(X2,X0) )
            | ~ r2_hidden(X2,X1) ) )
     => ! [X2] :
          ( ( r2_hidden(X2,sK240(X0))
            | ~ v3_ordinal1(X2)
            | ~ r2_hidden(X2,X0) )
          & ( ( v3_ordinal1(X2)
              & r2_hidden(X2,X0) )
            | ~ r2_hidden(X2,sK240(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2824,plain,(
    ! [X0,X2] :
      ( ( r2_hidden(X2,sK240(X0))
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,sK240(X0)) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK240])],[f2822,f2823])).

fof(f4592,plain,(
    ! [X2,X0] :
      ( v3_ordinal1(X2)
      | ~ r2_hidden(X2,sK240(X0)) ) ),
    inference(cnf_transformation,[],[f2824])).

fof(f1093,axiom,(
    ! [X0] :
      ~ ! [X1] :
          ( r2_hidden(X1,X0)
        <=> v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2155,plain,(
    ! [X0] :
    ? [X1] :
      ( r2_hidden(X1,X0)
    <~> v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f1093])).

fof(f2838,plain,(
    ! [X0] :
    ? [X1] :
      ( ( ~ v3_ordinal1(X1)
        | ~ r2_hidden(X1,X0) )
      & ( v3_ordinal1(X1)
        | r2_hidden(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f2155])).

fof(f2839,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v3_ordinal1(X1)
            | ~ r2_hidden(X1,X0) )
          & ( v3_ordinal1(X1)
            | r2_hidden(X1,X0) ) )
     => ( ( ~ v3_ordinal1(sK246(X0))
          | ~ r2_hidden(sK246(X0),X0) )
        & ( v3_ordinal1(sK246(X0))
          | r2_hidden(sK246(X0),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2840,plain,(
    ! [X0] :
      ( ( ~ v3_ordinal1(sK246(X0))
        | ~ r2_hidden(sK246(X0),X0) )
      & ( v3_ordinal1(sK246(X0))
        | r2_hidden(sK246(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK246])],[f2838,f2839])).

fof(f4624,plain,(
    ! [X0] :
      ( v3_ordinal1(sK246(X0))
      | r2_hidden(sK246(X0),X0) ) ),
    inference(cnf_transformation,[],[f2840])).

fof(f1094,conjecture,(
    ! [X0] :
      ~ ! [X1] :
          ( v3_ordinal1(X1)
         => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1095,negated_conjecture,(
    ~ ! [X0] :
        ~ ! [X1] :
            ( v3_ordinal1(X1)
           => r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f1094])).

fof(f2156,plain,(
    ? [X0] :
    ! [X1] :
      ( r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f1095])).

fof(f2841,plain,
    ( ? [X0] :
      ! [X1] :
        ( r2_hidden(X1,X0)
        | ~ v3_ordinal1(X1) )
   => ! [X1] :
        ( r2_hidden(X1,sK247)
        | ~ v3_ordinal1(X1) ) ),
    introduced(choice_axiom,[])).

fof(f2842,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK247)
      | ~ v3_ordinal1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK247])],[f2156,f2841])).

fof(f4626,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK247)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f2842])).

fof(f4593,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,sK240(X0))
      | ~ v3_ordinal1(X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f2824])).

fof(f4625,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK246(X0))
      | ~ r2_hidden(sK246(X0),X0) ) ),
    inference(cnf_transformation,[],[f2840])).

cnf(c_1734,plain,
    ( ~ r2_hidden(X0,sK240(X1))
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f4592])).

cnf(c_80861,plain,
    ( ~ r2_hidden(sK246(sK240(X0)),sK240(X0))
    | v3_ordinal1(sK246(sK240(X0))) ),
    inference(instantiation,[status(thm)],[c_1734])).

cnf(c_127811,plain,
    ( ~ r2_hidden(sK246(sK240(sK247)),sK240(sK247))
    | v3_ordinal1(sK246(sK240(sK247))) ),
    inference(instantiation,[status(thm)],[c_80861])).

cnf(c_127815,plain,
    ( r2_hidden(sK246(sK240(sK247)),sK240(sK247)) != iProver_top
    | v3_ordinal1(sK246(sK240(sK247))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_127811])).

cnf(c_1767,plain,
    ( r2_hidden(sK246(X0),X0)
    | v3_ordinal1(sK246(X0)) ),
    inference(cnf_transformation,[],[f4624])).

cnf(c_80860,plain,
    ( r2_hidden(sK246(sK240(X0)),sK240(X0))
    | v3_ordinal1(sK246(sK240(X0))) ),
    inference(instantiation,[status(thm)],[c_1767])).

cnf(c_127812,plain,
    ( r2_hidden(sK246(sK240(sK247)),sK240(sK247))
    | v3_ordinal1(sK246(sK240(sK247))) ),
    inference(instantiation,[status(thm)],[c_80860])).

cnf(c_127813,plain,
    ( r2_hidden(sK246(sK240(sK247)),sK240(sK247)) = iProver_top
    | v3_ordinal1(sK246(sK240(sK247))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_127812])).

cnf(c_1768,negated_conjecture,
    ( r2_hidden(X0,sK247)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f4626])).

cnf(c_122960,plain,
    ( r2_hidden(sK246(sK240(sK247)),sK247)
    | ~ v3_ordinal1(sK246(sK240(sK247))) ),
    inference(instantiation,[status(thm)],[c_1768])).

cnf(c_122961,plain,
    ( r2_hidden(sK246(sK240(sK247)),sK247) = iProver_top
    | v3_ordinal1(sK246(sK240(sK247))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_122960])).

cnf(c_1733,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,sK240(X1))
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f4593])).

cnf(c_82288,plain,
    ( r2_hidden(X0,sK240(sK247))
    | ~ r2_hidden(X0,sK247)
    | ~ v3_ordinal1(X0) ),
    inference(instantiation,[status(thm)],[c_1733])).

cnf(c_99814,plain,
    ( r2_hidden(sK246(sK240(sK247)),sK240(sK247))
    | ~ r2_hidden(sK246(sK240(sK247)),sK247)
    | ~ v3_ordinal1(sK246(sK240(sK247))) ),
    inference(instantiation,[status(thm)],[c_82288])).

cnf(c_99817,plain,
    ( r2_hidden(sK246(sK240(sK247)),sK240(sK247)) = iProver_top
    | r2_hidden(sK246(sK240(sK247)),sK247) != iProver_top
    | v3_ordinal1(sK246(sK240(sK247))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_99814])).

cnf(c_1766,plain,
    ( ~ r2_hidden(sK246(X0),X0)
    | ~ v3_ordinal1(sK246(X0)) ),
    inference(cnf_transformation,[],[f4625])).

cnf(c_99813,plain,
    ( ~ r2_hidden(sK246(sK240(sK247)),sK240(sK247))
    | ~ v3_ordinal1(sK246(sK240(sK247))) ),
    inference(instantiation,[status(thm)],[c_1766])).

cnf(c_99815,plain,
    ( r2_hidden(sK246(sK240(sK247)),sK240(sK247)) != iProver_top
    | v3_ordinal1(sK246(sK240(sK247))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_99813])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_127815,c_127813,c_122961,c_99817,c_99815])).

%------------------------------------------------------------------------------
