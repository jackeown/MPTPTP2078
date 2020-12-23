%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0732+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:51 EST 2020

% Result     : Theorem 23.49s
% Output     : CNFRefutation 23.49s
% Verified   : 
% Statistics : Number of formulae       :   36 (  54 expanded)
%              Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :   12
%              Number of atoms          :  102 ( 186 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1090,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f2126,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1090])).

fof(f2127,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f2126])).

fof(f2128,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK18(X0,X1),X1)
        & r2_hidden(sK18(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2129,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK18(X0,X1),X1)
          & r2_hidden(sK18(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f2127,f2128])).

fof(f2750,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2129])).

fof(f1063,conjecture,(
    ! [X0,X1,X2] :
      ( v1_ordinal1(X2)
     => ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X1) )
       => r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1064,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_ordinal1(X2)
       => ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X1) )
         => r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f1063])).

fof(f2087,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r2_hidden(X1,X2)
      & r2_hidden(X0,X1)
      & v1_ordinal1(X2) ) ),
    inference(ennf_transformation,[],[f1064])).

fof(f2088,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r2_hidden(X1,X2)
      & r2_hidden(X0,X1)
      & v1_ordinal1(X2) ) ),
    inference(flattening,[],[f2087])).

fof(f2740,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1)
        & v1_ordinal1(X2) )
   => ( ~ r2_hidden(sK235,sK237)
      & r2_hidden(sK236,sK237)
      & r2_hidden(sK235,sK236)
      & v1_ordinal1(sK237) ) ),
    introduced(choice_axiom,[])).

fof(f2741,plain,
    ( ~ r2_hidden(sK235,sK237)
    & r2_hidden(sK236,sK237)
    & r2_hidden(sK235,sK236)
    & v1_ordinal1(sK237) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK235,sK236,sK237])],[f2088,f2740])).

fof(f4469,plain,(
    r2_hidden(sK236,sK237) ),
    inference(cnf_transformation,[],[f2741])).

fof(f1055,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1085,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1055])).

fof(f2083,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1085])).

fof(f4458,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f2083])).

fof(f4467,plain,(
    v1_ordinal1(sK237) ),
    inference(cnf_transformation,[],[f2741])).

fof(f4470,plain,(
    ~ r2_hidden(sK235,sK237) ),
    inference(cnf_transformation,[],[f2741])).

fof(f4468,plain,(
    r2_hidden(sK235,sK236) ),
    inference(cnf_transformation,[],[f2741])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f2750])).

cnf(c_73946,plain,
    ( ~ r1_tarski(X0,sK237)
    | ~ r2_hidden(sK235,X0)
    | r2_hidden(sK235,sK237) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_90294,plain,
    ( ~ r1_tarski(sK236,sK237)
    | ~ r2_hidden(sK235,sK236)
    | r2_hidden(sK235,sK237) ),
    inference(instantiation,[status(thm)],[c_73946])).

cnf(c_1711,negated_conjecture,
    ( r2_hidden(sK236,sK237) ),
    inference(cnf_transformation,[],[f4469])).

cnf(c_70507,plain,
    ( r2_hidden(sK236,sK237) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1711])).

cnf(c_1701,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f4458])).

cnf(c_1713,negated_conjecture,
    ( v1_ordinal1(sK237) ),
    inference(cnf_transformation,[],[f4467])).

cnf(c_17965,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | sK237 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1701,c_1713])).

cnf(c_17966,plain,
    ( r1_tarski(X0,sK237)
    | ~ r2_hidden(X0,sK237) ),
    inference(unflattening,[status(thm)],[c_17965])).

cnf(c_70439,plain,
    ( r1_tarski(X0,sK237) = iProver_top
    | r2_hidden(X0,sK237) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17966])).

cnf(c_78458,plain,
    ( r1_tarski(sK236,sK237) = iProver_top ),
    inference(superposition,[status(thm)],[c_70507,c_70439])).

cnf(c_78459,plain,
    ( r1_tarski(sK236,sK237) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_78458])).

cnf(c_1710,negated_conjecture,
    ( ~ r2_hidden(sK235,sK237) ),
    inference(cnf_transformation,[],[f4470])).

cnf(c_1712,negated_conjecture,
    ( r2_hidden(sK235,sK236) ),
    inference(cnf_transformation,[],[f4468])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_90294,c_78459,c_1710,c_1712])).

%------------------------------------------------------------------------------
