%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0741+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:51 EST 2020

% Result     : Theorem 55.23s
% Output     : CNFRefutation 55.23s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 118 expanded)
%              Number of clauses        :   35 (  37 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  246 ( 584 expanded)
%              Number of equality atoms :   50 (  92 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1060,axiom,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2109,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ( r2_hidden(X2,X1)
          | X1 = X2
          | r2_hidden(X1,X2)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f1060])).

fof(f2788,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1,X2] :
            ( r2_hidden(X2,X1)
            | X1 = X2
            | r2_hidden(X1,X2)
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f2109])).

fof(f2789,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(rectify,[],[f2788])).

fof(f2790,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(X2,X1)
          & X1 != X2
          & ~ r2_hidden(X1,X2)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r2_hidden(sK237(X0),sK236(X0))
        & sK236(X0) != sK237(X0)
        & ~ r2_hidden(sK236(X0),sK237(X0))
        & r2_hidden(sK237(X0),X0)
        & r2_hidden(sK236(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2791,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ( ~ r2_hidden(sK237(X0),sK236(X0))
          & sK236(X0) != sK237(X0)
          & ~ r2_hidden(sK236(X0),sK237(X0))
          & r2_hidden(sK237(X0),X0)
          & r2_hidden(sK236(X0),X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK236,sK237])],[f2789,f2790])).

fof(f4529,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK237(X0),X0) ) ),
    inference(cnf_transformation,[],[f2791])).

fof(f1083,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => ( r1_tarski(X1,X0)
            & v3_ordinal1(X1) ) )
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1084,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( r2_hidden(X1,X0)
           => ( r1_tarski(X1,X0)
              & v3_ordinal1(X1) ) )
       => v3_ordinal1(X0) ) ),
    inference(negated_conjecture,[],[f1083])).

fof(f2134,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(X0)
      & ! [X1] :
          ( ( r1_tarski(X1,X0)
            & v3_ordinal1(X1) )
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f1084])).

fof(f2801,plain,
    ( ? [X0] :
        ( ~ v3_ordinal1(X0)
        & ! [X1] :
            ( ( r1_tarski(X1,X0)
              & v3_ordinal1(X1) )
            | ~ r2_hidden(X1,X0) ) )
   => ( ~ v3_ordinal1(sK240)
      & ! [X1] :
          ( ( r1_tarski(X1,sK240)
            & v3_ordinal1(X1) )
          | ~ r2_hidden(X1,sK240) ) ) ),
    introduced(choice_axiom,[])).

fof(f2802,plain,
    ( ~ v3_ordinal1(sK240)
    & ! [X1] :
        ( ( r1_tarski(X1,sK240)
          & v3_ordinal1(X1) )
        | ~ r2_hidden(X1,sK240) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK240])],[f2134,f2801])).

fof(f4562,plain,(
    ! [X1] :
      ( v3_ordinal1(X1)
      | ~ r2_hidden(X1,sK240) ) ),
    inference(cnf_transformation,[],[f2802])).

fof(f4528,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK236(X0),X0) ) ),
    inference(cnf_transformation,[],[f2791])).

fof(f1078,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2127,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1078])).

fof(f2128,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f2127])).

fof(f4557,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f2128])).

fof(f4563,plain,(
    ! [X1] :
      ( r1_tarski(X1,sK240)
      | ~ r2_hidden(X1,sK240) ) ),
    inference(cnf_transformation,[],[f2802])).

fof(f4531,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | sK236(X0) != sK237(X0) ) ),
    inference(cnf_transformation,[],[f2791])).

fof(f4532,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ~ r2_hidden(sK237(X0),sK236(X0)) ) ),
    inference(cnf_transformation,[],[f2791])).

fof(f4530,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ~ r2_hidden(sK236(X0),sK237(X0)) ) ),
    inference(cnf_transformation,[],[f2791])).

fof(f1059,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2108,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f1059])).

fof(f2784,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f2108])).

fof(f2785,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f2784])).

fof(f2786,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK235(X0),X0)
        & r2_hidden(sK235(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2787,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK235(X0),X0)
          & r2_hidden(sK235(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK235])],[f2785,f2786])).

fof(f4526,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ r1_tarski(sK235(X0),X0) ) ),
    inference(cnf_transformation,[],[f2787])).

fof(f4525,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | r2_hidden(sK235(X0),X0) ) ),
    inference(cnf_transformation,[],[f2787])).

fof(f1061,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
    <=> ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2792,plain,(
    ! [X0] :
      ( ( v3_ordinal1(X0)
        | ~ v2_ordinal1(X0)
        | ~ v1_ordinal1(X0) )
      & ( ( v2_ordinal1(X0)
          & v1_ordinal1(X0) )
        | ~ v3_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f1061])).

fof(f2793,plain,(
    ! [X0] :
      ( ( v3_ordinal1(X0)
        | ~ v2_ordinal1(X0)
        | ~ v1_ordinal1(X0) )
      & ( ( v2_ordinal1(X0)
          & v1_ordinal1(X0) )
        | ~ v3_ordinal1(X0) ) ) ),
    inference(flattening,[],[f2792])).

fof(f4535,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f2793])).

fof(f4564,plain,(
    ~ v3_ordinal1(sK240) ),
    inference(cnf_transformation,[],[f2802])).

cnf(c_1712,plain,
    ( r2_hidden(sK237(X0),X0)
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f4529])).

cnf(c_73065,plain,
    ( r2_hidden(sK237(X0),X0) = iProver_top
    | v2_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1712])).

cnf(c_1746,negated_conjecture,
    ( ~ r2_hidden(X0,sK240)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f4562])).

cnf(c_73035,plain,
    ( r2_hidden(X0,sK240) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1746])).

cnf(c_231548,plain,
    ( v3_ordinal1(sK237(sK240)) = iProver_top
    | v2_ordinal1(sK240) = iProver_top ),
    inference(superposition,[status(thm)],[c_73065,c_73035])).

cnf(c_1713,plain,
    ( r2_hidden(sK236(X0),X0)
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f4528])).

cnf(c_73064,plain,
    ( r2_hidden(sK236(X0),X0) = iProver_top
    | v2_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1713])).

cnf(c_231540,plain,
    ( v3_ordinal1(sK236(sK240)) = iProver_top
    | v2_ordinal1(sK240) = iProver_top ),
    inference(superposition,[status(thm)],[c_73064,c_73035])).

cnf(c_1739,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f4557])).

cnf(c_122929,plain,
    ( r2_hidden(sK236(sK240),sK237(sK240))
    | r2_hidden(sK237(sK240),sK236(sK240))
    | ~ v3_ordinal1(sK236(sK240))
    | ~ v3_ordinal1(sK237(sK240))
    | sK236(sK240) = sK237(sK240) ),
    inference(instantiation,[status(thm)],[c_1739])).

cnf(c_122944,plain,
    ( sK236(sK240) = sK237(sK240)
    | r2_hidden(sK236(sK240),sK237(sK240)) = iProver_top
    | r2_hidden(sK237(sK240),sK236(sK240)) = iProver_top
    | v3_ordinal1(sK236(sK240)) != iProver_top
    | v3_ordinal1(sK237(sK240)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_122929])).

cnf(c_1745,negated_conjecture,
    ( r1_tarski(X0,sK240)
    | ~ r2_hidden(X0,sK240) ),
    inference(cnf_transformation,[],[f4563])).

cnf(c_108969,plain,
    ( r1_tarski(sK235(sK240),sK240)
    | ~ r2_hidden(sK235(sK240),sK240) ),
    inference(instantiation,[status(thm)],[c_1745])).

cnf(c_108970,plain,
    ( r1_tarski(sK235(sK240),sK240) = iProver_top
    | r2_hidden(sK235(sK240),sK240) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_108969])).

cnf(c_1710,plain,
    ( v2_ordinal1(X0)
    | sK236(X0) != sK237(X0) ),
    inference(cnf_transformation,[],[f4531])).

cnf(c_102623,plain,
    ( v2_ordinal1(sK240)
    | sK236(sK240) != sK237(sK240) ),
    inference(instantiation,[status(thm)],[c_1710])).

cnf(c_102637,plain,
    ( sK236(sK240) != sK237(sK240)
    | v2_ordinal1(sK240) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_102623])).

cnf(c_1709,plain,
    ( ~ r2_hidden(sK237(X0),sK236(X0))
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f4532])).

cnf(c_102624,plain,
    ( ~ r2_hidden(sK237(sK240),sK236(sK240))
    | v2_ordinal1(sK240) ),
    inference(instantiation,[status(thm)],[c_1709])).

cnf(c_102635,plain,
    ( r2_hidden(sK237(sK240),sK236(sK240)) != iProver_top
    | v2_ordinal1(sK240) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_102624])).

cnf(c_1711,plain,
    ( ~ r2_hidden(sK236(X0),sK237(X0))
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f4530])).

cnf(c_102625,plain,
    ( ~ r2_hidden(sK236(sK240),sK237(sK240))
    | v2_ordinal1(sK240) ),
    inference(instantiation,[status(thm)],[c_1711])).

cnf(c_102633,plain,
    ( r2_hidden(sK236(sK240),sK237(sK240)) != iProver_top
    | v2_ordinal1(sK240) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_102625])).

cnf(c_1706,plain,
    ( ~ r1_tarski(sK235(X0),X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f4526])).

cnf(c_76965,plain,
    ( ~ r1_tarski(sK235(sK240),sK240)
    | v1_ordinal1(sK240) ),
    inference(instantiation,[status(thm)],[c_1706])).

cnf(c_76970,plain,
    ( r1_tarski(sK235(sK240),sK240) != iProver_top
    | v1_ordinal1(sK240) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_76965])).

cnf(c_1707,plain,
    ( r2_hidden(sK235(X0),X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f4525])).

cnf(c_76966,plain,
    ( r2_hidden(sK235(sK240),sK240)
    | v1_ordinal1(sK240) ),
    inference(instantiation,[status(thm)],[c_1707])).

cnf(c_76968,plain,
    ( r2_hidden(sK235(sK240),sK240) = iProver_top
    | v1_ordinal1(sK240) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_76966])).

cnf(c_1715,plain,
    ( ~ v1_ordinal1(X0)
    | v3_ordinal1(X0)
    | ~ v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f4535])).

cnf(c_76419,plain,
    ( ~ v1_ordinal1(sK240)
    | v3_ordinal1(sK240)
    | ~ v2_ordinal1(sK240) ),
    inference(instantiation,[status(thm)],[c_1715])).

cnf(c_76423,plain,
    ( v1_ordinal1(sK240) != iProver_top
    | v3_ordinal1(sK240) = iProver_top
    | v2_ordinal1(sK240) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_76419])).

cnf(c_1744,negated_conjecture,
    ( ~ v3_ordinal1(sK240) ),
    inference(cnf_transformation,[],[f4564])).

cnf(c_1758,plain,
    ( v3_ordinal1(sK240) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1744])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_231548,c_231540,c_122944,c_108970,c_102637,c_102635,c_102633,c_76970,c_76968,c_76423,c_1758])).

%------------------------------------------------------------------------------
