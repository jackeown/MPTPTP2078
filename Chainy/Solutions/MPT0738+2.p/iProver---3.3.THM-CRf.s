%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0738+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:51 EST 2020

% Result     : Theorem 27.81s
% Output     : CNFRefutation 27.81s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 554 expanded)
%              Number of clauses        :   44 ( 156 expanded)
%              Number of leaves         :   11 ( 137 expanded)
%              Depth                    :   18
%              Number of atoms          :  294 (2082 expanded)
%              Number of equality atoms :   74 ( 211 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1075,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2120,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1075])).

fof(f2121,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f2120])).

fof(f4536,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f2121])).

fof(f1077,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1078,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
              | r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f1077])).

fof(f2123,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,X0)
          & ~ r1_ordinal1(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1078])).

fof(f2124,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,X0)
          & ~ r1_ordinal1(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f2123])).

fof(f2788,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,X0)
          & ~ r1_ordinal1(X0,X1)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(sK240,X0)
        & ~ r1_ordinal1(X0,sK240)
        & v3_ordinal1(sK240) ) ) ),
    introduced(choice_axiom,[])).

fof(f2787,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_hidden(X1,X0)
            & ~ r1_ordinal1(X0,X1)
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ~ r2_hidden(X1,sK239)
          & ~ r1_ordinal1(sK239,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK239) ) ),
    introduced(choice_axiom,[])).

fof(f2789,plain,
    ( ~ r2_hidden(sK240,sK239)
    & ~ r1_ordinal1(sK239,sK240)
    & v3_ordinal1(sK240)
    & v3_ordinal1(sK239) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK239,sK240])],[f2124,f2788,f2787])).

fof(f4541,plain,(
    ~ r2_hidden(sK240,sK239) ),
    inference(cnf_transformation,[],[f2789])).

fof(f4538,plain,(
    v3_ordinal1(sK239) ),
    inference(cnf_transformation,[],[f2789])).

fof(f4539,plain,(
    v3_ordinal1(sK240) ),
    inference(cnf_transformation,[],[f2789])).

fof(f1056,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2099,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1056])).

fof(f2100,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f2099])).

fof(f4508,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f2100])).

fof(f4540,plain,(
    ~ r1_ordinal1(sK239,sK240) ),
    inference(cnf_transformation,[],[f2789])).

fof(f1065,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2107,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1065])).

fof(f2108,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f2107])).

fof(f2784,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f2108])).

fof(f4523,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f2784])).

fof(f1073,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ! [X2] :
              ( v3_ordinal1(X2)
             => ( ( r2_hidden(X1,X2)
                  & r1_tarski(X0,X1) )
               => r2_hidden(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2116,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X0,X2)
              | ~ r2_hidden(X1,X2)
              | ~ r1_tarski(X0,X1)
              | ~ v3_ordinal1(X2) )
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1073])).

fof(f2117,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X0,X2)
              | ~ r2_hidden(X1,X2)
              | ~ r1_tarski(X0,X1)
              | ~ v3_ordinal1(X2) )
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f2116])).

fof(f4534,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X2)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f2117])).

fof(f1074,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2118,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f1074])).

fof(f2119,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f2118])).

fof(f4535,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f2119])).

fof(f1054,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2096,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1054])).

fof(f4505,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f2096])).

fof(f4524,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f2784])).

fof(f1058,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2101,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f1058])).

fof(f2774,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f2101])).

fof(f2775,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f2774])).

fof(f2776,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK235(X0),X0)
        & r2_hidden(sK235(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2777,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK235(X0),X0)
          & r2_hidden(sK235(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK235])],[f2775,f2776])).

fof(f4510,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f2777])).

cnf(c_1731,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f4536])).

cnf(c_47956,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1731])).

cnf(c_1733,negated_conjecture,
    ( ~ r2_hidden(sK240,sK239) ),
    inference(cnf_transformation,[],[f4541])).

cnf(c_47954,plain,
    ( r2_hidden(sK240,sK239) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1733])).

cnf(c_62938,plain,
    ( sK239 = sK240
    | r2_hidden(sK239,sK240) = iProver_top
    | v3_ordinal1(sK239) != iProver_top
    | v3_ordinal1(sK240) != iProver_top ),
    inference(superposition,[status(thm)],[c_47956,c_47954])).

cnf(c_1736,negated_conjecture,
    ( v3_ordinal1(sK239) ),
    inference(cnf_transformation,[],[f4538])).

cnf(c_1742,plain,
    ( v3_ordinal1(sK239) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1736])).

cnf(c_1735,negated_conjecture,
    ( v3_ordinal1(sK240) ),
    inference(cnf_transformation,[],[f4539])).

cnf(c_1743,plain,
    ( v3_ordinal1(sK240) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1735])).

cnf(c_63388,plain,
    ( sK239 = sK240
    | r2_hidden(sK239,sK240) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_62938,c_1742,c_1743])).

cnf(c_1704,plain,
    ( r1_ordinal1(X0,X1)
    | r1_ordinal1(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f4508])).

cnf(c_47982,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1704])).

cnf(c_1734,negated_conjecture,
    ( ~ r1_ordinal1(sK239,sK240) ),
    inference(cnf_transformation,[],[f4540])).

cnf(c_47953,plain,
    ( r1_ordinal1(sK239,sK240) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1734])).

cnf(c_71705,plain,
    ( r1_ordinal1(sK240,sK239) = iProver_top
    | v3_ordinal1(sK239) != iProver_top
    | v3_ordinal1(sK240) != iProver_top ),
    inference(superposition,[status(thm)],[c_47982,c_47953])).

cnf(c_1744,plain,
    ( r1_ordinal1(sK239,sK240) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1734])).

cnf(c_64173,plain,
    ( r1_ordinal1(sK239,sK240)
    | r1_ordinal1(sK240,sK239)
    | ~ v3_ordinal1(sK239)
    | ~ v3_ordinal1(sK240) ),
    inference(instantiation,[status(thm)],[c_1704])).

cnf(c_64174,plain,
    ( r1_ordinal1(sK239,sK240) = iProver_top
    | r1_ordinal1(sK240,sK239) = iProver_top
    | v3_ordinal1(sK239) != iProver_top
    | v3_ordinal1(sK240) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64173])).

cnf(c_71920,plain,
    ( r1_ordinal1(sK240,sK239) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_71705,c_1742,c_1743,c_1744,c_64174])).

cnf(c_1719,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f4523])).

cnf(c_47967,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1719])).

cnf(c_71925,plain,
    ( r1_tarski(sK240,sK239) = iProver_top
    | v3_ordinal1(sK239) != iProver_top
    | v3_ordinal1(sK240) != iProver_top ),
    inference(superposition,[status(thm)],[c_71920,c_47967])).

cnf(c_72334,plain,
    ( r1_tarski(sK240,sK239) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_71925,c_1742,c_1743])).

cnf(c_1729,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X0,X2)
    | ~ v1_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(cnf_transformation,[],[f4534])).

cnf(c_47958,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | v1_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1729])).

cnf(c_1730,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f4535])).

cnf(c_47957,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1730])).

cnf(c_55506,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | v1_ordinal1(X0) != iProver_top
    | v3_ordinal1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_47958,c_47957])).

cnf(c_97574,plain,
    ( r2_hidden(sK239,X0) != iProver_top
    | r2_hidden(sK240,X0) = iProver_top
    | v1_ordinal1(sK240) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_72334,c_55506])).

cnf(c_1702,plain,
    ( v1_ordinal1(X0)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f4505])).

cnf(c_61688,plain,
    ( v1_ordinal1(sK240)
    | ~ v3_ordinal1(sK240) ),
    inference(instantiation,[status(thm)],[c_1702])).

cnf(c_61689,plain,
    ( v1_ordinal1(sK240) = iProver_top
    | v3_ordinal1(sK240) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61688])).

cnf(c_98524,plain,
    ( r2_hidden(sK240,X0) = iProver_top
    | r2_hidden(sK239,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_97574,c_1743,c_61689])).

cnf(c_98525,plain,
    ( r2_hidden(sK239,X0) != iProver_top
    | r2_hidden(sK240,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_98524])).

cnf(c_98538,plain,
    ( sK239 = sK240
    | r2_hidden(sK240,sK240) = iProver_top
    | v3_ordinal1(sK240) != iProver_top ),
    inference(superposition,[status(thm)],[c_63388,c_98525])).

cnf(c_63390,plain,
    ( r2_hidden(sK239,sK240)
    | sK239 = sK240 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_63388])).

cnf(c_1718,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f4524])).

cnf(c_64176,plain,
    ( r1_ordinal1(sK239,sK240)
    | ~ r1_tarski(sK239,sK240)
    | ~ v3_ordinal1(sK239)
    | ~ v3_ordinal1(sK240) ),
    inference(instantiation,[status(thm)],[c_1718])).

cnf(c_1707,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f4510])).

cnf(c_82775,plain,
    ( r1_tarski(sK239,sK240)
    | ~ r2_hidden(sK239,sK240)
    | ~ v1_ordinal1(sK240) ),
    inference(instantiation,[status(thm)],[c_1707])).

cnf(c_98575,plain,
    ( sK239 = sK240 ),
    inference(global_propositional_subsumption,[status(thm)],[c_98538,c_1736,c_1735,c_1734,c_61688,c_63390,c_64176,c_82775])).

cnf(c_98582,plain,
    ( r1_ordinal1(sK240,sK240) = iProver_top ),
    inference(demodulation,[status(thm)],[c_98575,c_71920])).

cnf(c_98584,plain,
    ( r1_ordinal1(sK240,sK240) != iProver_top ),
    inference(demodulation,[status(thm)],[c_98575,c_47953])).

cnf(c_98591,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_98582,c_98584])).

%------------------------------------------------------------------------------
