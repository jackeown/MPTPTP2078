%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0802+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:53 EST 2020

% Result     : Theorem 31.44s
% Output     : CNFRefutation 31.44s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 247 expanded)
%              Number of clauses        :   50 (  62 expanded)
%              Number of leaves         :    6 (  71 expanded)
%              Depth                    :    9
%              Number of atoms          :  397 (1791 expanded)
%              Number of equality atoms :  102 ( 106 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   15 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1192,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( r3_wellord1(X0,X1,X2)
                  & v2_wellord1(X0) )
               => v2_wellord1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1193,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( r3_wellord1(X0,X1,X2)
                    & v2_wellord1(X0) )
                 => v2_wellord1(X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f1192])).

fof(f2394,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_wellord1(X1)
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1193])).

fof(f2395,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_wellord1(X1)
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f2394])).

fof(f3233,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_wellord1(X1)
          & r3_wellord1(X0,X1,X2)
          & v2_wellord1(X0)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ~ v2_wellord1(X1)
        & r3_wellord1(X0,X1,sK309)
        & v2_wellord1(X0)
        & v1_funct_1(sK309)
        & v1_relat_1(sK309) ) ) ),
    introduced(choice_axiom,[])).

fof(f3232,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_wellord1(X1)
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ~ v2_wellord1(sK308)
            & r3_wellord1(X0,sK308,X2)
            & v2_wellord1(X0)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_relat_1(sK308) ) ) ),
    introduced(choice_axiom,[])).

fof(f3231,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_wellord1(X1)
                & r3_wellord1(X0,X1,X2)
                & v2_wellord1(X0)
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_wellord1(X1)
              & r3_wellord1(sK307,X1,X2)
              & v2_wellord1(sK307)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK307) ) ),
    introduced(choice_axiom,[])).

fof(f3234,plain,
    ( ~ v2_wellord1(sK308)
    & r3_wellord1(sK307,sK308,sK309)
    & v2_wellord1(sK307)
    & v1_funct_1(sK309)
    & v1_relat_1(sK309)
    & v1_relat_1(sK308)
    & v1_relat_1(sK307) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK307,sK308,sK309])],[f2395,f3233,f3232,f3231])).

fof(f5288,plain,(
    v1_relat_1(sK308) ),
    inference(cnf_transformation,[],[f3234])).

fof(f1133,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2305,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1133])).

fof(f3160,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f2305])).

fof(f3161,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f3160])).

fof(f5152,plain,(
    ! [X0] :
      ( v2_wellord1(X0)
      | ~ v1_wellord1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3161])).

fof(f5287,plain,(
    v1_relat_1(sK307) ),
    inference(cnf_transformation,[],[f3234])).

fof(f5147,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3161])).

fof(f5292,plain,(
    r3_wellord1(sK307,sK308,sK309) ),
    inference(cnf_transformation,[],[f3234])).

fof(f1191,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
               => ( ( v1_wellord1(X0)
                   => v1_wellord1(X1) )
                  & ( v4_relat_2(X0)
                   => v4_relat_2(X1) )
                  & ( v6_relat_2(X0)
                   => v6_relat_2(X1) )
                  & ( v8_relat_2(X0)
                   => v8_relat_2(X1) )
                  & ( v1_relat_2(X0)
                   => v1_relat_2(X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2392,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v1_wellord1(X1)
                  | ~ v1_wellord1(X0) )
                & ( v4_relat_2(X1)
                  | ~ v4_relat_2(X0) )
                & ( v6_relat_2(X1)
                  | ~ v6_relat_2(X0) )
                & ( v8_relat_2(X1)
                  | ~ v8_relat_2(X0) )
                & ( v1_relat_2(X1)
                  | ~ v1_relat_2(X0) ) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1191])).

fof(f2393,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v1_wellord1(X1)
                  | ~ v1_wellord1(X0) )
                & ( v4_relat_2(X1)
                  | ~ v4_relat_2(X0) )
                & ( v6_relat_2(X1)
                  | ~ v6_relat_2(X0) )
                & ( v8_relat_2(X1)
                  | ~ v8_relat_2(X0) )
                & ( v1_relat_2(X1)
                  | ~ v1_relat_2(X0) ) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2392])).

fof(f5286,plain,(
    ! [X2,X0,X1] :
      ( v1_wellord1(X1)
      | ~ v1_wellord1(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2393])).

fof(f5285,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_2(X1)
      | ~ v4_relat_2(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2393])).

fof(f5284,plain,(
    ! [X2,X0,X1] :
      ( v6_relat_2(X1)
      | ~ v6_relat_2(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2393])).

fof(f5283,plain,(
    ! [X2,X0,X1] :
      ( v8_relat_2(X1)
      | ~ v8_relat_2(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2393])).

fof(f5150,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3161])).

fof(f5291,plain,(
    v2_wellord1(sK307) ),
    inference(cnf_transformation,[],[f3234])).

fof(f5151,plain,(
    ! [X0] :
      ( v1_wellord1(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3161])).

fof(f5282,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_2(X1)
      | ~ v1_relat_2(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2393])).

fof(f5148,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3161])).

fof(f5149,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3161])).

fof(f5293,plain,(
    ~ v2_wellord1(sK308) ),
    inference(cnf_transformation,[],[f3234])).

fof(f5290,plain,(
    v1_funct_1(sK309) ),
    inference(cnf_transformation,[],[f3234])).

fof(f5289,plain,(
    v1_relat_1(sK309) ),
    inference(cnf_transformation,[],[f3234])).

cnf(c_2038,negated_conjecture,
    ( v1_relat_1(sK308) ),
    inference(cnf_transformation,[],[f5288])).

cnf(c_95667,plain,
    ( v1_relat_1(sK308) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2038])).

cnf(c_1893,plain,
    ( ~ v1_relat_2(X0)
    | v2_wellord1(X0)
    | ~ v1_wellord1(X0)
    | ~ v8_relat_2(X0)
    | ~ v6_relat_2(X0)
    | ~ v4_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5152])).

cnf(c_95804,plain,
    ( v1_relat_2(X0) != iProver_top
    | v2_wellord1(X0) = iProver_top
    | v1_wellord1(X0) != iProver_top
    | v8_relat_2(X0) != iProver_top
    | v6_relat_2(X0) != iProver_top
    | v4_relat_2(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1893])).

cnf(c_124581,plain,
    ( v1_relat_2(sK308) != iProver_top
    | v2_wellord1(sK308) = iProver_top
    | v1_wellord1(sK308) != iProver_top
    | v8_relat_2(sK308) != iProver_top
    | v6_relat_2(sK308) != iProver_top
    | v4_relat_2(sK308) != iProver_top ),
    inference(superposition,[status(thm)],[c_95667,c_95804])).

cnf(c_2039,negated_conjecture,
    ( v1_relat_1(sK307) ),
    inference(cnf_transformation,[],[f5287])).

cnf(c_95666,plain,
    ( v1_relat_1(sK307) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2039])).

cnf(c_1898,plain,
    ( v1_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5147])).

cnf(c_95799,plain,
    ( v1_relat_2(X0) = iProver_top
    | v2_wellord1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1898])).

cnf(c_121999,plain,
    ( v1_relat_2(sK307) = iProver_top
    | v2_wellord1(sK307) != iProver_top ),
    inference(superposition,[status(thm)],[c_95666,c_95799])).

cnf(c_2034,negated_conjecture,
    ( r3_wellord1(sK307,sK308,sK309) ),
    inference(cnf_transformation,[],[f5292])).

cnf(c_95671,plain,
    ( r3_wellord1(sK307,sK308,sK309) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2034])).

cnf(c_2028,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ v1_wellord1(X0)
    | v1_wellord1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f5286])).

cnf(c_95677,plain,
    ( r3_wellord1(X0,X1,X2) != iProver_top
    | v1_wellord1(X0) != iProver_top
    | v1_wellord1(X1) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2028])).

cnf(c_103103,plain,
    ( v1_wellord1(sK307) != iProver_top
    | v1_wellord1(sK308) = iProver_top
    | v1_funct_1(sK309) != iProver_top
    | v1_relat_1(sK309) != iProver_top
    | v1_relat_1(sK307) != iProver_top
    | v1_relat_1(sK308) != iProver_top ),
    inference(superposition,[status(thm)],[c_95671,c_95677])).

cnf(c_2029,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ v4_relat_2(X0)
    | v4_relat_2(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f5285])).

cnf(c_95676,plain,
    ( r3_wellord1(X0,X1,X2) != iProver_top
    | v4_relat_2(X0) != iProver_top
    | v4_relat_2(X1) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2029])).

cnf(c_102739,plain,
    ( v4_relat_2(sK307) != iProver_top
    | v4_relat_2(sK308) = iProver_top
    | v1_funct_1(sK309) != iProver_top
    | v1_relat_1(sK309) != iProver_top
    | v1_relat_1(sK307) != iProver_top
    | v1_relat_1(sK308) != iProver_top ),
    inference(superposition,[status(thm)],[c_95671,c_95676])).

cnf(c_2030,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ v6_relat_2(X0)
    | v6_relat_2(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f5284])).

cnf(c_95675,plain,
    ( r3_wellord1(X0,X1,X2) != iProver_top
    | v6_relat_2(X0) != iProver_top
    | v6_relat_2(X1) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2030])).

cnf(c_102210,plain,
    ( v6_relat_2(sK307) != iProver_top
    | v6_relat_2(sK308) = iProver_top
    | v1_funct_1(sK309) != iProver_top
    | v1_relat_1(sK309) != iProver_top
    | v1_relat_1(sK307) != iProver_top
    | v1_relat_1(sK308) != iProver_top ),
    inference(superposition,[status(thm)],[c_95671,c_95675])).

cnf(c_2031,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ v8_relat_2(X0)
    | v8_relat_2(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f5283])).

cnf(c_95674,plain,
    ( r3_wellord1(X0,X1,X2) != iProver_top
    | v8_relat_2(X0) != iProver_top
    | v8_relat_2(X1) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2031])).

cnf(c_102039,plain,
    ( v8_relat_2(sK307) != iProver_top
    | v8_relat_2(sK308) = iProver_top
    | v1_funct_1(sK309) != iProver_top
    | v1_relat_1(sK309) != iProver_top
    | v1_relat_1(sK307) != iProver_top
    | v1_relat_1(sK308) != iProver_top ),
    inference(superposition,[status(thm)],[c_95671,c_95674])).

cnf(c_1895,plain,
    ( ~ v2_wellord1(X0)
    | v6_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5150])).

cnf(c_2035,negated_conjecture,
    ( v2_wellord1(sK307) ),
    inference(cnf_transformation,[],[f5291])).

cnf(c_101947,plain,
    ( v6_relat_2(sK307)
    | ~ v1_relat_1(sK307) ),
    inference(resolution,[status(thm)],[c_1895,c_2035])).

cnf(c_101948,plain,
    ( v6_relat_2(sK307) = iProver_top
    | v1_relat_1(sK307) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_101947])).

cnf(c_1894,plain,
    ( ~ v2_wellord1(X0)
    | v1_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5151])).

cnf(c_101854,plain,
    ( v1_wellord1(sK307)
    | ~ v1_relat_1(sK307) ),
    inference(resolution,[status(thm)],[c_1894,c_2035])).

cnf(c_101855,plain,
    ( v1_wellord1(sK307) = iProver_top
    | v1_relat_1(sK307) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_101854])).

cnf(c_2032,plain,
    ( ~ r3_wellord1(X0,X1,X2)
    | ~ v1_relat_2(X0)
    | v1_relat_2(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f5282])).

cnf(c_95673,plain,
    ( r3_wellord1(X0,X1,X2) != iProver_top
    | v1_relat_2(X0) != iProver_top
    | v1_relat_2(X1) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2032])).

cnf(c_101807,plain,
    ( v1_relat_2(sK307) != iProver_top
    | v1_relat_2(sK308) = iProver_top
    | v1_funct_1(sK309) != iProver_top
    | v1_relat_1(sK309) != iProver_top
    | v1_relat_1(sK307) != iProver_top
    | v1_relat_1(sK308) != iProver_top ),
    inference(superposition,[status(thm)],[c_95671,c_95673])).

cnf(c_1897,plain,
    ( ~ v2_wellord1(X0)
    | v8_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5148])).

cnf(c_100656,plain,
    ( ~ v2_wellord1(sK307)
    | v8_relat_2(sK307)
    | ~ v1_relat_1(sK307) ),
    inference(instantiation,[status(thm)],[c_1897])).

cnf(c_100657,plain,
    ( v2_wellord1(sK307) != iProver_top
    | v8_relat_2(sK307) = iProver_top
    | v1_relat_1(sK307) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_100656])).

cnf(c_1896,plain,
    ( ~ v2_wellord1(X0)
    | v4_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5149])).

cnf(c_100653,plain,
    ( ~ v2_wellord1(sK307)
    | v4_relat_2(sK307)
    | ~ v1_relat_1(sK307) ),
    inference(instantiation,[status(thm)],[c_1896])).

cnf(c_100654,plain,
    ( v2_wellord1(sK307) != iProver_top
    | v4_relat_2(sK307) = iProver_top
    | v1_relat_1(sK307) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_100653])).

cnf(c_2033,negated_conjecture,
    ( ~ v2_wellord1(sK308) ),
    inference(cnf_transformation,[],[f5293])).

cnf(c_2052,plain,
    ( v2_wellord1(sK308) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2033])).

cnf(c_2050,plain,
    ( v2_wellord1(sK307) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2035])).

cnf(c_2036,negated_conjecture,
    ( v1_funct_1(sK309) ),
    inference(cnf_transformation,[],[f5290])).

cnf(c_2049,plain,
    ( v1_funct_1(sK309) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2036])).

cnf(c_2037,negated_conjecture,
    ( v1_relat_1(sK309) ),
    inference(cnf_transformation,[],[f5289])).

cnf(c_2048,plain,
    ( v1_relat_1(sK309) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2037])).

cnf(c_2047,plain,
    ( v1_relat_1(sK308) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2038])).

cnf(c_2046,plain,
    ( v1_relat_1(sK307) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2039])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_124581,c_121999,c_103103,c_102739,c_102210,c_102039,c_101948,c_101855,c_101807,c_100657,c_100654,c_2052,c_2050,c_2049,c_2048,c_2047,c_2046])).

%------------------------------------------------------------------------------
