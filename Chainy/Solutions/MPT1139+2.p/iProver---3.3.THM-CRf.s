%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1139+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:01 EST 2020

% Result     : Theorem 51.46s
% Output     : CNFRefutation 51.46s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 207 expanded)
%              Number of clauses        :   35 (  52 expanded)
%              Number of leaves         :    6 (  64 expanded)
%              Depth                    :   16
%              Number of atoms          :  215 (1098 expanded)
%              Number of equality atoms :   71 (  94 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1877,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( r2_orders_2(X0,X2,X1)
                  & r2_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1878,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( r2_orders_2(X0,X2,X1)
                    & r2_orders_2(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1877])).

fof(f4045,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_orders_2(X0,X2,X1)
              & r2_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1878])).

fof(f4046,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_orders_2(X0,X2,X1)
              & r2_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f4045])).

fof(f5710,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_orders_2(X0,X2,X1)
          & r2_orders_2(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r2_orders_2(X0,sK691,X1)
        & r2_orders_2(X0,X1,sK691)
        & m1_subset_1(sK691,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f5709,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_orders_2(X0,X2,X1)
              & r2_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( r2_orders_2(X0,X2,sK690)
            & r2_orders_2(X0,sK690,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK690,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f5708,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( r2_orders_2(X0,X2,X1)
                & r2_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( r2_orders_2(sK689,X2,X1)
              & r2_orders_2(sK689,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK689)) )
          & m1_subset_1(X1,u1_struct_0(sK689)) )
      & l1_orders_2(sK689)
      & v5_orders_2(sK689) ) ),
    introduced(choice_axiom,[])).

fof(f5711,plain,
    ( r2_orders_2(sK689,sK691,sK690)
    & r2_orders_2(sK689,sK690,sK691)
    & m1_subset_1(sK691,u1_struct_0(sK689))
    & m1_subset_1(sK690,u1_struct_0(sK689))
    & l1_orders_2(sK689)
    & v5_orders_2(sK689) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK689,sK690,sK691])],[f4046,f5710,f5709,f5708])).

fof(f9389,plain,(
    m1_subset_1(sK691,u1_struct_0(sK689)) ),
    inference(cnf_transformation,[],[f5711])).

fof(f1861,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4022,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1861])).

fof(f5700,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f4022])).

fof(f5701,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f5700])).

fof(f9365,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f5701])).

fof(f11654,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f9365])).

fof(f9388,plain,(
    m1_subset_1(sK690,u1_struct_0(sK689)) ),
    inference(cnf_transformation,[],[f5711])).

fof(f9364,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f5701])).

fof(f9387,plain,(
    l1_orders_2(sK689) ),
    inference(cnf_transformation,[],[f5711])).

fof(f9390,plain,(
    r2_orders_2(sK689,sK690,sK691) ),
    inference(cnf_transformation,[],[f5711])).

fof(f1875,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4041,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1875])).

fof(f4042,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f4041])).

fof(f9384,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4042])).

fof(f9386,plain,(
    v5_orders_2(sK689) ),
    inference(cnf_transformation,[],[f5711])).

fof(f9391,plain,(
    r2_orders_2(sK689,sK691,sK690) ),
    inference(cnf_transformation,[],[f5711])).

cnf(c_3649,negated_conjecture,
    ( m1_subset_1(sK691,u1_struct_0(sK689)) ),
    inference(cnf_transformation,[],[f9389])).

cnf(c_106775,plain,
    ( m1_subset_1(sK691,u1_struct_0(sK689)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3649])).

cnf(c_3626,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f11654])).

cnf(c_106797,plain,
    ( r2_orders_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3626])).

cnf(c_158374,plain,
    ( r2_orders_2(sK689,sK691,sK691) != iProver_top
    | l1_orders_2(sK689) != iProver_top ),
    inference(superposition,[status(thm)],[c_106775,c_106797])).

cnf(c_3650,negated_conjecture,
    ( m1_subset_1(sK690,u1_struct_0(sK689)) ),
    inference(cnf_transformation,[],[f9388])).

cnf(c_106774,plain,
    ( m1_subset_1(sK690,u1_struct_0(sK689)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3650])).

cnf(c_3627,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f9364])).

cnf(c_106796,plain,
    ( r1_orders_2(X0,X1,X2) = iProver_top
    | r2_orders_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3627])).

cnf(c_156118,plain,
    ( r1_orders_2(sK689,X0,sK691) = iProver_top
    | r2_orders_2(sK689,X0,sK691) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK689)) != iProver_top
    | l1_orders_2(sK689) != iProver_top ),
    inference(superposition,[status(thm)],[c_106775,c_106796])).

cnf(c_3651,negated_conjecture,
    ( l1_orders_2(sK689) ),
    inference(cnf_transformation,[],[f9387])).

cnf(c_3654,plain,
    ( l1_orders_2(sK689) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3651])).

cnf(c_156896,plain,
    ( m1_subset_1(X0,u1_struct_0(sK689)) != iProver_top
    | r2_orders_2(sK689,X0,sK691) != iProver_top
    | r1_orders_2(sK689,X0,sK691) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_156118,c_3654])).

cnf(c_156897,plain,
    ( r1_orders_2(sK689,X0,sK691) = iProver_top
    | r2_orders_2(sK689,X0,sK691) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK689)) != iProver_top ),
    inference(renaming,[status(thm)],[c_156896])).

cnf(c_156906,plain,
    ( r1_orders_2(sK689,sK690,sK691) = iProver_top
    | r2_orders_2(sK689,sK690,sK691) != iProver_top ),
    inference(superposition,[status(thm)],[c_106774,c_156897])).

cnf(c_3648,negated_conjecture,
    ( r2_orders_2(sK689,sK690,sK691) ),
    inference(cnf_transformation,[],[f9390])).

cnf(c_3657,plain,
    ( r2_orders_2(sK689,sK690,sK691) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3648])).

cnf(c_157944,plain,
    ( r1_orders_2(sK689,sK690,sK691) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_156906,c_3657])).

cnf(c_3645,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | X2 = X1 ),
    inference(cnf_transformation,[],[f9384])).

cnf(c_106779,plain,
    ( X0 = X1
    | r1_orders_2(X2,X1,X0) != iProver_top
    | r1_orders_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X2)) != iProver_top
    | v5_orders_2(X2) != iProver_top
    | l1_orders_2(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3645])).

cnf(c_157950,plain,
    ( sK690 = sK691
    | r1_orders_2(sK689,sK691,sK690) != iProver_top
    | m1_subset_1(sK690,u1_struct_0(sK689)) != iProver_top
    | m1_subset_1(sK691,u1_struct_0(sK689)) != iProver_top
    | v5_orders_2(sK689) != iProver_top
    | l1_orders_2(sK689) != iProver_top ),
    inference(superposition,[status(thm)],[c_157944,c_106779])).

cnf(c_3652,negated_conjecture,
    ( v5_orders_2(sK689) ),
    inference(cnf_transformation,[],[f9386])).

cnf(c_3653,plain,
    ( v5_orders_2(sK689) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3652])).

cnf(c_3655,plain,
    ( m1_subset_1(sK690,u1_struct_0(sK689)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3650])).

cnf(c_3656,plain,
    ( m1_subset_1(sK691,u1_struct_0(sK689)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3649])).

cnf(c_3647,negated_conjecture,
    ( r2_orders_2(sK689,sK691,sK690) ),
    inference(cnf_transformation,[],[f9391])).

cnf(c_3658,plain,
    ( r2_orders_2(sK689,sK691,sK690) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3647])).

cnf(c_156119,plain,
    ( r1_orders_2(sK689,X0,sK690) = iProver_top
    | r2_orders_2(sK689,X0,sK690) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK689)) != iProver_top
    | l1_orders_2(sK689) != iProver_top ),
    inference(superposition,[status(thm)],[c_106774,c_106796])).

cnf(c_157982,plain,
    ( m1_subset_1(X0,u1_struct_0(sK689)) != iProver_top
    | r2_orders_2(sK689,X0,sK690) != iProver_top
    | r1_orders_2(sK689,X0,sK690) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_156119,c_3654])).

cnf(c_157983,plain,
    ( r1_orders_2(sK689,X0,sK690) = iProver_top
    | r2_orders_2(sK689,X0,sK690) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK689)) != iProver_top ),
    inference(renaming,[status(thm)],[c_157982])).

cnf(c_157991,plain,
    ( r1_orders_2(sK689,sK691,sK690) = iProver_top
    | r2_orders_2(sK689,sK691,sK690) != iProver_top ),
    inference(superposition,[status(thm)],[c_106775,c_157983])).

cnf(c_158333,plain,
    ( sK690 = sK691 ),
    inference(global_propositional_subsumption,[status(thm)],[c_157950,c_3653,c_3654,c_3655,c_3656,c_3658,c_157991])).

cnf(c_106777,plain,
    ( r2_orders_2(sK689,sK691,sK690) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3647])).

cnf(c_158341,plain,
    ( r2_orders_2(sK689,sK691,sK691) = iProver_top ),
    inference(demodulation,[status(thm)],[c_158333,c_106777])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_158374,c_158341,c_3654])).

%------------------------------------------------------------------------------
