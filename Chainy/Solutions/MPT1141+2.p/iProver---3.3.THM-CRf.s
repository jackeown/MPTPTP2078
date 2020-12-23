%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1141+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:01 EST 2020

% Result     : Theorem 47.18s
% Output     : CNFRefutation 47.18s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 241 expanded)
%              Number of clauses        :   26 (  57 expanded)
%              Number of leaves         :    7 (  77 expanded)
%              Depth                    :   11
%              Number of atoms          :  217 (1303 expanded)
%              Number of equality atoms :   54 ( 100 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1879,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( r2_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1880,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( r2_orders_2(X0,X2,X1)
                    & r1_orders_2(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1879])).

fof(f4051,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_orders_2(X0,X2,X1)
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1880])).

fof(f4052,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_orders_2(X0,X2,X1)
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f4051])).

fof(f5716,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_orders_2(X0,X2,X1)
          & r1_orders_2(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r2_orders_2(X0,sK691,X1)
        & r1_orders_2(X0,X1,sK691)
        & m1_subset_1(sK691,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f5715,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_orders_2(X0,X2,X1)
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( r2_orders_2(X0,X2,sK690)
            & r1_orders_2(X0,sK690,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK690,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f5714,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( r2_orders_2(X0,X2,X1)
                & r1_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( r2_orders_2(sK689,X2,X1)
              & r1_orders_2(sK689,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK689)) )
          & m1_subset_1(X1,u1_struct_0(sK689)) )
      & l1_orders_2(sK689)
      & v5_orders_2(sK689) ) ),
    introduced(choice_axiom,[])).

fof(f5717,plain,
    ( r2_orders_2(sK689,sK691,sK690)
    & r1_orders_2(sK689,sK690,sK691)
    & m1_subset_1(sK691,u1_struct_0(sK689))
    & m1_subset_1(sK690,u1_struct_0(sK689))
    & l1_orders_2(sK689)
    & v5_orders_2(sK689) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK689,sK690,sK691])],[f4052,f5716,f5715,f5714])).

fof(f9398,plain,(
    r1_orders_2(sK689,sK690,sK691) ),
    inference(cnf_transformation,[],[f5717])).

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

fof(f4043,plain,(
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

fof(f4044,plain,(
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
    inference(flattening,[],[f4043])).

fof(f9390,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4044])).

fof(f9394,plain,(
    v5_orders_2(sK689) ),
    inference(cnf_transformation,[],[f5717])).

fof(f9395,plain,(
    l1_orders_2(sK689) ),
    inference(cnf_transformation,[],[f5717])).

fof(f9396,plain,(
    m1_subset_1(sK690,u1_struct_0(sK689)) ),
    inference(cnf_transformation,[],[f5717])).

fof(f9397,plain,(
    m1_subset_1(sK691,u1_struct_0(sK689)) ),
    inference(cnf_transformation,[],[f5717])).

fof(f9399,plain,(
    r2_orders_2(sK689,sK691,sK690) ),
    inference(cnf_transformation,[],[f5717])).

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

fof(f4024,plain,(
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

fof(f5706,plain,(
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
    inference(nnf_transformation,[],[f4024])).

fof(f5707,plain,(
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
    inference(flattening,[],[f5706])).

fof(f9370,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f5707])).

fof(f1877,axiom,(
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

fof(f4047,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r2_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1877])).

fof(f4048,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r2_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f4047])).

fof(f9392,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X2,X1)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4048])).

cnf(c_3650,negated_conjecture,
    ( r1_orders_2(sK689,sK690,sK691) ),
    inference(cnf_transformation,[],[f9398])).

cnf(c_106856,plain,
    ( r1_orders_2(sK689,sK690,sK691) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3650])).

cnf(c_3645,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | X2 = X1 ),
    inference(cnf_transformation,[],[f9390])).

cnf(c_106861,plain,
    ( X0 = X1
    | r1_orders_2(X2,X1,X0) != iProver_top
    | r1_orders_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X2)) != iProver_top
    | v5_orders_2(X2) != iProver_top
    | l1_orders_2(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3645])).

cnf(c_142340,plain,
    ( sK690 = sK691
    | r1_orders_2(sK689,sK691,sK690) != iProver_top
    | m1_subset_1(sK690,u1_struct_0(sK689)) != iProver_top
    | m1_subset_1(sK691,u1_struct_0(sK689)) != iProver_top
    | v5_orders_2(sK689) != iProver_top
    | l1_orders_2(sK689) != iProver_top ),
    inference(superposition,[status(thm)],[c_106856,c_106861])).

cnf(c_3654,negated_conjecture,
    ( v5_orders_2(sK689) ),
    inference(cnf_transformation,[],[f9394])).

cnf(c_3655,plain,
    ( v5_orders_2(sK689) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3654])).

cnf(c_3653,negated_conjecture,
    ( l1_orders_2(sK689) ),
    inference(cnf_transformation,[],[f9395])).

cnf(c_3656,plain,
    ( l1_orders_2(sK689) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3653])).

cnf(c_3652,negated_conjecture,
    ( m1_subset_1(sK690,u1_struct_0(sK689)) ),
    inference(cnf_transformation,[],[f9396])).

cnf(c_3657,plain,
    ( m1_subset_1(sK690,u1_struct_0(sK689)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3652])).

cnf(c_3651,negated_conjecture,
    ( m1_subset_1(sK691,u1_struct_0(sK689)) ),
    inference(cnf_transformation,[],[f9397])).

cnf(c_3658,plain,
    ( m1_subset_1(sK691,u1_struct_0(sK689)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3651])).

cnf(c_3649,negated_conjecture,
    ( r2_orders_2(sK689,sK691,sK690) ),
    inference(cnf_transformation,[],[f9399])).

cnf(c_106857,plain,
    ( r2_orders_2(sK689,sK691,sK690) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3649])).

cnf(c_3627,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f9370])).

cnf(c_106878,plain,
    ( r1_orders_2(X0,X1,X2) = iProver_top
    | r2_orders_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3627])).

cnf(c_149271,plain,
    ( r1_orders_2(sK689,sK691,sK690) = iProver_top
    | m1_subset_1(sK690,u1_struct_0(sK689)) != iProver_top
    | m1_subset_1(sK691,u1_struct_0(sK689)) != iProver_top
    | l1_orders_2(sK689) != iProver_top ),
    inference(superposition,[status(thm)],[c_106857,c_106878])).

cnf(c_152998,plain,
    ( sK690 = sK691 ),
    inference(global_propositional_subsumption,[status(thm)],[c_142340,c_3655,c_3656,c_3657,c_3658,c_149271])).

cnf(c_3647,plain,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f9392])).

cnf(c_106859,plain,
    ( r2_orders_2(X0,X1,X2) != iProver_top
    | r2_orders_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3647])).

cnf(c_141806,plain,
    ( r2_orders_2(sK689,sK690,sK691) != iProver_top
    | m1_subset_1(sK690,u1_struct_0(sK689)) != iProver_top
    | m1_subset_1(sK691,u1_struct_0(sK689)) != iProver_top
    | v5_orders_2(sK689) != iProver_top
    | l1_orders_2(sK689) != iProver_top ),
    inference(superposition,[status(thm)],[c_106857,c_106859])).

cnf(c_151980,plain,
    ( r2_orders_2(sK689,sK690,sK691) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_141806,c_3655,c_3656,c_3657,c_3658])).

cnf(c_153002,plain,
    ( r2_orders_2(sK689,sK691,sK691) != iProver_top ),
    inference(demodulation,[status(thm)],[c_152998,c_151980])).

cnf(c_153004,plain,
    ( r2_orders_2(sK689,sK691,sK691) = iProver_top ),
    inference(demodulation,[status(thm)],[c_152998,c_106857])).

cnf(c_153012,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_153002,c_153004])).

%------------------------------------------------------------------------------
