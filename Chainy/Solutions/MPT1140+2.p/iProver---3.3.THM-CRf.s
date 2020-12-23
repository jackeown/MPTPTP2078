%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1140+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:01 EST 2020

% Result     : Theorem 49.91s
% Output     : CNFRefutation 49.91s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 426 expanded)
%              Number of clauses        :   45 (  94 expanded)
%              Number of leaves         :    8 ( 157 expanded)
%              Depth                    :   17
%              Number of atoms          :  316 (3263 expanded)
%              Number of equality atoms :   90 ( 166 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1878,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r2_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) )
                   => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1879,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_orders_2(X0,X2,X3)
                        & r2_orders_2(X0,X1,X2) )
                     => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1878])).

fof(f4048,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & r2_orders_2(X0,X2,X3)
                  & r2_orders_2(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1879])).

fof(f4049,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & r2_orders_2(X0,X2,X3)
                  & r2_orders_2(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f4048])).

fof(f5714,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_orders_2(X0,X1,X3)
          & r2_orders_2(X0,X2,X3)
          & r2_orders_2(X0,X1,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,X1,sK692)
        & r2_orders_2(X0,X2,sK692)
        & r2_orders_2(X0,X1,X2)
        & m1_subset_1(sK692,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f5713,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_orders_2(X0,X1,X3)
              & r2_orders_2(X0,X2,X3)
              & r2_orders_2(X0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_orders_2(X0,X1,X3)
            & r2_orders_2(X0,sK691,X3)
            & r2_orders_2(X0,X1,sK691)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK691,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f5712,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & r2_orders_2(X0,X2,X3)
                  & r2_orders_2(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_orders_2(X0,sK690,X3)
                & r2_orders_2(X0,X2,X3)
                & r2_orders_2(X0,sK690,X2)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK690,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f5711,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_orders_2(X0,X1,X3)
                    & r2_orders_2(X0,X2,X3)
                    & r2_orders_2(X0,X1,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(sK689,X1,X3)
                  & r2_orders_2(sK689,X2,X3)
                  & r2_orders_2(sK689,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(sK689)) )
              & m1_subset_1(X2,u1_struct_0(sK689)) )
          & m1_subset_1(X1,u1_struct_0(sK689)) )
      & l1_orders_2(sK689)
      & v5_orders_2(sK689)
      & v4_orders_2(sK689) ) ),
    introduced(choice_axiom,[])).

fof(f5715,plain,
    ( ~ r2_orders_2(sK689,sK690,sK692)
    & r2_orders_2(sK689,sK691,sK692)
    & r2_orders_2(sK689,sK690,sK691)
    & m1_subset_1(sK692,u1_struct_0(sK689))
    & m1_subset_1(sK691,u1_struct_0(sK689))
    & m1_subset_1(sK690,u1_struct_0(sK689))
    & l1_orders_2(sK689)
    & v5_orders_2(sK689)
    & v4_orders_2(sK689) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK689,sK690,sK691,sK692])],[f4049,f5714,f5713,f5712,f5711])).

fof(f9398,plain,(
    r2_orders_2(sK689,sK691,sK692) ),
    inference(cnf_transformation,[],[f5715])).

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

fof(f4023,plain,(
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

fof(f5703,plain,(
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
    inference(nnf_transformation,[],[f4023])).

fof(f5704,plain,(
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
    inference(flattening,[],[f5703])).

fof(f9368,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f5704])).

fof(f9393,plain,(
    l1_orders_2(sK689) ),
    inference(cnf_transformation,[],[f5715])).

fof(f9395,plain,(
    m1_subset_1(sK691,u1_struct_0(sK689)) ),
    inference(cnf_transformation,[],[f5715])).

fof(f9396,plain,(
    m1_subset_1(sK692,u1_struct_0(sK689)) ),
    inference(cnf_transformation,[],[f5715])).

fof(f9394,plain,(
    m1_subset_1(sK690,u1_struct_0(sK689)) ),
    inference(cnf_transformation,[],[f5715])).

fof(f1876,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4044,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1876])).

fof(f4045,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f4044])).

fof(f9389,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4045])).

fof(f9391,plain,(
    v4_orders_2(sK689) ),
    inference(cnf_transformation,[],[f5715])).

fof(f9397,plain,(
    r2_orders_2(sK689,sK690,sK691) ),
    inference(cnf_transformation,[],[f5715])).

fof(f9370,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(X0,X1,X2)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f5704])).

fof(f9399,plain,(
    ~ r2_orders_2(sK689,sK690,sK692) ),
    inference(cnf_transformation,[],[f5715])).

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

fof(f4046,plain,(
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
    inference(flattening,[],[f4046])).

fof(f9390,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X2,X1)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4047])).

fof(f9392,plain,(
    v5_orders_2(sK689) ),
    inference(cnf_transformation,[],[f5715])).

cnf(c_3649,negated_conjecture,
    ( r2_orders_2(sK689,sK691,sK692) ),
    inference(cnf_transformation,[],[f9398])).

cnf(c_106911,plain,
    ( r2_orders_2(sK689,sK691,sK692) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3649])).

cnf(c_3627,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f9368])).

cnf(c_106932,plain,
    ( r1_orders_2(X0,X1,X2) = iProver_top
    | r2_orders_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3627])).

cnf(c_157995,plain,
    ( r1_orders_2(sK689,sK691,sK692) = iProver_top
    | m1_subset_1(sK691,u1_struct_0(sK689)) != iProver_top
    | m1_subset_1(sK692,u1_struct_0(sK689)) != iProver_top
    | l1_orders_2(sK689) != iProver_top ),
    inference(superposition,[status(thm)],[c_106911,c_106932])).

cnf(c_3654,negated_conjecture,
    ( l1_orders_2(sK689) ),
    inference(cnf_transformation,[],[f9393])).

cnf(c_3659,plain,
    ( l1_orders_2(sK689) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3654])).

cnf(c_3652,negated_conjecture,
    ( m1_subset_1(sK691,u1_struct_0(sK689)) ),
    inference(cnf_transformation,[],[f9395])).

cnf(c_3661,plain,
    ( m1_subset_1(sK691,u1_struct_0(sK689)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3652])).

cnf(c_3651,negated_conjecture,
    ( m1_subset_1(sK692,u1_struct_0(sK689)) ),
    inference(cnf_transformation,[],[f9396])).

cnf(c_3662,plain,
    ( m1_subset_1(sK692,u1_struct_0(sK689)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3651])).

cnf(c_158732,plain,
    ( r1_orders_2(sK689,sK691,sK692) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_157995,c_3659,c_3661,c_3662])).

cnf(c_106909,plain,
    ( m1_subset_1(sK692,u1_struct_0(sK689)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3651])).

cnf(c_3653,negated_conjecture,
    ( m1_subset_1(sK690,u1_struct_0(sK689)) ),
    inference(cnf_transformation,[],[f9394])).

cnf(c_106907,plain,
    ( m1_subset_1(sK690,u1_struct_0(sK689)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3653])).

cnf(c_106908,plain,
    ( m1_subset_1(sK691,u1_struct_0(sK689)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3652])).

cnf(c_3646,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f9389])).

cnf(c_106914,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | r1_orders_2(X0,X2,X3) != iProver_top
    | r1_orders_2(X0,X1,X3) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3646])).

cnf(c_141718,plain,
    ( r1_orders_2(sK689,X0,X1) = iProver_top
    | r1_orders_2(sK689,X0,sK691) != iProver_top
    | r1_orders_2(sK689,sK691,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK689)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK689)) != iProver_top
    | v4_orders_2(sK689) != iProver_top
    | l1_orders_2(sK689) != iProver_top ),
    inference(superposition,[status(thm)],[c_106908,c_106914])).

cnf(c_3656,negated_conjecture,
    ( v4_orders_2(sK689) ),
    inference(cnf_transformation,[],[f9391])).

cnf(c_3657,plain,
    ( v4_orders_2(sK689) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3656])).

cnf(c_142647,plain,
    ( r1_orders_2(sK689,X0,X1) = iProver_top
    | r1_orders_2(sK689,X0,sK691) != iProver_top
    | r1_orders_2(sK689,sK691,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK689)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK689)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_141718,c_3657,c_3659])).

cnf(c_142660,plain,
    ( r1_orders_2(sK689,sK691,X0) != iProver_top
    | r1_orders_2(sK689,sK690,X0) = iProver_top
    | r1_orders_2(sK689,sK690,sK691) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK689)) != iProver_top ),
    inference(superposition,[status(thm)],[c_106907,c_142647])).

cnf(c_143009,plain,
    ( r1_orders_2(sK689,sK691,sK692) != iProver_top
    | r1_orders_2(sK689,sK690,sK691) != iProver_top
    | r1_orders_2(sK689,sK690,sK692) = iProver_top ),
    inference(superposition,[status(thm)],[c_106909,c_142660])).

cnf(c_158738,plain,
    ( r1_orders_2(sK689,sK690,sK691) != iProver_top
    | r1_orders_2(sK689,sK690,sK692) = iProver_top ),
    inference(superposition,[status(thm)],[c_158732,c_143009])).

cnf(c_3660,plain,
    ( m1_subset_1(sK690,u1_struct_0(sK689)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3653])).

cnf(c_3650,negated_conjecture,
    ( r2_orders_2(sK689,sK690,sK691) ),
    inference(cnf_transformation,[],[f9397])).

cnf(c_106910,plain,
    ( r2_orders_2(sK689,sK690,sK691) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3650])).

cnf(c_157996,plain,
    ( r1_orders_2(sK689,sK690,sK691) = iProver_top
    | m1_subset_1(sK691,u1_struct_0(sK689)) != iProver_top
    | m1_subset_1(sK690,u1_struct_0(sK689)) != iProver_top
    | l1_orders_2(sK689) != iProver_top ),
    inference(superposition,[status(thm)],[c_106910,c_106932])).

cnf(c_158908,plain,
    ( r1_orders_2(sK689,sK690,sK692) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_158738,c_3659,c_3660,c_3661,c_3662,c_143009,c_157995,c_157996])).

cnf(c_3625,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X2 = X1 ),
    inference(cnf_transformation,[],[f9370])).

cnf(c_106934,plain,
    ( X0 = X1
    | r1_orders_2(X2,X1,X0) != iProver_top
    | r2_orders_2(X2,X1,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X2)) != iProver_top
    | l1_orders_2(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3625])).

cnf(c_160912,plain,
    ( sK692 = sK690
    | r2_orders_2(sK689,sK690,sK692) = iProver_top
    | m1_subset_1(sK692,u1_struct_0(sK689)) != iProver_top
    | m1_subset_1(sK690,u1_struct_0(sK689)) != iProver_top
    | l1_orders_2(sK689) != iProver_top ),
    inference(superposition,[status(thm)],[c_158908,c_106934])).

cnf(c_3648,negated_conjecture,
    ( ~ r2_orders_2(sK689,sK690,sK692) ),
    inference(cnf_transformation,[],[f9399])).

cnf(c_3665,plain,
    ( r2_orders_2(sK689,sK690,sK692) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3648])).

cnf(c_163225,plain,
    ( sK692 = sK690 ),
    inference(global_propositional_subsumption,[status(thm)],[c_160912,c_3659,c_3660,c_3662,c_3665])).

cnf(c_3647,plain,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f9390])).

cnf(c_106913,plain,
    ( r2_orders_2(X0,X1,X2) != iProver_top
    | r2_orders_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3647])).

cnf(c_140595,plain,
    ( r2_orders_2(sK689,sK692,sK691) != iProver_top
    | m1_subset_1(sK691,u1_struct_0(sK689)) != iProver_top
    | m1_subset_1(sK692,u1_struct_0(sK689)) != iProver_top
    | v5_orders_2(sK689) != iProver_top
    | l1_orders_2(sK689) != iProver_top ),
    inference(superposition,[status(thm)],[c_106911,c_106913])).

cnf(c_3655,negated_conjecture,
    ( v5_orders_2(sK689) ),
    inference(cnf_transformation,[],[f9392])).

cnf(c_3658,plain,
    ( v5_orders_2(sK689) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3655])).

cnf(c_141429,plain,
    ( r2_orders_2(sK689,sK692,sK691) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_140595,c_3658,c_3659,c_3661,c_3662])).

cnf(c_163251,plain,
    ( r2_orders_2(sK689,sK690,sK691) != iProver_top ),
    inference(demodulation,[status(thm)],[c_163225,c_141429])).

cnf(c_3663,plain,
    ( r2_orders_2(sK689,sK690,sK691) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3650])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_163251,c_3663])).

%------------------------------------------------------------------------------
