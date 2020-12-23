%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2032+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:39 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 463 expanded)
%              Number of leaves         :   10 ( 200 expanded)
%              Depth                    :   20
%              Number of atoms          :  489 (4642 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6723,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6722,f4645])).

fof(f4645,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f4556])).

fof(f4556,plain,
    ( ~ r3_waybel_9(sK3,sK4,sK6)
    & r3_waybel_9(sK3,sK5,sK6)
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m2_yellow_6(sK5,sK3,sK4)
    & l1_waybel_0(sK4,sK3)
    & v7_waybel_0(sK4)
    & v4_orders_2(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f4455,f4555,f4554,f4553,f4552])).

fof(f4552,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r3_waybel_9(X0,X1,X3)
                    & r3_waybel_9(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_waybel_9(sK3,X1,X3)
                  & r3_waybel_9(sK3,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(sK3)) )
              & m2_yellow_6(X2,sK3,X1) )
          & l1_waybel_0(X1,sK3)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f4553,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r3_waybel_9(sK3,X1,X3)
                & r3_waybel_9(sK3,X2,X3)
                & m1_subset_1(X3,u1_struct_0(sK3)) )
            & m2_yellow_6(X2,sK3,X1) )
        & l1_waybel_0(X1,sK3)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r3_waybel_9(sK3,sK4,X3)
              & r3_waybel_9(sK3,X2,X3)
              & m1_subset_1(X3,u1_struct_0(sK3)) )
          & m2_yellow_6(X2,sK3,sK4) )
      & l1_waybel_0(sK4,sK3)
      & v7_waybel_0(sK4)
      & v4_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f4554,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r3_waybel_9(sK3,sK4,X3)
            & r3_waybel_9(sK3,X2,X3)
            & m1_subset_1(X3,u1_struct_0(sK3)) )
        & m2_yellow_6(X2,sK3,sK4) )
   => ( ? [X3] :
          ( ~ r3_waybel_9(sK3,sK4,X3)
          & r3_waybel_9(sK3,sK5,X3)
          & m1_subset_1(X3,u1_struct_0(sK3)) )
      & m2_yellow_6(sK5,sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f4555,plain,
    ( ? [X3] :
        ( ~ r3_waybel_9(sK3,sK4,X3)
        & r3_waybel_9(sK3,sK5,X3)
        & m1_subset_1(X3,u1_struct_0(sK3)) )
   => ( ~ r3_waybel_9(sK3,sK4,sK6)
      & r3_waybel_9(sK3,sK5,sK6)
      & m1_subset_1(sK6,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f4455,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_waybel_9(X0,X1,X3)
                  & r3_waybel_9(X0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m2_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4454])).

fof(f4454,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_waybel_9(X0,X1,X3)
                  & r3_waybel_9(X0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m2_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4430])).

fof(f4430,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m2_yellow_6(X2,X0,X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_waybel_9(X0,X2,X3)
                     => r3_waybel_9(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4429])).

fof(f4429,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r3_waybel_9(X0,X2,X3)
                   => r3_waybel_9(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_9)).

fof(f6722,plain,(
    ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f6700,f4779])).

fof(f4779,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4543])).

fof(f4543,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f6700,plain,(
    ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f6699,f5170])).

fof(f5170,plain,
    ( ~ v2_struct_0(sK5)
    | ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f5169,f4643])).

fof(f4643,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f4556])).

fof(f5169,plain,
    ( ~ v2_struct_0(sK5)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f5168,f4646])).

fof(f4646,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f4556])).

fof(f5168,plain,
    ( ~ v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f5167,f4647])).

fof(f4647,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f4556])).

fof(f5167,plain,
    ( ~ v2_struct_0(sK5)
    | ~ v4_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f5166,f4648])).

fof(f4648,plain,(
    v7_waybel_0(sK4) ),
    inference(cnf_transformation,[],[f4556])).

fof(f5166,plain,
    ( ~ v2_struct_0(sK5)
    | ~ v7_waybel_0(sK4)
    | ~ v4_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f5158,f4649])).

fof(f4649,plain,(
    l1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f4556])).

fof(f5158,plain,
    ( ~ v2_struct_0(sK5)
    | ~ l1_waybel_0(sK4,sK3)
    | ~ v7_waybel_0(sK4)
    | ~ v4_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f4650,f4662])).

fof(f4662,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4465])).

fof(f4465,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4464])).

fof(f4464,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3888])).

fof(f3888,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_yellow_6(X2,X0,X1)
         => ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).

fof(f4650,plain,(
    m2_yellow_6(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f4556])).

fof(f6699,plain,
    ( v2_struct_0(sK5)
    | ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f6698,f5185])).

fof(f5185,plain,
    ( l1_waybel_0(sK5,sK3)
    | ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f5184,f4643])).

fof(f5184,plain,
    ( l1_waybel_0(sK5,sK3)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f5183,f4646])).

fof(f5183,plain,
    ( l1_waybel_0(sK5,sK3)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f5182,f4647])).

fof(f5182,plain,
    ( l1_waybel_0(sK5,sK3)
    | ~ v4_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f5181,f4648])).

fof(f5181,plain,
    ( l1_waybel_0(sK5,sK3)
    | ~ v7_waybel_0(sK4)
    | ~ v4_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f5161,f4649])).

fof(f5161,plain,
    ( l1_waybel_0(sK5,sK3)
    | ~ l1_waybel_0(sK4,sK3)
    | ~ v7_waybel_0(sK4)
    | ~ v4_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f4650,f4665])).

fof(f4665,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4465])).

fof(f6698,plain,
    ( ~ l1_waybel_0(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f6686,f5278])).

fof(f5278,plain,(
    ~ r2_waybel_0(sK3,sK4,sK7(sK3,sK4,sK6)) ),
    inference(subsumption_resolution,[],[f5277,f4643])).

fof(f5277,plain,
    ( ~ r2_waybel_0(sK3,sK4,sK7(sK3,sK4,sK6))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f5276,f4644])).

fof(f4644,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f4556])).

fof(f5276,plain,
    ( ~ r2_waybel_0(sK3,sK4,sK7(sK3,sK4,sK6))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f5275,f4645])).

fof(f5275,plain,
    ( ~ r2_waybel_0(sK3,sK4,sK7(sK3,sK4,sK6))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f5274,f4646])).

fof(f5274,plain,
    ( ~ r2_waybel_0(sK3,sK4,sK7(sK3,sK4,sK6))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f5273,f4649])).

fof(f5273,plain,
    ( ~ r2_waybel_0(sK3,sK4,sK7(sK3,sK4,sK6))
    | ~ l1_waybel_0(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f5258,f4651])).

fof(f4651,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f4556])).

fof(f5258,plain,
    ( ~ r2_waybel_0(sK3,sK4,sK7(sK3,sK4,sK6))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_waybel_0(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f4653,f4656])).

fof(f4656,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | ~ r2_waybel_0(X0,X1,sK7(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4560])).

fof(f4560,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ( ~ r2_waybel_0(X0,X1,sK7(X0,X1,X2))
                    & m1_connsp_2(sK7(X0,X1,X2),X0,X2) ) )
                & ( ! [X4] :
                      ( r2_waybel_0(X0,X1,X4)
                      | ~ m1_connsp_2(X4,X0,X2) )
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f4558,f4559])).

fof(f4559,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_waybel_0(X0,X1,X3)
          & m1_connsp_2(X3,X0,X2) )
     => ( ~ r2_waybel_0(X0,X1,sK7(X0,X1,X2))
        & m1_connsp_2(sK7(X0,X1,X2),X0,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f4558,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ? [X3] :
                      ( ~ r2_waybel_0(X0,X1,X3)
                      & m1_connsp_2(X3,X0,X2) ) )
                & ( ! [X4] :
                      ( r2_waybel_0(X0,X1,X4)
                      | ~ m1_connsp_2(X4,X0,X2) )
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f4557])).

fof(f4557,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ? [X3] :
                      ( ~ r2_waybel_0(X0,X1,X3)
                      & m1_connsp_2(X3,X0,X2) ) )
                & ( ! [X3] :
                      ( r2_waybel_0(X0,X1,X3)
                      | ~ m1_connsp_2(X3,X0,X2) )
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f4457])).

fof(f4457,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> ! [X3] :
                    ( r2_waybel_0(X0,X1,X3)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4456])).

fof(f4456,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> ! [X3] :
                    ( r2_waybel_0(X0,X1,X3)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4332])).

fof(f4332,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,X1,X2)
              <=> ! [X3] :
                    ( m1_connsp_2(X3,X0,X2)
                   => r2_waybel_0(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_waybel_9)).

fof(f4653,plain,(
    ~ r3_waybel_9(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f4556])).

fof(f6686,plain,
    ( ~ l1_waybel_0(sK5,sK3)
    | v2_struct_0(sK5)
    | r2_waybel_0(sK3,sK4,sK7(sK3,sK4,sK6))
    | ~ l1_struct_0(sK3) ),
    inference(resolution,[],[f5954,f5202])).

fof(f5202,plain,(
    ! [X2] :
      ( ~ r2_waybel_0(sK3,sK5,X2)
      | r2_waybel_0(sK3,sK4,X2)
      | ~ l1_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f5201,f4643])).

fof(f5201,plain,(
    ! [X2] :
      ( r2_waybel_0(sK3,sK4,X2)
      | ~ r2_waybel_0(sK3,sK5,X2)
      | ~ l1_struct_0(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f5200,f4646])).

fof(f5200,plain,(
    ! [X2] :
      ( r2_waybel_0(sK3,sK4,X2)
      | ~ r2_waybel_0(sK3,sK5,X2)
      | v2_struct_0(sK4)
      | ~ l1_struct_0(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f5199,f4647])).

fof(f5199,plain,(
    ! [X2] :
      ( r2_waybel_0(sK3,sK4,X2)
      | ~ r2_waybel_0(sK3,sK5,X2)
      | ~ v4_orders_2(sK4)
      | v2_struct_0(sK4)
      | ~ l1_struct_0(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f5198,f4648])).

fof(f5198,plain,(
    ! [X2] :
      ( r2_waybel_0(sK3,sK4,X2)
      | ~ r2_waybel_0(sK3,sK5,X2)
      | ~ v7_waybel_0(sK4)
      | ~ v4_orders_2(sK4)
      | v2_struct_0(sK4)
      | ~ l1_struct_0(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f5164,f4649])).

fof(f5164,plain,(
    ! [X2] :
      ( r2_waybel_0(sK3,sK4,X2)
      | ~ r2_waybel_0(sK3,sK5,X2)
      | ~ l1_waybel_0(sK4,sK3)
      | ~ v7_waybel_0(sK4)
      | ~ v4_orders_2(sK4)
      | v2_struct_0(sK4)
      | ~ l1_struct_0(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f4650,f4682])).

fof(f4682,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_waybel_0(X0,X1,X3)
      | ~ r2_waybel_0(X0,X2,X3)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4481])).

fof(f4481,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X2,X3) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4480])).

fof(f4480,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X2,X3) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4067])).

fof(f4067,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( r2_waybel_0(X0,X2,X3)
                 => r2_waybel_0(X0,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_6)).

fof(f5954,plain,
    ( r2_waybel_0(sK3,sK5,sK7(sK3,sK4,sK6))
    | ~ l1_waybel_0(sK5,sK3)
    | v2_struct_0(sK5) ),
    inference(resolution,[],[f5255,f5272])).

fof(f5272,plain,(
    m1_connsp_2(sK7(sK3,sK4,sK6),sK3,sK6) ),
    inference(subsumption_resolution,[],[f5271,f4643])).

fof(f5271,plain,
    ( m1_connsp_2(sK7(sK3,sK4,sK6),sK3,sK6)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f5270,f4644])).

fof(f5270,plain,
    ( m1_connsp_2(sK7(sK3,sK4,sK6),sK3,sK6)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f5269,f4645])).

fof(f5269,plain,
    ( m1_connsp_2(sK7(sK3,sK4,sK6),sK3,sK6)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f5268,f4646])).

fof(f5268,plain,
    ( m1_connsp_2(sK7(sK3,sK4,sK6),sK3,sK6)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f5267,f4649])).

fof(f5267,plain,
    ( m1_connsp_2(sK7(sK3,sK4,sK6),sK3,sK6)
    | ~ l1_waybel_0(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f5257,f4651])).

fof(f5257,plain,
    ( m1_connsp_2(sK7(sK3,sK4,sK6),sK3,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_waybel_0(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f4653,f4655])).

fof(f4655,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | m1_connsp_2(sK7(X0,X1,X2),X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4560])).

fof(f5255,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK6)
      | r2_waybel_0(sK3,sK5,X0)
      | ~ l1_waybel_0(sK5,sK3)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f5254,f4643])).

fof(f5254,plain,(
    ! [X0] :
      ( r2_waybel_0(sK3,sK5,X0)
      | ~ m1_connsp_2(X0,sK3,sK6)
      | ~ l1_waybel_0(sK5,sK3)
      | v2_struct_0(sK5)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f5253,f4644])).

fof(f5253,plain,(
    ! [X0] :
      ( r2_waybel_0(sK3,sK5,X0)
      | ~ m1_connsp_2(X0,sK3,sK6)
      | ~ l1_waybel_0(sK5,sK3)
      | v2_struct_0(sK5)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f5252,f4645])).

fof(f5252,plain,(
    ! [X0] :
      ( r2_waybel_0(sK3,sK5,X0)
      | ~ m1_connsp_2(X0,sK3,sK6)
      | ~ l1_waybel_0(sK5,sK3)
      | v2_struct_0(sK5)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f5251,f4651])).

fof(f5251,plain,(
    ! [X0] :
      ( r2_waybel_0(sK3,sK5,X0)
      | ~ m1_connsp_2(X0,sK3,sK6)
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ l1_waybel_0(sK5,sK3)
      | v2_struct_0(sK5)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f4652,f4654])).

fof(f4654,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X4)
      | ~ m1_connsp_2(X4,X0,X2)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4560])).

fof(f4652,plain,(
    r3_waybel_9(sK3,sK5,sK6) ),
    inference(cnf_transformation,[],[f4556])).
%------------------------------------------------------------------------------
