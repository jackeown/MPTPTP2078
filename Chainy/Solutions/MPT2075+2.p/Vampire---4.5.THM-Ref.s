%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2075+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:40 EST 2020

% Result     : Theorem 56.04s
% Output     : Refutation 56.04s
% Verified   : 
% Statistics : Number of formulae       :   91 (2083 expanded)
%              Number of leaves         :    8 ( 632 expanded)
%              Depth                    :   42
%              Number of atoms          :  573 (25613 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13793,plain,(
    $false ),
    inference(subsumption_resolution,[],[f13792,f5864])).

fof(f5864,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f5262])).

fof(f5262,plain,
    ( ( ( ! [X2] :
            ( ~ r3_waybel_9(sK4,sK5,X2)
            | ~ m1_subset_1(X2,u1_struct_0(sK4)) )
        & l1_waybel_0(sK5,sK4)
        & v7_waybel_0(sK5)
        & v4_orders_2(sK5)
        & ~ v2_struct_0(sK5) )
      | ~ v1_compts_1(sK4) )
    & ( ! [X3] :
          ( ( r3_waybel_9(sK4,X3,sK6(X3))
            & m1_subset_1(sK6(X3),u1_struct_0(sK4)) )
          | ~ l1_waybel_0(X3,sK4)
          | ~ v7_waybel_0(X3)
          | ~ v4_orders_2(X3)
          | v2_struct_0(X3) )
      | v1_compts_1(sK4) )
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f5258,f5261,f5260,f5259])).

fof(f5259,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
          | ~ v1_compts_1(X0) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( r3_waybel_9(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | v1_compts_1(X0) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ( ? [X1] :
            ( ! [X2] :
                ( ~ r3_waybel_9(sK4,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(sK4)) )
            & l1_waybel_0(X1,sK4)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(sK4) )
      & ( ! [X3] :
            ( ? [X4] :
                ( r3_waybel_9(sK4,X3,X4)
                & m1_subset_1(X4,u1_struct_0(sK4)) )
            | ~ l1_waybel_0(X3,sK4)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(sK4) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f5260,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( ~ r3_waybel_9(sK4,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(sK4)) )
        & l1_waybel_0(X1,sK4)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ! [X2] :
          ( ~ r3_waybel_9(sK4,sK5,X2)
          | ~ m1_subset_1(X2,u1_struct_0(sK4)) )
      & l1_waybel_0(sK5,sK4)
      & v7_waybel_0(sK5)
      & v4_orders_2(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f5261,plain,(
    ! [X3] :
      ( ? [X4] :
          ( r3_waybel_9(sK4,X3,X4)
          & m1_subset_1(X4,u1_struct_0(sK4)) )
     => ( r3_waybel_9(sK4,X3,sK6(X3))
        & m1_subset_1(sK6(X3),u1_struct_0(sK4)) ) ) ),
    introduced(choice_axiom,[])).

fof(f5258,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ r3_waybel_9(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X3] :
            ( ? [X4] :
                ( r3_waybel_9(X0,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f5257])).

fof(f5257,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ r3_waybel_9(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5256])).

fof(f5256,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ r3_waybel_9(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f4603])).

fof(f4603,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4602])).

fof(f4602,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4551])).

fof(f4551,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v1_compts_1(X0)
        <=> ! [X1] :
              ( ( l1_waybel_0(X1,X0)
                & v7_waybel_0(X1)
                & v4_orders_2(X1)
                & ~ v2_struct_0(X1) )
             => ? [X2] :
                  ( r3_waybel_9(X0,X1,X2)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f4550])).

fof(f4550,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_yellow19)).

fof(f13792,plain,(
    v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f13791,f5865])).

fof(f5865,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f5262])).

fof(f13791,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f13790,f5866])).

fof(f5866,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f5262])).

fof(f13790,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f13784,f9135])).

fof(f9135,plain,(
    ~ v1_compts_1(sK4) ),
    inference(subsumption_resolution,[],[f9134,f5869])).

fof(f5869,plain,
    ( ~ v1_compts_1(sK4)
    | ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f5262])).

fof(f9134,plain,
    ( ~ v1_compts_1(sK4)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f9133,f5870])).

fof(f5870,plain,
    ( ~ v1_compts_1(sK4)
    | v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f5262])).

fof(f9133,plain,
    ( ~ v1_compts_1(sK4)
    | ~ v4_orders_2(sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f9132,f5871])).

fof(f5871,plain,
    ( ~ v1_compts_1(sK4)
    | v7_waybel_0(sK5) ),
    inference(cnf_transformation,[],[f5262])).

fof(f9132,plain,
    ( ~ v1_compts_1(sK4)
    | ~ v7_waybel_0(sK5)
    | ~ v4_orders_2(sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f9131,f5872])).

fof(f5872,plain,
    ( l1_waybel_0(sK5,sK4)
    | ~ v1_compts_1(sK4) ),
    inference(cnf_transformation,[],[f5262])).

fof(f9131,plain,
    ( ~ v1_compts_1(sK4)
    | ~ l1_waybel_0(sK5,sK4)
    | ~ v7_waybel_0(sK5)
    | ~ v4_orders_2(sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f9130,f8905])).

fof(f8905,plain,
    ( ~ v1_compts_1(sK4)
    | m1_subset_1(sK16(sK4,sK5),u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f8904,f5869])).

fof(f8904,plain,
    ( ~ v1_compts_1(sK4)
    | m1_subset_1(sK16(sK4,sK5),u1_struct_0(sK4))
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f8903,f5870])).

fof(f8903,plain,
    ( ~ v1_compts_1(sK4)
    | m1_subset_1(sK16(sK4,sK5),u1_struct_0(sK4))
    | ~ v4_orders_2(sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f8902,f5871])).

fof(f8902,plain,
    ( ~ v1_compts_1(sK4)
    | m1_subset_1(sK16(sK4,sK5),u1_struct_0(sK4))
    | ~ v7_waybel_0(sK5)
    | ~ v4_orders_2(sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f8901,f5864])).

fof(f8901,plain,
    ( ~ v1_compts_1(sK4)
    | m1_subset_1(sK16(sK4,sK5),u1_struct_0(sK4))
    | ~ v7_waybel_0(sK5)
    | ~ v4_orders_2(sK5)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f8900,f5865])).

fof(f8900,plain,
    ( ~ v1_compts_1(sK4)
    | m1_subset_1(sK16(sK4,sK5),u1_struct_0(sK4))
    | ~ v7_waybel_0(sK5)
    | ~ v4_orders_2(sK5)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f8899,f5866])).

fof(f8899,plain,
    ( ~ v1_compts_1(sK4)
    | m1_subset_1(sK16(sK4,sK5),u1_struct_0(sK4))
    | ~ v7_waybel_0(sK5)
    | ~ v4_orders_2(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(duplicate_literal_removal,[],[f8803])).

fof(f8803,plain,
    ( ~ v1_compts_1(sK4)
    | m1_subset_1(sK16(sK4,sK5),u1_struct_0(sK4))
    | ~ v7_waybel_0(sK5)
    | ~ v4_orders_2(sK5)
    | v2_struct_0(sK5)
    | ~ v1_compts_1(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f5872,f5910])).

fof(f5910,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK16(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f5289])).

fof(f5289,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_waybel_9(X0,X1,sK16(X0,X1))
            & m1_subset_1(sK16(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f4627,f5288])).

fof(f5288,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK16(X0,X1))
        & m1_subset_1(sK16(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4627,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4626])).

fof(f4626,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4520])).

fof(f4520,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l37_yellow19)).

fof(f9130,plain,
    ( ~ m1_subset_1(sK16(sK4,sK5),u1_struct_0(sK4))
    | ~ v1_compts_1(sK4)
    | ~ l1_waybel_0(sK5,sK4)
    | ~ v7_waybel_0(sK5)
    | ~ v4_orders_2(sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f9129,f5864])).

fof(f9129,plain,
    ( ~ m1_subset_1(sK16(sK4,sK5),u1_struct_0(sK4))
    | ~ v1_compts_1(sK4)
    | ~ l1_waybel_0(sK5,sK4)
    | ~ v7_waybel_0(sK5)
    | ~ v4_orders_2(sK5)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f9128,f5865])).

fof(f9128,plain,
    ( ~ m1_subset_1(sK16(sK4,sK5),u1_struct_0(sK4))
    | ~ v1_compts_1(sK4)
    | ~ l1_waybel_0(sK5,sK4)
    | ~ v7_waybel_0(sK5)
    | ~ v4_orders_2(sK5)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f9099,f5866])).

fof(f9099,plain,
    ( ~ m1_subset_1(sK16(sK4,sK5),u1_struct_0(sK4))
    | ~ v1_compts_1(sK4)
    | ~ l1_waybel_0(sK5,sK4)
    | ~ v7_waybel_0(sK5)
    | ~ v4_orders_2(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(duplicate_literal_removal,[],[f9092])).

fof(f9092,plain,
    ( ~ m1_subset_1(sK16(sK4,sK5),u1_struct_0(sK4))
    | ~ v1_compts_1(sK4)
    | ~ l1_waybel_0(sK5,sK4)
    | ~ v7_waybel_0(sK5)
    | ~ v4_orders_2(sK5)
    | v2_struct_0(sK5)
    | ~ v1_compts_1(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f5873,f5911])).

fof(f5911,plain,(
    ! [X0,X1] :
      ( r3_waybel_9(X0,X1,sK16(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f5289])).

fof(f5873,plain,(
    ! [X2] :
      ( ~ r3_waybel_9(sK4,sK5,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ v1_compts_1(sK4) ) ),
    inference(cnf_transformation,[],[f5262])).

fof(f13784,plain,
    ( v1_compts_1(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f13775,f5906])).

fof(f5906,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v7_waybel_0(sK15(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f5287])).

fof(f5287,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK15(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r2_hidden(sK15(X0),k6_yellow_6(X0))
        & l1_waybel_0(sK15(X0),X0)
        & v7_waybel_0(sK15(X0))
        & v4_orders_2(sK15(X0))
        & ~ v2_struct_0(sK15(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f4625,f5286])).

fof(f5286,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK15(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r2_hidden(sK15(X0),k6_yellow_6(X0))
        & l1_waybel_0(sK15(X0),X0)
        & v7_waybel_0(sK15(X0))
        & v4_orders_2(sK15(X0))
        & ~ v2_struct_0(sK15(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4625,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4624])).

fof(f4624,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4521])).

fof(f4521,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ~ r3_waybel_9(X0,X1,X2) )
                & r2_hidden(X1,k6_yellow_6(X0)) ) )
       => v1_compts_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_yellow19)).

fof(f13775,plain,(
    ~ v7_waybel_0(sK15(sK4)) ),
    inference(subsumption_resolution,[],[f13774,f5864])).

fof(f13774,plain,
    ( ~ v7_waybel_0(sK15(sK4))
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f13773,f5865])).

fof(f13773,plain,
    ( ~ v7_waybel_0(sK15(sK4))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f13772,f5866])).

fof(f13772,plain,
    ( ~ v7_waybel_0(sK15(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f13770,f9135])).

fof(f13770,plain,
    ( ~ v7_waybel_0(sK15(sK4))
    | v1_compts_1(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f9886,f5907])).

fof(f5907,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | l1_waybel_0(sK15(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f5287])).

fof(f9886,plain,
    ( ~ l1_waybel_0(sK15(sK4),sK4)
    | ~ v7_waybel_0(sK15(sK4)) ),
    inference(subsumption_resolution,[],[f9885,f9175])).

fof(f9175,plain,
    ( m1_subset_1(sK6(sK15(sK4)),u1_struct_0(sK4))
    | ~ v7_waybel_0(sK15(sK4)) ),
    inference(subsumption_resolution,[],[f9174,f5864])).

fof(f9174,plain,
    ( m1_subset_1(sK6(sK15(sK4)),u1_struct_0(sK4))
    | ~ v7_waybel_0(sK15(sK4))
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f9173,f5865])).

fof(f9173,plain,
    ( m1_subset_1(sK6(sK15(sK4)),u1_struct_0(sK4))
    | ~ v7_waybel_0(sK15(sK4))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f9172,f5866])).

fof(f9172,plain,
    ( m1_subset_1(sK6(sK15(sK4)),u1_struct_0(sK4))
    | ~ v7_waybel_0(sK15(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f9171,f9135])).

fof(f9171,plain,
    ( m1_subset_1(sK6(sK15(sK4)),u1_struct_0(sK4))
    | ~ v7_waybel_0(sK15(sK4))
    | v1_compts_1(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f9170,f9146])).

fof(f9146,plain,(
    ~ v2_struct_0(sK15(sK4)) ),
    inference(subsumption_resolution,[],[f9145,f5864])).

fof(f9145,plain,
    ( ~ v2_struct_0(sK15(sK4))
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f9144,f5865])).

fof(f9144,plain,
    ( ~ v2_struct_0(sK15(sK4))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f9136,f5866])).

fof(f9136,plain,
    ( ~ v2_struct_0(sK15(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f9135,f5904])).

fof(f5904,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_struct_0(sK15(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f5287])).

fof(f9170,plain,
    ( m1_subset_1(sK6(sK15(sK4)),u1_struct_0(sK4))
    | ~ v7_waybel_0(sK15(sK4))
    | v2_struct_0(sK15(sK4))
    | v1_compts_1(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f9161,f9149])).

fof(f9149,plain,(
    v4_orders_2(sK15(sK4)) ),
    inference(subsumption_resolution,[],[f9148,f5864])).

fof(f9148,plain,
    ( v4_orders_2(sK15(sK4))
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f9147,f5865])).

fof(f9147,plain,
    ( v4_orders_2(sK15(sK4))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f9137,f5866])).

fof(f9137,plain,
    ( v4_orders_2(sK15(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f9135,f5905])).

fof(f5905,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v4_orders_2(sK15(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f5287])).

fof(f9161,plain,
    ( m1_subset_1(sK6(sK15(sK4)),u1_struct_0(sK4))
    | ~ v7_waybel_0(sK15(sK4))
    | ~ v4_orders_2(sK15(sK4))
    | v2_struct_0(sK15(sK4))
    | v1_compts_1(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(duplicate_literal_removal,[],[f9155])).

fof(f9155,plain,
    ( m1_subset_1(sK6(sK15(sK4)),u1_struct_0(sK4))
    | ~ v7_waybel_0(sK15(sK4))
    | ~ v4_orders_2(sK15(sK4))
    | v2_struct_0(sK15(sK4))
    | v1_compts_1(sK4)
    | v1_compts_1(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f5867,f5907])).

fof(f5867,plain,(
    ! [X3] :
      ( ~ l1_waybel_0(X3,sK4)
      | m1_subset_1(sK6(X3),u1_struct_0(sK4))
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK4) ) ),
    inference(cnf_transformation,[],[f5262])).

fof(f9885,plain,
    ( ~ l1_waybel_0(sK15(sK4),sK4)
    | ~ v7_waybel_0(sK15(sK4))
    | ~ m1_subset_1(sK6(sK15(sK4)),u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f9884,f5864])).

fof(f9884,plain,
    ( ~ l1_waybel_0(sK15(sK4),sK4)
    | ~ v7_waybel_0(sK15(sK4))
    | ~ m1_subset_1(sK6(sK15(sK4)),u1_struct_0(sK4))
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f9883,f5865])).

fof(f9883,plain,
    ( ~ l1_waybel_0(sK15(sK4),sK4)
    | ~ v7_waybel_0(sK15(sK4))
    | ~ m1_subset_1(sK6(sK15(sK4)),u1_struct_0(sK4))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f9882,f5866])).

fof(f9882,plain,
    ( ~ l1_waybel_0(sK15(sK4),sK4)
    | ~ v7_waybel_0(sK15(sK4))
    | ~ m1_subset_1(sK6(sK15(sK4)),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f9881,f9135])).

fof(f9881,plain,
    ( ~ l1_waybel_0(sK15(sK4),sK4)
    | ~ v7_waybel_0(sK15(sK4))
    | v1_compts_1(sK4)
    | ~ m1_subset_1(sK6(sK15(sK4)),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f9880,f9146])).

fof(f9880,plain,
    ( ~ l1_waybel_0(sK15(sK4),sK4)
    | ~ v7_waybel_0(sK15(sK4))
    | v2_struct_0(sK15(sK4))
    | v1_compts_1(sK4)
    | ~ m1_subset_1(sK6(sK15(sK4)),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f9838,f9149])).

fof(f9838,plain,
    ( ~ l1_waybel_0(sK15(sK4),sK4)
    | ~ v7_waybel_0(sK15(sK4))
    | ~ v4_orders_2(sK15(sK4))
    | v2_struct_0(sK15(sK4))
    | v1_compts_1(sK4)
    | ~ m1_subset_1(sK6(sK15(sK4)),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(duplicate_literal_removal,[],[f9837])).

fof(f9837,plain,
    ( ~ l1_waybel_0(sK15(sK4),sK4)
    | ~ v7_waybel_0(sK15(sK4))
    | ~ v4_orders_2(sK15(sK4))
    | v2_struct_0(sK15(sK4))
    | v1_compts_1(sK4)
    | v1_compts_1(sK4)
    | ~ m1_subset_1(sK6(sK15(sK4)),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f5868,f5909])).

fof(f5909,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK15(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f5287])).

fof(f5868,plain,(
    ! [X3] :
      ( r3_waybel_9(sK4,X3,sK6(X3))
      | ~ l1_waybel_0(X3,sK4)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK4) ) ),
    inference(cnf_transformation,[],[f5262])).
%------------------------------------------------------------------------------
