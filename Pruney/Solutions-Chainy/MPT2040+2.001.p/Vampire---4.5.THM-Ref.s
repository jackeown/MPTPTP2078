%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  321 (5325 expanded)
%              Number of leaves         :   20 (1415 expanded)
%              Depth                    :  117
%              Number of atoms          : 4187 (88785 expanded)
%              Number of equality atoms :  116 ( 711 expanded)
%              Maximal formula depth    :   38 (  15 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f586,plain,(
    $false ),
    inference(subsumption_resolution,[],[f585,f104])).

fof(f104,plain,(
    l1_orders_2(sK0) ),
    inference(resolution,[],[f76,f64])).

fof(f64,plain,(
    l1_waybel_9(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( ~ r2_hidden(k1_waybel_9(sK0,sK1),k10_yellow_6(sK0,sK1))
      | ~ r2_waybel_9(sK0,sK1) )
    & v11_waybel_0(sK1,sK0)
    & l1_waybel_0(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & ! [X2] :
        ( v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    & l1_waybel_9(sK0)
    & v1_compts_1(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & v8_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1))
              | ~ r2_waybel_9(X0,X1) )
            & v11_waybel_0(X1,X0)
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & ! [X2] :
            ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r2_hidden(k1_waybel_9(sK0,X1),k10_yellow_6(sK0,X1))
            | ~ r2_waybel_9(sK0,X1) )
          & v11_waybel_0(X1,sK0)
          & l1_waybel_0(X1,sK0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & ! [X2] :
          ( v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
          | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
      & l1_waybel_9(sK0)
      & v1_compts_1(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & v8_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ( ~ r2_hidden(k1_waybel_9(sK0,X1),k10_yellow_6(sK0,X1))
          | ~ r2_waybel_9(sK0,X1) )
        & v11_waybel_0(X1,sK0)
        & l1_waybel_0(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ( ~ r2_hidden(k1_waybel_9(sK0,sK1),k10_yellow_6(sK0,sK1))
        | ~ r2_waybel_9(sK0,sK1) )
      & v11_waybel_0(sK1,sK0)
      & l1_waybel_0(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1))
            | ~ r2_waybel_9(X0,X1) )
          & v11_waybel_0(X1,X0)
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & ! [X2] :
          ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_9(X0,X2),k10_yellow_6(X0,X2))
            | ~ r2_waybel_9(X0,X2) )
          & v11_waybel_0(X2,X0)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & ! [X1] :
          ( v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_waybel_9(X0,X2),k10_yellow_6(X0,X2))
            | ~ r2_waybel_9(X0,X2) )
          & v11_waybel_0(X2,X0)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & ! [X1] :
          ( v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_waybel_9(X0)
          & v1_compts_1(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ( ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( v11_waybel_0(X2,X0)
               => ( r2_hidden(k1_waybel_9(X0,X2),k10_yellow_6(X0,X2))
                  & r2_waybel_9(X0,X2) ) ) ) ) ) ),
    inference(rectify,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_waybel_9(X0)
          & v1_compts_1(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ( ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
         => ! [X1] :
              ( ( l1_waybel_0(X1,X0)
                & v7_waybel_0(X1)
                & v4_orders_2(X1)
                & ~ v2_struct_0(X1) )
             => ( v11_waybel_0(X1,X0)
               => ( r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1))
                  & r2_waybel_9(X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ( v11_waybel_0(X1,X0)
             => ( r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1))
                & r2_waybel_9(X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_waybel_9)).

fof(f76,plain,(
    ! [X0] :
      ( ~ l1_waybel_9(X0)
      | l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).

fof(f585,plain,(
    ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f584,f61])).

fof(f61,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f584,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f583,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f583,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f582,f64])).

fof(f582,plain,
    ( v2_struct_0(sK0)
    | ~ l1_waybel_9(sK0) ),
    inference(resolution,[],[f581,f75])).

fof(f75,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
      | ~ l1_waybel_9(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f581,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f580,f311])).

fof(f311,plain,
    ( ~ r2_waybel_9(sK0,sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f310,f56])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f310,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_waybel_9(sK0,sK1)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f309,f57])).

fof(f57,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f309,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_waybel_9(sK0,sK1)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f308,f63])).

fof(f63,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f308,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_waybel_9(sK0,sK1)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f307,f66])).

fof(f66,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f307,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_waybel_9(sK0,sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f306,f67])).

fof(f67,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f306,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_waybel_9(sK0,sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f305,f68])).

fof(f68,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f305,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_waybel_9(sK0,sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f304,f69])).

fof(f69,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f304,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_waybel_9(sK0,sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f299])).

fof(f299,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_waybel_9(sK0,sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f298,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_waybel_9(X0,X1,sK4(X0,X1))
            & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK4(X0,X1))
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_compts_1(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_waybel_9)).

fof(f298,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_waybel_9(sK0,sK1) ),
    inference(subsumption_resolution,[],[f297,f56])).

fof(f297,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_waybel_9(sK0,sK1)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f296,f57])).

fof(f296,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_waybel_9(sK0,sK1)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f295,f63])).

fof(f295,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_waybel_9(sK0,sK1)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f294,f66])).

fof(f294,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_waybel_9(sK0,sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f293,f67])).

fof(f293,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_waybel_9(sK0,sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f292,f68])).

fof(f292,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_waybel_9(sK0,sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f291,f69])).

fof(f291,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_waybel_9(sK0,sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f286])).

fof(f286,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_waybel_9(sK0,sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f282,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r3_waybel_9(X0,X1,sK4(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f282,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f281,f143])).

fof(f143,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k10_yellow_6(sK0,sK1))
      | ~ r2_waybel_9(sK0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f142,f66])).

fof(f142,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k10_yellow_6(sK0,sK1))
      | ~ r2_waybel_9(sK0,sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f141,f67])).

fof(f141,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k10_yellow_6(sK0,sK1))
      | ~ r2_waybel_9(sK0,sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f140,f68])).

fof(f140,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k10_yellow_6(sK0,sK1))
      | ~ r2_waybel_9(sK0,sK1)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f139,f69])).

fof(f139,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k10_yellow_6(sK0,sK1))
      | ~ r2_waybel_9(sK0,sK1)
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f137,f70])).

fof(f70,plain,(
    v11_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f137,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k10_yellow_6(sK0,sK1))
      | ~ r2_waybel_9(sK0,sK1)
      | ~ v11_waybel_0(sK1,sK0)
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X0) ) ),
    inference(superposition,[],[f71,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( k1_waybel_9(sK0,X0) = X1
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f134,f56])).

fof(f134,plain,(
    ! [X0,X1] :
      ( k1_waybel_9(sK0,X0) = X1
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f133,f57])).

fof(f133,plain,(
    ! [X0,X1] :
      ( k1_waybel_9(sK0,X0) = X1
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f132,f58])).

fof(f58,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f132,plain,(
    ! [X0,X1] :
      ( k1_waybel_9(sK0,X0) = X1
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f131,f59])).

fof(f59,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f131,plain,(
    ! [X0,X1] :
      ( k1_waybel_9(sK0,X0) = X1
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f130,f60])).

fof(f60,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f130,plain,(
    ! [X0,X1] :
      ( k1_waybel_9(sK0,X0) = X1
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f129,f61])).

fof(f129,plain,(
    ! [X0,X1] :
      ( k1_waybel_9(sK0,X0) = X1
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f128,f62])).

fof(f62,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f128,plain,(
    ! [X0,X1] :
      ( k1_waybel_9(sK0,X0) = X1
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f127,f63])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k1_waybel_9(sK0,X0) = X1
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f126,f64])).

fof(f126,plain,(
    ! [X0,X1] :
      ( k1_waybel_9(sK0,X0) = X1
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k1_waybel_9(sK0,X0) = X1
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(condensation,[],[f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ v11_waybel_0(X0,sK0)
      | k1_waybel_9(sK0,X0) = X1
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ r3_waybel_9(sK0,X0,X2)
      | k1_waybel_9(sK0,X0) = X2
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ v11_waybel_0(X0,sK0)
      | k1_waybel_9(sK0,X0) = X1
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ r3_waybel_9(sK0,X0,X2)
      | k1_waybel_9(sK0,X0) = X2
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(condensation,[],[f122])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v11_waybel_0(X0,sK0)
      | k1_waybel_9(sK0,X0) = X1
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ r3_waybel_9(sK0,X2,X3)
      | ~ v11_waybel_0(X2,sK0)
      | k1_waybel_9(sK0,X2) = X3
      | ~ l1_waybel_0(X2,sK0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f121,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X2,X1)
      | ~ v11_waybel_0(X2,X0)
      | k1_waybel_9(X0,X2) = X1
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_waybel_9(X0,X2) = X1
              | ~ r3_waybel_9(X0,X2,X1)
              | ~ v11_waybel_0(X2,X0)
              | ( ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
                & m1_subset_1(sK7(X0),u1_struct_0(X0)) )
              | ~ l1_waybel_0(X2,X0)
              | ~ v7_waybel_0(X2)
              | ~ v4_orders_2(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_waybel_9(X0,X2) = X1
              | ~ r3_waybel_9(X0,X2,X1)
              | ~ v11_waybel_0(X2,X0)
              | ? [X3] :
                  ( ~ v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ l1_waybel_0(X2,X0)
              | ~ v7_waybel_0(X2)
              | ~ v4_orders_2(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_waybel_9(X0,X2) = X1
              | ~ r3_waybel_9(X0,X2,X1)
              | ~ v11_waybel_0(X2,X0)
              | ? [X3] :
                  ( ~ v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ l1_waybel_0(X2,X0)
              | ~ v7_waybel_0(X2)
              | ~ v4_orders_2(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( ( r3_waybel_9(X0,X2,X1)
                  & v11_waybel_0(X2,X0)
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) ) )
               => k1_waybel_9(X0,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_waybel_9)).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK7(sK0),u1_struct_0(sK0))
      | ~ v11_waybel_0(X0,sK0)
      | k1_waybel_9(sK0,X0) = X1
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f120,f56])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | k1_waybel_9(sK0,X0) = X1
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(sK7(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f119,f57])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | k1_waybel_9(sK0,X0) = X1
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(sK7(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f118,f58])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | k1_waybel_9(sK0,X0) = X1
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(sK7(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f117,f59])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | k1_waybel_9(sK0,X0) = X1
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(sK7(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f116,f60])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | k1_waybel_9(sK0,X0) = X1
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(sK7(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f115,f61])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | k1_waybel_9(sK0,X0) = X1
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(sK7(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f114,f62])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | k1_waybel_9(sK0,X0) = X1
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(sK7(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f113,f63])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | k1_waybel_9(sK0,X0) = X1
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(sK7(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f112,f64])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | k1_waybel_9(sK0,X0) = X1
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(sK7(sK0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f91,f65])).

fof(f65,plain,(
    ! [X2] :
      ( v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0)
      | ~ r3_waybel_9(X0,X2,X1)
      | ~ v11_waybel_0(X2,X0)
      | k1_waybel_9(X0,X2) = X1
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f71,plain,
    ( ~ r2_hidden(k1_waybel_9(sK0,sK1),k10_yellow_6(sK0,sK1))
    | ~ r2_waybel_9(sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f281,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k10_yellow_6(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f280])).

fof(f280,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k10_yellow_6(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_waybel_9(sK0,sK1) ) ),
    inference(condensation,[],[f279])).

fof(f279,plain,(
    ! [X2,X3] :
      ( ~ r3_waybel_9(sK0,sK1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X3,k10_yellow_6(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_waybel_9(sK0,sK1)
      | ~ r3_waybel_9(sK0,sK1,X2) ) ),
    inference(subsumption_resolution,[],[f278,f193])).

fof(f193,plain,(
    ! [X0] :
      ( sK2(sK0,sK1) = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f192,f70])).

fof(f192,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v11_waybel_0(sK1,sK0)
      | sK2(sK0,sK1) = X0
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f191,f66])).

fof(f191,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK1)
      | ~ v11_waybel_0(sK1,sK0)
      | sK2(sK0,sK1) = X0
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f190,f67])).

fof(f190,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v11_waybel_0(sK1,sK0)
      | sK2(sK0,sK1) = X0
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f189,f68])).

fof(f189,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v11_waybel_0(sK1,sK0)
      | sK2(sK0,sK1) = X0
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f183,f69])).

fof(f183,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v11_waybel_0(sK1,sK0)
      | sK2(sK0,sK1) = X0
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v11_waybel_0(sK1,sK0)
      | sK2(sK0,sK1) = X0
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1) ) ),
    inference(condensation,[],[f181])).

fof(f181,plain,(
    ! [X2,X1] :
      ( ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v11_waybel_0(sK1,sK0)
      | sK2(sK0,sK1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X2)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,(
    ! [X2,X1] :
      ( ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v11_waybel_0(sK1,sK0)
      | sK2(sK0,sK1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X2)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X2) ) ),
    inference(resolution,[],[f178,f143])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k10_yellow_6(sK0,X0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | sK2(sK0,X0) = X2
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f177,f56])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | sK2(sK0,X0) = X2
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k10_yellow_6(sK0,X0))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f176,f57])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | sK2(sK0,X0) = X2
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k10_yellow_6(sK0,X0))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f175,f63])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | sK2(sK0,X0) = X2
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k10_yellow_6(sK0,X0))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | sK2(sK0,X0) = X2
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k10_yellow_6(sK0,X0))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k10_yellow_6(sK0,X0))
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(condensation,[],[f173])).

fof(f173,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | sK2(sK0,X0) = X1
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ r3_waybel_9(sK0,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(X2,k10_yellow_6(sK0,X0))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r3_waybel_9(sK0,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X3,k10_yellow_6(sK0,X0))
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | sK2(sK0,X0) = X1
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ r3_waybel_9(sK0,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(X2,k10_yellow_6(sK0,X0))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r3_waybel_9(sK0,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X3,k10_yellow_6(sK0,X0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f155,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ( sK2(X0,X1) != sK3(X0,X1)
            & r3_waybel_9(X0,X1,sK3(X0,X1))
            & r3_waybel_9(X0,X1,sK2(X0,X1))
            & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
            & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f38,f40,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( X3 != X4
              & r3_waybel_9(X0,X1,X4)
              & r3_waybel_9(X0,X1,X3)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( sK2(X0,X1) != X4
            & r3_waybel_9(X0,X1,X4)
            & r3_waybel_9(X0,X1,sK2(X0,X1))
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( sK2(X0,X1) != X4
          & r3_waybel_9(X0,X1,X4)
          & r3_waybel_9(X0,X1,sK2(X0,X1))
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( sK2(X0,X1) != sK3(X0,X1)
        & r3_waybel_9(X0,X1,sK3(X0,X1))
        & r3_waybel_9(X0,X1,sK2(X0,X1))
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ? [X3] :
              ( ? [X4] :
                  ( X3 != X4
                  & r3_waybel_9(X0,X1,X4)
                  & r3_waybel_9(X0,X1,X3)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X4] :
              ( r2_hidden(X4,k10_yellow_6(X0,X1))
              | ~ r3_waybel_9(X0,X1,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & r3_waybel_9(X0,X1,X3)
                  & r3_waybel_9(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X4] :
              ( r2_hidden(X4,k10_yellow_6(X0,X1))
              | ~ r3_waybel_9(X0,X1,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & r3_waybel_9(X0,X1,X3)
                  & r3_waybel_9(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_compts_1(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r3_waybel_9(X0,X1,X3)
                        & r3_waybel_9(X0,X1,X2) )
                     => X2 = X3 ) ) )
           => ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X0))
               => ( r3_waybel_9(X0,X1,X4)
                 => r2_hidden(X4,k10_yellow_6(X0,X1)) ) ) ) ) ) ),
    inference(rectify,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_compts_1(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r3_waybel_9(X0,X1,X3)
                        & r3_waybel_9(X0,X1,X2) )
                     => X2 = X3 ) ) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_waybel_9(X0,X1,X2)
                 => r2_hidden(X2,k10_yellow_6(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_waybel_9)).

fof(f155,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(sK2(sK0,X2),u1_struct_0(sK0))
      | ~ l1_waybel_0(X2,sK0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ v11_waybel_0(X2,sK0)
      | sK2(sK0,X2) = X3
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X2,X3)
      | ~ r3_waybel_9(sK0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,k10_yellow_6(sK0,X2))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f154,f56])).

fof(f154,plain,(
    ! [X4,X2,X3] :
      ( ~ v11_waybel_0(X2,sK0)
      | ~ l1_waybel_0(X2,sK0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(sK2(sK0,X2),u1_struct_0(sK0))
      | sK2(sK0,X2) = X3
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X2,X3)
      | ~ r3_waybel_9(sK0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,k10_yellow_6(sK0,X2))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f153,f57])).

fof(f153,plain,(
    ! [X4,X2,X3] :
      ( ~ v11_waybel_0(X2,sK0)
      | ~ l1_waybel_0(X2,sK0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(sK2(sK0,X2),u1_struct_0(sK0))
      | sK2(sK0,X2) = X3
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X2,X3)
      | ~ r3_waybel_9(sK0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,k10_yellow_6(sK0,X2))
      | ~ l1_pre_topc(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f148,f63])).

fof(f148,plain,(
    ! [X4,X2,X3] :
      ( ~ v11_waybel_0(X2,sK0)
      | ~ l1_waybel_0(X2,sK0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(sK2(sK0,X2),u1_struct_0(sK0))
      | sK2(sK0,X2) = X3
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X2,X3)
      | ~ r3_waybel_9(sK0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,k10_yellow_6(sK0,X2))
      | ~ l1_pre_topc(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,(
    ! [X4,X2,X3] :
      ( ~ v11_waybel_0(X2,sK0)
      | ~ l1_waybel_0(X2,sK0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(sK2(sK0,X2),u1_struct_0(sK0))
      | sK2(sK0,X2) = X3
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X2,X3)
      | ~ r3_waybel_9(sK0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,k10_yellow_6(sK0,X2))
      | ~ l1_waybel_0(X2,sK0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f138,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,sK2(X0,X1))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X2)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | X1 = X2
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X2)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1) ) ),
    inference(superposition,[],[f135,f135])).

fof(f278,plain,(
    ! [X2,X3] :
      ( sK2(sK0,sK1) != X2
      | ~ r3_waybel_9(sK0,sK1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X3,k10_yellow_6(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_waybel_9(sK0,sK1)
      | ~ r3_waybel_9(sK0,sK1,X2) ) ),
    inference(subsumption_resolution,[],[f277,f56])).

fof(f277,plain,(
    ! [X2,X3] :
      ( sK2(sK0,sK1) != X2
      | ~ r3_waybel_9(sK0,sK1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X3,k10_yellow_6(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_waybel_9(sK0,sK1)
      | ~ r3_waybel_9(sK0,sK1,X2) ) ),
    inference(subsumption_resolution,[],[f276,f57])).

fof(f276,plain,(
    ! [X2,X3] :
      ( sK2(sK0,sK1) != X2
      | ~ r3_waybel_9(sK0,sK1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X3,k10_yellow_6(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_waybel_9(sK0,sK1)
      | ~ r3_waybel_9(sK0,sK1,X2) ) ),
    inference(subsumption_resolution,[],[f275,f63])).

fof(f275,plain,(
    ! [X2,X3] :
      ( sK2(sK0,sK1) != X2
      | ~ r3_waybel_9(sK0,sK1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X3,k10_yellow_6(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_waybel_9(sK0,sK1)
      | ~ r3_waybel_9(sK0,sK1,X2) ) ),
    inference(subsumption_resolution,[],[f274,f66])).

fof(f274,plain,(
    ! [X2,X3] :
      ( sK2(sK0,sK1) != X2
      | ~ r3_waybel_9(sK0,sK1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X3,k10_yellow_6(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_waybel_9(sK0,sK1)
      | ~ r3_waybel_9(sK0,sK1,X2) ) ),
    inference(subsumption_resolution,[],[f273,f67])).

fof(f273,plain,(
    ! [X2,X3] :
      ( sK2(sK0,sK1) != X2
      | ~ r3_waybel_9(sK0,sK1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X3,k10_yellow_6(sK0,sK1))
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_waybel_9(sK0,sK1)
      | ~ r3_waybel_9(sK0,sK1,X2) ) ),
    inference(subsumption_resolution,[],[f272,f68])).

fof(f272,plain,(
    ! [X2,X3] :
      ( sK2(sK0,sK1) != X2
      | ~ r3_waybel_9(sK0,sK1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X3,k10_yellow_6(sK0,sK1))
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_waybel_9(sK0,sK1)
      | ~ r3_waybel_9(sK0,sK1,X2) ) ),
    inference(subsumption_resolution,[],[f269,f69])).

fof(f269,plain,(
    ! [X2,X3] :
      ( sK2(sK0,sK1) != X2
      | ~ r3_waybel_9(sK0,sK1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X3,k10_yellow_6(sK0,sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_waybel_9(sK0,sK1)
      | ~ r3_waybel_9(sK0,sK1,X2) ) ),
    inference(duplicate_literal_removal,[],[f264])).

fof(f264,plain,(
    ! [X2,X3] :
      ( sK2(sK0,sK1) != X2
      | ~ r3_waybel_9(sK0,sK1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X3,k10_yellow_6(sK0,sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ r3_waybel_9(sK0,sK1,X2) ) ),
    inference(superposition,[],[f81,f261])).

fof(f261,plain,(
    ! [X0] :
      ( sK3(sK0,sK1) = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ r3_waybel_9(sK0,sK1,X0) ) ),
    inference(duplicate_literal_removal,[],[f260])).

fof(f260,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK3(sK0,sK1) = X0
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ r3_waybel_9(sK0,sK1,X0) ) ),
    inference(condensation,[],[f259])).

fof(f259,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK3(sK0,sK1) = X0
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ r3_waybel_9(sK0,sK1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f258,f143])).

fof(f258,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK3(sK0,sK1) = X0
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ r3_waybel_9(sK0,sK1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k10_yellow_6(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f257,f56])).

fof(f257,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK3(sK0,sK1) = X0
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ r3_waybel_9(sK0,sK1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k10_yellow_6(sK0,sK1))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f256,f57])).

fof(f256,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK3(sK0,sK1) = X0
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ r3_waybel_9(sK0,sK1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k10_yellow_6(sK0,sK1))
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f255,f63])).

fof(f255,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK3(sK0,sK1) = X0
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ r3_waybel_9(sK0,sK1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k10_yellow_6(sK0,sK1))
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f254,f66])).

fof(f254,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK3(sK0,sK1) = X0
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ r3_waybel_9(sK0,sK1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k10_yellow_6(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f253,f67])).

fof(f253,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK3(sK0,sK1) = X0
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ r3_waybel_9(sK0,sK1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k10_yellow_6(sK0,sK1))
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f252,f68])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK3(sK0,sK1) = X0
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ r3_waybel_9(sK0,sK1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k10_yellow_6(sK0,sK1))
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f251,f69])).

fof(f251,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK3(sK0,sK1) = X0
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ r3_waybel_9(sK0,sK1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k10_yellow_6(sK0,sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(duplicate_literal_removal,[],[f250])).

fof(f250,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK3(sK0,sK1) = X0
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ r3_waybel_9(sK0,sK1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k10_yellow_6(sK0,sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f224,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f224,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK3(sK0,sK1) = X0
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ r3_waybel_9(sK0,sK1,X0) ) ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
      | sK3(sK0,sK1) = X0
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ r3_waybel_9(sK0,sK1,X0) ) ),
    inference(condensation,[],[f222])).

fof(f222,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
      | sK3(sK0,sK1) = X3
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X3)
      | ~ r3_waybel_9(sK0,sK1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f221,f143])).

fof(f221,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
      | sK3(sK0,sK1) = X3
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X3)
      | ~ r3_waybel_9(sK0,sK1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,k10_yellow_6(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f220,f56])).

fof(f220,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
      | sK3(sK0,sK1) = X3
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X3)
      | ~ r3_waybel_9(sK0,sK1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,k10_yellow_6(sK0,sK1))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f219,f57])).

fof(f219,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
      | sK3(sK0,sK1) = X3
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X3)
      | ~ r3_waybel_9(sK0,sK1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,k10_yellow_6(sK0,sK1))
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f218,f63])).

fof(f218,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
      | sK3(sK0,sK1) = X3
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X3)
      | ~ r3_waybel_9(sK0,sK1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,k10_yellow_6(sK0,sK1))
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f217,f66])).

fof(f217,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
      | sK3(sK0,sK1) = X3
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X3)
      | ~ r3_waybel_9(sK0,sK1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,k10_yellow_6(sK0,sK1))
      | v2_struct_0(sK1)
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f216,f67])).

fof(f216,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
      | sK3(sK0,sK1) = X3
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X3)
      | ~ r3_waybel_9(sK0,sK1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,k10_yellow_6(sK0,sK1))
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f215,f68])).

fof(f215,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
      | sK3(sK0,sK1) = X3
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X3)
      | ~ r3_waybel_9(sK0,sK1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,k10_yellow_6(sK0,sK1))
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f205,f69])).

fof(f205,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
      | sK3(sK0,sK1) = X3
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X3)
      | ~ r3_waybel_9(sK0,sK1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,k10_yellow_6(sK0,sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(duplicate_literal_removal,[],[f204])).

fof(f204,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
      | sK3(sK0,sK1) = X3
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X3)
      | ~ r3_waybel_9(sK0,sK1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,k10_yellow_6(sK0,sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f201,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,sK3(X0,X1))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f201,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,sK1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | X0 = X1
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X0) ) ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X1)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_9(sK0,sK1) ) ),
    inference(superposition,[],[f193,f193])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1) != sK3(X0,X1)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f580,plain,
    ( r2_waybel_9(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f579,f67])).

fof(f579,plain,
    ( r2_waybel_9(sK0,sK1)
    | ~ v4_orders_2(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f578,f68])).

fof(f578,plain,
    ( r2_waybel_9(sK0,sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f577,f69])).

fof(f577,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | r2_waybel_9(sK0,sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f576,f66])).

fof(f576,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | r2_waybel_9(sK0,sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f575,f70])).

fof(f575,plain,(
    ! [X0] :
      ( ~ v11_waybel_0(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f574,f56])).

fof(f574,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f573,f57])).

fof(f573,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f572,f63])).

fof(f572,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(duplicate_literal_removal,[],[f567])).

fof(f567,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f566,f82])).

fof(f566,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4(sK0,X0),u1_struct_0(sK0))
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f565,f56])).

fof(f565,plain,(
    ! [X0] :
      ( ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ m1_subset_1(sK4(sK0,X0),u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f564,f57])).

fof(f564,plain,(
    ! [X0] :
      ( ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ m1_subset_1(sK4(sK0,X0),u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f563,f63])).

fof(f563,plain,(
    ! [X0] :
      ( ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ m1_subset_1(sK4(sK0,X0),u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f558])).

fof(f558,plain,(
    ! [X0] :
      ( ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ m1_subset_1(sK4(sK0,X0),u1_struct_0(sK0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f557,f83])).

fof(f557,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f556,f529])).

fof(f529,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK8(sK0),u1_struct_0(sK0))
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0) ) ),
    inference(subsumption_resolution,[],[f528,f487])).

fof(f487,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK9(sK0),u1_struct_0(sK0))
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f486,f56])).

fof(f486,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK0)
      | m1_subset_1(sK9(sK0),u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f485,f57])).

fof(f485,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | m1_subset_1(sK9(sK0),u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f484,f58])).

fof(f484,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | m1_subset_1(sK9(sK0),u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f483,f59])).

fof(f483,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | m1_subset_1(sK9(sK0),u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f482,f60])).

fof(f482,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | m1_subset_1(sK9(sK0),u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f481,f61])).

fof(f481,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | m1_subset_1(sK9(sK0),u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f480,f62])).

fof(f480,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | m1_subset_1(sK9(sK0),u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f479,f63])).

fof(f479,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | m1_subset_1(sK9(sK0),u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f478,f64])).

fof(f478,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | m1_subset_1(sK9(sK0),u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f477,f65])).

fof(f477,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_pre_topc(k4_waybel_1(X1,sK8(X1)),X1,X1)
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_waybel_9(X1)
      | ~ v1_compts_1(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v8_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | m1_subset_1(sK9(X1),u1_struct_0(X1))
      | ~ r3_waybel_9(X1,X2,X0)
      | ~ v11_waybel_0(X2,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | r2_waybel_9(X1,X2) ) ),
    inference(subsumption_resolution,[],[f476,f76])).

fof(f476,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_waybel_9(X1)
      | ~ v1_compts_1(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v8_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | m1_subset_1(sK9(X1),u1_struct_0(X1))
      | ~ r3_waybel_9(X1,X2,X0)
      | ~ v11_waybel_0(X2,X1)
      | ~ v5_pre_topc(k4_waybel_1(X1,sK8(X1)),X1,X1)
      | r2_waybel_9(X1,X2)
      | ~ l1_orders_2(X1) ) ),
    inference(duplicate_literal_removal,[],[f475])).

fof(f475,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_waybel_9(X1)
      | ~ v1_compts_1(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v8_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | m1_subset_1(sK9(X1),u1_struct_0(X1))
      | ~ r3_waybel_9(X1,X2,X0)
      | ~ v11_waybel_0(X2,X1)
      | ~ v5_pre_topc(k4_waybel_1(X1,sK8(X1)),X1,X1)
      | r2_waybel_9(X1,X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f466,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | r2_waybel_9(X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_waybel_9(X0,X1)
              | ~ r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) )
            & ( r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
              | ~ r2_waybel_9(X0,X1) ) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_waybel_9(X0,X1)
          <=> r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ( r2_waybel_9(X0,X1)
          <=> r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_waybel_9)).

fof(f466,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(sK9(X0),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X2,X1)
      | ~ v11_waybel_0(X2,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f459])).

fof(f459,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)))
      | ~ r3_waybel_9(X0,X2,X1)
      | ~ r3_waybel_9(X0,X2,X1)
      | ~ v11_waybel_0(X2,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f458,f103])).

fof(f103,plain,(
    ! [X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v11_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v11_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v11_waybel_0(X1,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v11_waybel_0(X1,X0)
                  | ( ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
                    & m1_subset_1(sK8(X0),u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f30,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X4] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v11_waybel_0(X1,X0)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v11_waybel_0(X1,X0)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & v11_waybel_0(X1,X0)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_waybel_9)).

fof(f458,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
      | m1_subset_1(sK9(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ r3_waybel_9(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f457,f76])).

fof(f457,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | m1_subset_1(sK9(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f456])).

fof(f456,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | m1_subset_1(sK9(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
      | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f455,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
                  & r1_lattice3(X0,X1,sK5(X0,X1,X2))
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,X5,sK6(X0,X1))
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,sK6(X0,X1))
              & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f45,f47,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X5,X4)
              | ~ r1_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,X5,sK6(X0,X1))
            | ~ r1_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK6(X0,X1))
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X5,X4)
                    | ~ r1_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X3,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow_0)).

fof(f455,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK5(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | m1_subset_1(sK9(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2) ) ),
    inference(subsumption_resolution,[],[f454,f76])).

fof(f454,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK5(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | m1_subset_1(sK9(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f453])).

fof(f453,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK5(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | m1_subset_1(sK9(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f342,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f342,plain,(
    ! [X14,X12,X13,X11] :
      ( r1_orders_2(X11,sK5(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13),X14)
      | ~ m1_subset_1(sK5(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13),u1_struct_0(X11))
      | ~ r3_waybel_9(X11,X12,X14)
      | m1_subset_1(sK9(X11),u1_struct_0(X11))
      | ~ m1_subset_1(X14,u1_struct_0(X11))
      | ~ l1_waybel_0(X12,X11)
      | ~ v7_waybel_0(X12)
      | ~ v4_orders_2(X12)
      | v2_struct_0(X12)
      | ~ l1_waybel_9(X11)
      | ~ v1_compts_1(X11)
      | ~ v2_lattice3(X11)
      | ~ v1_lattice3(X11)
      | ~ v5_orders_2(X11)
      | ~ v4_orders_2(X11)
      | ~ v3_orders_2(X11)
      | ~ v8_pre_topc(X11)
      | ~ v2_pre_topc(X11)
      | r2_yellow_0(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)))
      | ~ r1_lattice3(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13)
      | ~ m1_subset_1(X13,u1_struct_0(X11)) ) ),
    inference(subsumption_resolution,[],[f337,f76])).

fof(f337,plain,(
    ! [X14,X12,X13,X11] :
      ( r1_orders_2(X11,sK5(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13),X14)
      | ~ m1_subset_1(sK5(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13),u1_struct_0(X11))
      | ~ r3_waybel_9(X11,X12,X14)
      | m1_subset_1(sK9(X11),u1_struct_0(X11))
      | ~ m1_subset_1(X14,u1_struct_0(X11))
      | ~ l1_waybel_0(X12,X11)
      | ~ v7_waybel_0(X12)
      | ~ v4_orders_2(X12)
      | v2_struct_0(X12)
      | ~ l1_waybel_9(X11)
      | ~ v1_compts_1(X11)
      | ~ v2_lattice3(X11)
      | ~ v1_lattice3(X11)
      | ~ v5_orders_2(X11)
      | ~ v4_orders_2(X11)
      | ~ v3_orders_2(X11)
      | ~ v8_pre_topc(X11)
      | ~ v2_pre_topc(X11)
      | r2_yellow_0(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)))
      | ~ r1_lattice3(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13)
      | ~ m1_subset_1(X13,u1_struct_0(X11))
      | ~ l1_orders_2(X11) ) ),
    inference(duplicate_literal_removal,[],[f336])).

fof(f336,plain,(
    ! [X14,X12,X13,X11] :
      ( r1_orders_2(X11,sK5(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13),X14)
      | ~ m1_subset_1(sK5(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13),u1_struct_0(X11))
      | ~ r3_waybel_9(X11,X12,X14)
      | m1_subset_1(sK9(X11),u1_struct_0(X11))
      | ~ m1_subset_1(X14,u1_struct_0(X11))
      | ~ l1_waybel_0(X12,X11)
      | ~ v7_waybel_0(X12)
      | ~ v4_orders_2(X12)
      | v2_struct_0(X12)
      | ~ l1_waybel_9(X11)
      | ~ v1_compts_1(X11)
      | ~ v2_lattice3(X11)
      | ~ v1_lattice3(X11)
      | ~ v5_orders_2(X11)
      | ~ v4_orders_2(X11)
      | ~ v3_orders_2(X11)
      | ~ v8_pre_topc(X11)
      | ~ v2_pre_topc(X11)
      | r2_yellow_0(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)))
      | ~ r1_lattice3(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13)
      | ~ m1_subset_1(X13,u1_struct_0(X11))
      | ~ l1_orders_2(X11)
      | ~ v5_orders_2(X11) ) ),
    inference(resolution,[],[f100,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK5(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f100,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | r1_orders_2(X0,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | m1_subset_1(sK9(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X4,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | m1_subset_1(sK9(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | m1_subset_1(sK9(X0),u1_struct_0(X0))
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r1_orders_2(X0,X4,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ( ~ v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0)
                    & m1_subset_1(sK9(X0),u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f53,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X5] :
          ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0)
        & m1_subset_1(sK9(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r1_orders_2(X0,X4,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X5] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X5),X0,X0)
                      & m1_subset_1(X5,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X5,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X5,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X0))
                       => ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                         => r1_orders_2(X0,X5,X3) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                         => r1_orders_2(X0,X4,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l52_waybel_9)).

fof(f528,plain,(
    ! [X0,X1] :
      ( ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f527,f65])).

fof(f527,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f526,f56])).

fof(f526,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f525,f57])).

fof(f525,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f524,f58])).

fof(f524,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f523,f59])).

fof(f523,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f522,f60])).

fof(f522,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f521,f61])).

fof(f521,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f520,f62])).

fof(f520,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f519,f63])).

fof(f519,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f518,f64])).

fof(f518,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f517,f65])).

fof(f517,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_pre_topc(k4_waybel_1(X1,sK9(X1)),X1,X1)
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_waybel_9(X1)
      | ~ v1_compts_1(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v8_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r3_waybel_9(X1,X2,X0)
      | ~ v11_waybel_0(X2,X1)
      | ~ v5_pre_topc(k4_waybel_1(X1,sK8(X1)),X1,X1)
      | r2_waybel_9(X1,X2) ) ),
    inference(subsumption_resolution,[],[f516,f76])).

fof(f516,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_waybel_9(X1)
      | ~ v1_compts_1(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v8_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ v5_pre_topc(k4_waybel_1(X1,sK9(X1)),X1,X1)
      | ~ r3_waybel_9(X1,X2,X0)
      | ~ v11_waybel_0(X2,X1)
      | ~ v5_pre_topc(k4_waybel_1(X1,sK8(X1)),X1,X1)
      | r2_waybel_9(X1,X2)
      | ~ l1_orders_2(X1) ) ),
    inference(duplicate_literal_removal,[],[f515])).

fof(f515,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_waybel_9(X1)
      | ~ v1_compts_1(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v8_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ v5_pre_topc(k4_waybel_1(X1,sK9(X1)),X1,X1)
      | ~ r3_waybel_9(X1,X2,X0)
      | ~ v11_waybel_0(X2,X1)
      | ~ v5_pre_topc(k4_waybel_1(X1,sK8(X1)),X1,X1)
      | r2_waybel_9(X1,X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f499,f74])).

fof(f499,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0)
      | ~ r3_waybel_9(X0,X2,X1)
      | ~ v11_waybel_0(X2,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f492])).

fof(f492,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)))
      | ~ r3_waybel_9(X0,X2,X1)
      | ~ r3_waybel_9(X0,X2,X1)
      | ~ v11_waybel_0(X2,X0)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f491,f103])).

fof(f491,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ r3_waybel_9(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f490,f76])).

fof(f490,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f489])).

fof(f489,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
      | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f474,f87])).

fof(f474,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK5(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2) ) ),
    inference(subsumption_resolution,[],[f473,f76])).

fof(f473,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK5(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f472])).

fof(f472,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK5(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f352,f89])).

fof(f352,plain,(
    ! [X14,X12,X13,X11] :
      ( r1_orders_2(X11,sK5(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13),X14)
      | ~ m1_subset_1(sK5(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13),u1_struct_0(X11))
      | ~ r3_waybel_9(X11,X12,X14)
      | ~ v5_pre_topc(k4_waybel_1(X11,sK9(X11)),X11,X11)
      | ~ m1_subset_1(X14,u1_struct_0(X11))
      | ~ l1_waybel_0(X12,X11)
      | ~ v7_waybel_0(X12)
      | ~ v4_orders_2(X12)
      | v2_struct_0(X12)
      | ~ l1_waybel_9(X11)
      | ~ v1_compts_1(X11)
      | ~ v2_lattice3(X11)
      | ~ v1_lattice3(X11)
      | ~ v5_orders_2(X11)
      | ~ v4_orders_2(X11)
      | ~ v3_orders_2(X11)
      | ~ v8_pre_topc(X11)
      | ~ v2_pre_topc(X11)
      | r2_yellow_0(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)))
      | ~ r1_lattice3(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13)
      | ~ m1_subset_1(X13,u1_struct_0(X11)) ) ),
    inference(subsumption_resolution,[],[f347,f76])).

fof(f347,plain,(
    ! [X14,X12,X13,X11] :
      ( r1_orders_2(X11,sK5(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13),X14)
      | ~ m1_subset_1(sK5(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13),u1_struct_0(X11))
      | ~ r3_waybel_9(X11,X12,X14)
      | ~ v5_pre_topc(k4_waybel_1(X11,sK9(X11)),X11,X11)
      | ~ m1_subset_1(X14,u1_struct_0(X11))
      | ~ l1_waybel_0(X12,X11)
      | ~ v7_waybel_0(X12)
      | ~ v4_orders_2(X12)
      | v2_struct_0(X12)
      | ~ l1_waybel_9(X11)
      | ~ v1_compts_1(X11)
      | ~ v2_lattice3(X11)
      | ~ v1_lattice3(X11)
      | ~ v5_orders_2(X11)
      | ~ v4_orders_2(X11)
      | ~ v3_orders_2(X11)
      | ~ v8_pre_topc(X11)
      | ~ v2_pre_topc(X11)
      | r2_yellow_0(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)))
      | ~ r1_lattice3(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13)
      | ~ m1_subset_1(X13,u1_struct_0(X11))
      | ~ l1_orders_2(X11) ) ),
    inference(duplicate_literal_removal,[],[f346])).

fof(f346,plain,(
    ! [X14,X12,X13,X11] :
      ( r1_orders_2(X11,sK5(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13),X14)
      | ~ m1_subset_1(sK5(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13),u1_struct_0(X11))
      | ~ r3_waybel_9(X11,X12,X14)
      | ~ v5_pre_topc(k4_waybel_1(X11,sK9(X11)),X11,X11)
      | ~ m1_subset_1(X14,u1_struct_0(X11))
      | ~ l1_waybel_0(X12,X11)
      | ~ v7_waybel_0(X12)
      | ~ v4_orders_2(X12)
      | v2_struct_0(X12)
      | ~ l1_waybel_9(X11)
      | ~ v1_compts_1(X11)
      | ~ v2_lattice3(X11)
      | ~ v1_lattice3(X11)
      | ~ v5_orders_2(X11)
      | ~ v4_orders_2(X11)
      | ~ v3_orders_2(X11)
      | ~ v8_pre_topc(X11)
      | ~ v2_pre_topc(X11)
      | r2_yellow_0(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)))
      | ~ r1_lattice3(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13)
      | ~ m1_subset_1(X13,u1_struct_0(X11))
      | ~ l1_orders_2(X11)
      | ~ v5_orders_2(X11) ) ),
    inference(resolution,[],[f101,f88])).

fof(f101,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | r1_orders_2(X0,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X4,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X4,X3)
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f556,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f555,f56])).

fof(f555,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f554,f57])).

fof(f554,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f553,f58])).

fof(f553,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f552,f59])).

fof(f552,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f551,f60])).

fof(f551,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f550,f61])).

fof(f550,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f549,f62])).

fof(f549,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f548,f63])).

fof(f548,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f543,f64])).

fof(f543,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f542])).

fof(f542,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,X0,X1)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ) ),
    inference(condensation,[],[f541])).

fof(f541,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X2)
      | m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f540])).

fof(f540,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X2)
      | ~ v11_waybel_0(X0,sK0)
      | m1_subset_1(sK8(sK0),u1_struct_0(sK0))
      | r2_waybel_9(sK0,X0) ) ),
    inference(condensation,[],[f538])).

fof(f538,plain,(
    ! [X12,X10,X11,X9] :
      ( ~ v4_orders_2(X9)
      | v2_struct_0(X9)
      | ~ r3_waybel_9(sK0,X9,X10)
      | ~ v11_waybel_0(X9,sK0)
      | ~ l1_waybel_0(X9,sK0)
      | r2_waybel_9(sK0,X9)
      | ~ v7_waybel_0(X9)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ l1_waybel_0(X11,sK0)
      | ~ v7_waybel_0(X11)
      | ~ v4_orders_2(X11)
      | v2_struct_0(X11)
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X12,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X11,X12)
      | ~ v11_waybel_0(X11,sK0)
      | m1_subset_1(sK8(sK0),u1_struct_0(sK0))
      | r2_waybel_9(sK0,X11) ) ),
    inference(resolution,[],[f535,f470])).

fof(f470,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_waybel_9(X1)
      | ~ v1_compts_1(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v8_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r3_waybel_9(X1,X2,X0)
      | ~ v11_waybel_0(X2,X1)
      | m1_subset_1(sK8(X1),u1_struct_0(X1))
      | r2_waybel_9(X1,X2) ) ),
    inference(subsumption_resolution,[],[f469,f76])).

fof(f469,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_waybel_9(X1)
      | ~ v1_compts_1(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v8_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | m1_subset_1(sK9(X1),u1_struct_0(X1))
      | ~ r3_waybel_9(X1,X2,X0)
      | ~ v11_waybel_0(X2,X1)
      | m1_subset_1(sK8(X1),u1_struct_0(X1))
      | r2_waybel_9(X1,X2)
      | ~ l1_orders_2(X1) ) ),
    inference(duplicate_literal_removal,[],[f468])).

fof(f468,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_waybel_9(X1)
      | ~ v1_compts_1(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v8_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | m1_subset_1(sK9(X1),u1_struct_0(X1))
      | ~ r3_waybel_9(X1,X2,X0)
      | ~ v11_waybel_0(X2,X1)
      | m1_subset_1(sK8(X1),u1_struct_0(X1))
      | r2_waybel_9(X1,X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f465,f74])).

fof(f465,plain,(
    ! [X4,X5,X3] :
      ( r2_yellow_0(X3,k2_relset_1(u1_struct_0(X5),u1_struct_0(X3),u1_waybel_0(X3,X5)))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_waybel_0(X5,X3)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_waybel_9(X3)
      | ~ v1_compts_1(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | ~ v8_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | m1_subset_1(sK9(X3),u1_struct_0(X3))
      | ~ r3_waybel_9(X3,X5,X4)
      | ~ v11_waybel_0(X5,X3)
      | m1_subset_1(sK8(X3),u1_struct_0(X3)) ) ),
    inference(duplicate_literal_removal,[],[f460])).

fof(f460,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(sK9(X3),u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_waybel_0(X5,X3)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_waybel_9(X3)
      | ~ v1_compts_1(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | ~ v8_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | r2_yellow_0(X3,k2_relset_1(u1_struct_0(X5),u1_struct_0(X3),u1_waybel_0(X3,X5)))
      | ~ r3_waybel_9(X3,X5,X4)
      | ~ r3_waybel_9(X3,X5,X4)
      | ~ v11_waybel_0(X5,X3)
      | m1_subset_1(sK8(X3),u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_waybel_0(X5,X3)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_waybel_9(X3)
      | ~ v1_compts_1(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | ~ v8_pre_topc(X3)
      | ~ v2_pre_topc(X3) ) ),
    inference(resolution,[],[f458,f102])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v11_waybel_0(X1,X0)
      | m1_subset_1(sK8(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ v11_waybel_0(X1,X0)
      | m1_subset_1(sK8(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ v11_waybel_0(X1,X0)
      | m1_subset_1(sK8(X0),u1_struct_0(X0))
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f535,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0))
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ r3_waybel_9(sK0,X1,X0)
      | ~ v11_waybel_0(X1,sK0)
      | ~ l1_waybel_0(X1,sK0)
      | r2_waybel_9(sK0,X1)
      | ~ v7_waybel_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f534])).

fof(f534,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ r3_waybel_9(sK0,X1,X0)
      | ~ v11_waybel_0(X1,sK0)
      | ~ l1_waybel_0(X1,sK0)
      | r2_waybel_9(sK0,X1)
      | ~ v7_waybel_0(X1)
      | ~ r3_waybel_9(sK0,X1,X0)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ) ),
    inference(condensation,[],[f533])).

fof(f533,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X2)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f532])).

fof(f532,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ v7_waybel_0(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X2)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ) ),
    inference(condensation,[],[f530])).

fof(f530,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ v7_waybel_0(X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X2,X3)
      | ~ v11_waybel_0(X2,sK0)
      | ~ l1_waybel_0(X2,sK0)
      | r2_waybel_9(sK0,X2)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f529,f513])).

fof(f513,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK8(sK0),u1_struct_0(sK0))
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f512,f56])).

fof(f512,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | m1_subset_1(sK8(sK0),u1_struct_0(sK0))
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f511,f57])).

fof(f511,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | m1_subset_1(sK8(sK0),u1_struct_0(sK0))
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f510,f58])).

fof(f510,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | m1_subset_1(sK8(sK0),u1_struct_0(sK0))
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f509,f59])).

fof(f509,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | m1_subset_1(sK8(sK0),u1_struct_0(sK0))
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f508,f60])).

fof(f508,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | m1_subset_1(sK8(sK0),u1_struct_0(sK0))
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f507,f61])).

fof(f507,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | m1_subset_1(sK8(sK0),u1_struct_0(sK0))
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f506,f62])).

fof(f506,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | m1_subset_1(sK8(sK0),u1_struct_0(sK0))
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f505,f63])).

fof(f505,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | m1_subset_1(sK8(sK0),u1_struct_0(sK0))
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f504,f64])).

fof(f504,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_9(sK0)
      | ~ v1_compts_1(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v8_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X0,X1)
      | ~ v11_waybel_0(X0,sK0)
      | m1_subset_1(sK8(sK0),u1_struct_0(sK0))
      | r2_waybel_9(sK0,X0)
      | ~ m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f503,f65])).

fof(f503,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_pre_topc(k4_waybel_1(X1,sK9(X1)),X1,X1)
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_waybel_9(X1)
      | ~ v1_compts_1(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v8_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r3_waybel_9(X1,X2,X0)
      | ~ v11_waybel_0(X2,X1)
      | m1_subset_1(sK8(X1),u1_struct_0(X1))
      | r2_waybel_9(X1,X2) ) ),
    inference(subsumption_resolution,[],[f502,f76])).

fof(f502,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_waybel_9(X1)
      | ~ v1_compts_1(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v8_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ v5_pre_topc(k4_waybel_1(X1,sK9(X1)),X1,X1)
      | ~ r3_waybel_9(X1,X2,X0)
      | ~ v11_waybel_0(X2,X1)
      | m1_subset_1(sK8(X1),u1_struct_0(X1))
      | r2_waybel_9(X1,X2)
      | ~ l1_orders_2(X1) ) ),
    inference(duplicate_literal_removal,[],[f501])).

fof(f501,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_waybel_9(X1)
      | ~ v1_compts_1(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v8_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ v5_pre_topc(k4_waybel_1(X1,sK9(X1)),X1,X1)
      | ~ r3_waybel_9(X1,X2,X0)
      | ~ v11_waybel_0(X2,X1)
      | m1_subset_1(sK8(X1),u1_struct_0(X1))
      | r2_waybel_9(X1,X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f498,f74])).

fof(f498,plain,(
    ! [X4,X5,X3] :
      ( r2_yellow_0(X3,k2_relset_1(u1_struct_0(X5),u1_struct_0(X3),u1_waybel_0(X3,X5)))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_waybel_0(X5,X3)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_waybel_9(X3)
      | ~ v1_compts_1(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | ~ v8_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | ~ v5_pre_topc(k4_waybel_1(X3,sK9(X3)),X3,X3)
      | ~ r3_waybel_9(X3,X5,X4)
      | ~ v11_waybel_0(X5,X3)
      | m1_subset_1(sK8(X3),u1_struct_0(X3)) ) ),
    inference(duplicate_literal_removal,[],[f493])).

fof(f493,plain,(
    ! [X4,X5,X3] :
      ( ~ v5_pre_topc(k4_waybel_1(X3,sK9(X3)),X3,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_waybel_0(X5,X3)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_waybel_9(X3)
      | ~ v1_compts_1(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | ~ v8_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | r2_yellow_0(X3,k2_relset_1(u1_struct_0(X5),u1_struct_0(X3),u1_waybel_0(X3,X5)))
      | ~ r3_waybel_9(X3,X5,X4)
      | ~ r3_waybel_9(X3,X5,X4)
      | ~ v11_waybel_0(X5,X3)
      | m1_subset_1(sK8(X3),u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_waybel_0(X5,X3)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_waybel_9(X3)
      | ~ v1_compts_1(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | ~ v8_pre_topc(X3)
      | ~ v2_pre_topc(X3) ) ),
    inference(resolution,[],[f491,f102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:27:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (32059)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.45  % (32059)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f586,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(subsumption_resolution,[],[f585,f104])).
% 0.22/0.45  fof(f104,plain,(
% 0.22/0.45    l1_orders_2(sK0)),
% 0.22/0.45    inference(resolution,[],[f76,f64])).
% 0.22/0.45  fof(f64,plain,(
% 0.22/0.45    l1_waybel_9(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f36])).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    ((~r2_hidden(k1_waybel_9(sK0,sK1),k10_yellow_6(sK0,sK1)) | ~r2_waybel_9(sK0,sK1)) & v11_waybel_0(sK1,sK0) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) & l1_waybel_9(sK0) & v1_compts_1(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f35,f34])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : ((~r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1)) | ~r2_waybel_9(X0,X1)) & v11_waybel_0(X1,X0) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((~r2_hidden(k1_waybel_9(sK0,X1),k10_yellow_6(sK0,X1)) | ~r2_waybel_9(sK0,X1)) & v11_waybel_0(X1,sK0) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) & l1_waybel_9(sK0) & v1_compts_1(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & v8_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f35,plain,(
% 0.22/0.45    ? [X1] : ((~r2_hidden(k1_waybel_9(sK0,X1),k10_yellow_6(sK0,X1)) | ~r2_waybel_9(sK0,X1)) & v11_waybel_0(X1,sK0) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ((~r2_hidden(k1_waybel_9(sK0,sK1),k10_yellow_6(sK0,sK1)) | ~r2_waybel_9(sK0,sK1)) & v11_waybel_0(sK1,sK0) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : ((~r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1)) | ~r2_waybel_9(X0,X1)) & v11_waybel_0(X1,X0) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & ! [X2] : (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.45    inference(rectify,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ? [X0] : (? [X2] : ((~r2_hidden(k1_waybel_9(X0,X2),k10_yellow_6(X0,X2)) | ~r2_waybel_9(X0,X2)) & v11_waybel_0(X2,X0) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & ! [X1] : (v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.45    inference(flattening,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ? [X0] : ((? [X2] : (((~r2_hidden(k1_waybel_9(X0,X2),k10_yellow_6(X0,X2)) | ~r2_waybel_9(X0,X2)) & v11_waybel_0(X2,X0)) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & ! [X1] : (v5_pre_topc(k4_waybel_1(X0,X1),X0,X0) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (v11_waybel_0(X2,X0) => (r2_hidden(k1_waybel_9(X0,X2),k10_yellow_6(X0,X2)) & r2_waybel_9(X0,X2))))))),
% 0.22/0.45    inference(rectify,[],[f11])).
% 0.22/0.45  fof(f11,negated_conjecture,(
% 0.22/0.45    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v11_waybel_0(X1,X0) => (r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1)) & r2_waybel_9(X0,X1))))))),
% 0.22/0.45    inference(negated_conjecture,[],[f10])).
% 0.22/0.45  fof(f10,conjecture,(
% 0.22/0.45    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X1),X0,X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v11_waybel_0(X1,X0) => (r2_hidden(k1_waybel_9(X0,X1),k10_yellow_6(X0,X1)) & r2_waybel_9(X0,X1))))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_waybel_9)).
% 0.22/0.45  fof(f76,plain,(
% 0.22/0.45    ( ! [X0] : (~l1_waybel_9(X0) | l1_orders_2(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).
% 0.22/0.45  fof(f585,plain,(
% 0.22/0.45    ~l1_orders_2(sK0)),
% 0.22/0.45    inference(subsumption_resolution,[],[f584,f61])).
% 0.22/0.45  fof(f61,plain,(
% 0.22/0.45    v1_lattice3(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f36])).
% 0.22/0.45  fof(f584,plain,(
% 0.22/0.45    ~v1_lattice3(sK0) | ~l1_orders_2(sK0)),
% 0.22/0.45    inference(resolution,[],[f583,f72])).
% 0.22/0.45  fof(f72,plain,(
% 0.22/0.45    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.22/0.45    inference(flattening,[],[f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.22/0.45  fof(f583,plain,(
% 0.22/0.45    v2_struct_0(sK0)),
% 0.22/0.45    inference(subsumption_resolution,[],[f582,f64])).
% 0.22/0.45  fof(f582,plain,(
% 0.22/0.45    v2_struct_0(sK0) | ~l1_waybel_9(sK0)),
% 0.22/0.45    inference(resolution,[],[f581,f75])).
% 0.22/0.45  fof(f75,plain,(
% 0.22/0.45    ( ! [X0] : (l1_pre_topc(X0) | ~l1_waybel_9(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  fof(f581,plain,(
% 0.22/0.45    ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.45    inference(subsumption_resolution,[],[f580,f311])).
% 0.22/0.45  fof(f311,plain,(
% 0.22/0.45    ~r2_waybel_9(sK0,sK1) | v2_struct_0(sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.45    inference(subsumption_resolution,[],[f310,f56])).
% 0.22/0.45  fof(f56,plain,(
% 0.22/0.45    v2_pre_topc(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f36])).
% 0.22/0.45  fof(f310,plain,(
% 0.22/0.45    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~v2_pre_topc(sK0)),
% 0.22/0.45    inference(subsumption_resolution,[],[f309,f57])).
% 0.22/0.45  fof(f57,plain,(
% 0.22/0.45    v8_pre_topc(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f36])).
% 0.22/0.45  fof(f309,plain,(
% 0.22/0.45    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.45    inference(subsumption_resolution,[],[f308,f63])).
% 0.22/0.45  fof(f63,plain,(
% 0.22/0.45    v1_compts_1(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f36])).
% 0.22/0.45  fof(f308,plain,(
% 0.22/0.45    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.45    inference(subsumption_resolution,[],[f307,f66])).
% 0.22/0.45  fof(f66,plain,(
% 0.22/0.45    ~v2_struct_0(sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f36])).
% 0.22/0.45  fof(f307,plain,(
% 0.22/0.45    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.45    inference(subsumption_resolution,[],[f306,f67])).
% 0.22/0.45  fof(f67,plain,(
% 0.22/0.45    v4_orders_2(sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f36])).
% 0.22/0.45  fof(f306,plain,(
% 0.22/0.45    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.45    inference(subsumption_resolution,[],[f305,f68])).
% 0.22/0.45  fof(f68,plain,(
% 0.22/0.45    v7_waybel_0(sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f36])).
% 0.22/0.45  fof(f305,plain,(
% 0.22/0.45    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.45    inference(subsumption_resolution,[],[f304,f69])).
% 0.22/0.45  fof(f69,plain,(
% 0.22/0.45    l1_waybel_0(sK1,sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f36])).
% 0.22/0.45  fof(f304,plain,(
% 0.22/0.45    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.45    inference(duplicate_literal_removal,[],[f299])).
% 0.22/0.45  fof(f299,plain,(
% 0.22/0.45    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.45    inference(resolution,[],[f298,f82])).
% 0.22/0.45  fof(f82,plain,(
% 0.22/0.45    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f43])).
% 0.22/0.45  fof(f43,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : ((r3_waybel_9(X0,X1,sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f42])).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    ! [X1,X0] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r3_waybel_9(X0,X1,sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.45    inference(flattening,[],[f23])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,axiom,(
% 0.22/0.45    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_waybel_9)).
% 0.22/0.45  fof(f298,plain,(
% 0.22/0.45    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1)),
% 0.22/0.45    inference(subsumption_resolution,[],[f297,f56])).
% 0.22/0.45  fof(f297,plain,(
% 0.22/0.45    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~v2_pre_topc(sK0)),
% 0.22/0.45    inference(subsumption_resolution,[],[f296,f57])).
% 0.22/0.45  fof(f296,plain,(
% 0.22/0.45    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.45    inference(subsumption_resolution,[],[f295,f63])).
% 0.22/0.45  fof(f295,plain,(
% 0.22/0.45    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.45    inference(subsumption_resolution,[],[f294,f66])).
% 0.22/0.45  fof(f294,plain,(
% 0.22/0.45    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.45    inference(subsumption_resolution,[],[f293,f67])).
% 0.22/0.45  fof(f293,plain,(
% 0.22/0.45    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.45    inference(subsumption_resolution,[],[f292,f68])).
% 0.22/0.45  fof(f292,plain,(
% 0.22/0.45    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.45    inference(subsumption_resolution,[],[f291,f69])).
% 0.22/0.45  fof(f291,plain,(
% 0.22/0.45    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.45    inference(duplicate_literal_removal,[],[f286])).
% 0.22/0.45  fof(f286,plain,(
% 0.22/0.45    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.45    inference(resolution,[],[f282,f83])).
% 0.22/0.45  fof(f83,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r3_waybel_9(X0,X1,sK4(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f43])).
% 0.22/0.45  fof(f282,plain,(
% 0.22/0.45    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f281,f143])).
% 0.22/0.45  fof(f143,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~r2_waybel_9(sK0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f142,f66])).
% 0.22/0.45  fof(f142,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~r2_waybel_9(sK0,sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f141,f67])).
% 0.22/0.45  fof(f141,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~r2_waybel_9(sK0,sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f140,f68])).
% 0.22/0.45  fof(f140,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~r2_waybel_9(sK0,sK1) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f139,f69])).
% 0.22/0.45  fof(f139,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~r2_waybel_9(sK0,sK1) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f137,f70])).
% 0.22/0.45  fof(f70,plain,(
% 0.22/0.45    v11_waybel_0(sK1,sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f36])).
% 0.22/0.45  fof(f137,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~r2_waybel_9(sK0,sK1) | ~v11_waybel_0(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0)) )),
% 0.22/0.45    inference(superposition,[],[f71,f135])).
% 0.22/0.45  fof(f135,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k1_waybel_9(sK0,X0) = X1 | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f134,f56])).
% 0.22/0.45  fof(f134,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k1_waybel_9(sK0,X0) = X1 | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v2_pre_topc(sK0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f133,f57])).
% 0.22/0.45  fof(f133,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k1_waybel_9(sK0,X0) = X1 | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f132,f58])).
% 0.22/0.45  fof(f58,plain,(
% 0.22/0.45    v3_orders_2(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f36])).
% 0.22/0.45  fof(f132,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k1_waybel_9(sK0,X0) = X1 | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f131,f59])).
% 0.22/0.45  fof(f59,plain,(
% 0.22/0.45    v4_orders_2(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f36])).
% 0.22/0.45  fof(f131,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k1_waybel_9(sK0,X0) = X1 | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f130,f60])).
% 0.22/0.45  fof(f60,plain,(
% 0.22/0.45    v5_orders_2(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f36])).
% 0.22/0.45  fof(f130,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k1_waybel_9(sK0,X0) = X1 | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f129,f61])).
% 0.22/0.45  fof(f129,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k1_waybel_9(sK0,X0) = X1 | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f128,f62])).
% 0.22/0.45  fof(f62,plain,(
% 0.22/0.45    v2_lattice3(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f36])).
% 0.22/0.45  fof(f128,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k1_waybel_9(sK0,X0) = X1 | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f127,f63])).
% 0.22/0.45  fof(f127,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k1_waybel_9(sK0,X0) = X1 | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f126,f64])).
% 0.22/0.45  fof(f126,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k1_waybel_9(sK0,X0) = X1 | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.45    inference(duplicate_literal_removal,[],[f125])).
% 0.22/0.45  fof(f125,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k1_waybel_9(sK0,X0) = X1 | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.45    inference(condensation,[],[f124])).
% 0.22/0.45  fof(f124,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~v11_waybel_0(X0,sK0) | k1_waybel_9(sK0,X0) = X1 | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~r3_waybel_9(sK0,X0,X2) | k1_waybel_9(sK0,X0) = X2 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.45    inference(duplicate_literal_removal,[],[f123])).
% 0.22/0.45  fof(f123,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~v11_waybel_0(X0,sK0) | k1_waybel_9(sK0,X0) = X1 | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~r3_waybel_9(sK0,X0,X2) | k1_waybel_9(sK0,X0) = X2 | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.45    inference(condensation,[],[f122])).
% 0.22/0.45  fof(f122,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (~v11_waybel_0(X0,sK0) | k1_waybel_9(sK0,X0) = X1 | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~r3_waybel_9(sK0,X2,X3) | ~v11_waybel_0(X2,sK0) | k1_waybel_9(sK0,X2) = X3 | ~l1_waybel_0(X2,sK0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.45    inference(resolution,[],[f121,f90])).
% 0.22/0.45  fof(f90,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0),u1_struct_0(X0)) | ~r3_waybel_9(X0,X2,X1) | ~v11_waybel_0(X2,X0) | k1_waybel_9(X0,X2) = X1 | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f50])).
% 0.22/0.45  fof(f50,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (! [X2] : (k1_waybel_9(X0,X2) = X1 | ~r3_waybel_9(X0,X2,X1) | ~v11_waybel_0(X2,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) & m1_subset_1(sK7(X0),u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f49])).
% 0.22/0.45  fof(f49,plain,(
% 0.22/0.45    ! [X0] : (? [X3] : (~v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) & m1_subset_1(X3,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) & m1_subset_1(sK7(X0),u1_struct_0(X0))))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (! [X2] : (k1_waybel_9(X0,X2) = X1 | ~r3_waybel_9(X0,X2,X1) | ~v11_waybel_0(X2,X0) | ? [X3] : (~v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) & m1_subset_1(X3,u1_struct_0(X0))) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.45    inference(flattening,[],[f27])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (! [X2] : ((k1_waybel_9(X0,X2) = X1 | (~r3_waybel_9(X0,X2,X1) | ~v11_waybel_0(X2,X0) | ? [X3] : (~v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) & m1_subset_1(X3,u1_struct_0(X0))))) | (~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,axiom,(
% 0.22/0.45    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_9(X0,X2) = X1))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_waybel_9)).
% 0.22/0.45  fof(f121,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~m1_subset_1(sK7(sK0),u1_struct_0(sK0)) | ~v11_waybel_0(X0,sK0) | k1_waybel_9(sK0,X0) = X1 | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f120,f56])).
% 0.22/0.45  fof(f120,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | k1_waybel_9(sK0,X0) = X1 | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK7(sK0),u1_struct_0(sK0))) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f119,f57])).
% 0.22/0.45  fof(f119,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | k1_waybel_9(sK0,X0) = X1 | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK7(sK0),u1_struct_0(sK0))) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f118,f58])).
% 0.22/0.45  fof(f118,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | k1_waybel_9(sK0,X0) = X1 | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK7(sK0),u1_struct_0(sK0))) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f117,f59])).
% 0.22/0.45  fof(f117,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | k1_waybel_9(sK0,X0) = X1 | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK7(sK0),u1_struct_0(sK0))) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f116,f60])).
% 0.22/0.45  fof(f116,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | k1_waybel_9(sK0,X0) = X1 | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK7(sK0),u1_struct_0(sK0))) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f115,f61])).
% 0.22/0.45  fof(f115,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | k1_waybel_9(sK0,X0) = X1 | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK7(sK0),u1_struct_0(sK0))) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f114,f62])).
% 0.22/0.45  fof(f114,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | k1_waybel_9(sK0,X0) = X1 | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK7(sK0),u1_struct_0(sK0))) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f113,f63])).
% 0.22/0.45  fof(f113,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | k1_waybel_9(sK0,X0) = X1 | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK7(sK0),u1_struct_0(sK0))) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f112,f64])).
% 0.22/0.45  fof(f112,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | k1_waybel_9(sK0,X0) = X1 | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK7(sK0),u1_struct_0(sK0))) )),
% 0.22/0.45    inference(resolution,[],[f91,f65])).
% 0.22/0.45  fof(f65,plain,(
% 0.22/0.45    ( ! [X2] : (v5_pre_topc(k4_waybel_1(sK0,X2),sK0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f36])).
% 0.22/0.45  fof(f91,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~v5_pre_topc(k4_waybel_1(X0,sK7(X0)),X0,X0) | ~r3_waybel_9(X0,X2,X1) | ~v11_waybel_0(X2,X0) | k1_waybel_9(X0,X2) = X1 | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f50])).
% 0.22/0.45  fof(f71,plain,(
% 0.22/0.45    ~r2_hidden(k1_waybel_9(sK0,sK1),k10_yellow_6(sK0,sK1)) | ~r2_waybel_9(sK0,sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f36])).
% 0.22/0.45  fof(f281,plain,(
% 0.22/0.45    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1)) )),
% 0.22/0.45    inference(duplicate_literal_removal,[],[f280])).
% 0.22/0.45  fof(f280,plain,(
% 0.22/0.45    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_waybel_9(sK0,sK1)) )),
% 0.22/0.45    inference(condensation,[],[f279])).
% 0.22/0.45  fof(f279,plain,(
% 0.22/0.45    ( ! [X2,X3] : (~r3_waybel_9(sK0,sK1,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,k10_yellow_6(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X2)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f278,f193])).
% 0.22/0.45  fof(f193,plain,(
% 0.22/0.45    ( ! [X0] : (sK2(sK0,sK1) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f192,f70])).
% 0.22/0.45  fof(f192,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v11_waybel_0(sK1,sK0) | sK2(sK0,sK1) = X0 | ~r3_waybel_9(sK0,sK1,X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f191,f66])).
% 0.22/0.45  fof(f191,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK1) | ~v11_waybel_0(sK1,sK0) | sK2(sK0,sK1) = X0 | ~r3_waybel_9(sK0,sK1,X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f190,f67])).
% 0.22/0.45  fof(f190,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v11_waybel_0(sK1,sK0) | sK2(sK0,sK1) = X0 | ~r3_waybel_9(sK0,sK1,X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f189,f68])).
% 0.22/0.45  fof(f189,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v11_waybel_0(sK1,sK0) | sK2(sK0,sK1) = X0 | ~r3_waybel_9(sK0,sK1,X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f183,f69])).
% 0.22/0.45  fof(f183,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v11_waybel_0(sK1,sK0) | sK2(sK0,sK1) = X0 | ~r3_waybel_9(sK0,sK1,X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1)) )),
% 0.22/0.45    inference(duplicate_literal_removal,[],[f182])).
% 0.22/0.45  fof(f182,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v11_waybel_0(sK1,sK0) | sK2(sK0,sK1) = X0 | ~r3_waybel_9(sK0,sK1,X0) | ~r3_waybel_9(sK0,sK1,X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1)) )),
% 0.22/0.45    inference(condensation,[],[f181])).
% 0.22/0.45  fof(f181,plain,(
% 0.22/0.45    ( ! [X2,X1] : (~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v11_waybel_0(sK1,sK0) | sK2(sK0,sK1) = X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1)) )),
% 0.22/0.45    inference(duplicate_literal_removal,[],[f180])).
% 0.22/0.45  fof(f180,plain,(
% 0.22/0.45    ( ! [X2,X1] : (~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v11_waybel_0(sK1,sK0) | sK2(sK0,sK1) = X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X2)) )),
% 0.22/0.45    inference(resolution,[],[f178,f143])).
% 0.22/0.45  fof(f178,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (r2_hidden(X1,k10_yellow_6(sK0,X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | sK2(sK0,X0) = X2 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f177,f56])).
% 0.22/0.45  fof(f177,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | sK2(sK0,X0) = X2 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k10_yellow_6(sK0,X0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f176,f57])).
% 0.22/0.45  fof(f176,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | sK2(sK0,X0) = X2 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k10_yellow_6(sK0,X0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f175,f63])).
% 0.22/0.45  fof(f175,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | sK2(sK0,X0) = X2 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k10_yellow_6(sK0,X0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.45    inference(duplicate_literal_removal,[],[f174])).
% 0.22/0.45  fof(f174,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | sK2(sK0,X0) = X2 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k10_yellow_6(sK0,X0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k10_yellow_6(sK0,X0)) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.45    inference(condensation,[],[f173])).
% 0.22/0.45  fof(f173,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | sK2(sK0,X0) = X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~r3_waybel_9(sK0,X0,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r2_hidden(X2,k10_yellow_6(sK0,X0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r3_waybel_9(sK0,X0,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,k10_yellow_6(sK0,X0)) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.45    inference(duplicate_literal_removal,[],[f172])).
% 0.22/0.45  fof(f172,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | sK2(sK0,X0) = X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~r3_waybel_9(sK0,X0,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r2_hidden(X2,k10_yellow_6(sK0,X0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r3_waybel_9(sK0,X0,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,k10_yellow_6(sK0,X0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.45    inference(resolution,[],[f155,f77])).
% 0.22/0.45  fof(f77,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f41])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ((sK2(X0,X1) != sK3(X0,X1) & r3_waybel_9(X0,X1,sK3(X0,X1)) & r3_waybel_9(X0,X1,sK2(X0,X1)) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f38,f40,f39])).
% 0.22/0.45  fof(f39,plain,(
% 0.22/0.45    ! [X1,X0] : (? [X3] : (? [X4] : (X3 != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,X3) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (? [X4] : (sK2(X0,X1) != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,sK2(X0,X1)) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    ! [X1,X0] : (? [X4] : (sK2(X0,X1) != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,sK2(X0,X1)) & m1_subset_1(X4,u1_struct_0(X0))) => (sK2(X0,X1) != sK3(X0,X1) & r3_waybel_9(X0,X1,sK3(X0,X1)) & r3_waybel_9(X0,X1,sK2(X0,X1)) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f38,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ? [X3] : (? [X4] : (X3 != X4 & r3_waybel_9(X0,X1,X4) & r3_waybel_9(X0,X1,X3) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.45    inference(rectify,[],[f22])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (! [X4] : (r2_hidden(X4,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ? [X2] : (? [X3] : (X2 != X3 & r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.45    inference(flattening,[],[f21])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : ((! [X4] : ((r2_hidden(X4,k10_yellow_6(X0,X1)) | ~r3_waybel_9(X0,X1,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) | ? [X2] : (? [X3] : ((X2 != X3 & (r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2)) => X2 = X3))) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X4) => r2_hidden(X4,k10_yellow_6(X0,X1)))))))),
% 0.22/0.45    inference(rectify,[],[f8])).
% 0.22/0.45  fof(f8,axiom,(
% 0.22/0.45    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2)) => X2 = X3))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) => r2_hidden(X2,k10_yellow_6(X0,X1)))))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_waybel_9)).
% 0.22/0.45  fof(f155,plain,(
% 0.22/0.45    ( ! [X4,X2,X3] : (~m1_subset_1(sK2(sK0,X2),u1_struct_0(sK0)) | ~l1_waybel_0(X2,sK0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~v11_waybel_0(X2,sK0) | sK2(sK0,X2) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X2,X3) | ~r3_waybel_9(sK0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r2_hidden(X4,k10_yellow_6(sK0,X2)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f154,f56])).
% 0.22/0.46  fof(f154,plain,(
% 0.22/0.46    ( ! [X4,X2,X3] : (~v11_waybel_0(X2,sK0) | ~l1_waybel_0(X2,sK0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~m1_subset_1(sK2(sK0,X2),u1_struct_0(sK0)) | sK2(sK0,X2) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X2,X3) | ~r3_waybel_9(sK0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r2_hidden(X4,k10_yellow_6(sK0,X2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f153,f57])).
% 0.22/0.46  fof(f153,plain,(
% 0.22/0.46    ( ! [X4,X2,X3] : (~v11_waybel_0(X2,sK0) | ~l1_waybel_0(X2,sK0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~m1_subset_1(sK2(sK0,X2),u1_struct_0(sK0)) | sK2(sK0,X2) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X2,X3) | ~r3_waybel_9(sK0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r2_hidden(X4,k10_yellow_6(sK0,X2)) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f148,f63])).
% 0.22/0.46  fof(f148,plain,(
% 0.22/0.46    ( ! [X4,X2,X3] : (~v11_waybel_0(X2,sK0) | ~l1_waybel_0(X2,sK0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~m1_subset_1(sK2(sK0,X2),u1_struct_0(sK0)) | sK2(sK0,X2) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X2,X3) | ~r3_waybel_9(sK0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r2_hidden(X4,k10_yellow_6(sK0,X2)) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f145])).
% 0.22/0.46  fof(f145,plain,(
% 0.22/0.46    ( ! [X4,X2,X3] : (~v11_waybel_0(X2,sK0) | ~l1_waybel_0(X2,sK0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~m1_subset_1(sK2(sK0,X2),u1_struct_0(sK0)) | sK2(sK0,X2) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X2,X3) | ~r3_waybel_9(sK0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r2_hidden(X4,k10_yellow_6(sK0,X2)) | ~l1_waybel_0(X2,sK0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.46    inference(resolution,[],[f138,f79])).
% 0.22/0.46  fof(f79,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,sK2(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f41])).
% 0.22/0.46  fof(f138,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~r3_waybel_9(sK0,X0,X2) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | X1 = X2 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f136])).
% 0.22/0.46  fof(f136,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (X1 = X2 | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X2) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1)) )),
% 0.22/0.46    inference(superposition,[],[f135,f135])).
% 0.22/0.46  fof(f278,plain,(
% 0.22/0.46    ( ! [X2,X3] : (sK2(sK0,sK1) != X2 | ~r3_waybel_9(sK0,sK1,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,k10_yellow_6(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X2)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f277,f56])).
% 0.22/0.46  fof(f277,plain,(
% 0.22/0.46    ( ! [X2,X3] : (sK2(sK0,sK1) != X2 | ~r3_waybel_9(sK0,sK1,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,k10_yellow_6(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X2)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f276,f57])).
% 0.22/0.46  fof(f276,plain,(
% 0.22/0.46    ( ! [X2,X3] : (sK2(sK0,sK1) != X2 | ~r3_waybel_9(sK0,sK1,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,k10_yellow_6(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X2)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f275,f63])).
% 0.22/0.46  fof(f275,plain,(
% 0.22/0.46    ( ! [X2,X3] : (sK2(sK0,sK1) != X2 | ~r3_waybel_9(sK0,sK1,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,k10_yellow_6(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X2)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f274,f66])).
% 0.22/0.46  fof(f274,plain,(
% 0.22/0.46    ( ! [X2,X3] : (sK2(sK0,sK1) != X2 | ~r3_waybel_9(sK0,sK1,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,k10_yellow_6(sK0,sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X2)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f273,f67])).
% 0.22/0.46  fof(f273,plain,(
% 0.22/0.46    ( ! [X2,X3] : (sK2(sK0,sK1) != X2 | ~r3_waybel_9(sK0,sK1,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,k10_yellow_6(sK0,sK1)) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X2)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f272,f68])).
% 0.22/0.46  fof(f272,plain,(
% 0.22/0.46    ( ! [X2,X3] : (sK2(sK0,sK1) != X2 | ~r3_waybel_9(sK0,sK1,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,k10_yellow_6(sK0,sK1)) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X2)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f269,f69])).
% 0.22/0.46  fof(f269,plain,(
% 0.22/0.46    ( ! [X2,X3] : (sK2(sK0,sK1) != X2 | ~r3_waybel_9(sK0,sK1,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X2)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f264])).
% 0.22/0.46  fof(f264,plain,(
% 0.22/0.46    ( ! [X2,X3] : (sK2(sK0,sK1) != X2 | ~r3_waybel_9(sK0,sK1,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X3,k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X2)) )),
% 0.22/0.46    inference(superposition,[],[f81,f261])).
% 0.22/0.46  fof(f261,plain,(
% 0.22/0.46    ( ! [X0] : (sK3(sK0,sK1) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X0)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f260])).
% 0.22/0.46  fof(f260,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK3(sK0,sK1) = X0 | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~r3_waybel_9(sK0,sK1,X0)) )),
% 0.22/0.46    inference(condensation,[],[f259])).
% 0.22/0.46  fof(f259,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK3(sK0,sK1) = X0 | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f258,f143])).
% 0.22/0.46  fof(f258,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK3(sK0,sK1) = X0 | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k10_yellow_6(sK0,sK1))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f257,f56])).
% 0.22/0.46  fof(f257,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK3(sK0,sK1) = X0 | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k10_yellow_6(sK0,sK1)) | ~v2_pre_topc(sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f256,f57])).
% 0.22/0.46  fof(f256,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK3(sK0,sK1) = X0 | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k10_yellow_6(sK0,sK1)) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f255,f63])).
% 0.22/0.46  fof(f255,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK3(sK0,sK1) = X0 | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k10_yellow_6(sK0,sK1)) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f254,f66])).
% 0.22/0.46  fof(f254,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK3(sK0,sK1) = X0 | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k10_yellow_6(sK0,sK1)) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f253,f67])).
% 0.22/0.46  fof(f253,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK3(sK0,sK1) = X0 | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k10_yellow_6(sK0,sK1)) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f252,f68])).
% 0.22/0.46  fof(f252,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK3(sK0,sK1) = X0 | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k10_yellow_6(sK0,sK1)) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f251,f69])).
% 0.22/0.46  fof(f251,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK3(sK0,sK1) = X0 | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f250])).
% 0.22/0.46  fof(f250,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK3(sK0,sK1) = X0 | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.46    inference(resolution,[],[f224,f78])).
% 0.22/0.46  fof(f78,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f41])).
% 0.22/0.46  fof(f224,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK3(sK0,sK1) = X0 | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X0)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f223])).
% 0.22/0.46  fof(f223,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | sK3(sK0,sK1) = X0 | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~r3_waybel_9(sK0,sK1,X0) | ~r3_waybel_9(sK0,sK1,X0)) )),
% 0.22/0.46    inference(condensation,[],[f222])).
% 0.22/0.46  fof(f222,plain,(
% 0.22/0.46    ( ! [X4,X3] : (~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | sK3(sK0,sK1) = X3 | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X3) | ~r3_waybel_9(sK0,sK1,X4) | ~m1_subset_1(X4,u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f221,f143])).
% 0.22/0.46  fof(f221,plain,(
% 0.22/0.46    ( ! [X4,X3] : (~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | sK3(sK0,sK1) = X3 | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X3) | ~r3_waybel_9(sK0,sK1,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r2_hidden(X4,k10_yellow_6(sK0,sK1))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f220,f56])).
% 0.22/0.46  fof(f220,plain,(
% 0.22/0.46    ( ! [X4,X3] : (~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | sK3(sK0,sK1) = X3 | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X3) | ~r3_waybel_9(sK0,sK1,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r2_hidden(X4,k10_yellow_6(sK0,sK1)) | ~v2_pre_topc(sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f219,f57])).
% 0.22/0.46  fof(f219,plain,(
% 0.22/0.46    ( ! [X4,X3] : (~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | sK3(sK0,sK1) = X3 | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X3) | ~r3_waybel_9(sK0,sK1,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r2_hidden(X4,k10_yellow_6(sK0,sK1)) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f218,f63])).
% 0.22/0.46  fof(f218,plain,(
% 0.22/0.46    ( ! [X4,X3] : (~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | sK3(sK0,sK1) = X3 | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X3) | ~r3_waybel_9(sK0,sK1,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r2_hidden(X4,k10_yellow_6(sK0,sK1)) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f217,f66])).
% 0.22/0.46  fof(f217,plain,(
% 0.22/0.46    ( ! [X4,X3] : (~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | sK3(sK0,sK1) = X3 | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X3) | ~r3_waybel_9(sK0,sK1,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r2_hidden(X4,k10_yellow_6(sK0,sK1)) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f216,f67])).
% 0.22/0.46  fof(f216,plain,(
% 0.22/0.46    ( ! [X4,X3] : (~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | sK3(sK0,sK1) = X3 | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X3) | ~r3_waybel_9(sK0,sK1,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r2_hidden(X4,k10_yellow_6(sK0,sK1)) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f215,f68])).
% 0.22/0.46  fof(f215,plain,(
% 0.22/0.46    ( ! [X4,X3] : (~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | sK3(sK0,sK1) = X3 | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X3) | ~r3_waybel_9(sK0,sK1,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r2_hidden(X4,k10_yellow_6(sK0,sK1)) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f205,f69])).
% 0.22/0.46  fof(f205,plain,(
% 0.22/0.46    ( ! [X4,X3] : (~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | sK3(sK0,sK1) = X3 | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X3) | ~r3_waybel_9(sK0,sK1,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r2_hidden(X4,k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f204])).
% 0.22/0.46  fof(f204,plain,(
% 0.22/0.46    ( ! [X4,X3] : (~m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) | sK3(sK0,sK1) = X3 | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X3) | ~r3_waybel_9(sK0,sK1,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r2_hidden(X4,k10_yellow_6(sK0,sK1)) | ~l1_waybel_0(sK1,sK0) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.46    inference(resolution,[],[f201,f80])).
% 0.22/0.46  fof(f80,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,sK3(X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f41])).
% 0.22/0.46  fof(f201,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r3_waybel_9(sK0,sK1,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | X0 = X1 | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f194])).
% 0.22/0.46  fof(f194,plain,(
% 0.22/0.46    ( ! [X0,X1] : (X0 = X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_9(sK0,sK1)) )),
% 0.22/0.46    inference(superposition,[],[f193,f193])).
% 0.22/0.46  fof(f81,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (sK2(X0,X1) != sK3(X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f41])).
% 0.22/0.46  fof(f580,plain,(
% 0.22/0.46    r2_waybel_9(sK0,sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.46    inference(subsumption_resolution,[],[f579,f67])).
% 0.22/0.46  fof(f579,plain,(
% 0.22/0.46    r2_waybel_9(sK0,sK1) | ~v4_orders_2(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.46    inference(subsumption_resolution,[],[f578,f68])).
% 0.22/0.46  fof(f578,plain,(
% 0.22/0.46    r2_waybel_9(sK0,sK1) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.46    inference(subsumption_resolution,[],[f577,f69])).
% 0.22/0.46  fof(f577,plain,(
% 0.22/0.46    ~l1_waybel_0(sK1,sK0) | r2_waybel_9(sK0,sK1) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.46    inference(subsumption_resolution,[],[f576,f66])).
% 0.22/0.46  fof(f576,plain,(
% 0.22/0.46    v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | r2_waybel_9(sK0,sK1) | ~v7_waybel_0(sK1) | ~v4_orders_2(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.46    inference(resolution,[],[f575,f70])).
% 0.22/0.46  fof(f575,plain,(
% 0.22/0.46    ( ! [X0] : (~v11_waybel_0(X0,sK0) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f574,f56])).
% 0.22/0.46  fof(f574,plain,(
% 0.22/0.46    ( ! [X0] : (v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f573,f57])).
% 0.22/0.46  fof(f573,plain,(
% 0.22/0.46    ( ! [X0] : (v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f572,f63])).
% 0.22/0.46  fof(f572,plain,(
% 0.22/0.46    ( ! [X0] : (v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f567])).
% 0.22/0.46  fof(f567,plain,(
% 0.22/0.46    ( ! [X0] : (v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.46    inference(resolution,[],[f566,f82])).
% 0.22/0.46  fof(f566,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(sK4(sK0,X0),u1_struct_0(sK0)) | v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f565,f56])).
% 0.22/0.46  fof(f565,plain,(
% 0.22/0.46    ( ! [X0] : (~v4_orders_2(X0) | v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~m1_subset_1(sK4(sK0,X0),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f564,f57])).
% 0.22/0.46  fof(f564,plain,(
% 0.22/0.46    ( ! [X0] : (~v4_orders_2(X0) | v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~m1_subset_1(sK4(sK0,X0),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f563,f63])).
% 0.22/0.46  fof(f563,plain,(
% 0.22/0.46    ( ! [X0] : (~v4_orders_2(X0) | v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~m1_subset_1(sK4(sK0,X0),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f558])).
% 0.22/0.46  fof(f558,plain,(
% 0.22/0.46    ( ! [X0] : (~v4_orders_2(X0) | v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~m1_subset_1(sK4(sK0,X0),u1_struct_0(sK0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.46    inference(resolution,[],[f557,f83])).
% 0.22/0.46  fof(f557,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f556,f529])).
% 0.22/0.46  fof(f529,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(sK8(sK0),u1_struct_0(sK0)) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f528,f487])).
% 0.22/0.46  fof(f487,plain,(
% 0.22/0.46    ( ! [X0,X1] : (m1_subset_1(sK9(sK0),u1_struct_0(sK0)) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK8(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f486,f56])).
% 0.22/0.46  fof(f486,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | m1_subset_1(sK9(sK0),u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK8(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f485,f57])).
% 0.22/0.46  fof(f485,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(sK9(sK0),u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK8(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f484,f58])).
% 0.22/0.46  fof(f484,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(sK9(sK0),u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK8(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f483,f59])).
% 0.22/0.46  fof(f483,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(sK9(sK0),u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK8(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f482,f60])).
% 0.22/0.46  fof(f482,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(sK9(sK0),u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK8(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f481,f61])).
% 0.22/0.46  fof(f481,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(sK9(sK0),u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK8(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f480,f62])).
% 0.22/0.46  fof(f480,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(sK9(sK0),u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK8(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f479,f63])).
% 0.22/0.46  fof(f479,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(sK9(sK0),u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK8(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f478,f64])).
% 0.22/0.46  fof(f478,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(sK9(sK0),u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK8(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(resolution,[],[f477,f65])).
% 0.22/0.46  fof(f477,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~v5_pre_topc(k4_waybel_1(X1,sK8(X1)),X1,X1) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_waybel_9(X1) | ~v1_compts_1(X1) | ~v2_lattice3(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | ~v8_pre_topc(X1) | ~v2_pre_topc(X1) | m1_subset_1(sK9(X1),u1_struct_0(X1)) | ~r3_waybel_9(X1,X2,X0) | ~v11_waybel_0(X2,X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | r2_waybel_9(X1,X2)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f476,f76])).
% 0.22/0.46  fof(f476,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_waybel_9(X1) | ~v1_compts_1(X1) | ~v2_lattice3(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | ~v8_pre_topc(X1) | ~v2_pre_topc(X1) | m1_subset_1(sK9(X1),u1_struct_0(X1)) | ~r3_waybel_9(X1,X2,X0) | ~v11_waybel_0(X2,X1) | ~v5_pre_topc(k4_waybel_1(X1,sK8(X1)),X1,X1) | r2_waybel_9(X1,X2) | ~l1_orders_2(X1)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f475])).
% 0.22/0.46  fof(f475,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_waybel_9(X1) | ~v1_compts_1(X1) | ~v2_lattice3(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | ~v8_pre_topc(X1) | ~v2_pre_topc(X1) | m1_subset_1(sK9(X1),u1_struct_0(X1)) | ~r3_waybel_9(X1,X2,X0) | ~v11_waybel_0(X2,X1) | ~v5_pre_topc(k4_waybel_1(X1,sK8(X1)),X1,X1) | r2_waybel_9(X1,X2) | ~l1_waybel_0(X2,X1) | ~l1_orders_2(X1)) )),
% 0.22/0.46    inference(resolution,[],[f466,f74])).
% 0.22/0.46  fof(f74,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | r2_waybel_9(X0,X1) | ~l1_waybel_0(X1,X0) | ~l1_orders_2(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f37])).
% 0.22/0.46  fof(f37,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (((r2_waybel_9(X0,X1) | ~r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))) & (r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~r2_waybel_9(X0,X1))) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0))),
% 0.22/0.46    inference(nnf_transformation,[],[f19])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : ((r2_waybel_9(X0,X1) <=> r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_waybel_0(X1,X0) => (r2_waybel_9(X0,X1) <=> r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_waybel_9)).
% 0.22/0.46  fof(f466,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (r2_yellow_0(X0,k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | m1_subset_1(sK9(X0),u1_struct_0(X0)) | ~r3_waybel_9(X0,X2,X1) | ~v11_waybel_0(X2,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f459])).
% 0.22/0.46  fof(f459,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (m1_subset_1(sK9(X0),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2))) | ~r3_waybel_9(X0,X2,X1) | ~r3_waybel_9(X0,X2,X1) | ~v11_waybel_0(X2,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.46    inference(resolution,[],[f458,f103])).
% 0.22/0.46  fof(f103,plain,(
% 0.22/0.46    ( ! [X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v11_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f96])).
% 0.22/0.46  fof(f96,plain,(
% 0.22/0.46    ( ! [X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v11_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.46    inference(equality_resolution,[],[f93])).
% 0.22/0.46  fof(f93,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f52])).
% 0.22/0.46  fof(f52,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | (~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) & m1_subset_1(sK8(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f30,f51])).
% 0.22/0.46  fof(f51,plain,(
% 0.22/0.46    ! [X0] : (? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) & m1_subset_1(sK8(X0),u1_struct_0(X0))))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f30,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.46    inference(flattening,[],[f29])).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | (~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & v11_waybel_0(X1,X0) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3))))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_waybel_9)).
% 0.22/0.46  fof(f458,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2) | m1_subset_1(sK9(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~r3_waybel_9(X0,X1,X2)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f457,f76])).
% 0.22/0.46  fof(f457,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | m1_subset_1(sK9(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2) | ~l1_orders_2(X0)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f456])).
% 0.22/0.46  fof(f456,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | m1_subset_1(sK9(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2) | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.46    inference(resolution,[],[f455,f87])).
% 0.22/0.46  fof(f87,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | r2_yellow_0(X0,X1) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f48])).
% 0.22/0.46  fof(f48,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : ((r2_yellow_0(X0,X1) | ! [X2] : ((~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)))) & ((! [X5] : (r1_orders_2(X0,X5,sK6(X0,X1)) | ~r1_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_lattice3(X0,X1,sK6(X0,X1)) & m1_subset_1(sK6(X0,X1),u1_struct_0(X0))) | ~r2_yellow_0(X0,X1))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f45,f47,f46])).
% 0.22/0.46  fof(f46,plain,(
% 0.22/0.46    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f47,plain,(
% 0.22/0.46    ! [X1,X0] : (? [X4] : (! [X5] : (r1_orders_2(X0,X5,X4) | ~r1_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_lattice3(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (! [X5] : (r1_orders_2(X0,X5,sK6(X0,X1)) | ~r1_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_lattice3(X0,X1,sK6(X0,X1)) & m1_subset_1(sK6(X0,X1),u1_struct_0(X0))))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f45,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : ((r2_yellow_0(X0,X1) | ! [X2] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (? [X4] : (! [X5] : (r1_orders_2(X0,X5,X4) | ~r1_lattice3(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_lattice3(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_yellow_0(X0,X1))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.22/0.46    inference(rectify,[],[f44])).
% 0.22/0.46  fof(f44,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : ((r2_yellow_0(X0,X1) | ! [X2] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (? [X2] : (! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_yellow_0(X0,X1))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.22/0.46    inference(nnf_transformation,[],[f26])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (r2_yellow_0(X0,X1) <=> ? [X2] : (! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.22/0.46    inference(flattening,[],[f25])).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (r2_yellow_0(X0,X1) <=> ? [X2] : (! [X3] : ((r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (r2_yellow_0(X0,X1) <=> ? [X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) => r1_orders_2(X0,X3,X2))) & r1_lattice3(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow_0)).
% 0.22/0.46  fof(f455,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(sK5(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2),u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | m1_subset_1(sK9(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f454,f76])).
% 0.22/0.46  fof(f454,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(sK5(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2),u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | m1_subset_1(sK9(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2) | ~l1_orders_2(X0)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f453])).
% 0.22/0.46  fof(f453,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(sK5(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2),u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | m1_subset_1(sK9(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.46    inference(resolution,[],[f342,f89])).
% 0.22/0.46  fof(f89,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK5(X0,X1,X2),X2) | r2_yellow_0(X0,X1) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f48])).
% 0.22/0.46  fof(f342,plain,(
% 0.22/0.46    ( ! [X14,X12,X13,X11] : (r1_orders_2(X11,sK5(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13),X14) | ~m1_subset_1(sK5(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13),u1_struct_0(X11)) | ~r3_waybel_9(X11,X12,X14) | m1_subset_1(sK9(X11),u1_struct_0(X11)) | ~m1_subset_1(X14,u1_struct_0(X11)) | ~l1_waybel_0(X12,X11) | ~v7_waybel_0(X12) | ~v4_orders_2(X12) | v2_struct_0(X12) | ~l1_waybel_9(X11) | ~v1_compts_1(X11) | ~v2_lattice3(X11) | ~v1_lattice3(X11) | ~v5_orders_2(X11) | ~v4_orders_2(X11) | ~v3_orders_2(X11) | ~v8_pre_topc(X11) | ~v2_pre_topc(X11) | r2_yellow_0(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12))) | ~r1_lattice3(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13) | ~m1_subset_1(X13,u1_struct_0(X11))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f337,f76])).
% 0.22/0.46  fof(f337,plain,(
% 0.22/0.46    ( ! [X14,X12,X13,X11] : (r1_orders_2(X11,sK5(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13),X14) | ~m1_subset_1(sK5(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13),u1_struct_0(X11)) | ~r3_waybel_9(X11,X12,X14) | m1_subset_1(sK9(X11),u1_struct_0(X11)) | ~m1_subset_1(X14,u1_struct_0(X11)) | ~l1_waybel_0(X12,X11) | ~v7_waybel_0(X12) | ~v4_orders_2(X12) | v2_struct_0(X12) | ~l1_waybel_9(X11) | ~v1_compts_1(X11) | ~v2_lattice3(X11) | ~v1_lattice3(X11) | ~v5_orders_2(X11) | ~v4_orders_2(X11) | ~v3_orders_2(X11) | ~v8_pre_topc(X11) | ~v2_pre_topc(X11) | r2_yellow_0(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12))) | ~r1_lattice3(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13) | ~m1_subset_1(X13,u1_struct_0(X11)) | ~l1_orders_2(X11)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f336])).
% 0.22/0.46  fof(f336,plain,(
% 0.22/0.46    ( ! [X14,X12,X13,X11] : (r1_orders_2(X11,sK5(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13),X14) | ~m1_subset_1(sK5(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13),u1_struct_0(X11)) | ~r3_waybel_9(X11,X12,X14) | m1_subset_1(sK9(X11),u1_struct_0(X11)) | ~m1_subset_1(X14,u1_struct_0(X11)) | ~l1_waybel_0(X12,X11) | ~v7_waybel_0(X12) | ~v4_orders_2(X12) | v2_struct_0(X12) | ~l1_waybel_9(X11) | ~v1_compts_1(X11) | ~v2_lattice3(X11) | ~v1_lattice3(X11) | ~v5_orders_2(X11) | ~v4_orders_2(X11) | ~v3_orders_2(X11) | ~v8_pre_topc(X11) | ~v2_pre_topc(X11) | r2_yellow_0(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12))) | ~r1_lattice3(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13) | ~m1_subset_1(X13,u1_struct_0(X11)) | ~l1_orders_2(X11) | ~v5_orders_2(X11)) )),
% 0.22/0.46    inference(resolution,[],[f100,f88])).
% 0.22/0.46  fof(f88,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,sK5(X0,X1,X2)) | r2_yellow_0(X0,X1) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f48])).
% 0.22/0.46  fof(f100,plain,(
% 0.22/0.46    ( ! [X4,X0,X3,X1] : (~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | r1_orders_2(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | m1_subset_1(sK9(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f99])).
% 0.22/0.46  fof(f99,plain,(
% 0.22/0.46    ( ! [X4,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | m1_subset_1(sK9(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.46    inference(equality_resolution,[],[f94])).
% 0.22/0.46  fof(f94,plain,(
% 0.22/0.46    ( ! [X4,X2,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | m1_subset_1(sK9(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f55])).
% 0.22/0.46  fof(f55,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | (~v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0) & m1_subset_1(sK9(X0),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f53,f54])).
% 0.22/0.46  fof(f54,plain,(
% 0.22/0.46    ! [X0] : (? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) => (~v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0) & m1_subset_1(sK9(X0),u1_struct_0(X0))))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f53,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X5] : (~v5_pre_topc(k4_waybel_1(X0,X5),X0,X0) & m1_subset_1(X5,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.46    inference(rectify,[],[f32])).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.46    inference(flattening,[],[f31])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X5] : ((r1_orders_2(X0,X5,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)) | ~m1_subset_1(X5,u1_struct_0(X0))) | (~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f14])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) => r1_orders_2(X0,X5,X3))))))))),
% 0.22/0.46    inference(rectify,[],[f6])).
% 0.22/0.46  fof(f6,axiom,(
% 0.22/0.46    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) => r1_orders_2(X0,X4,X3))))))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l52_waybel_9)).
% 0.22/0.46  fof(f528,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK8(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(resolution,[],[f527,f65])).
% 0.22/0.46  fof(f527,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f526,f56])).
% 0.22/0.46  fof(f526,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f525,f57])).
% 0.22/0.46  fof(f525,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f524,f58])).
% 0.22/0.46  fof(f524,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f523,f59])).
% 0.22/0.46  fof(f523,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f522,f60])).
% 0.22/0.46  fof(f522,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f521,f61])).
% 0.22/0.46  fof(f521,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f520,f62])).
% 0.22/0.46  fof(f520,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f519,f63])).
% 0.22/0.46  fof(f519,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f518,f64])).
% 0.22/0.46  fof(f518,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~v5_pre_topc(k4_waybel_1(sK0,sK8(sK0)),sK0,sK0) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(resolution,[],[f517,f65])).
% 0.22/0.46  fof(f517,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~v5_pre_topc(k4_waybel_1(X1,sK9(X1)),X1,X1) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_waybel_9(X1) | ~v1_compts_1(X1) | ~v2_lattice3(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | ~v8_pre_topc(X1) | ~v2_pre_topc(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~r3_waybel_9(X1,X2,X0) | ~v11_waybel_0(X2,X1) | ~v5_pre_topc(k4_waybel_1(X1,sK8(X1)),X1,X1) | r2_waybel_9(X1,X2)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f516,f76])).
% 0.22/0.46  fof(f516,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_waybel_9(X1) | ~v1_compts_1(X1) | ~v2_lattice3(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | ~v8_pre_topc(X1) | ~v2_pre_topc(X1) | ~v5_pre_topc(k4_waybel_1(X1,sK9(X1)),X1,X1) | ~r3_waybel_9(X1,X2,X0) | ~v11_waybel_0(X2,X1) | ~v5_pre_topc(k4_waybel_1(X1,sK8(X1)),X1,X1) | r2_waybel_9(X1,X2) | ~l1_orders_2(X1)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f515])).
% 0.22/0.46  fof(f515,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_waybel_9(X1) | ~v1_compts_1(X1) | ~v2_lattice3(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | ~v8_pre_topc(X1) | ~v2_pre_topc(X1) | ~v5_pre_topc(k4_waybel_1(X1,sK9(X1)),X1,X1) | ~r3_waybel_9(X1,X2,X0) | ~v11_waybel_0(X2,X1) | ~v5_pre_topc(k4_waybel_1(X1,sK8(X1)),X1,X1) | r2_waybel_9(X1,X2) | ~l1_waybel_0(X2,X1) | ~l1_orders_2(X1)) )),
% 0.22/0.46    inference(resolution,[],[f499,f74])).
% 0.22/0.46  fof(f499,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (r2_yellow_0(X0,k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | ~v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0) | ~r3_waybel_9(X0,X2,X1) | ~v11_waybel_0(X2,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f492])).
% 0.22/0.46  fof(f492,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2))) | ~r3_waybel_9(X0,X2,X1) | ~r3_waybel_9(X0,X2,X1) | ~v11_waybel_0(X2,X0) | ~v5_pre_topc(k4_waybel_1(X0,sK8(X0)),X0,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.46    inference(resolution,[],[f491,f103])).
% 0.22/0.46  fof(f491,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2) | ~v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~r3_waybel_9(X0,X1,X2)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f490,f76])).
% 0.22/0.46  fof(f490,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2) | ~l1_orders_2(X0)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f489])).
% 0.22/0.46  fof(f489,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2) | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.46    inference(resolution,[],[f474,f87])).
% 0.22/0.46  fof(f474,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(sK5(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2),u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f473,f76])).
% 0.22/0.46  fof(f473,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(sK5(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2),u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2) | ~l1_orders_2(X0)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f472])).
% 0.22/0.46  fof(f472,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(sK5(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2),u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_yellow_0(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.46    inference(resolution,[],[f352,f89])).
% 0.22/0.46  fof(f352,plain,(
% 0.22/0.46    ( ! [X14,X12,X13,X11] : (r1_orders_2(X11,sK5(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13),X14) | ~m1_subset_1(sK5(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13),u1_struct_0(X11)) | ~r3_waybel_9(X11,X12,X14) | ~v5_pre_topc(k4_waybel_1(X11,sK9(X11)),X11,X11) | ~m1_subset_1(X14,u1_struct_0(X11)) | ~l1_waybel_0(X12,X11) | ~v7_waybel_0(X12) | ~v4_orders_2(X12) | v2_struct_0(X12) | ~l1_waybel_9(X11) | ~v1_compts_1(X11) | ~v2_lattice3(X11) | ~v1_lattice3(X11) | ~v5_orders_2(X11) | ~v4_orders_2(X11) | ~v3_orders_2(X11) | ~v8_pre_topc(X11) | ~v2_pre_topc(X11) | r2_yellow_0(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12))) | ~r1_lattice3(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13) | ~m1_subset_1(X13,u1_struct_0(X11))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f347,f76])).
% 0.22/0.46  fof(f347,plain,(
% 0.22/0.46    ( ! [X14,X12,X13,X11] : (r1_orders_2(X11,sK5(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13),X14) | ~m1_subset_1(sK5(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13),u1_struct_0(X11)) | ~r3_waybel_9(X11,X12,X14) | ~v5_pre_topc(k4_waybel_1(X11,sK9(X11)),X11,X11) | ~m1_subset_1(X14,u1_struct_0(X11)) | ~l1_waybel_0(X12,X11) | ~v7_waybel_0(X12) | ~v4_orders_2(X12) | v2_struct_0(X12) | ~l1_waybel_9(X11) | ~v1_compts_1(X11) | ~v2_lattice3(X11) | ~v1_lattice3(X11) | ~v5_orders_2(X11) | ~v4_orders_2(X11) | ~v3_orders_2(X11) | ~v8_pre_topc(X11) | ~v2_pre_topc(X11) | r2_yellow_0(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12))) | ~r1_lattice3(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13) | ~m1_subset_1(X13,u1_struct_0(X11)) | ~l1_orders_2(X11)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f346])).
% 0.22/0.46  fof(f346,plain,(
% 0.22/0.46    ( ! [X14,X12,X13,X11] : (r1_orders_2(X11,sK5(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13),X14) | ~m1_subset_1(sK5(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13),u1_struct_0(X11)) | ~r3_waybel_9(X11,X12,X14) | ~v5_pre_topc(k4_waybel_1(X11,sK9(X11)),X11,X11) | ~m1_subset_1(X14,u1_struct_0(X11)) | ~l1_waybel_0(X12,X11) | ~v7_waybel_0(X12) | ~v4_orders_2(X12) | v2_struct_0(X12) | ~l1_waybel_9(X11) | ~v1_compts_1(X11) | ~v2_lattice3(X11) | ~v1_lattice3(X11) | ~v5_orders_2(X11) | ~v4_orders_2(X11) | ~v3_orders_2(X11) | ~v8_pre_topc(X11) | ~v2_pre_topc(X11) | r2_yellow_0(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12))) | ~r1_lattice3(X11,k2_relset_1(u1_struct_0(X12),u1_struct_0(X11),u1_waybel_0(X11,X12)),X13) | ~m1_subset_1(X13,u1_struct_0(X11)) | ~l1_orders_2(X11) | ~v5_orders_2(X11)) )),
% 0.22/0.46    inference(resolution,[],[f101,f88])).
% 0.22/0.46  fof(f101,plain,(
% 0.22/0.46    ( ! [X4,X0,X3,X1] : (~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | r1_orders_2(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f98])).
% 0.22/0.46  fof(f98,plain,(
% 0.22/0.46    ( ! [X4,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.46    inference(equality_resolution,[],[f95])).
% 0.22/0.46  fof(f95,plain,(
% 0.22/0.46    ( ! [X4,X2,X0,X3,X1] : (r1_orders_2(X0,X4,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~v5_pre_topc(k4_waybel_1(X0,sK9(X0)),X0,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f55])).
% 0.22/0.46  fof(f556,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(sK8(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f555,f56])).
% 0.22/0.46  fof(f555,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | m1_subset_1(sK8(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f554,f57])).
% 0.22/0.46  fof(f554,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(sK8(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f553,f58])).
% 0.22/0.46  fof(f553,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(sK8(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f552,f59])).
% 0.22/0.46  fof(f552,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(sK8(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f551,f60])).
% 0.22/0.46  fof(f551,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(sK8(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f550,f61])).
% 0.22/0.46  fof(f550,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(sK8(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f549,f62])).
% 0.22/0.46  fof(f549,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(sK8(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f548,f63])).
% 0.22/0.46  fof(f548,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(sK8(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f543,f64])).
% 0.22/0.46  fof(f543,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(sK8(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f542])).
% 0.22/0.46  fof(f542,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r3_waybel_9(sK0,X0,X1) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(sK8(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(condensation,[],[f541])).
% 0.22/0.46  fof(f541,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~v4_orders_2(X0) | v2_struct_0(X0) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X2) | m1_subset_1(sK8(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f540])).
% 0.22/0.46  fof(f540,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~v4_orders_2(X0) | v2_struct_0(X0) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | v2_struct_0(X0) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X2) | ~v11_waybel_0(X0,sK0) | m1_subset_1(sK8(sK0),u1_struct_0(sK0)) | r2_waybel_9(sK0,X0)) )),
% 0.22/0.46    inference(condensation,[],[f538])).
% 0.22/0.46  fof(f538,plain,(
% 0.22/0.46    ( ! [X12,X10,X11,X9] : (~v4_orders_2(X9) | v2_struct_0(X9) | ~r3_waybel_9(sK0,X9,X10) | ~v11_waybel_0(X9,sK0) | ~l1_waybel_0(X9,sK0) | r2_waybel_9(sK0,X9) | ~v7_waybel_0(X9) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~l1_waybel_0(X11,sK0) | ~v7_waybel_0(X11) | ~v4_orders_2(X11) | v2_struct_0(X11) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X12,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X11,X12) | ~v11_waybel_0(X11,sK0) | m1_subset_1(sK8(sK0),u1_struct_0(sK0)) | r2_waybel_9(sK0,X11)) )),
% 0.22/0.46    inference(resolution,[],[f535,f470])).
% 0.22/0.46  fof(f470,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (m1_subset_1(sK9(X1),u1_struct_0(X1)) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_waybel_9(X1) | ~v1_compts_1(X1) | ~v2_lattice3(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | ~v8_pre_topc(X1) | ~v2_pre_topc(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~r3_waybel_9(X1,X2,X0) | ~v11_waybel_0(X2,X1) | m1_subset_1(sK8(X1),u1_struct_0(X1)) | r2_waybel_9(X1,X2)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f469,f76])).
% 0.22/0.46  fof(f469,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_waybel_9(X1) | ~v1_compts_1(X1) | ~v2_lattice3(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | ~v8_pre_topc(X1) | ~v2_pre_topc(X1) | m1_subset_1(sK9(X1),u1_struct_0(X1)) | ~r3_waybel_9(X1,X2,X0) | ~v11_waybel_0(X2,X1) | m1_subset_1(sK8(X1),u1_struct_0(X1)) | r2_waybel_9(X1,X2) | ~l1_orders_2(X1)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f468])).
% 0.22/0.46  fof(f468,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_waybel_9(X1) | ~v1_compts_1(X1) | ~v2_lattice3(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | ~v8_pre_topc(X1) | ~v2_pre_topc(X1) | m1_subset_1(sK9(X1),u1_struct_0(X1)) | ~r3_waybel_9(X1,X2,X0) | ~v11_waybel_0(X2,X1) | m1_subset_1(sK8(X1),u1_struct_0(X1)) | r2_waybel_9(X1,X2) | ~l1_waybel_0(X2,X1) | ~l1_orders_2(X1)) )),
% 0.22/0.46    inference(resolution,[],[f465,f74])).
% 0.22/0.46  fof(f465,plain,(
% 0.22/0.46    ( ! [X4,X5,X3] : (r2_yellow_0(X3,k2_relset_1(u1_struct_0(X5),u1_struct_0(X3),u1_waybel_0(X3,X5))) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_waybel_0(X5,X3) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_waybel_9(X3) | ~v1_compts_1(X3) | ~v2_lattice3(X3) | ~v1_lattice3(X3) | ~v5_orders_2(X3) | ~v4_orders_2(X3) | ~v3_orders_2(X3) | ~v8_pre_topc(X3) | ~v2_pre_topc(X3) | m1_subset_1(sK9(X3),u1_struct_0(X3)) | ~r3_waybel_9(X3,X5,X4) | ~v11_waybel_0(X5,X3) | m1_subset_1(sK8(X3),u1_struct_0(X3))) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f460])).
% 0.22/0.46  fof(f460,plain,(
% 0.22/0.46    ( ! [X4,X5,X3] : (m1_subset_1(sK9(X3),u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_waybel_0(X5,X3) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_waybel_9(X3) | ~v1_compts_1(X3) | ~v2_lattice3(X3) | ~v1_lattice3(X3) | ~v5_orders_2(X3) | ~v4_orders_2(X3) | ~v3_orders_2(X3) | ~v8_pre_topc(X3) | ~v2_pre_topc(X3) | r2_yellow_0(X3,k2_relset_1(u1_struct_0(X5),u1_struct_0(X3),u1_waybel_0(X3,X5))) | ~r3_waybel_9(X3,X5,X4) | ~r3_waybel_9(X3,X5,X4) | ~v11_waybel_0(X5,X3) | m1_subset_1(sK8(X3),u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_waybel_0(X5,X3) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_waybel_9(X3) | ~v1_compts_1(X3) | ~v2_lattice3(X3) | ~v1_lattice3(X3) | ~v5_orders_2(X3) | ~v4_orders_2(X3) | ~v3_orders_2(X3) | ~v8_pre_topc(X3) | ~v2_pre_topc(X3)) )),
% 0.22/0.46    inference(resolution,[],[f458,f102])).
% 0.22/0.46  fof(f102,plain,(
% 0.22/0.46    ( ! [X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v11_waybel_0(X1,X0) | m1_subset_1(sK8(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f97])).
% 0.22/0.46  fof(f97,plain,(
% 0.22/0.46    ( ! [X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X3) | ~v11_waybel_0(X1,X0) | m1_subset_1(sK8(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.46    inference(equality_resolution,[],[f92])).
% 0.22/0.46  fof(f92,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | m1_subset_1(sK8(X0),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f52])).
% 0.22/0.46  fof(f535,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(sK9(sK0),u1_struct_0(sK0)) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~r3_waybel_9(sK0,X1,X0) | ~v11_waybel_0(X1,sK0) | ~l1_waybel_0(X1,sK0) | r2_waybel_9(sK0,X1) | ~v7_waybel_0(X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f534])).
% 0.22/0.46  fof(f534,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~r3_waybel_9(sK0,X1,X0) | ~v11_waybel_0(X1,sK0) | ~l1_waybel_0(X1,sK0) | r2_waybel_9(sK0,X1) | ~v7_waybel_0(X1) | ~r3_waybel_9(sK0,X1,X0) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(condensation,[],[f533])).
% 0.22/0.46  fof(f533,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X2) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f532])).
% 0.22/0.46  fof(f532,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~v7_waybel_0(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X2) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(condensation,[],[f530])).
% 0.22/0.46  fof(f530,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~v7_waybel_0(X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X2,X3) | ~v11_waybel_0(X2,sK0) | ~l1_waybel_0(X2,sK0) | r2_waybel_9(sK0,X2) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(resolution,[],[f529,f513])).
% 0.22/0.46  fof(f513,plain,(
% 0.22/0.46    ( ! [X0,X1] : (m1_subset_1(sK8(sK0),u1_struct_0(sK0)) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | ~l1_waybel_0(X0,sK0) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f512,f56])).
% 0.22/0.46  fof(f512,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | m1_subset_1(sK8(sK0),u1_struct_0(sK0)) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f511,f57])).
% 0.22/0.46  fof(f511,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | m1_subset_1(sK8(sK0),u1_struct_0(sK0)) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f510,f58])).
% 0.22/0.46  fof(f510,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | m1_subset_1(sK8(sK0),u1_struct_0(sK0)) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f509,f59])).
% 0.22/0.46  fof(f509,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | m1_subset_1(sK8(sK0),u1_struct_0(sK0)) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f508,f60])).
% 0.22/0.46  fof(f508,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | m1_subset_1(sK8(sK0),u1_struct_0(sK0)) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f507,f61])).
% 0.22/0.46  fof(f507,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | m1_subset_1(sK8(sK0),u1_struct_0(sK0)) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f506,f62])).
% 0.22/0.46  fof(f506,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | m1_subset_1(sK8(sK0),u1_struct_0(sK0)) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f505,f63])).
% 0.22/0.46  fof(f505,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | m1_subset_1(sK8(sK0),u1_struct_0(sK0)) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f504,f64])).
% 0.22/0.46  fof(f504,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_9(sK0) | ~v1_compts_1(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~v8_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~v11_waybel_0(X0,sK0) | m1_subset_1(sK8(sK0),u1_struct_0(sK0)) | r2_waybel_9(sK0,X0) | ~m1_subset_1(sK9(sK0),u1_struct_0(sK0))) )),
% 0.22/0.46    inference(resolution,[],[f503,f65])).
% 0.22/0.46  fof(f503,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~v5_pre_topc(k4_waybel_1(X1,sK9(X1)),X1,X1) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_waybel_9(X1) | ~v1_compts_1(X1) | ~v2_lattice3(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | ~v8_pre_topc(X1) | ~v2_pre_topc(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~r3_waybel_9(X1,X2,X0) | ~v11_waybel_0(X2,X1) | m1_subset_1(sK8(X1),u1_struct_0(X1)) | r2_waybel_9(X1,X2)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f502,f76])).
% 0.22/0.46  fof(f502,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_waybel_9(X1) | ~v1_compts_1(X1) | ~v2_lattice3(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | ~v8_pre_topc(X1) | ~v2_pre_topc(X1) | ~v5_pre_topc(k4_waybel_1(X1,sK9(X1)),X1,X1) | ~r3_waybel_9(X1,X2,X0) | ~v11_waybel_0(X2,X1) | m1_subset_1(sK8(X1),u1_struct_0(X1)) | r2_waybel_9(X1,X2) | ~l1_orders_2(X1)) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f501])).
% 0.22/0.46  fof(f501,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_waybel_0(X2,X1) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~l1_waybel_9(X1) | ~v1_compts_1(X1) | ~v2_lattice3(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | ~v8_pre_topc(X1) | ~v2_pre_topc(X1) | ~v5_pre_topc(k4_waybel_1(X1,sK9(X1)),X1,X1) | ~r3_waybel_9(X1,X2,X0) | ~v11_waybel_0(X2,X1) | m1_subset_1(sK8(X1),u1_struct_0(X1)) | r2_waybel_9(X1,X2) | ~l1_waybel_0(X2,X1) | ~l1_orders_2(X1)) )),
% 0.22/0.46    inference(resolution,[],[f498,f74])).
% 0.22/0.46  fof(f498,plain,(
% 0.22/0.46    ( ! [X4,X5,X3] : (r2_yellow_0(X3,k2_relset_1(u1_struct_0(X5),u1_struct_0(X3),u1_waybel_0(X3,X5))) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_waybel_0(X5,X3) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_waybel_9(X3) | ~v1_compts_1(X3) | ~v2_lattice3(X3) | ~v1_lattice3(X3) | ~v5_orders_2(X3) | ~v4_orders_2(X3) | ~v3_orders_2(X3) | ~v8_pre_topc(X3) | ~v2_pre_topc(X3) | ~v5_pre_topc(k4_waybel_1(X3,sK9(X3)),X3,X3) | ~r3_waybel_9(X3,X5,X4) | ~v11_waybel_0(X5,X3) | m1_subset_1(sK8(X3),u1_struct_0(X3))) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f493])).
% 0.22/0.46  fof(f493,plain,(
% 0.22/0.46    ( ! [X4,X5,X3] : (~v5_pre_topc(k4_waybel_1(X3,sK9(X3)),X3,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_waybel_0(X5,X3) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_waybel_9(X3) | ~v1_compts_1(X3) | ~v2_lattice3(X3) | ~v1_lattice3(X3) | ~v5_orders_2(X3) | ~v4_orders_2(X3) | ~v3_orders_2(X3) | ~v8_pre_topc(X3) | ~v2_pre_topc(X3) | r2_yellow_0(X3,k2_relset_1(u1_struct_0(X5),u1_struct_0(X3),u1_waybel_0(X3,X5))) | ~r3_waybel_9(X3,X5,X4) | ~r3_waybel_9(X3,X5,X4) | ~v11_waybel_0(X5,X3) | m1_subset_1(sK8(X3),u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_waybel_0(X5,X3) | ~v7_waybel_0(X5) | ~v4_orders_2(X5) | v2_struct_0(X5) | ~l1_waybel_9(X3) | ~v1_compts_1(X3) | ~v2_lattice3(X3) | ~v1_lattice3(X3) | ~v5_orders_2(X3) | ~v4_orders_2(X3) | ~v3_orders_2(X3) | ~v8_pre_topc(X3) | ~v2_pre_topc(X3)) )),
% 0.22/0.46    inference(resolution,[],[f491,f102])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (32059)------------------------------
% 0.22/0.46  % (32059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (32059)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (32059)Memory used [KB]: 2046
% 0.22/0.46  % (32059)Time elapsed: 0.040 s
% 0.22/0.46  % (32059)------------------------------
% 0.22/0.46  % (32059)------------------------------
% 0.22/0.47  % (32040)Success in time 0.106 s
%------------------------------------------------------------------------------
