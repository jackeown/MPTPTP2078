%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:16 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  169 (3992 expanded)
%              Number of leaves         :    7 ( 602 expanded)
%              Depth                    :   84
%              Number of atoms          :  980 (49478 expanded)
%              Number of equality atoms :   24 (2553 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f375,plain,(
    $false ),
    inference(subsumption_resolution,[],[f374,f35])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X4] :
              ( ~ r2_hidden(X4,k10_yellow_6(X0,X1))
              & r3_waybel_9(X0,X1,X4)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & ! [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ~ r3_waybel_9(X0,X1,X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v1_compts_1(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X4] :
              ( ~ r2_hidden(X4,k10_yellow_6(X0,X1))
              & r3_waybel_9(X0,X1,X4)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & ! [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ~ r3_waybel_9(X0,X1,X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v1_compts_1(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ~ ! [X0] :
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

fof(f8,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_waybel_9)).

fof(f374,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f373,f36])).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f373,plain,(
    ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f372,f31])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f372,plain,
    ( v2_struct_0(sK0)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f371,f30])).

fof(f30,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f371,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f370,f137])).

fof(f137,plain,(
    m2_yellow_6(sK5(sK0,sK1,sK2),sK0,sK1) ),
    inference(subsumption_resolution,[],[f136,f27])).

fof(f27,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f136,plain,
    ( v2_struct_0(sK1)
    | m2_yellow_6(sK5(sK0,sK1,sK2),sK0,sK1) ),
    inference(subsumption_resolution,[],[f135,f24])).

fof(f24,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f135,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | m2_yellow_6(sK5(sK0,sK1,sK2),sK0,sK1) ),
    inference(subsumption_resolution,[],[f134,f30])).

fof(f134,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | m2_yellow_6(sK5(sK0,sK1,sK2),sK0,sK1) ),
    inference(subsumption_resolution,[],[f133,f29])).

fof(f29,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f133,plain,
    ( ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | m2_yellow_6(sK5(sK0,sK1,sK2),sK0,sK1) ),
    inference(subsumption_resolution,[],[f132,f28])).

fof(f28,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f132,plain,
    ( ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | m2_yellow_6(sK5(sK0,sK1,sK2),sK0,sK1) ),
    inference(resolution,[],[f131,f26])).

fof(f26,plain,(
    ~ r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f131,plain,(
    ! [X6,X7] :
      ( r2_hidden(X7,k10_yellow_6(sK0,X6))
      | ~ v4_orders_2(X6)
      | ~ v7_waybel_0(X6)
      | ~ l1_waybel_0(X6,sK0)
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | v2_struct_0(X6)
      | m2_yellow_6(sK5(sK0,X6,X7),sK0,X6) ) ),
    inference(subsumption_resolution,[],[f67,f35])).

fof(f67,plain,(
    ! [X6,X7] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(X6)
      | ~ v4_orders_2(X6)
      | ~ v7_waybel_0(X6)
      | ~ l1_waybel_0(X6,sK0)
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | r2_hidden(X7,k10_yellow_6(sK0,X6))
      | m2_yellow_6(sK5(sK0,X6,X7),sK0,X6) ) ),
    inference(subsumption_resolution,[],[f62,f31])).

fof(f62,plain,(
    ! [X6,X7] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X6)
      | ~ v4_orders_2(X6)
      | ~ v7_waybel_0(X6)
      | ~ l1_waybel_0(X6,sK0)
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | r2_hidden(X7,k10_yellow_6(sK0,X6))
      | m2_yellow_6(sK5(sK0,X6,X7),sK0,X6) ) ),
    inference(resolution,[],[f32,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | m2_yellow_6(sK5(X0,X1,X2),X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r2_hidden(X2,k10_yellow_6(X0,X4))
                      | ~ m2_yellow_6(X4,X0,X3) )
                  & m2_yellow_6(X3,X0,X1) )
              | r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r2_hidden(X2,k10_yellow_6(X0,X4))
                      | ~ m2_yellow_6(X4,X0,X3) )
                  & m2_yellow_6(X3,X0,X1) )
              | r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( ! [X3] :
                      ( m2_yellow_6(X3,X0,X1)
                     => ? [X4] :
                          ( r2_hidden(X2,k10_yellow_6(X0,X4))
                          & m2_yellow_6(X4,X0,X3) ) )
                  & ~ r2_hidden(X2,k10_yellow_6(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_yellow_6)).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f370,plain,(
    ! [X2] :
      ( ~ m2_yellow_6(sK5(sK0,sK1,sK2),X2,sK1)
      | ~ l1_waybel_0(sK1,X2)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f367,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK1,X0)
      | ~ m2_yellow_6(X1,X0,sK1)
      | ~ l1_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f52,f28])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK1,X0)
      | ~ m2_yellow_6(X1,X0,sK1)
      | ~ v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f48,f27])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK1,X0)
      | ~ m2_yellow_6(X1,X0,sK1)
      | ~ v2_struct_0(X1) ) ),
    inference(resolution,[],[f29,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_yellow_6)).

fof(f367,plain,(
    ! [X2] :
      ( v2_struct_0(sK5(sK0,sK1,sK2))
      | v2_struct_0(X2)
      | ~ l1_waybel_0(sK1,X2)
      | ~ m2_yellow_6(sK5(sK0,sK1,sK2),X2,sK1)
      | ~ l1_struct_0(X2) ) ),
    inference(resolution,[],[f363,f55])).

fof(f55,plain,(
    ! [X2,X3] :
      ( v4_orders_2(X3)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(sK1,X2)
      | ~ m2_yellow_6(X3,X2,sK1)
      | ~ l1_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f54,f28])).

fof(f54,plain,(
    ! [X2,X3] :
      ( ~ l1_struct_0(X2)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(sK1,X2)
      | ~ m2_yellow_6(X3,X2,sK1)
      | v4_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f49,f27])).

fof(f49,plain,(
    ! [X2,X3] :
      ( ~ l1_struct_0(X2)
      | v2_struct_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(sK1,X2)
      | ~ m2_yellow_6(X3,X2,sK1)
      | v4_orders_2(X3) ) ),
    inference(resolution,[],[f29,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | v4_orders_2(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f363,plain,
    ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f362,f208])).

fof(f208,plain,
    ( r3_waybel_9(sK0,sK5(sK0,sK1,sK2),sK2)
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f160,f207])).

fof(f207,plain,(
    sK2 = sK3(sK0,sK5(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f206,f35])).

fof(f206,plain,
    ( sK2 = sK3(sK0,sK5(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f205,f36])).

fof(f205,plain,
    ( ~ l1_struct_0(sK0)
    | sK2 = sK3(sK0,sK5(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f204,f30])).

fof(f204,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | sK2 = sK3(sK0,sK5(sK0,sK1,sK2))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f203,f31])).

fof(f203,plain,
    ( v2_struct_0(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | sK2 = sK3(sK0,sK5(sK0,sK1,sK2))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f191,f137])).

fof(f191,plain,(
    ! [X0] :
      ( ~ m2_yellow_6(sK5(sK0,sK1,sK2),X0,sK1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK1,X0)
      | sK2 = sK3(sK0,sK5(sK0,sK1,sK2))
      | ~ l1_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f190,f53])).

fof(f190,plain,(
    ! [X0] :
      ( v2_struct_0(sK5(sK0,sK1,sK2))
      | sK2 = sK3(sK0,sK5(sK0,sK1,sK2))
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK1,X0)
      | ~ m2_yellow_6(sK5(sK0,sK1,sK2),X0,sK1)
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f189,f55])).

fof(f189,plain,
    ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | sK2 = sK3(sK0,sK5(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f188,f31])).

fof(f188,plain,
    ( sK2 = sK3(sK0,sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f187,f156])).

fof(f156,plain,(
    l1_waybel_0(sK5(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f155,f35])).

fof(f155,plain,
    ( l1_waybel_0(sK5(sK0,sK1,sK2),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f146,f36])).

fof(f146,plain,
    ( ~ l1_struct_0(sK0)
    | l1_waybel_0(sK5(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f145,f30])).

fof(f145,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | l1_waybel_0(sK5(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f139,f31])).

fof(f139,plain,
    ( v2_struct_0(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | l1_waybel_0(sK5(sK0,sK1,sK2),sK0) ),
    inference(resolution,[],[f137,f59])).

fof(f59,plain,(
    ! [X6,X7] :
      ( ~ m2_yellow_6(X7,X6,sK1)
      | v2_struct_0(X6)
      | ~ l1_waybel_0(sK1,X6)
      | ~ l1_struct_0(X6)
      | l1_waybel_0(X7,X6) ) ),
    inference(subsumption_resolution,[],[f58,f28])).

fof(f58,plain,(
    ! [X6,X7] :
      ( ~ l1_struct_0(X6)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(X6)
      | ~ l1_waybel_0(sK1,X6)
      | ~ m2_yellow_6(X7,X6,sK1)
      | l1_waybel_0(X7,X6) ) ),
    inference(subsumption_resolution,[],[f51,f27])).

fof(f51,plain,(
    ! [X6,X7] :
      ( ~ l1_struct_0(X6)
      | v2_struct_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(X6)
      | ~ l1_waybel_0(sK1,X6)
      | ~ m2_yellow_6(X7,X6,sK1)
      | l1_waybel_0(X7,X6) ) ),
    inference(resolution,[],[f29,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | l1_waybel_0(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f187,plain,
    ( sK2 = sK3(sK0,sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK5(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f186,f150])).

fof(f150,plain,(
    v7_waybel_0(sK5(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f149,f35])).

fof(f149,plain,
    ( v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f148,f36])).

fof(f148,plain,
    ( ~ l1_struct_0(sK0)
    | v7_waybel_0(sK5(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f147,f30])).

fof(f147,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | v7_waybel_0(sK5(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f140,f31])).

fof(f140,plain,
    ( v2_struct_0(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | v7_waybel_0(sK5(sK0,sK1,sK2)) ),
    inference(resolution,[],[f137,f57])).

fof(f57,plain,(
    ! [X4,X5] :
      ( ~ m2_yellow_6(X5,X4,sK1)
      | v2_struct_0(X4)
      | ~ l1_waybel_0(sK1,X4)
      | ~ l1_struct_0(X4)
      | v7_waybel_0(X5) ) ),
    inference(subsumption_resolution,[],[f56,f28])).

fof(f56,plain,(
    ! [X4,X5] :
      ( ~ l1_struct_0(X4)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(X4)
      | ~ l1_waybel_0(sK1,X4)
      | ~ m2_yellow_6(X5,X4,sK1)
      | v7_waybel_0(X5) ) ),
    inference(subsumption_resolution,[],[f50,f27])).

fof(f50,plain,(
    ! [X4,X5] :
      ( ~ l1_struct_0(X4)
      | v2_struct_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(X4)
      | ~ l1_waybel_0(sK1,X4)
      | ~ m2_yellow_6(X5,X4,sK1)
      | v7_waybel_0(X5) ) ),
    inference(resolution,[],[f29,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | v7_waybel_0(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f186,plain,
    ( sK2 = sK3(sK0,sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK5(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f185,f35])).

fof(f185,plain,
    ( sK2 = sK3(sK0,sK5(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK5(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f184,f34])).

fof(f34,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f184,plain,
    ( sK2 = sK3(sK0,sK5(sK0,sK1,sK2))
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK5(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f183,f33])).

fof(f33,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f183,plain,
    ( sK2 = sK3(sK0,sK5(sK0,sK1,sK2))
    | ~ v8_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK5(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f182,f32])).

fof(f182,plain,
    ( sK2 = sK3(sK0,sK5(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK5(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f180,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_waybel_9)).

fof(f180,plain,
    ( ~ m1_subset_1(sK3(sK0,sK5(sK0,sK1,sK2)),u1_struct_0(sK0))
    | sK2 = sK3(sK0,sK5(sK0,sK1,sK2)) ),
    inference(resolution,[],[f178,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK2 = X0 ) ),
    inference(subsumption_resolution,[],[f74,f24])).

fof(f74,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X0)
      | sK2 = X0 ) ),
    inference(resolution,[],[f23,f25])).

fof(f25,plain,(
    r3_waybel_9(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X2,X3] :
      ( ~ r3_waybel_9(sK0,sK1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK1,X3)
      | X2 = X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f178,plain,(
    r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f177,f35])).

fof(f177,plain,
    ( r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f176,f36])).

fof(f176,plain,
    ( ~ l1_struct_0(sK0)
    | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f175,f30])).

fof(f175,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2)))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f174,f31])).

fof(f174,plain,
    ( v2_struct_0(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2)))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f173,f137])).

fof(f173,plain,(
    ! [X0] :
      ( ~ m2_yellow_6(sK5(sK0,sK1,sK2),X0,sK1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK1,X0)
      | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2)))
      | ~ l1_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f172,f53])).

fof(f172,plain,(
    ! [X0] :
      ( v2_struct_0(sK5(sK0,sK1,sK2))
      | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2)))
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK1,X0)
      | ~ m2_yellow_6(sK5(sK0,sK1,sK2),X0,sK1)
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f171,f55])).

fof(f171,plain,
    ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f170,f31])).

fof(f170,plain,
    ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f169,f156])).

fof(f169,plain,
    ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2)))
    | ~ l1_waybel_0(sK5(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f168,f150])).

fof(f168,plain,
    ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2)))
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK5(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f167,f35])).

fof(f167,plain,
    ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2)))
    | ~ l1_pre_topc(sK0)
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK5(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f166,f34])).

fof(f166,plain,
    ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2)))
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK5(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f165,f33])).

fof(f165,plain,
    ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2)))
    | ~ v8_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK5(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f164,f32])).

fof(f164,plain,
    ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2)))
    | ~ v2_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK5(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,
    ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2)))
    | ~ v2_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK5(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f161,f37])).

fof(f161,plain,
    ( ~ m1_subset_1(sK3(sK0,sK5(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2))) ),
    inference(resolution,[],[f160,f144])).

fof(f144,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK5(sK0,sK1,sK2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_waybel_9(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f143,f27])).

fof(f143,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK5(sK0,sK1,sK2),X0)
      | r3_waybel_9(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f142,f30])).

fof(f142,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK5(sK0,sK1,sK2),X0)
      | r3_waybel_9(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f141,f29])).

fof(f141,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK1)
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK5(sK0,sK1,sK2),X0)
      | r3_waybel_9(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f138,f28])).

fof(f138,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK1)
      | ~ v7_waybel_0(sK1)
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK5(sK0,sK1,sK2),X0)
      | r3_waybel_9(sK0,sK1,X0) ) ),
    inference(resolution,[],[f137,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X1,sK0,X0)
      | ~ v4_orders_2(X0)
      | ~ v7_waybel_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X1,X2)
      | r3_waybel_9(sK0,X0,X2) ) ),
    inference(subsumption_resolution,[],[f65,f35])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(X0)
      | ~ v7_waybel_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ m2_yellow_6(X1,sK0,X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X1,X2)
      | r3_waybel_9(sK0,X0,X2) ) ),
    inference(subsumption_resolution,[],[f60,f31])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(X0)
      | ~ v7_waybel_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ m2_yellow_6(X1,sK0,X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X1,X2)
      | r3_waybel_9(sK0,X0,X2) ) ),
    inference(resolution,[],[f32,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X2,X3)
      | r3_waybel_9(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_waybel_9(X0,X1,X3)
                  | ~ r3_waybel_9(X0,X2,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_waybel_9(X0,X1,X3)
                  | ~ r3_waybel_9(X0,X2,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_waybel_9)).

fof(f160,plain,
    ( r3_waybel_9(sK0,sK5(sK0,sK1,sK2),sK3(sK0,sK5(sK0,sK1,sK2)))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f158,f150])).

fof(f158,plain,
    ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | r3_waybel_9(sK0,sK5(sK0,sK1,sK2),sK3(sK0,sK5(sK0,sK1,sK2))) ),
    inference(resolution,[],[f156,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v4_orders_2(X0)
      | ~ v7_waybel_0(X0)
      | v2_struct_0(X0)
      | r3_waybel_9(sK0,X0,sK3(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f73,f35])).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(X0)
      | ~ v7_waybel_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | r3_waybel_9(sK0,X0,sK3(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f72,f31])).

fof(f72,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(X0)
      | ~ v7_waybel_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | r3_waybel_9(sK0,X0,sK3(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f71,f33])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v8_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(X0)
      | ~ v7_waybel_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | r3_waybel_9(sK0,X0,sK3(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f70,f32])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ v8_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(X0)
      | ~ v7_waybel_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | r3_waybel_9(sK0,X0,sK3(sK0,X0)) ) ),
    inference(resolution,[],[f34,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_compts_1(X0)
      | ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | r3_waybel_9(X0,X1,sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f362,plain,
    ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ r3_waybel_9(sK0,sK5(sK0,sK1,sK2),sK2)
    | v2_struct_0(sK5(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f361,f24])).

fof(f361,plain,
    ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r3_waybel_9(sK0,sK5(sK0,sK1,sK2),sK2)
    | v2_struct_0(sK5(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f360,f156])).

fof(f360,plain,
    ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK5(sK0,sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r3_waybel_9(sK0,sK5(sK0,sK1,sK2),sK2)
    | v2_struct_0(sK5(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f358,f150])).

fof(f358,plain,
    ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK5(sK0,sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r3_waybel_9(sK0,sK5(sK0,sK1,sK2),sK2)
    | v2_struct_0(sK5(sK0,sK1,sK2)) ),
    inference(resolution,[],[f351,f162])).

fof(f162,plain,(
    ! [X10,X11] :
      ( r2_hidden(X11,k10_yellow_6(sK0,sK4(sK0,X10,X11)))
      | ~ v4_orders_2(X10)
      | ~ v7_waybel_0(X10)
      | ~ l1_waybel_0(X10,sK0)
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X10,X11)
      | v2_struct_0(X10) ) ),
    inference(subsumption_resolution,[],[f69,f35])).

fof(f69,plain,(
    ! [X10,X11] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(X10)
      | ~ v4_orders_2(X10)
      | ~ v7_waybel_0(X10)
      | ~ l1_waybel_0(X10,sK0)
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X10,X11)
      | r2_hidden(X11,k10_yellow_6(sK0,sK4(sK0,X10,X11))) ) ),
    inference(subsumption_resolution,[],[f64,f31])).

fof(f64,plain,(
    ! [X10,X11] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X10)
      | ~ v4_orders_2(X10)
      | ~ v7_waybel_0(X10)
      | ~ l1_waybel_0(X10,sK0)
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X10,X11)
      | r2_hidden(X11,k10_yellow_6(sK0,sK4(sK0,X10,X11))) ) ),
    inference(resolution,[],[f32,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | r2_hidden(X2,k10_yellow_6(X0,sK4(X0,X1,X2))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X2,k10_yellow_6(X0,X3))
                  & m2_yellow_6(X3,X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X2,k10_yellow_6(X0,X3))
                  & m2_yellow_6(X3,X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( ! [X3] :
                      ( m2_yellow_6(X3,X0,X1)
                     => ~ r2_hidden(X2,k10_yellow_6(X0,X3)) )
                  & r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_waybel_9)).

fof(f351,plain,(
    ~ r2_hidden(sK2,k10_yellow_6(sK0,sK4(sK0,sK5(sK0,sK1,sK2),sK2))) ),
    inference(subsumption_resolution,[],[f350,f27])).

fof(f350,plain,
    ( v2_struct_0(sK1)
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,sK4(sK0,sK5(sK0,sK1,sK2),sK2))) ),
    inference(subsumption_resolution,[],[f349,f26])).

fof(f349,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,sK1))
    | v2_struct_0(sK1)
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,sK4(sK0,sK5(sK0,sK1,sK2),sK2))) ),
    inference(subsumption_resolution,[],[f348,f24])).

fof(f348,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(sK2,k10_yellow_6(sK0,sK1))
    | v2_struct_0(sK1)
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,sK4(sK0,sK5(sK0,sK1,sK2),sK2))) ),
    inference(subsumption_resolution,[],[f347,f30])).

fof(f347,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(sK2,k10_yellow_6(sK0,sK1))
    | v2_struct_0(sK1)
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,sK4(sK0,sK5(sK0,sK1,sK2),sK2))) ),
    inference(subsumption_resolution,[],[f346,f29])).

fof(f346,plain,
    ( ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(sK2,k10_yellow_6(sK0,sK1))
    | v2_struct_0(sK1)
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,sK4(sK0,sK5(sK0,sK1,sK2),sK2))) ),
    inference(subsumption_resolution,[],[f342,f28])).

fof(f342,plain,
    ( ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(sK2,k10_yellow_6(sK0,sK1))
    | v2_struct_0(sK1)
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,sK4(sK0,sK5(sK0,sK1,sK2),sK2))) ),
    inference(resolution,[],[f341,f202])).

fof(f202,plain,(
    ! [X4,X5,X3] :
      ( ~ m2_yellow_6(X5,sK0,sK5(sK0,X3,X4))
      | ~ v4_orders_2(X3)
      | ~ v7_waybel_0(X3)
      | ~ l1_waybel_0(X3,sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,k10_yellow_6(sK0,X3))
      | v2_struct_0(X3)
      | ~ r2_hidden(X4,k10_yellow_6(sK0,X5)) ) ),
    inference(subsumption_resolution,[],[f66,f35])).

fof(f66,plain,(
    ! [X4,X5,X3] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(X3)
      | ~ v4_orders_2(X3)
      | ~ v7_waybel_0(X3)
      | ~ l1_waybel_0(X3,sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,k10_yellow_6(sK0,X3))
      | ~ m2_yellow_6(X5,sK0,sK5(sK0,X3,X4))
      | ~ r2_hidden(X4,k10_yellow_6(sK0,X5)) ) ),
    inference(subsumption_resolution,[],[f61,f31])).

fof(f61,plain,(
    ! [X4,X5,X3] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X3)
      | ~ v4_orders_2(X3)
      | ~ v7_waybel_0(X3)
      | ~ l1_waybel_0(X3,sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,k10_yellow_6(sK0,X3))
      | ~ m2_yellow_6(X5,sK0,sK5(sK0,X3,X4))
      | ~ r2_hidden(X4,k10_yellow_6(sK0,X5)) ) ),
    inference(resolution,[],[f32,f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ m2_yellow_6(X4,X0,sK5(X0,X1,X2))
      | ~ r2_hidden(X2,k10_yellow_6(X0,X4)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f341,plain,(
    m2_yellow_6(sK4(sK0,sK5(sK0,sK1,sK2),sK2),sK0,sK5(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f340,f35])).

fof(f340,plain,
    ( m2_yellow_6(sK4(sK0,sK5(sK0,sK1,sK2),sK2),sK0,sK5(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f339,f36])).

fof(f339,plain,
    ( ~ l1_struct_0(sK0)
    | m2_yellow_6(sK4(sK0,sK5(sK0,sK1,sK2),sK2),sK0,sK5(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f338,f30])).

fof(f338,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | m2_yellow_6(sK4(sK0,sK5(sK0,sK1,sK2),sK2),sK0,sK5(sK0,sK1,sK2))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f337,f31])).

fof(f337,plain,
    ( v2_struct_0(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | m2_yellow_6(sK4(sK0,sK5(sK0,sK1,sK2),sK2),sK0,sK5(sK0,sK1,sK2))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f298,f137])).

fof(f298,plain,(
    ! [X2] :
      ( ~ m2_yellow_6(sK5(sK0,sK1,sK2),X2,sK1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(sK1,X2)
      | m2_yellow_6(sK4(sK0,sK5(sK0,sK1,sK2),sK2),sK0,sK5(sK0,sK1,sK2))
      | ~ l1_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f295,f53])).

fof(f295,plain,(
    ! [X2] :
      ( v2_struct_0(sK5(sK0,sK1,sK2))
      | m2_yellow_6(sK4(sK0,sK5(sK0,sK1,sK2),sK2),sK0,sK5(sK0,sK1,sK2))
      | v2_struct_0(X2)
      | ~ l1_waybel_0(sK1,X2)
      | ~ m2_yellow_6(sK5(sK0,sK1,sK2),X2,sK1)
      | ~ l1_struct_0(X2) ) ),
    inference(resolution,[],[f292,f55])).

fof(f292,plain,
    ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | m2_yellow_6(sK4(sK0,sK5(sK0,sK1,sK2),sK2),sK0,sK5(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f291,f24])).

% (12325)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (12334)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (12319)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (12326)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (12324)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (12317)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (12323)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (12313)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% (12331)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (12312)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% (12335)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f291,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | m2_yellow_6(sK4(sK0,sK5(sK0,sK1,sK2),sK2),sK0,sK5(sK0,sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f290])).

fof(f290,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | m2_yellow_6(sK4(sK0,sK5(sK0,sK1,sK2),sK2),sK0,sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2)) ),
    inference(resolution,[],[f159,f208])).

fof(f159,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK5(sK0,sK1,sK2),X0)
      | v2_struct_0(sK5(sK0,sK1,sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK5(sK0,sK1,sK2))
      | m2_yellow_6(sK4(sK0,sK5(sK0,sK1,sK2),X0),sK0,sK5(sK0,sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f157,f150])).

fof(f157,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
      | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
      | v2_struct_0(sK5(sK0,sK1,sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK5(sK0,sK1,sK2),X0)
      | m2_yellow_6(sK4(sK0,sK5(sK0,sK1,sK2),X0),sK0,sK5(sK0,sK1,sK2)) ) ),
    inference(resolution,[],[f156,f96])).

fof(f96,plain,(
    ! [X8,X9] :
      ( ~ l1_waybel_0(X8,sK0)
      | ~ v4_orders_2(X8)
      | ~ v7_waybel_0(X8)
      | v2_struct_0(X8)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X8,X9)
      | m2_yellow_6(sK4(sK0,X8,X9),sK0,X8) ) ),
    inference(subsumption_resolution,[],[f68,f35])).

fof(f68,plain,(
    ! [X8,X9] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(X8)
      | ~ v4_orders_2(X8)
      | ~ v7_waybel_0(X8)
      | ~ l1_waybel_0(X8,sK0)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X8,X9)
      | m2_yellow_6(sK4(sK0,X8,X9),sK0,X8) ) ),
    inference(subsumption_resolution,[],[f63,f31])).

fof(f63,plain,(
    ! [X8,X9] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X8)
      | ~ v4_orders_2(X8)
      | ~ v7_waybel_0(X8)
      | ~ l1_waybel_0(X8,sK0)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X8,X9)
      | m2_yellow_6(sK4(sK0,X8,X9),sK0,X8) ) ),
    inference(resolution,[],[f32,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | m2_yellow_6(sK4(X0,X1,X2),X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:03:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.46  % (12315)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.48  % (12332)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.49  % (12310)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.49  % (12340)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.49  % (12333)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.50  % (12311)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.50  % (12316)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.50  % (12314)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.50  % (12327)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.50  % (12322)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.50  % (12321)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.50  % (12332)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f375,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(subsumption_resolution,[],[f374,f35])).
% 0.19/0.50  fof(f35,plain,(
% 0.19/0.50    l1_pre_topc(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f11])).
% 0.19/0.50  fof(f11,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X4] : (~r2_hidden(X4,k10_yellow_6(X0,X1)) & r3_waybel_9(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) & ! [X2] : (! [X3] : (X2 = X3 | ~r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f10])).
% 0.19/0.50  fof(f10,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : ((? [X4] : ((~r2_hidden(X4,k10_yellow_6(X0,X1)) & r3_waybel_9(X0,X1,X4)) & m1_subset_1(X4,u1_struct_0(X0))) & ! [X2] : (! [X3] : ((X2 = X3 | (~r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f9])).
% 0.19/0.50  fof(f9,plain,(
% 0.19/0.50    ~! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2)) => X2 = X3))) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X4) => r2_hidden(X4,k10_yellow_6(X0,X1)))))))),
% 0.19/0.50    inference(rectify,[],[f8])).
% 0.19/0.50  fof(f8,negated_conjecture,(
% 0.19/0.50    ~! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2)) => X2 = X3))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) => r2_hidden(X2,k10_yellow_6(X0,X1)))))))),
% 0.19/0.50    inference(negated_conjecture,[],[f7])).
% 0.19/0.50  fof(f7,conjecture,(
% 0.19/0.50    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X3) & r3_waybel_9(X0,X1,X2)) => X2 = X3))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) => r2_hidden(X2,k10_yellow_6(X0,X1)))))))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_waybel_9)).
% 0.19/0.50  fof(f374,plain,(
% 0.19/0.50    ~l1_pre_topc(sK0)),
% 0.19/0.50    inference(resolution,[],[f373,f36])).
% 0.19/0.50  fof(f36,plain,(
% 0.19/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f12])).
% 0.19/0.50  fof(f12,plain,(
% 0.19/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f1])).
% 0.19/0.50  fof(f1,axiom,(
% 0.19/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.19/0.50  fof(f373,plain,(
% 0.19/0.50    ~l1_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f372,f31])).
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    ~v2_struct_0(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f11])).
% 0.19/0.50  fof(f372,plain,(
% 0.19/0.50    v2_struct_0(sK0) | ~l1_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f371,f30])).
% 0.19/0.50  fof(f30,plain,(
% 0.19/0.50    l1_waybel_0(sK1,sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f11])).
% 0.19/0.50  fof(f371,plain,(
% 0.19/0.50    ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0) | ~l1_struct_0(sK0)),
% 0.19/0.50    inference(resolution,[],[f370,f137])).
% 0.19/0.50  fof(f137,plain,(
% 0.19/0.50    m2_yellow_6(sK5(sK0,sK1,sK2),sK0,sK1)),
% 0.19/0.50    inference(subsumption_resolution,[],[f136,f27])).
% 0.19/0.50  fof(f27,plain,(
% 0.19/0.50    ~v2_struct_0(sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f11])).
% 0.19/0.50  fof(f136,plain,(
% 0.19/0.50    v2_struct_0(sK1) | m2_yellow_6(sK5(sK0,sK1,sK2),sK0,sK1)),
% 0.19/0.50    inference(subsumption_resolution,[],[f135,f24])).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.19/0.50    inference(cnf_transformation,[],[f11])).
% 0.19/0.50  fof(f135,plain,(
% 0.19/0.50    ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(sK1) | m2_yellow_6(sK5(sK0,sK1,sK2),sK0,sK1)),
% 0.19/0.50    inference(subsumption_resolution,[],[f134,f30])).
% 0.19/0.50  fof(f134,plain,(
% 0.19/0.50    ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(sK1) | m2_yellow_6(sK5(sK0,sK1,sK2),sK0,sK1)),
% 0.19/0.50    inference(subsumption_resolution,[],[f133,f29])).
% 0.19/0.50  fof(f29,plain,(
% 0.19/0.50    v7_waybel_0(sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f11])).
% 0.19/0.50  fof(f133,plain,(
% 0.19/0.50    ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(sK1) | m2_yellow_6(sK5(sK0,sK1,sK2),sK0,sK1)),
% 0.19/0.50    inference(subsumption_resolution,[],[f132,f28])).
% 0.19/0.50  fof(f28,plain,(
% 0.19/0.50    v4_orders_2(sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f11])).
% 0.19/0.50  fof(f132,plain,(
% 0.19/0.50    ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(sK1) | m2_yellow_6(sK5(sK0,sK1,sK2),sK0,sK1)),
% 0.19/0.50    inference(resolution,[],[f131,f26])).
% 0.19/0.50  fof(f26,plain,(
% 0.19/0.50    ~r2_hidden(sK2,k10_yellow_6(sK0,sK1))),
% 0.19/0.50    inference(cnf_transformation,[],[f11])).
% 0.19/0.50  fof(f131,plain,(
% 0.19/0.50    ( ! [X6,X7] : (r2_hidden(X7,k10_yellow_6(sK0,X6)) | ~v4_orders_2(X6) | ~v7_waybel_0(X6) | ~l1_waybel_0(X6,sK0) | ~m1_subset_1(X7,u1_struct_0(sK0)) | v2_struct_0(X6) | m2_yellow_6(sK5(sK0,X6,X7),sK0,X6)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f67,f35])).
% 0.19/0.50  fof(f67,plain,(
% 0.19/0.50    ( ! [X6,X7] : (~l1_pre_topc(sK0) | v2_struct_0(X6) | ~v4_orders_2(X6) | ~v7_waybel_0(X6) | ~l1_waybel_0(X6,sK0) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_hidden(X7,k10_yellow_6(sK0,X6)) | m2_yellow_6(sK5(sK0,X6,X7),sK0,X6)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f62,f31])).
% 0.19/0.50  fof(f62,plain,(
% 0.19/0.50    ( ! [X6,X7] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X6) | ~v4_orders_2(X6) | ~v7_waybel_0(X6) | ~l1_waybel_0(X6,sK0) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_hidden(X7,k10_yellow_6(sK0,X6)) | m2_yellow_6(sK5(sK0,X6,X7),sK0,X6)) )),
% 0.19/0.50    inference(resolution,[],[f32,f42])).
% 0.19/0.50  fof(f42,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,k10_yellow_6(X0,X1)) | m2_yellow_6(sK5(X0,X1,X2),X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f18])).
% 0.19/0.50  fof(f18,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (! [X4] : (~r2_hidden(X2,k10_yellow_6(X0,X4)) | ~m2_yellow_6(X4,X0,X3)) & m2_yellow_6(X3,X0,X1)) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f17])).
% 0.19/0.50  fof(f17,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (! [X4] : (~r2_hidden(X2,k10_yellow_6(X0,X4)) | ~m2_yellow_6(X4,X0,X3)) & m2_yellow_6(X3,X0,X1)) | r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ? [X4] : (r2_hidden(X2,k10_yellow_6(X0,X4)) & m2_yellow_6(X4,X0,X3))) & ~r2_hidden(X2,k10_yellow_6(X0,X1))))))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_yellow_6)).
% 0.19/0.50  fof(f32,plain,(
% 0.19/0.50    v2_pre_topc(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f11])).
% 0.19/0.50  fof(f370,plain,(
% 0.19/0.50    ( ! [X2] : (~m2_yellow_6(sK5(sK0,sK1,sK2),X2,sK1) | ~l1_waybel_0(sK1,X2) | v2_struct_0(X2) | ~l1_struct_0(X2)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f367,f53])).
% 0.19/0.50  fof(f53,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~v2_struct_0(X1) | v2_struct_0(X0) | ~l1_waybel_0(sK1,X0) | ~m2_yellow_6(X1,X0,sK1) | ~l1_struct_0(X0)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f52,f28])).
% 0.19/0.50  fof(f52,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~l1_struct_0(X0) | ~v4_orders_2(sK1) | v2_struct_0(X0) | ~l1_waybel_0(sK1,X0) | ~m2_yellow_6(X1,X0,sK1) | ~v2_struct_0(X1)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f48,f27])).
% 0.19/0.50  fof(f48,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~l1_struct_0(X0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(X0) | ~l1_waybel_0(sK1,X0) | ~m2_yellow_6(X1,X0,sK1) | ~v2_struct_0(X1)) )),
% 0.19/0.50    inference(resolution,[],[f29,f44])).
% 0.19/0.50  fof(f44,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X0) | ~l1_waybel_0(X1,X0) | ~m2_yellow_6(X2,X0,X1) | ~v2_struct_0(X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f22])).
% 0.19/0.50  fof(f22,plain,(
% 0.19/0.50    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f21])).
% 0.19/0.50  fof(f21,plain,(
% 0.19/0.50    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_yellow_6)).
% 0.19/0.50  fof(f367,plain,(
% 0.19/0.50    ( ! [X2] : (v2_struct_0(sK5(sK0,sK1,sK2)) | v2_struct_0(X2) | ~l1_waybel_0(sK1,X2) | ~m2_yellow_6(sK5(sK0,sK1,sK2),X2,sK1) | ~l1_struct_0(X2)) )),
% 0.19/0.50    inference(resolution,[],[f363,f55])).
% 0.19/0.50  fof(f55,plain,(
% 0.19/0.50    ( ! [X2,X3] : (v4_orders_2(X3) | v2_struct_0(X2) | ~l1_waybel_0(sK1,X2) | ~m2_yellow_6(X3,X2,sK1) | ~l1_struct_0(X2)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f54,f28])).
% 0.19/0.50  fof(f54,plain,(
% 0.19/0.50    ( ! [X2,X3] : (~l1_struct_0(X2) | ~v4_orders_2(sK1) | v2_struct_0(X2) | ~l1_waybel_0(sK1,X2) | ~m2_yellow_6(X3,X2,sK1) | v4_orders_2(X3)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f49,f27])).
% 0.19/0.50  fof(f49,plain,(
% 0.19/0.50    ( ! [X2,X3] : (~l1_struct_0(X2) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(X2) | ~l1_waybel_0(sK1,X2) | ~m2_yellow_6(X3,X2,sK1) | v4_orders_2(X3)) )),
% 0.19/0.50    inference(resolution,[],[f29,f45])).
% 0.19/0.50  fof(f45,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X0) | ~l1_waybel_0(X1,X0) | ~m2_yellow_6(X2,X0,X1) | v4_orders_2(X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f22])).
% 0.19/0.50  fof(f363,plain,(
% 0.19/0.50    ~v4_orders_2(sK5(sK0,sK1,sK2)) | v2_struct_0(sK5(sK0,sK1,sK2))),
% 0.19/0.50    inference(subsumption_resolution,[],[f362,f208])).
% 0.19/0.50  fof(f208,plain,(
% 0.19/0.50    r3_waybel_9(sK0,sK5(sK0,sK1,sK2),sK2) | v2_struct_0(sK5(sK0,sK1,sK2)) | ~v4_orders_2(sK5(sK0,sK1,sK2))),
% 0.19/0.50    inference(backward_demodulation,[],[f160,f207])).
% 0.19/0.50  fof(f207,plain,(
% 0.19/0.50    sK2 = sK3(sK0,sK5(sK0,sK1,sK2))),
% 0.19/0.50    inference(subsumption_resolution,[],[f206,f35])).
% 0.19/0.50  fof(f206,plain,(
% 0.19/0.50    sK2 = sK3(sK0,sK5(sK0,sK1,sK2)) | ~l1_pre_topc(sK0)),
% 0.19/0.50    inference(resolution,[],[f205,f36])).
% 0.19/0.50  fof(f205,plain,(
% 0.19/0.50    ~l1_struct_0(sK0) | sK2 = sK3(sK0,sK5(sK0,sK1,sK2))),
% 0.19/0.50    inference(subsumption_resolution,[],[f204,f30])).
% 0.19/0.50  fof(f204,plain,(
% 0.19/0.50    ~l1_waybel_0(sK1,sK0) | sK2 = sK3(sK0,sK5(sK0,sK1,sK2)) | ~l1_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f203,f31])).
% 0.19/0.50  fof(f203,plain,(
% 0.19/0.50    v2_struct_0(sK0) | ~l1_waybel_0(sK1,sK0) | sK2 = sK3(sK0,sK5(sK0,sK1,sK2)) | ~l1_struct_0(sK0)),
% 0.19/0.50    inference(resolution,[],[f191,f137])).
% 0.19/0.50  fof(f191,plain,(
% 0.19/0.50    ( ! [X0] : (~m2_yellow_6(sK5(sK0,sK1,sK2),X0,sK1) | v2_struct_0(X0) | ~l1_waybel_0(sK1,X0) | sK2 = sK3(sK0,sK5(sK0,sK1,sK2)) | ~l1_struct_0(X0)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f190,f53])).
% 0.19/0.50  fof(f190,plain,(
% 0.19/0.50    ( ! [X0] : (v2_struct_0(sK5(sK0,sK1,sK2)) | sK2 = sK3(sK0,sK5(sK0,sK1,sK2)) | v2_struct_0(X0) | ~l1_waybel_0(sK1,X0) | ~m2_yellow_6(sK5(sK0,sK1,sK2),X0,sK1) | ~l1_struct_0(X0)) )),
% 0.19/0.50    inference(resolution,[],[f189,f55])).
% 0.19/0.50  fof(f189,plain,(
% 0.19/0.50    ~v4_orders_2(sK5(sK0,sK1,sK2)) | v2_struct_0(sK5(sK0,sK1,sK2)) | sK2 = sK3(sK0,sK5(sK0,sK1,sK2))),
% 0.19/0.50    inference(subsumption_resolution,[],[f188,f31])).
% 0.19/0.50  fof(f188,plain,(
% 0.19/0.50    sK2 = sK3(sK0,sK5(sK0,sK1,sK2)) | v2_struct_0(sK5(sK0,sK1,sK2)) | ~v4_orders_2(sK5(sK0,sK1,sK2)) | v2_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f187,f156])).
% 0.19/0.50  fof(f156,plain,(
% 0.19/0.50    l1_waybel_0(sK5(sK0,sK1,sK2),sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f155,f35])).
% 0.19/0.50  fof(f155,plain,(
% 0.19/0.50    l1_waybel_0(sK5(sK0,sK1,sK2),sK0) | ~l1_pre_topc(sK0)),
% 0.19/0.50    inference(resolution,[],[f146,f36])).
% 0.19/0.50  fof(f146,plain,(
% 0.19/0.50    ~l1_struct_0(sK0) | l1_waybel_0(sK5(sK0,sK1,sK2),sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f145,f30])).
% 0.19/0.50  fof(f145,plain,(
% 0.19/0.50    ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0) | l1_waybel_0(sK5(sK0,sK1,sK2),sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f139,f31])).
% 0.19/0.50  fof(f139,plain,(
% 0.19/0.50    v2_struct_0(sK0) | ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0) | l1_waybel_0(sK5(sK0,sK1,sK2),sK0)),
% 0.19/0.50    inference(resolution,[],[f137,f59])).
% 0.19/0.50  fof(f59,plain,(
% 0.19/0.50    ( ! [X6,X7] : (~m2_yellow_6(X7,X6,sK1) | v2_struct_0(X6) | ~l1_waybel_0(sK1,X6) | ~l1_struct_0(X6) | l1_waybel_0(X7,X6)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f58,f28])).
% 0.19/0.50  fof(f58,plain,(
% 0.19/0.50    ( ! [X6,X7] : (~l1_struct_0(X6) | ~v4_orders_2(sK1) | v2_struct_0(X6) | ~l1_waybel_0(sK1,X6) | ~m2_yellow_6(X7,X6,sK1) | l1_waybel_0(X7,X6)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f51,f27])).
% 0.19/0.50  fof(f51,plain,(
% 0.19/0.50    ( ! [X6,X7] : (~l1_struct_0(X6) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(X6) | ~l1_waybel_0(sK1,X6) | ~m2_yellow_6(X7,X6,sK1) | l1_waybel_0(X7,X6)) )),
% 0.19/0.50    inference(resolution,[],[f29,f47])).
% 0.19/0.50  fof(f47,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X0) | ~l1_waybel_0(X1,X0) | ~m2_yellow_6(X2,X0,X1) | l1_waybel_0(X2,X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f22])).
% 0.19/0.50  fof(f187,plain,(
% 0.19/0.50    sK2 = sK3(sK0,sK5(sK0,sK1,sK2)) | v2_struct_0(sK5(sK0,sK1,sK2)) | ~v4_orders_2(sK5(sK0,sK1,sK2)) | ~l1_waybel_0(sK5(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f186,f150])).
% 0.19/0.50  fof(f150,plain,(
% 0.19/0.50    v7_waybel_0(sK5(sK0,sK1,sK2))),
% 0.19/0.50    inference(subsumption_resolution,[],[f149,f35])).
% 0.19/0.50  fof(f149,plain,(
% 0.19/0.50    v7_waybel_0(sK5(sK0,sK1,sK2)) | ~l1_pre_topc(sK0)),
% 0.19/0.50    inference(resolution,[],[f148,f36])).
% 0.19/0.50  fof(f148,plain,(
% 0.19/0.50    ~l1_struct_0(sK0) | v7_waybel_0(sK5(sK0,sK1,sK2))),
% 0.19/0.50    inference(subsumption_resolution,[],[f147,f30])).
% 0.19/0.50  fof(f147,plain,(
% 0.19/0.50    ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0) | v7_waybel_0(sK5(sK0,sK1,sK2))),
% 0.19/0.50    inference(subsumption_resolution,[],[f140,f31])).
% 0.19/0.50  fof(f140,plain,(
% 0.19/0.50    v2_struct_0(sK0) | ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0) | v7_waybel_0(sK5(sK0,sK1,sK2))),
% 0.19/0.50    inference(resolution,[],[f137,f57])).
% 0.19/0.50  fof(f57,plain,(
% 0.19/0.50    ( ! [X4,X5] : (~m2_yellow_6(X5,X4,sK1) | v2_struct_0(X4) | ~l1_waybel_0(sK1,X4) | ~l1_struct_0(X4) | v7_waybel_0(X5)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f56,f28])).
% 0.19/0.50  fof(f56,plain,(
% 0.19/0.50    ( ! [X4,X5] : (~l1_struct_0(X4) | ~v4_orders_2(sK1) | v2_struct_0(X4) | ~l1_waybel_0(sK1,X4) | ~m2_yellow_6(X5,X4,sK1) | v7_waybel_0(X5)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f50,f27])).
% 0.19/0.50  fof(f50,plain,(
% 0.19/0.50    ( ! [X4,X5] : (~l1_struct_0(X4) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(X4) | ~l1_waybel_0(sK1,X4) | ~m2_yellow_6(X5,X4,sK1) | v7_waybel_0(X5)) )),
% 0.19/0.50    inference(resolution,[],[f29,f46])).
% 0.19/0.50  fof(f46,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X0) | ~l1_waybel_0(X1,X0) | ~m2_yellow_6(X2,X0,X1) | v7_waybel_0(X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f22])).
% 0.19/0.50  fof(f186,plain,(
% 0.19/0.50    sK2 = sK3(sK0,sK5(sK0,sK1,sK2)) | v2_struct_0(sK5(sK0,sK1,sK2)) | ~v4_orders_2(sK5(sK0,sK1,sK2)) | ~v7_waybel_0(sK5(sK0,sK1,sK2)) | ~l1_waybel_0(sK5(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f185,f35])).
% 0.19/0.50  fof(f185,plain,(
% 0.19/0.50    sK2 = sK3(sK0,sK5(sK0,sK1,sK2)) | ~l1_pre_topc(sK0) | v2_struct_0(sK5(sK0,sK1,sK2)) | ~v4_orders_2(sK5(sK0,sK1,sK2)) | ~v7_waybel_0(sK5(sK0,sK1,sK2)) | ~l1_waybel_0(sK5(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f184,f34])).
% 0.19/0.50  fof(f34,plain,(
% 0.19/0.50    v1_compts_1(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f11])).
% 0.19/0.50  fof(f184,plain,(
% 0.19/0.50    sK2 = sK3(sK0,sK5(sK0,sK1,sK2)) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK5(sK0,sK1,sK2)) | ~v4_orders_2(sK5(sK0,sK1,sK2)) | ~v7_waybel_0(sK5(sK0,sK1,sK2)) | ~l1_waybel_0(sK5(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f183,f33])).
% 0.19/0.50  fof(f33,plain,(
% 0.19/0.50    v8_pre_topc(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f11])).
% 0.19/0.50  fof(f183,plain,(
% 0.19/0.50    sK2 = sK3(sK0,sK5(sK0,sK1,sK2)) | ~v8_pre_topc(sK0) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK5(sK0,sK1,sK2)) | ~v4_orders_2(sK5(sK0,sK1,sK2)) | ~v7_waybel_0(sK5(sK0,sK1,sK2)) | ~l1_waybel_0(sK5(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f182,f32])).
% 0.19/0.50  fof(f182,plain,(
% 0.19/0.50    sK2 = sK3(sK0,sK5(sK0,sK1,sK2)) | ~v2_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK5(sK0,sK1,sK2)) | ~v4_orders_2(sK5(sK0,sK1,sK2)) | ~v7_waybel_0(sK5(sK0,sK1,sK2)) | ~l1_waybel_0(sK5(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.19/0.50    inference(resolution,[],[f180,f37])).
% 0.19/0.50  fof(f37,plain,(
% 0.19/0.50    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f14])).
% 0.19/0.50  fof(f14,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f13])).
% 0.19/0.50  fof(f13,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v1_compts_1(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f4])).
% 0.19/0.50  fof(f4,axiom,(
% 0.19/0.50    ! [X0] : ((l1_pre_topc(X0) & v1_compts_1(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_waybel_9)).
% 0.19/0.50  fof(f180,plain,(
% 0.19/0.50    ~m1_subset_1(sK3(sK0,sK5(sK0,sK1,sK2)),u1_struct_0(sK0)) | sK2 = sK3(sK0,sK5(sK0,sK1,sK2))),
% 0.19/0.50    inference(resolution,[],[f178,f75])).
% 0.19/0.50  fof(f75,plain,(
% 0.19/0.50    ( ! [X0] : (~r3_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK2 = X0) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f74,f24])).
% 0.19/0.50  fof(f74,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X0) | sK2 = X0) )),
% 0.19/0.50    inference(resolution,[],[f23,f25])).
% 0.19/0.50  fof(f25,plain,(
% 0.19/0.50    r3_waybel_9(sK0,sK1,sK2)),
% 0.19/0.50    inference(cnf_transformation,[],[f11])).
% 0.19/0.50  fof(f23,plain,(
% 0.19/0.50    ( ! [X2,X3] : (~r3_waybel_9(sK0,sK1,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK1,X3) | X2 = X3) )),
% 0.19/0.50    inference(cnf_transformation,[],[f11])).
% 0.19/0.50  fof(f178,plain,(
% 0.19/0.50    r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2)))),
% 0.19/0.50    inference(subsumption_resolution,[],[f177,f35])).
% 0.19/0.50  fof(f177,plain,(
% 0.19/0.50    r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2))) | ~l1_pre_topc(sK0)),
% 0.19/0.50    inference(resolution,[],[f176,f36])).
% 0.19/0.50  fof(f176,plain,(
% 0.19/0.50    ~l1_struct_0(sK0) | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2)))),
% 0.19/0.50    inference(subsumption_resolution,[],[f175,f30])).
% 0.19/0.50  fof(f175,plain,(
% 0.19/0.50    ~l1_waybel_0(sK1,sK0) | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2))) | ~l1_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f174,f31])).
% 0.19/0.50  fof(f174,plain,(
% 0.19/0.50    v2_struct_0(sK0) | ~l1_waybel_0(sK1,sK0) | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2))) | ~l1_struct_0(sK0)),
% 0.19/0.50    inference(resolution,[],[f173,f137])).
% 0.19/0.50  fof(f173,plain,(
% 0.19/0.50    ( ! [X0] : (~m2_yellow_6(sK5(sK0,sK1,sK2),X0,sK1) | v2_struct_0(X0) | ~l1_waybel_0(sK1,X0) | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2))) | ~l1_struct_0(X0)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f172,f53])).
% 0.19/0.50  fof(f172,plain,(
% 0.19/0.50    ( ! [X0] : (v2_struct_0(sK5(sK0,sK1,sK2)) | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2))) | v2_struct_0(X0) | ~l1_waybel_0(sK1,X0) | ~m2_yellow_6(sK5(sK0,sK1,sK2),X0,sK1) | ~l1_struct_0(X0)) )),
% 0.19/0.50    inference(resolution,[],[f171,f55])).
% 0.19/0.50  fof(f171,plain,(
% 0.19/0.50    ~v4_orders_2(sK5(sK0,sK1,sK2)) | v2_struct_0(sK5(sK0,sK1,sK2)) | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2)))),
% 0.19/0.50    inference(subsumption_resolution,[],[f170,f31])).
% 0.19/0.50  fof(f170,plain,(
% 0.19/0.50    ~v4_orders_2(sK5(sK0,sK1,sK2)) | v2_struct_0(sK5(sK0,sK1,sK2)) | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2))) | v2_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f169,f156])).
% 0.19/0.50  fof(f169,plain,(
% 0.19/0.50    ~v4_orders_2(sK5(sK0,sK1,sK2)) | v2_struct_0(sK5(sK0,sK1,sK2)) | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2))) | ~l1_waybel_0(sK5(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f168,f150])).
% 0.19/0.50  fof(f168,plain,(
% 0.19/0.50    ~v4_orders_2(sK5(sK0,sK1,sK2)) | v2_struct_0(sK5(sK0,sK1,sK2)) | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2))) | ~v7_waybel_0(sK5(sK0,sK1,sK2)) | ~l1_waybel_0(sK5(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f167,f35])).
% 0.19/0.50  fof(f167,plain,(
% 0.19/0.50    ~v4_orders_2(sK5(sK0,sK1,sK2)) | v2_struct_0(sK5(sK0,sK1,sK2)) | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2))) | ~l1_pre_topc(sK0) | ~v7_waybel_0(sK5(sK0,sK1,sK2)) | ~l1_waybel_0(sK5(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f166,f34])).
% 0.19/0.50  fof(f166,plain,(
% 0.19/0.50    ~v4_orders_2(sK5(sK0,sK1,sK2)) | v2_struct_0(sK5(sK0,sK1,sK2)) | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2))) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v7_waybel_0(sK5(sK0,sK1,sK2)) | ~l1_waybel_0(sK5(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f165,f33])).
% 0.19/0.50  fof(f165,plain,(
% 0.19/0.50    ~v4_orders_2(sK5(sK0,sK1,sK2)) | v2_struct_0(sK5(sK0,sK1,sK2)) | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2))) | ~v8_pre_topc(sK0) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v7_waybel_0(sK5(sK0,sK1,sK2)) | ~l1_waybel_0(sK5(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f164,f32])).
% 0.19/0.50  fof(f164,plain,(
% 0.19/0.50    ~v4_orders_2(sK5(sK0,sK1,sK2)) | v2_struct_0(sK5(sK0,sK1,sK2)) | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2))) | ~v2_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | ~v7_waybel_0(sK5(sK0,sK1,sK2)) | ~l1_waybel_0(sK5(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f163])).
% 0.19/0.50  fof(f163,plain,(
% 0.19/0.50    ~v4_orders_2(sK5(sK0,sK1,sK2)) | v2_struct_0(sK5(sK0,sK1,sK2)) | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2))) | ~v2_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v1_compts_1(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK5(sK0,sK1,sK2)) | ~v4_orders_2(sK5(sK0,sK1,sK2)) | ~v7_waybel_0(sK5(sK0,sK1,sK2)) | ~l1_waybel_0(sK5(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.19/0.50    inference(resolution,[],[f161,f37])).
% 0.19/0.50  fof(f161,plain,(
% 0.19/0.50    ~m1_subset_1(sK3(sK0,sK5(sK0,sK1,sK2)),u1_struct_0(sK0)) | ~v4_orders_2(sK5(sK0,sK1,sK2)) | v2_struct_0(sK5(sK0,sK1,sK2)) | r3_waybel_9(sK0,sK1,sK3(sK0,sK5(sK0,sK1,sK2)))),
% 0.19/0.50    inference(resolution,[],[f160,f144])).
% 0.19/0.50  fof(f144,plain,(
% 0.19/0.50    ( ! [X0] : (~r3_waybel_9(sK0,sK5(sK0,sK1,sK2),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_waybel_9(sK0,sK1,X0)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f143,f27])).
% 0.19/0.50  fof(f143,plain,(
% 0.19/0.50    ( ! [X0] : (v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK5(sK0,sK1,sK2),X0) | r3_waybel_9(sK0,sK1,X0)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f142,f30])).
% 0.19/0.50  fof(f142,plain,(
% 0.19/0.50    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK5(sK0,sK1,sK2),X0) | r3_waybel_9(sK0,sK1,X0)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f141,f29])).
% 0.19/0.50  fof(f141,plain,(
% 0.19/0.50    ( ! [X0] : (~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK5(sK0,sK1,sK2),X0) | r3_waybel_9(sK0,sK1,X0)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f138,f28])).
% 0.19/0.50  fof(f138,plain,(
% 0.19/0.50    ( ! [X0] : (~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK5(sK0,sK1,sK2),X0) | r3_waybel_9(sK0,sK1,X0)) )),
% 0.19/0.50    inference(resolution,[],[f137,f124])).
% 0.19/0.50  fof(f124,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~m2_yellow_6(X1,sK0,X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X1,X2) | r3_waybel_9(sK0,X0,X2)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f65,f35])).
% 0.19/0.50  fof(f65,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m2_yellow_6(X1,sK0,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X1,X2) | r3_waybel_9(sK0,X0,X2)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f60,f31])).
% 0.19/0.50  fof(f60,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m2_yellow_6(X1,sK0,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X1,X2) | r3_waybel_9(sK0,X0,X2)) )),
% 0.19/0.50    inference(resolution,[],[f32,f43])).
% 0.19/0.51  fof(f43,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m2_yellow_6(X2,X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r3_waybel_9(X0,X2,X3) | r3_waybel_9(X0,X1,X3)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f20])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f19])).
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f5])).
% 0.19/0.51  fof(f5,axiom,(
% 0.19/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r3_waybel_9(X0,X1,X3))))))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_waybel_9)).
% 0.19/0.51  fof(f160,plain,(
% 0.19/0.51    r3_waybel_9(sK0,sK5(sK0,sK1,sK2),sK3(sK0,sK5(sK0,sK1,sK2))) | v2_struct_0(sK5(sK0,sK1,sK2)) | ~v4_orders_2(sK5(sK0,sK1,sK2))),
% 0.19/0.51    inference(subsumption_resolution,[],[f158,f150])).
% 0.19/0.51  fof(f158,plain,(
% 0.19/0.51    ~v4_orders_2(sK5(sK0,sK1,sK2)) | ~v7_waybel_0(sK5(sK0,sK1,sK2)) | v2_struct_0(sK5(sK0,sK1,sK2)) | r3_waybel_9(sK0,sK5(sK0,sK1,sK2),sK3(sK0,sK5(sK0,sK1,sK2)))),
% 0.19/0.51    inference(resolution,[],[f156,f77])).
% 0.19/0.51  fof(f77,plain,(
% 0.19/0.51    ( ! [X0] : (~l1_waybel_0(X0,sK0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | v2_struct_0(X0) | r3_waybel_9(sK0,X0,sK3(sK0,X0))) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f73,f35])).
% 0.19/0.51  fof(f73,plain,(
% 0.19/0.51    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | r3_waybel_9(sK0,X0,sK3(sK0,X0))) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f72,f31])).
% 0.19/0.51  fof(f72,plain,(
% 0.19/0.51    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | r3_waybel_9(sK0,X0,sK3(sK0,X0))) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f71,f33])).
% 0.19/0.51  fof(f71,plain,(
% 0.19/0.51    ( ! [X0] : (~v8_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | r3_waybel_9(sK0,X0,sK3(sK0,X0))) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f70,f32])).
% 0.19/0.51  fof(f70,plain,(
% 0.19/0.51    ( ! [X0] : (~v2_pre_topc(sK0) | ~v8_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | r3_waybel_9(sK0,X0,sK3(sK0,X0))) )),
% 0.19/0.51    inference(resolution,[],[f34,f38])).
% 0.19/0.51  fof(f38,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~v1_compts_1(X0) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | r3_waybel_9(X0,X1,sK3(X0,X1))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f14])).
% 0.19/0.51  fof(f362,plain,(
% 0.19/0.51    ~v4_orders_2(sK5(sK0,sK1,sK2)) | ~r3_waybel_9(sK0,sK5(sK0,sK1,sK2),sK2) | v2_struct_0(sK5(sK0,sK1,sK2))),
% 0.19/0.51    inference(subsumption_resolution,[],[f361,f24])).
% 0.19/0.51  fof(f361,plain,(
% 0.19/0.51    ~v4_orders_2(sK5(sK0,sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK5(sK0,sK1,sK2),sK2) | v2_struct_0(sK5(sK0,sK1,sK2))),
% 0.19/0.51    inference(subsumption_resolution,[],[f360,f156])).
% 0.19/0.51  fof(f360,plain,(
% 0.19/0.51    ~v4_orders_2(sK5(sK0,sK1,sK2)) | ~l1_waybel_0(sK5(sK0,sK1,sK2),sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK5(sK0,sK1,sK2),sK2) | v2_struct_0(sK5(sK0,sK1,sK2))),
% 0.19/0.51    inference(subsumption_resolution,[],[f358,f150])).
% 0.19/0.51  fof(f358,plain,(
% 0.19/0.51    ~v4_orders_2(sK5(sK0,sK1,sK2)) | ~v7_waybel_0(sK5(sK0,sK1,sK2)) | ~l1_waybel_0(sK5(sK0,sK1,sK2),sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK5(sK0,sK1,sK2),sK2) | v2_struct_0(sK5(sK0,sK1,sK2))),
% 0.19/0.51    inference(resolution,[],[f351,f162])).
% 0.19/0.51  fof(f162,plain,(
% 0.19/0.51    ( ! [X10,X11] : (r2_hidden(X11,k10_yellow_6(sK0,sK4(sK0,X10,X11))) | ~v4_orders_2(X10) | ~v7_waybel_0(X10) | ~l1_waybel_0(X10,sK0) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X10,X11) | v2_struct_0(X10)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f69,f35])).
% 0.19/0.51  fof(f69,plain,(
% 0.19/0.51    ( ! [X10,X11] : (~l1_pre_topc(sK0) | v2_struct_0(X10) | ~v4_orders_2(X10) | ~v7_waybel_0(X10) | ~l1_waybel_0(X10,sK0) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X10,X11) | r2_hidden(X11,k10_yellow_6(sK0,sK4(sK0,X10,X11)))) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f64,f31])).
% 0.19/0.51  fof(f64,plain,(
% 0.19/0.51    ( ! [X10,X11] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X10) | ~v4_orders_2(X10) | ~v7_waybel_0(X10) | ~l1_waybel_0(X10,sK0) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X10,X11) | r2_hidden(X11,k10_yellow_6(sK0,sK4(sK0,X10,X11)))) )),
% 0.19/0.51    inference(resolution,[],[f32,f40])).
% 0.19/0.51  fof(f40,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,sK4(X0,X1,X2)))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f16])).
% 0.19/0.51  fof(f16,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f15])).
% 0.19/0.51  fof(f15,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f6])).
% 0.19/0.51  fof(f6,axiom,(
% 0.19/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_waybel_9)).
% 0.19/0.51  fof(f351,plain,(
% 0.19/0.51    ~r2_hidden(sK2,k10_yellow_6(sK0,sK4(sK0,sK5(sK0,sK1,sK2),sK2)))),
% 0.19/0.51    inference(subsumption_resolution,[],[f350,f27])).
% 0.19/0.51  fof(f350,plain,(
% 0.19/0.51    v2_struct_0(sK1) | ~r2_hidden(sK2,k10_yellow_6(sK0,sK4(sK0,sK5(sK0,sK1,sK2),sK2)))),
% 0.19/0.51    inference(subsumption_resolution,[],[f349,f26])).
% 0.19/0.51  fof(f349,plain,(
% 0.19/0.51    r2_hidden(sK2,k10_yellow_6(sK0,sK1)) | v2_struct_0(sK1) | ~r2_hidden(sK2,k10_yellow_6(sK0,sK4(sK0,sK5(sK0,sK1,sK2),sK2)))),
% 0.19/0.51    inference(subsumption_resolution,[],[f348,f24])).
% 0.19/0.51  fof(f348,plain,(
% 0.19/0.51    ~m1_subset_1(sK2,u1_struct_0(sK0)) | r2_hidden(sK2,k10_yellow_6(sK0,sK1)) | v2_struct_0(sK1) | ~r2_hidden(sK2,k10_yellow_6(sK0,sK4(sK0,sK5(sK0,sK1,sK2),sK2)))),
% 0.19/0.51    inference(subsumption_resolution,[],[f347,f30])).
% 0.19/0.51  fof(f347,plain,(
% 0.19/0.51    ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | r2_hidden(sK2,k10_yellow_6(sK0,sK1)) | v2_struct_0(sK1) | ~r2_hidden(sK2,k10_yellow_6(sK0,sK4(sK0,sK5(sK0,sK1,sK2),sK2)))),
% 0.19/0.51    inference(subsumption_resolution,[],[f346,f29])).
% 0.19/0.51  fof(f346,plain,(
% 0.19/0.51    ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | r2_hidden(sK2,k10_yellow_6(sK0,sK1)) | v2_struct_0(sK1) | ~r2_hidden(sK2,k10_yellow_6(sK0,sK4(sK0,sK5(sK0,sK1,sK2),sK2)))),
% 0.19/0.51    inference(subsumption_resolution,[],[f342,f28])).
% 0.19/0.51  fof(f342,plain,(
% 0.19/0.51    ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | r2_hidden(sK2,k10_yellow_6(sK0,sK1)) | v2_struct_0(sK1) | ~r2_hidden(sK2,k10_yellow_6(sK0,sK4(sK0,sK5(sK0,sK1,sK2),sK2)))),
% 0.19/0.51    inference(resolution,[],[f341,f202])).
% 0.19/0.51  fof(f202,plain,(
% 0.19/0.51    ( ! [X4,X5,X3] : (~m2_yellow_6(X5,sK0,sK5(sK0,X3,X4)) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r2_hidden(X4,k10_yellow_6(sK0,X3)) | v2_struct_0(X3) | ~r2_hidden(X4,k10_yellow_6(sK0,X5))) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f66,f35])).
% 0.19/0.51  fof(f66,plain,(
% 0.19/0.51    ( ! [X4,X5,X3] : (~l1_pre_topc(sK0) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r2_hidden(X4,k10_yellow_6(sK0,X3)) | ~m2_yellow_6(X5,sK0,sK5(sK0,X3,X4)) | ~r2_hidden(X4,k10_yellow_6(sK0,X5))) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f61,f31])).
% 0.19/0.51  fof(f61,plain,(
% 0.19/0.51    ( ! [X4,X5,X3] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X3) | ~v4_orders_2(X3) | ~v7_waybel_0(X3) | ~l1_waybel_0(X3,sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r2_hidden(X4,k10_yellow_6(sK0,X3)) | ~m2_yellow_6(X5,sK0,sK5(sK0,X3,X4)) | ~r2_hidden(X4,k10_yellow_6(sK0,X5))) )),
% 0.19/0.51    inference(resolution,[],[f32,f41])).
% 0.19/0.51  fof(f41,plain,(
% 0.19/0.51    ( ! [X4,X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m2_yellow_6(X4,X0,sK5(X0,X1,X2)) | ~r2_hidden(X2,k10_yellow_6(X0,X4))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f18])).
% 0.19/0.51  fof(f341,plain,(
% 0.19/0.51    m2_yellow_6(sK4(sK0,sK5(sK0,sK1,sK2),sK2),sK0,sK5(sK0,sK1,sK2))),
% 0.19/0.51    inference(subsumption_resolution,[],[f340,f35])).
% 0.19/0.51  fof(f340,plain,(
% 0.19/0.51    m2_yellow_6(sK4(sK0,sK5(sK0,sK1,sK2),sK2),sK0,sK5(sK0,sK1,sK2)) | ~l1_pre_topc(sK0)),
% 0.19/0.51    inference(resolution,[],[f339,f36])).
% 0.19/0.51  fof(f339,plain,(
% 0.19/0.51    ~l1_struct_0(sK0) | m2_yellow_6(sK4(sK0,sK5(sK0,sK1,sK2),sK2),sK0,sK5(sK0,sK1,sK2))),
% 0.19/0.51    inference(subsumption_resolution,[],[f338,f30])).
% 0.19/0.51  fof(f338,plain,(
% 0.19/0.51    ~l1_waybel_0(sK1,sK0) | m2_yellow_6(sK4(sK0,sK5(sK0,sK1,sK2),sK2),sK0,sK5(sK0,sK1,sK2)) | ~l1_struct_0(sK0)),
% 0.19/0.51    inference(subsumption_resolution,[],[f337,f31])).
% 0.19/0.51  fof(f337,plain,(
% 0.19/0.51    v2_struct_0(sK0) | ~l1_waybel_0(sK1,sK0) | m2_yellow_6(sK4(sK0,sK5(sK0,sK1,sK2),sK2),sK0,sK5(sK0,sK1,sK2)) | ~l1_struct_0(sK0)),
% 0.19/0.51    inference(resolution,[],[f298,f137])).
% 0.19/0.51  fof(f298,plain,(
% 0.19/0.51    ( ! [X2] : (~m2_yellow_6(sK5(sK0,sK1,sK2),X2,sK1) | v2_struct_0(X2) | ~l1_waybel_0(sK1,X2) | m2_yellow_6(sK4(sK0,sK5(sK0,sK1,sK2),sK2),sK0,sK5(sK0,sK1,sK2)) | ~l1_struct_0(X2)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f295,f53])).
% 0.19/0.51  fof(f295,plain,(
% 0.19/0.51    ( ! [X2] : (v2_struct_0(sK5(sK0,sK1,sK2)) | m2_yellow_6(sK4(sK0,sK5(sK0,sK1,sK2),sK2),sK0,sK5(sK0,sK1,sK2)) | v2_struct_0(X2) | ~l1_waybel_0(sK1,X2) | ~m2_yellow_6(sK5(sK0,sK1,sK2),X2,sK1) | ~l1_struct_0(X2)) )),
% 0.19/0.51    inference(resolution,[],[f292,f55])).
% 0.19/0.51  fof(f292,plain,(
% 0.19/0.51    ~v4_orders_2(sK5(sK0,sK1,sK2)) | v2_struct_0(sK5(sK0,sK1,sK2)) | m2_yellow_6(sK4(sK0,sK5(sK0,sK1,sK2),sK2),sK0,sK5(sK0,sK1,sK2))),
% 0.19/0.51    inference(subsumption_resolution,[],[f291,f24])).
% 0.19/0.51  % (12325)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.51  % (12334)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.51  % (12319)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.51  % (12326)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.51  % (12324)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.51  % (12317)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.52  % (12323)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.52  % (12313)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.52  % (12331)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.52  % (12312)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.52  % (12335)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.52  fof(f291,plain,(
% 0.19/0.52    v2_struct_0(sK5(sK0,sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v4_orders_2(sK5(sK0,sK1,sK2)) | m2_yellow_6(sK4(sK0,sK5(sK0,sK1,sK2),sK2),sK0,sK5(sK0,sK1,sK2))),
% 0.19/0.52    inference(duplicate_literal_removal,[],[f290])).
% 0.19/0.52  fof(f290,plain,(
% 0.19/0.52    v2_struct_0(sK5(sK0,sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v4_orders_2(sK5(sK0,sK1,sK2)) | m2_yellow_6(sK4(sK0,sK5(sK0,sK1,sK2),sK2),sK0,sK5(sK0,sK1,sK2)) | v2_struct_0(sK5(sK0,sK1,sK2)) | ~v4_orders_2(sK5(sK0,sK1,sK2))),
% 0.19/0.52    inference(resolution,[],[f159,f208])).
% 0.19/0.52  fof(f159,plain,(
% 0.19/0.52    ( ! [X0] : (~r3_waybel_9(sK0,sK5(sK0,sK1,sK2),X0) | v2_struct_0(sK5(sK0,sK1,sK2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK5(sK0,sK1,sK2)) | m2_yellow_6(sK4(sK0,sK5(sK0,sK1,sK2),X0),sK0,sK5(sK0,sK1,sK2))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f157,f150])).
% 0.19/0.52  fof(f157,plain,(
% 0.19/0.52    ( ! [X0] : (~v4_orders_2(sK5(sK0,sK1,sK2)) | ~v7_waybel_0(sK5(sK0,sK1,sK2)) | v2_struct_0(sK5(sK0,sK1,sK2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK5(sK0,sK1,sK2),X0) | m2_yellow_6(sK4(sK0,sK5(sK0,sK1,sK2),X0),sK0,sK5(sK0,sK1,sK2))) )),
% 0.19/0.52    inference(resolution,[],[f156,f96])).
% 0.19/0.52  fof(f96,plain,(
% 0.19/0.52    ( ! [X8,X9] : (~l1_waybel_0(X8,sK0) | ~v4_orders_2(X8) | ~v7_waybel_0(X8) | v2_struct_0(X8) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X8,X9) | m2_yellow_6(sK4(sK0,X8,X9),sK0,X8)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f68,f35])).
% 0.19/0.52  fof(f68,plain,(
% 0.19/0.52    ( ! [X8,X9] : (~l1_pre_topc(sK0) | v2_struct_0(X8) | ~v4_orders_2(X8) | ~v7_waybel_0(X8) | ~l1_waybel_0(X8,sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X8,X9) | m2_yellow_6(sK4(sK0,X8,X9),sK0,X8)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f63,f31])).
% 0.19/0.52  fof(f63,plain,(
% 0.19/0.52    ( ! [X8,X9] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X8) | ~v4_orders_2(X8) | ~v7_waybel_0(X8) | ~l1_waybel_0(X8,sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X8,X9) | m2_yellow_6(sK4(sK0,X8,X9),sK0,X8)) )),
% 0.19/0.52    inference(resolution,[],[f32,f39])).
% 0.19/0.52  fof(f39,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | m2_yellow_6(sK4(X0,X1,X2),X0,X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f16])).
% 0.19/0.52  % SZS output end Proof for theBenchmark
% 0.19/0.52  % (12332)------------------------------
% 0.19/0.52  % (12332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (12332)Termination reason: Refutation
% 0.19/0.52  
% 0.19/0.52  % (12332)Memory used [KB]: 1918
% 0.19/0.52  % (12332)Time elapsed: 0.128 s
% 0.19/0.52  % (12332)------------------------------
% 0.19/0.52  % (12332)------------------------------
% 0.19/0.53  % (12309)Success in time 0.18 s
%------------------------------------------------------------------------------
