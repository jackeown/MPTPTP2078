%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2034+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
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

% (7719)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
