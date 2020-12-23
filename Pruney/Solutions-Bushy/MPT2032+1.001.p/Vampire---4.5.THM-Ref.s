%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2032+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 454 expanded)
%              Number of leaves         :   10 ( 212 expanded)
%              Depth                    :    9
%              Number of atoms          :  308 (4691 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f25,f45,f28,f29,f30,f31,f32,f56,f57,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | ~ r2_waybel_0(X0,X2,X3)
      | r2_waybel_0(X0,X1,X3)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f57,plain,(
    r2_waybel_0(sK0,sK2,sK4(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f25,f26,f27,f46,f49,f34,f33,f55,f37])).

fof(f37,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ( ~ r2_waybel_0(X0,X1,sK4(X0,X1,X2))
                    & m1_connsp_2(sK4(X0,X1,X2),X0,X2) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_waybel_0(X0,X1,X3)
          & m1_connsp_2(X3,X0,X2) )
     => ( ~ r2_waybel_0(X0,X1,sK4(X0,X1,X2))
        & m1_connsp_2(sK4(X0,X1,X2),X0,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f55,plain,(
    m1_connsp_2(sK4(sK0,sK1,sK3),sK0,sK3) ),
    inference(unit_resulting_resolution,[],[f25,f26,f27,f28,f31,f33,f35,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK4(X0,X1,X2),X0,X2)
      | r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f35,plain,(
    ~ r3_waybel_9(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r3_waybel_9(sK0,sK1,sK3)
    & r3_waybel_9(sK0,sK2,sK3)
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m2_yellow_6(sK2,sK0,sK1)
    & l1_waybel_0(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f19,f18,f17,f16])).

fof(f16,plain,
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
                  ( ~ r3_waybel_9(sK0,X1,X3)
                  & r3_waybel_9(sK0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m2_yellow_6(X2,sK0,X1) )
          & l1_waybel_0(X1,sK0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r3_waybel_9(sK0,X1,X3)
                & r3_waybel_9(sK0,X2,X3)
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m2_yellow_6(X2,sK0,X1) )
        & l1_waybel_0(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r3_waybel_9(sK0,sK1,X3)
              & r3_waybel_9(sK0,X2,X3)
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m2_yellow_6(X2,sK0,sK1) )
      & l1_waybel_0(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

% (6895)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
fof(f18,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r3_waybel_9(sK0,sK1,X3)
            & r3_waybel_9(sK0,X2,X3)
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m2_yellow_6(X2,sK0,sK1) )
   => ( ? [X3] :
          ( ~ r3_waybel_9(sK0,sK1,X3)
          & r3_waybel_9(sK0,sK2,X3)
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m2_yellow_6(sK2,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X3] :
        ( ~ r3_waybel_9(sK0,sK1,X3)
        & r3_waybel_9(sK0,sK2,X3)
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ~ r3_waybel_9(sK0,sK1,sK3)
      & r3_waybel_9(sK0,sK2,sK3)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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

fof(f33,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    r3_waybel_9(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    l1_waybel_0(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f25,f45,f28,f29,f30,f31,f32,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f46,plain,(
    ~ v2_struct_0(sK2) ),
    inference(unit_resulting_resolution,[],[f25,f45,f28,f29,f30,f31,f32,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | ~ v2_struct_0(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f26,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    ~ r2_waybel_0(sK0,sK1,sK4(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f25,f26,f27,f28,f31,f33,f35,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_waybel_0(X0,X1,sK4(X0,X1,X2))
      | r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f32,plain,(
    m2_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f31,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f29,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f28,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f27,f36])).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f25,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

%------------------------------------------------------------------------------
