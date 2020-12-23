%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  136 (14411 expanded)
%              Number of leaves         :   12 (4283 expanded)
%              Depth                    :   47
%              Number of atoms          : 1432 (249090 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   24 (  11 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f217,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f145,f133,f143,f38,f152,f170,f171,f172,f173,f174,f175,f49])).

fof(f49,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(X5,k10_yellow_6(X0,X4))
      | r2_hidden(X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_waybel_0(X0,X4,X1)
      | ~ l1_waybel_0(X4,X0)
      | ~ v3_yellow_6(X4,X0)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ( ~ r2_hidden(sK5(X0,X1),X1)
                & r2_hidden(sK5(X0,X1),k10_yellow_6(X0,sK4(X0,X1)))
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
                & r1_waybel_0(X0,sK4(X0,X1),X1)
                & l1_waybel_0(sK4(X0,X1),X0)
                & v3_yellow_6(sK4(X0,X1),X0)
                & v7_waybel_0(sK4(X0,X1))
                & v4_orders_2(sK4(X0,X1))
                & ~ v2_struct_0(sK4(X0,X1)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r2_hidden(X5,k10_yellow_6(X0,X4))
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r1_waybel_0(X0,X4,X1)
                  | ~ l1_waybel_0(X4,X0)
                  | ~ v3_yellow_6(X4,X0)
                  | ~ v7_waybel_0(X4)
                  | ~ v4_orders_2(X4)
                  | v2_struct_0(X4) )
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f23,f25,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,k10_yellow_6(X0,X2))
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_waybel_0(X0,X2,X1)
          & l1_waybel_0(X2,X0)
          & v3_yellow_6(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,k10_yellow_6(X0,sK4(X0,X1)))
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & r1_waybel_0(X0,sK4(X0,X1),X1)
        & l1_waybel_0(sK4(X0,X1),X0)
        & v3_yellow_6(sK4(X0,X1),X0)
        & v7_waybel_0(sK4(X0,X1))
        & v4_orders_2(sK4(X0,X1))
        & ~ v2_struct_0(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,k10_yellow_6(X0,sK4(X0,X1)))
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),k10_yellow_6(X0,sK4(X0,X1)))
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r2_hidden(X3,k10_yellow_6(X0,X2))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & r1_waybel_0(X0,X2,X1)
                  & l1_waybel_0(X2,X0)
                  & v3_yellow_6(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r2_hidden(X5,k10_yellow_6(X0,X4))
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r1_waybel_0(X0,X4,X1)
                  | ~ l1_waybel_0(X4,X0)
                  | ~ v3_yellow_6(X4,X0)
                  | ~ v7_waybel_0(X4)
                  | ~ v4_orders_2(X4)
                  | v2_struct_0(X4) )
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r2_hidden(X3,k10_yellow_6(X0,X2))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & r1_waybel_0(X0,X2,X1)
                  & l1_waybel_0(X2,X0)
                  & v3_yellow_6(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r2_hidden(X3,k10_yellow_6(X0,X2))
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r1_waybel_0(X0,X2,X1)
                  | ~ l1_waybel_0(X2,X0)
                  | ~ v3_yellow_6(X2,X0)
                  | ~ v7_waybel_0(X2)
                  | ~ v4_orders_2(X2)
                  | v2_struct_0(X2) )
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,k10_yellow_6(X0,X2))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X2,X1)
                | ~ l1_waybel_0(X2,X0)
                | ~ v3_yellow_6(X2,X0)
                | ~ v7_waybel_0(X2)
                | ~ v4_orders_2(X2)
                | v2_struct_0(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,k10_yellow_6(X0,X2))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X2,X1)
                | ~ l1_waybel_0(X2,X0)
                | ~ v3_yellow_6(X2,X0)
                | ~ v7_waybel_0(X2)
                | ~ v4_orders_2(X2)
                | v2_struct_0(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ( l1_waybel_0(X2,X0)
                  & v3_yellow_6(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ( r1_waybel_0(X0,X2,X1)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,k10_yellow_6(X0,X2))
                       => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow19)).

fof(f175,plain,(
    r2_hidden(sK3,k10_yellow_6(sK0,sK7(sK0,sK1,sK3))) ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f143,f38,f154,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,sK7(X0,X1,X2)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r2_hidden(X2,k10_yellow_6(X0,X3))
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v3_yellow_6(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ( r2_hidden(X2,k10_yellow_6(X0,sK7(X0,X1,X2)))
                    & r1_waybel_0(X0,sK7(X0,X1,X2),X1)
                    & l1_waybel_0(sK7(X0,X1,X2),X0)
                    & v3_yellow_6(sK7(X0,X1,X2),X0)
                    & v7_waybel_0(sK7(X0,X1,X2))
                    & v4_orders_2(sK7(X0,X1,X2))
                    & ~ v2_struct_0(sK7(X0,X1,X2)) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X2,k10_yellow_6(X0,X4))
          & r1_waybel_0(X0,X4,X1)
          & l1_waybel_0(X4,X0)
          & v3_yellow_6(X4,X0)
          & v7_waybel_0(X4)
          & v4_orders_2(X4)
          & ~ v2_struct_0(X4) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK7(X0,X1,X2)))
        & r1_waybel_0(X0,sK7(X0,X1,X2),X1)
        & l1_waybel_0(sK7(X0,X1,X2),X0)
        & v3_yellow_6(sK7(X0,X1,X2),X0)
        & v7_waybel_0(sK7(X0,X1,X2))
        & v4_orders_2(sK7(X0,X1,X2))
        & ~ v2_struct_0(sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r2_hidden(X2,k10_yellow_6(X0,X3))
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v3_yellow_6(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ? [X4] :
                      ( r2_hidden(X2,k10_yellow_6(X0,X4))
                      & r1_waybel_0(X0,X4,X1)
                      & l1_waybel_0(X4,X0)
                      & v3_yellow_6(X4,X0)
                      & v7_waybel_0(X4)
                      & v4_orders_2(X4)
                      & ~ v2_struct_0(X4) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r2_hidden(X2,k10_yellow_6(X0,X3))
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v3_yellow_6(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ? [X3] :
                      ( r2_hidden(X2,k10_yellow_6(X0,X3))
                      & r1_waybel_0(X0,X3,X1)
                      & l1_waybel_0(X3,X0)
                      & v3_yellow_6(X3,X0)
                      & v7_waybel_0(X3)
                      & v4_orders_2(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

% (31591)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r2_hidden(X2,k10_yellow_6(X0,X3))
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v3_yellow_6(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r2_hidden(X2,k10_yellow_6(X0,X3))
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v3_yellow_6(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r2_hidden(X2,k10_yellow_6(X0,X3))
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v3_yellow_6(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow19)).

fof(f154,plain,(
    r2_hidden(sK3,k2_pre_topc(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f137,f142,f133,f38,f143,f144,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_pre_topc(sK0,X1))
      | ~ v4_pre_topc(sK1,sK0)
      | ~ r2_waybel_7(sK0,sK2,X0)
      | ~ r2_hidden(X1,sK2)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_pre_topc(sK0,X1))
      | ~ v4_pre_topc(sK1,sK0)
      | ~ r2_waybel_7(sK0,sK2,X0)
      | ~ r2_hidden(X1,sK2)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v4_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f89,f41])).

fof(f41,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ( ~ r2_hidden(sK3,sK1)
        & r2_waybel_7(sK0,sK2,sK3)
        & m1_subset_1(sK3,u1_struct_0(sK0))
        & r2_hidden(sK1,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0)))
        & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
        & ~ v1_xboole_0(sK2) )
      | ~ v4_pre_topc(sK1,sK0) )
    & ( ! [X4] :
          ( ! [X5] :
              ( r2_hidden(X5,sK1)
              | ~ r2_waybel_7(sK0,X4,X5)
              | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
          | ~ r2_hidden(sK1,X4)
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0)))
          | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
          | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
          | v1_xboole_0(X4) )
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f20,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r2_waybel_7(X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_hidden(X1,X2)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & ~ v1_xboole_0(X2) )
              | ~ v4_pre_topc(X1,X0) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r2_waybel_7(X0,X4,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r2_hidden(X1,X4)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                  | v1_xboole_0(X4) )
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_waybel_7(sK0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(sK0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0)))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,sK0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r2_waybel_7(sK0,X4,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
                | ~ r2_hidden(X1,X4)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0)))
                | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
                | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
                | v1_xboole_0(X4) )
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X3,X1)
                  & r2_waybel_7(sK0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
              & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0)))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
              & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
              & ~ v1_xboole_0(X2) )
          | ~ v4_pre_topc(X1,sK0) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,X1)
                  | ~ r2_waybel_7(sK0,X4,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
              | ~ r2_hidden(X1,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
              | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0)))
              | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
              | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
              | v1_xboole_0(X4) )
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,sK1)
                & r2_waybel_7(sK0,X2,X3)
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & r2_hidden(sK1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
            & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0)))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
            & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
            & ~ v1_xboole_0(X2) )
        | ~ v4_pre_topc(sK1,sK0) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,sK1)
                | ~ r2_waybel_7(sK0,X4,X5)
                | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
            | ~ r2_hidden(sK1,X4)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
            | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0)))
            | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
            | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
            | v1_xboole_0(X4) )
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r2_hidden(X3,sK1)
            & r2_waybel_7(sK0,X2,X3)
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & r2_hidden(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0)))
        & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ~ r2_hidden(X3,sK1)
          & r2_waybel_7(sK0,sK2,X3)
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & r2_hidden(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0)))
      & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
      & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X3] :
        ( ~ r2_hidden(X3,sK1)
        & r2_waybel_7(sK0,sK2,X3)
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ~ r2_hidden(sK3,sK1)
      & r2_waybel_7(sK0,sK2,sK3)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r2_waybel_7(X0,X4,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X4)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X4) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X2) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X2) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X2) )
                 => ( r2_hidden(X1,X2)
                   => ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r2_waybel_7(X0,X2,X3)
                         => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & ~ v1_xboole_0(X2) )
               => ( r2_hidden(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_waybel_7(X0,X2,X3)
                       => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow19)).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
      | r2_hidden(X1,k2_pre_topc(sK0,X0))
      | ~ v4_pre_topc(sK1,sK0)
      | ~ r2_waybel_7(sK0,sK2,X1)
      | ~ r2_hidden(X0,sK2)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X1,k2_pre_topc(sK0,X0))
      | ~ v4_pre_topc(sK1,sK0)
      | ~ r2_waybel_7(sK0,sK2,X1)
      | ~ v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v4_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f85,f42])).

fof(f42,plain,
    ( v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X1,sK2)
      | r2_hidden(X0,k2_pre_topc(sK0,X1))
      | ~ v4_pre_topc(sK1,sK0)
      | ~ r2_waybel_7(sK0,sK2,X0)
      | ~ v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_waybel_7(sK0,sK2,X0)
      | ~ r2_hidden(X1,sK2)
      | r2_hidden(X0,k2_pre_topc(sK0,X1))
      | ~ v4_pre_topc(sK1,sK0)
      | ~ v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v4_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f78,f43])).

fof(f43,plain,
    ( v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0)))
      | ~ r2_waybel_7(sK0,sK2,X0)
      | ~ r2_hidden(X1,sK2)
      | r2_hidden(X0,k2_pre_topc(sK0,X1))
      | ~ v4_pre_topc(sK1,sK0)
      | ~ v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f44,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ r2_waybel_7(X0,X3,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r2_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | v1_xboole_0(X3) ) )
                & ( ( r2_waybel_7(X0,sK6(X0,X1,X2),X2)
                    & r2_hidden(X1,sK6(X0,X1,X2))
                    & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(sK6(X0,X1,X2)) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_waybel_7(X0,X4,X2)
          & r2_hidden(X1,X4)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
          & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
          & ~ v1_xboole_0(X4) )
     => ( r2_waybel_7(X0,sK6(X0,X1,X2),X2)
        & r2_hidden(X1,sK6(X0,X1,X2))
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v3_waybel_7(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
        & v13_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r2_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | v1_xboole_0(X3) ) )
                & ( ? [X4] :
                      ( r2_waybel_7(X0,X4,X2)
                      & r2_hidden(X1,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
                      & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                      & ~ v1_xboole_0(X4) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r2_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | v1_xboole_0(X3) ) )
                & ( ? [X3] :
                      ( r2_waybel_7(X0,X3,X2)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & ~ v1_xboole_0(X3) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r2_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

% (31592)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r2_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r2_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_yellow19)).

fof(f44,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f144,plain,(
    r2_waybel_7(sK0,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f133,f47])).

fof(f47,plain,
    ( r2_waybel_7(sK0,sK2,sK3)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f142,plain,(
    r2_hidden(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f133,f45])).

fof(f45,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f137,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(unit_resulting_resolution,[],[f133,f40])).

fof(f40,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f174,plain,(
    r1_waybel_0(sK0,sK7(sK0,sK1,sK3),sK1) ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f143,f38,f154,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,sK7(X0,X1,X2),X1)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f173,plain,(
    l1_waybel_0(sK7(sK0,sK1,sK3),sK0) ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f143,f38,f154,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(sK7(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f172,plain,(
    v3_yellow_6(sK7(sK0,sK1,sK3),sK0) ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f143,f38,f154,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v3_yellow_6(sK7(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f171,plain,(
    v7_waybel_0(sK7(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f143,f38,f154,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(sK7(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f170,plain,(
    v4_orders_2(sK7(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f35,f36,f37,f143,f38,f154,f68])).

% (31595)Refutation not found, incomplete strategy% (31595)------------------------------
% (31595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(sK7(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f152,plain,(
    ~ v2_struct_0(sK7(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f137,f35,f36,f37,f142,f133,f143,f144,f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK7(sK0,sK1,X0))
      | ~ r2_hidden(sK1,sK2)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_pre_topc(sK1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_waybel_7(sK0,sK2,X0) ) ),
    inference(resolution,[],[f98,f38])).

fof(f98,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_waybel_7(sK0,sK2,X2)
      | ~ r2_hidden(X3,sK2)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v4_pre_topc(sK1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v2_struct_0(sK7(sK0,X3,X2)) ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X2,X3] :
      ( ~ v4_pre_topc(sK1,sK0)
      | ~ r2_waybel_7(sK0,sK2,X2)
      | ~ r2_hidden(X3,sK2)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v2_struct_0(sK7(sK0,X3,X2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f93,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ v2_struct_0(sK7(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f143,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f133,f46])).

fof(f46,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f133,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f35,f37,f36,f132])).

fof(f132,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f130,f75])).

fof(f75,plain,
    ( ~ v2_struct_0(sK4(sK0,sK1))
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f38,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_struct_0(sK4(X0,X1))
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f130,plain,
    ( v2_struct_0(sK4(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | v2_struct_0(sK4(sK0,sK1))
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f128,f76])).

fof(f76,plain,
    ( v4_orders_2(sK4(sK0,sK1))
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f38,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_orders_2(sK4(X0,X1))
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f128,plain,
    ( ~ v4_orders_2(sK4(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | v2_struct_0(sK4(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,
    ( v4_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v4_orders_2(sK4(sK0,sK1))
    | v2_struct_0(sK4(sK0,sK1))
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f126,f77])).

fof(f77,plain,
    ( v7_waybel_0(sK4(sK0,sK1))
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f38,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v7_waybel_0(sK4(X0,X1))
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f126,plain,
    ( ~ v7_waybel_0(sK4(sK0,sK1))
    | v4_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v4_orders_2(sK4(sK0,sK1))
    | v2_struct_0(sK4(sK0,sK1)) ),
    inference(resolution,[],[f125,f38])).

fof(f125,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v7_waybel_0(sK4(sK0,sK1))
    | ~ v4_orders_2(sK4(sK0,sK1))
    | v2_struct_0(sK4(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v7_waybel_0(sK4(sK0,sK1))
    | ~ v4_orders_2(sK4(sK0,sK1))
    | v2_struct_0(sK4(sK0,sK1))
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f123,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f123,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v7_waybel_0(sK4(sK0,sK1))
    | ~ v4_orders_2(sK4(sK0,sK1))
    | v2_struct_0(sK4(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r2_hidden(sK5(sK0,sK1),sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v7_waybel_0(sK4(sK0,sK1))
    | ~ v4_orders_2(sK4(sK0,sK1))
    | v2_struct_0(sK4(sK0,sK1))
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f121,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v3_yellow_6(sK4(X0,X1),X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f121,plain,
    ( ~ v3_yellow_6(sK4(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r2_hidden(sK5(sK0,sK1),sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v7_waybel_0(sK4(sK0,sK1))
    | ~ v4_orders_2(sK4(sK0,sK1))
    | v2_struct_0(sK4(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r2_hidden(sK5(sK0,sK1),sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_yellow_6(sK4(sK0,sK1),sK0)
    | ~ v7_waybel_0(sK4(sK0,sK1))
    | ~ v4_orders_2(sK4(sK0,sK1))
    | v2_struct_0(sK4(sK0,sK1))
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f117,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( l1_waybel_0(sK4(X0,X1),X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f117,plain,
    ( ~ l1_waybel_0(sK4(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r2_hidden(sK5(sK0,sK1),sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_yellow_6(sK4(sK0,sK1),sK0)
    | ~ v7_waybel_0(sK4(sK0,sK1))
    | ~ v4_orders_2(sK4(sK0,sK1))
    | v2_struct_0(sK4(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r2_hidden(sK5(sK0,sK1),sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_waybel_0(sK4(sK0,sK1),sK0)
    | ~ v3_yellow_6(sK4(sK0,sK1),sK0)
    | ~ v7_waybel_0(sK4(sK0,sK1))
    | ~ v4_orders_2(sK4(sK0,sK1))
    | v2_struct_0(sK4(sK0,sK1))
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f115,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f115,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r2_hidden(sK5(sK0,sK1),sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_waybel_0(sK4(sK0,sK1),sK0)
    | ~ v3_yellow_6(sK4(sK0,sK1),sK0)
    | ~ v7_waybel_0(sK4(sK0,sK1))
    | ~ v4_orders_2(sK4(sK0,sK1))
    | v2_struct_0(sK4(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f114])).

% (31595)Termination reason: Refutation not found, incomplete strategy

fof(f114,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | v4_pre_topc(sK1,sK0)
    | ~ l1_waybel_0(sK4(sK0,sK1),sK0)
    | ~ v3_yellow_6(sK4(sK0,sK1),sK0)
    | ~ v7_waybel_0(sK4(sK0,sK1))
    | ~ v4_orders_2(sK4(sK0,sK1))
    | v2_struct_0(sK4(sK0,sK1))
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f113,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(X0,sK4(X0,X1),X1)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

% (31595)Memory used [KB]: 895
% (31595)Time elapsed: 0.077 s
fof(f113,plain,(
    ! [X0] :
      ( ~ r1_waybel_0(sK0,sK4(sK0,X0),sK1)
      | r2_hidden(sK5(sK0,X0),sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0))
      | v4_pre_topc(sK1,sK0)
      | ~ l1_waybel_0(sK4(sK0,X0),sK0)
      | ~ v3_yellow_6(sK4(sK0,X0),sK0)
      | ~ v7_waybel_0(sK4(sK0,X0))
      | ~ v4_orders_2(sK4(sK0,X0))
      | v2_struct_0(sK4(sK0,X0))
      | v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X0] :
      ( v4_pre_topc(sK1,sK0)
      | r2_hidden(sK5(sK0,X0),sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0))
      | ~ r1_waybel_0(sK0,sK4(sK0,X0),sK1)
      | ~ l1_waybel_0(sK4(sK0,X0),sK0)
      | ~ v3_yellow_6(sK4(sK0,X0),sK0)
      | ~ v7_waybel_0(sK4(sK0,X0))
      | ~ v4_orders_2(sK4(sK0,X0))
      | v2_struct_0(sK4(sK0,X0))
      | v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f108,f57])).

% (31595)------------------------------
% (31595)------------------------------
fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),k10_yellow_6(X0,sK4(X0,X1)))
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f108,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k10_yellow_6(sK0,X2))
      | v4_pre_topc(sK1,sK0)
      | r2_hidden(X1,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_waybel_0(sK0,X2,sK1)
      | ~ l1_waybel_0(X2,sK0)
      | ~ v3_yellow_6(X2,sK0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v4_pre_topc(sK1,sK0)
      | r2_hidden(X1,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_hidden(X1,k10_yellow_6(sK0,X2))
      | ~ r1_waybel_0(sK0,X2,sK1)
      | ~ l1_waybel_0(X2,sK0)
      | ~ v3_yellow_6(X2,sK0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f105,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ r2_hidden(X2,k10_yellow_6(X0,X3))
      | ~ r1_waybel_0(X0,X3,X1)
      | ~ l1_waybel_0(X3,X0)
      | ~ v3_yellow_6(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f105,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v4_pre_topc(sK1,sK0)
      | r2_hidden(X0,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v4_pre_topc(sK1,sK0)
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f103,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(sK6(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f103,plain,(
    ! [X0] :
      ( v1_xboole_0(sK6(sK0,sK1,X0))
      | r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v4_pre_topc(sK1,sK0)
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK1)
      | v1_xboole_0(sK6(sK0,sK1,X0))
      | v4_pre_topc(sK1,sK0)
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f100,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK6(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1,sK6(sK0,X1,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK1)
      | v1_xboole_0(sK6(sK0,X1,X0))
      | v4_pre_topc(sK1,sK0)
      | ~ r2_hidden(X0,k2_pre_topc(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK1,sK6(sK0,X1,X0))
      | v1_xboole_0(sK6(sK0,X1,X0))
      | v4_pre_topc(sK1,sK0)
      | ~ r2_hidden(X0,k2_pre_topc(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,k2_pre_topc(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f95,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,sK6(X0,X1,X2),X2)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_waybel_7(sK0,sK6(sK0,X1,X2),X0)
      | r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK1,sK6(sK0,X1,X2))
      | v1_xboole_0(sK6(sK0,X1,X2))
      | v4_pre_topc(sK1,sK0)
      | ~ r2_hidden(X2,k2_pre_topc(sK0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,sK1)
      | ~ r2_waybel_7(sK0,sK6(sK0,X1,X2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK1,sK6(sK0,X1,X2))
      | v1_xboole_0(sK6(sK0,X1,X2))
      | v4_pre_topc(sK1,sK0)
      | ~ r2_hidden(X2,k2_pre_topc(sK0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_hidden(X2,k2_pre_topc(sK0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f91,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
      | r2_hidden(X2,sK1)
      | ~ r2_waybel_7(sK0,sK6(sK0,X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(sK1,sK6(sK0,X0,X1))
      | v1_xboole_0(sK6(sK0,X0,X1))
      | v4_pre_topc(sK1,sK0)
      | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK1,sK6(sK0,X0,X1))
      | r2_hidden(X2,sK1)
      | ~ r2_waybel_7(sK0,sK6(sK0,X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(sK6(sK0,X0,X1))
      | v4_pre_topc(sK1,sK0)
      | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f87,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v13_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v13_waybel_0(sK6(sK0,X1,X2),k3_yellow_1(k2_struct_0(sK0)))
      | ~ r2_hidden(sK1,sK6(sK0,X1,X2))
      | r2_hidden(X0,sK1)
      | ~ r2_waybel_7(sK0,sK6(sK0,X1,X2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v2_waybel_0(sK6(sK0,X1,X2),k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(sK6(sK0,X1,X2))
      | v4_pre_topc(sK1,sK0)
      | ~ r2_hidden(X2,k2_pre_topc(sK0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK1,sK6(sK0,X1,X2))
      | r2_hidden(X0,sK1)
      | ~ r2_waybel_7(sK0,sK6(sK0,X1,X2),X0)
      | ~ v13_waybel_0(sK6(sK0,X1,X2),k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(sK6(sK0,X1,X2),k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(sK6(sK0,X1,X2))
      | v4_pre_topc(sK1,sK0)
      | ~ r2_hidden(X2,k2_pre_topc(sK0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_hidden(X2,k2_pre_topc(sK0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f83,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v3_waybel_7(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f83,plain,(
    ! [X2,X3,X1] :
      ( ~ v3_waybel_7(sK6(sK0,X1,X2),k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(sK1,sK6(sK0,X1,X2))
      | r2_hidden(X3,sK1)
      | ~ r2_waybel_7(sK0,sK6(sK0,X1,X2),X3)
      | ~ v13_waybel_0(sK6(sK0,X1,X2),k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(sK6(sK0,X1,X2),k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(sK6(sK0,X1,X2))
      | v4_pre_topc(sK1,sK0)
      | ~ r2_hidden(X2,k2_pre_topc(sK0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f39,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f39,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ r2_waybel_7(sK0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(sK1,X4)
      | r2_hidden(X5,sK1)
      | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(X4)
      | v4_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f145,plain,(
    ~ r2_hidden(sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f133,f48])).

fof(f48,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:27:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (31585)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.47  % (31594)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.48  % (31590)WARNING: option uwaf not known.
% 0.21/0.48  % (31586)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.48  % (31594)Refutation not found, incomplete strategy% (31594)------------------------------
% 0.21/0.48  % (31594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31594)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (31594)Memory used [KB]: 5373
% 0.21/0.48  % (31594)Time elapsed: 0.009 s
% 0.21/0.48  % (31594)------------------------------
% 0.21/0.48  % (31594)------------------------------
% 0.21/0.48  % (31585)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (31593)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.49  % (31598)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (31590)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.21/0.49  % (31595)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.49  % (31579)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f35,f36,f37,f145,f133,f143,f38,f152,f170,f171,f172,f173,f174,f175,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X4,X0,X5,X1] : (~r2_hidden(X5,k10_yellow_6(X0,X4)) | r2_hidden(X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~r1_waybel_0(X0,X4,X1) | ~l1_waybel_0(X4,X0) | ~v3_yellow_6(X4,X0) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ((~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),k10_yellow_6(X0,sK4(X0,X1))) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))) & r1_waybel_0(X0,sK4(X0,X1),X1) & l1_waybel_0(sK4(X0,X1),X0) & v3_yellow_6(sK4(X0,X1),X0) & v7_waybel_0(sK4(X0,X1)) & v4_orders_2(sK4(X0,X1)) & ~v2_struct_0(sK4(X0,X1)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_hidden(X5,k10_yellow_6(X0,X4)) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r1_waybel_0(X0,X4,X1) | ~l1_waybel_0(X4,X0) | ~v3_yellow_6(X4,X0) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4)) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f23,f25,f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X3,k10_yellow_6(X0,X2)) & m1_subset_1(X3,u1_struct_0(X0))) & r1_waybel_0(X0,X2,X1) & l1_waybel_0(X2,X0) & v3_yellow_6(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X3,k10_yellow_6(X0,sK4(X0,X1))) & m1_subset_1(X3,u1_struct_0(X0))) & r1_waybel_0(X0,sK4(X0,X1),X1) & l1_waybel_0(sK4(X0,X1),X0) & v3_yellow_6(sK4(X0,X1),X0) & v7_waybel_0(sK4(X0,X1)) & v4_orders_2(sK4(X0,X1)) & ~v2_struct_0(sK4(X0,X1))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X3,k10_yellow_6(X0,sK4(X0,X1))) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),k10_yellow_6(X0,sK4(X0,X1))) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X3,k10_yellow_6(X0,X2)) & m1_subset_1(X3,u1_struct_0(X0))) & r1_waybel_0(X0,X2,X1) & l1_waybel_0(X2,X0) & v3_yellow_6(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_hidden(X5,k10_yellow_6(X0,X4)) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r1_waybel_0(X0,X4,X1) | ~l1_waybel_0(X4,X0) | ~v3_yellow_6(X4,X0) | ~v7_waybel_0(X4) | ~v4_orders_2(X4) | v2_struct_0(X4)) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(rectify,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X3,k10_yellow_6(X0,X2)) & m1_subset_1(X3,u1_struct_0(X0))) & r1_waybel_0(X0,X2,X1) & l1_waybel_0(X2,X0) & v3_yellow_6(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k10_yellow_6(X0,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1) | ~l1_waybel_0(X2,X0) | ~v3_yellow_6(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k10_yellow_6(X0,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1) | ~l1_waybel_0(X2,X0) | ~v3_yellow_6(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> ! [X2] : ((! [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,k10_yellow_6(X0,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_waybel_0(X0,X2,X1)) | (~l1_waybel_0(X2,X0) | ~v3_yellow_6(X2,X0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> ! [X2] : ((l1_waybel_0(X2,X0) & v3_yellow_6(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (r1_waybel_0(X0,X2,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,k10_yellow_6(X0,X2)) => r2_hidden(X3,X1))))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow19)).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    r2_hidden(sK3,k10_yellow_6(sK0,sK7(sK0,sK1,sK3)))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f35,f36,f37,f143,f38,f154,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK7(X0,X1,X2))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r2_hidden(X2,k10_yellow_6(X0,X3)) | ~r1_waybel_0(X0,X3,X1) | ~l1_waybel_0(X3,X0) | ~v3_yellow_6(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3))) & ((r2_hidden(X2,k10_yellow_6(X0,sK7(X0,X1,X2))) & r1_waybel_0(X0,sK7(X0,X1,X2),X1) & l1_waybel_0(sK7(X0,X1,X2),X0) & v3_yellow_6(sK7(X0,X1,X2),X0) & v7_waybel_0(sK7(X0,X1,X2)) & v4_orders_2(sK7(X0,X1,X2)) & ~v2_struct_0(sK7(X0,X1,X2))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X2,k10_yellow_6(X0,X4)) & r1_waybel_0(X0,X4,X1) & l1_waybel_0(X4,X0) & v3_yellow_6(X4,X0) & v7_waybel_0(X4) & v4_orders_2(X4) & ~v2_struct_0(X4)) => (r2_hidden(X2,k10_yellow_6(X0,sK7(X0,X1,X2))) & r1_waybel_0(X0,sK7(X0,X1,X2),X1) & l1_waybel_0(sK7(X0,X1,X2),X0) & v3_yellow_6(sK7(X0,X1,X2),X0) & v7_waybel_0(sK7(X0,X1,X2)) & v4_orders_2(sK7(X0,X1,X2)) & ~v2_struct_0(sK7(X0,X1,X2))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r2_hidden(X2,k10_yellow_6(X0,X3)) | ~r1_waybel_0(X0,X3,X1) | ~l1_waybel_0(X3,X0) | ~v3_yellow_6(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3))) & (? [X4] : (r2_hidden(X2,k10_yellow_6(X0,X4)) & r1_waybel_0(X0,X4,X1) & l1_waybel_0(X4,X0) & v3_yellow_6(X4,X0) & v7_waybel_0(X4) & v4_orders_2(X4) & ~v2_struct_0(X4)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(rectify,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r2_hidden(X2,k10_yellow_6(X0,X3)) | ~r1_waybel_0(X0,X3,X1) | ~l1_waybel_0(X3,X0) | ~v3_yellow_6(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3))) & (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v3_yellow_6(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f13])).
% 0.21/0.50  % (31591)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v3_yellow_6(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v3_yellow_6(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & r1_waybel_0(X0,X3,X1) & l1_waybel_0(X3,X0) & v3_yellow_6(X3,X0) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow19)).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    r2_hidden(sK3,k2_pre_topc(sK0,sK1))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f35,f36,f37,f137,f142,f133,f38,f143,f144,f93])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(X0,k2_pre_topc(sK0,X1)) | ~v4_pre_topc(sK1,sK0) | ~r2_waybel_7(sK0,sK2,X0) | ~r2_hidden(X1,sK2) | v1_xboole_0(sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f92])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(X0,k2_pre_topc(sK0,X1)) | ~v4_pre_topc(sK1,sK0) | ~r2_waybel_7(sK0,sK2,X0) | ~r2_hidden(X1,sK2) | v1_xboole_0(sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v4_pre_topc(sK1,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f89,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ((((~r2_hidden(sK3,sK1) & r2_waybel_7(sK0,sK2,sK3) & m1_subset_1(sK3,u1_struct_0(sK0))) & r2_hidden(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) & ~v1_xboole_0(sK2)) | ~v4_pre_topc(sK1,sK0)) & (! [X4] : (! [X5] : (r2_hidden(X5,sK1) | ~r2_waybel_7(sK0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK0))) | ~r2_hidden(sK1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(X4)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f20,f19,f18,f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_waybel_7(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X4)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(sK0,X2,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,sK0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_waybel_7(sK0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK0))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(X4)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(sK0,X2,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,sK0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_waybel_7(sK0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK0))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(X4)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((? [X2] : (? [X3] : (~r2_hidden(X3,sK1) & r2_waybel_7(sK0,X2,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & r2_hidden(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(sK1,sK0)) & (! [X4] : (! [X5] : (r2_hidden(X5,sK1) | ~r2_waybel_7(sK0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK0))) | ~r2_hidden(sK1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(X4)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ? [X2] : (? [X3] : (~r2_hidden(X3,sK1) & r2_waybel_7(sK0,X2,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & r2_hidden(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) & ~v1_xboole_0(X2)) => (? [X3] : (~r2_hidden(X3,sK1) & r2_waybel_7(sK0,sK2,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & r2_hidden(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) & ~v1_xboole_0(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ? [X3] : (~r2_hidden(X3,sK1) & r2_waybel_7(sK0,sK2,X3) & m1_subset_1(X3,u1_struct_0(sK0))) => (~r2_hidden(sK3,sK1) & r2_waybel_7(sK0,sK2,sK3) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_waybel_7(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X4)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(rectify,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X2)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X2)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f6])).
% 0.21/0.50  fof(f6,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> ! [X2] : ((! [X3] : ((r2_hidden(X3,X1) | ~r2_waybel_7(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) => (r2_hidden(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_waybel_7(X0,X2,X3) => r2_hidden(X3,X1))))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f4])).
% 0.21/0.50  fof(f4,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) => (r2_hidden(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_waybel_7(X0,X2,X3) => r2_hidden(X3,X1))))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow19)).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) | r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~v4_pre_topc(sK1,sK0) | ~r2_waybel_7(sK0,sK2,X1) | ~r2_hidden(X0,sK2) | v1_xboole_0(sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f88])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,sK2) | r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~v4_pre_topc(sK1,sK0) | ~r2_waybel_7(sK0,sK2,X1) | ~v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v4_pre_topc(sK1,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f85,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) | ~r2_hidden(X1,sK2) | r2_hidden(X0,k2_pre_topc(sK0,X1)) | ~v4_pre_topc(sK1,sK0) | ~r2_waybel_7(sK0,sK2,X0) | ~v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f84])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_waybel_7(sK0,sK2,X0) | ~r2_hidden(X1,sK2) | r2_hidden(X0,k2_pre_topc(sK0,X1)) | ~v4_pre_topc(sK1,sK0) | ~v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v4_pre_topc(sK1,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f78,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0))) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v3_waybel_7(sK2,k3_yellow_1(k2_struct_0(sK0))) | ~r2_waybel_7(sK0,sK2,X0) | ~r2_hidden(X1,sK2) | r2_hidden(X0,k2_pre_topc(sK0,X1)) | ~v4_pre_topc(sK1,sK0) | ~v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f44,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~r2_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | r2_hidden(X2,k2_pre_topc(X0,X1)) | ~v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X3) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r2_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X3))) & ((r2_waybel_7(X0,sK6(X0,X1,X2),X2) & r2_hidden(X1,sK6(X0,X1,X2)) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(sK6(X0,X1,X2))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X4] : (r2_waybel_7(X0,X4,X2) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X4)) => (r2_waybel_7(X0,sK6(X0,X1,X2),X2) & r2_hidden(X1,sK6(X0,X1,X2)) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(sK6(X0,X1,X2))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r2_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X3))) & (? [X4] : (r2_waybel_7(X0,X4,X2) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X4)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(rectify,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r2_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X3))) & (? [X3] : (r2_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X3)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f10])).
% 0.21/0.50  % (31592)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X3))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_yellow19)).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    r2_waybel_7(sK0,sK2,sK3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f133,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    r2_waybel_7(sK0,sK2,sK3) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    r2_hidden(sK1,sK2)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f133,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ~v4_pre_topc(sK1,sK0) | r2_hidden(sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    ~v1_xboole_0(sK2)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f133,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ~v4_pre_topc(sK1,sK0) | ~v1_xboole_0(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    r1_waybel_0(sK0,sK7(sK0,sK1,sK3),sK1)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f35,f36,f37,f143,f38,f154,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_waybel_0(X0,sK7(X0,X1,X2),X1) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    l1_waybel_0(sK7(sK0,sK1,sK3),sK0)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f35,f36,f37,f143,f38,f154,f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (l1_waybel_0(sK7(X0,X1,X2),X0) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    v3_yellow_6(sK7(sK0,sK1,sK3),sK0)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f35,f36,f37,f143,f38,f154,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v3_yellow_6(sK7(X0,X1,X2),X0) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    v7_waybel_0(sK7(sK0,sK1,sK3))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f35,f36,f37,f143,f38,f154,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v7_waybel_0(sK7(X0,X1,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    v4_orders_2(sK7(sK0,sK1,sK3))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f35,f36,f37,f143,f38,f154,f68])).
% 0.21/0.50  % (31595)Refutation not found, incomplete strategy% (31595)------------------------------
% 0.21/0.50  % (31595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v4_orders_2(sK7(X0,X1,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    ~v2_struct_0(sK7(sK0,sK1,sK3))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f137,f35,f36,f37,f142,f133,f143,f144,f101])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_struct_0(sK7(sK0,sK1,X0)) | ~r2_hidden(sK1,sK2) | v1_xboole_0(sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_waybel_7(sK0,sK2,X0)) )),
% 0.21/0.50    inference(resolution,[],[f98,f38])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_waybel_7(sK0,sK2,X2) | ~r2_hidden(X3,sK2) | v1_xboole_0(sK2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_struct_0(sK7(sK0,X3,X2))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f97])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~v4_pre_topc(sK1,sK0) | ~r2_waybel_7(sK0,sK2,X2) | ~r2_hidden(X3,sK2) | v1_xboole_0(sK2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_struct_0(sK7(sK0,X3,X2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f93,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~v2_struct_0(sK7(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f133,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    m1_subset_1(sK3,u1_struct_0(sK0)) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    v4_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f35,f37,f36,f132])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    v4_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f131])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | v2_struct_0(sK0) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f130,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ~v2_struct_0(sK4(sK0,sK1)) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f38,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_struct_0(sK4(X0,X1)) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    v2_struct_0(sK4(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f129])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | v2_struct_0(sK4(sK0,sK1)) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f128,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    v4_orders_2(sK4(sK0,sK1)) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f38,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_orders_2(sK4(X0,X1)) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    ~v4_orders_2(sK4(sK0,sK1)) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | v2_struct_0(sK4(sK0,sK1))),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f127])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    v4_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v4_orders_2(sK4(sK0,sK1)) | v2_struct_0(sK4(sK0,sK1)) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f126,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    v7_waybel_0(sK4(sK0,sK1)) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f38,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v7_waybel_0(sK4(X0,X1)) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    ~v7_waybel_0(sK4(sK0,sK1)) | v4_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v4_orders_2(sK4(sK0,sK1)) | v2_struct_0(sK4(sK0,sK1))),
% 0.21/0.50    inference(resolution,[],[f125,f38])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v7_waybel_0(sK4(sK0,sK1)) | ~v4_orders_2(sK4(sK0,sK1)) | v2_struct_0(sK4(sK0,sK1))),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f124])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v7_waybel_0(sK4(sK0,sK1)) | ~v4_orders_2(sK4(sK0,sK1)) | v2_struct_0(sK4(sK0,sK1)) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f123,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    r2_hidden(sK5(sK0,sK1),sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v7_waybel_0(sK4(sK0,sK1)) | ~v4_orders_2(sK4(sK0,sK1)) | v2_struct_0(sK4(sK0,sK1))),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f122])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r2_hidden(sK5(sK0,sK1),sK1) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v7_waybel_0(sK4(sK0,sK1)) | ~v4_orders_2(sK4(sK0,sK1)) | v2_struct_0(sK4(sK0,sK1)) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f121,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v3_yellow_6(sK4(X0,X1),X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    ~v3_yellow_6(sK4(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r2_hidden(sK5(sK0,sK1),sK1) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v7_waybel_0(sK4(sK0,sK1)) | ~v4_orders_2(sK4(sK0,sK1)) | v2_struct_0(sK4(sK0,sK1))),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f120])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r2_hidden(sK5(sK0,sK1),sK1) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_yellow_6(sK4(sK0,sK1),sK0) | ~v7_waybel_0(sK4(sK0,sK1)) | ~v4_orders_2(sK4(sK0,sK1)) | v2_struct_0(sK4(sK0,sK1)) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f117,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0,X1] : (l1_waybel_0(sK4(X0,X1),X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    ~l1_waybel_0(sK4(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r2_hidden(sK5(sK0,sK1),sK1) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_yellow_6(sK4(sK0,sK1),sK0) | ~v7_waybel_0(sK4(sK0,sK1)) | ~v4_orders_2(sK4(sK0,sK1)) | v2_struct_0(sK4(sK0,sK1))),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f116])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r2_hidden(sK5(sK0,sK1),sK1) | v4_pre_topc(sK1,sK0) | ~l1_waybel_0(sK4(sK0,sK1),sK0) | ~v3_yellow_6(sK4(sK0,sK1),sK0) | ~v7_waybel_0(sK4(sK0,sK1)) | ~v4_orders_2(sK4(sK0,sK1)) | v2_struct_0(sK4(sK0,sK1)) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f115,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r2_hidden(sK5(sK0,sK1),sK1) | v4_pre_topc(sK1,sK0) | ~l1_waybel_0(sK4(sK0,sK1),sK0) | ~v3_yellow_6(sK4(sK0,sK1),sK0) | ~v7_waybel_0(sK4(sK0,sK1)) | ~v4_orders_2(sK4(sK0,sK1)) | v2_struct_0(sK4(sK0,sK1))),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f114])).
% 0.21/0.50  % (31595)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    r2_hidden(sK5(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | v4_pre_topc(sK1,sK0) | ~l1_waybel_0(sK4(sK0,sK1),sK0) | ~v3_yellow_6(sK4(sK0,sK1),sK0) | ~v7_waybel_0(sK4(sK0,sK1)) | ~v4_orders_2(sK4(sK0,sK1)) | v2_struct_0(sK4(sK0,sK1)) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f113,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_waybel_0(X0,sK4(X0,X1),X1) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  % (31595)Memory used [KB]: 895
% 0.21/0.50  % (31595)Time elapsed: 0.077 s
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_waybel_0(sK0,sK4(sK0,X0),sK1) | r2_hidden(sK5(sK0,X0),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0)) | v4_pre_topc(sK1,sK0) | ~l1_waybel_0(sK4(sK0,X0),sK0) | ~v3_yellow_6(sK4(sK0,X0),sK0) | ~v7_waybel_0(sK4(sK0,X0)) | ~v4_orders_2(sK4(sK0,X0)) | v2_struct_0(sK4(sK0,X0)) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f110])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    ( ! [X0] : (v4_pre_topc(sK1,sK0) | r2_hidden(sK5(sK0,X0),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0)) | ~r1_waybel_0(sK0,sK4(sK0,X0),sK1) | ~l1_waybel_0(sK4(sK0,X0),sK0) | ~v3_yellow_6(sK4(sK0,X0),sK0) | ~v7_waybel_0(sK4(sK0,X0)) | ~v4_orders_2(sK4(sK0,X0)) | v2_struct_0(sK4(sK0,X0)) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f108,f57])).
% 0.21/0.50  % (31595)------------------------------
% 0.21/0.50  % (31595)------------------------------
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),k10_yellow_6(X0,sK4(X0,X1))) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~r2_hidden(X1,k10_yellow_6(sK0,X2)) | v4_pre_topc(sK1,sK0) | r2_hidden(X1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_waybel_0(sK0,X2,sK1) | ~l1_waybel_0(X2,sK0) | ~v3_yellow_6(X2,sK0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f107])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | v4_pre_topc(sK1,sK0) | r2_hidden(X1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_hidden(X1,k10_yellow_6(sK0,X2)) | ~r1_waybel_0(sK0,X2,sK1) | ~l1_waybel_0(X2,sK0) | ~v3_yellow_6(X2,sK0) | ~v7_waybel_0(X2) | ~v4_orders_2(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f105,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | ~r2_hidden(X2,k10_yellow_6(X0,X3)) | ~r1_waybel_0(X0,X3,X1) | ~l1_waybel_0(X3,X0) | ~v3_yellow_6(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v4_pre_topc(sK1,sK0) | r2_hidden(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f104])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v4_pre_topc(sK1,sK0) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f103,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_xboole_0(sK6(X0,X1,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    ( ! [X0] : (v1_xboole_0(sK6(sK0,sK1,X0)) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v4_pre_topc(sK1,sK0) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f102])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1) | v1_xboole_0(sK6(sK0,sK1,X0)) | v4_pre_topc(sK1,sK0) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f100,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X1,sK6(X0,X1,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(sK1,sK6(sK0,X1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1) | v1_xboole_0(sK6(sK0,X1,X0)) | v4_pre_topc(sK1,sK0) | ~r2_hidden(X0,k2_pre_topc(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f99])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1,sK6(sK0,X1,X0)) | v1_xboole_0(sK6(sK0,X1,X0)) | v4_pre_topc(sK1,sK0) | ~r2_hidden(X0,k2_pre_topc(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_hidden(X0,k2_pre_topc(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f95,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_waybel_7(X0,sK6(X0,X1,X2),X2) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_waybel_7(sK0,sK6(sK0,X1,X2),X0) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1,sK6(sK0,X1,X2)) | v1_xboole_0(sK6(sK0,X1,X2)) | v4_pre_topc(sK1,sK0) | ~r2_hidden(X2,k2_pre_topc(sK0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X0,sK1) | ~r2_waybel_7(sK0,sK6(sK0,X1,X2),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1,sK6(sK0,X1,X2)) | v1_xboole_0(sK6(sK0,X1,X2)) | v4_pre_topc(sK1,sK0) | ~r2_hidden(X2,k2_pre_topc(sK0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_hidden(X2,k2_pre_topc(sK0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f91,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v2_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | r2_hidden(X2,sK1) | ~r2_waybel_7(sK0,sK6(sK0,X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(sK1,sK6(sK0,X0,X1)) | v1_xboole_0(sK6(sK0,X0,X1)) | v4_pre_topc(sK1,sK0) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f90])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(sK1,sK6(sK0,X0,X1)) | r2_hidden(X2,sK1) | ~r2_waybel_7(sK0,sK6(sK0,X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~v2_waybel_0(sK6(sK0,X0,X1),k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK6(sK0,X0,X1)) | v4_pre_topc(sK1,sK0) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_hidden(X1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f87,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v13_waybel_0(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v13_waybel_0(sK6(sK0,X1,X2),k3_yellow_1(k2_struct_0(sK0))) | ~r2_hidden(sK1,sK6(sK0,X1,X2)) | r2_hidden(X0,sK1) | ~r2_waybel_7(sK0,sK6(sK0,X1,X2),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v2_waybel_0(sK6(sK0,X1,X2),k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK6(sK0,X1,X2)) | v4_pre_topc(sK1,sK0) | ~r2_hidden(X2,k2_pre_topc(sK0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK1,sK6(sK0,X1,X2)) | r2_hidden(X0,sK1) | ~r2_waybel_7(sK0,sK6(sK0,X1,X2),X0) | ~v13_waybel_0(sK6(sK0,X1,X2),k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK6(sK0,X1,X2),k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK6(sK0,X1,X2)) | v4_pre_topc(sK1,sK0) | ~r2_hidden(X2,k2_pre_topc(sK0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_hidden(X2,k2_pre_topc(sK0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f83,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v3_waybel_7(sK6(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X2,X3,X1] : (~v3_waybel_7(sK6(sK0,X1,X2),k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(sK1,sK6(sK0,X1,X2)) | r2_hidden(X3,sK1) | ~r2_waybel_7(sK0,sK6(sK0,X1,X2),X3) | ~v13_waybel_0(sK6(sK0,X1,X2),k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK6(sK0,X1,X2),k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK6(sK0,X1,X2)) | v4_pre_topc(sK1,sK0) | ~r2_hidden(X2,k2_pre_topc(sK0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f39,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~r2_waybel_7(sK0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r2_hidden(sK1,X4) | r2_hidden(X5,sK1) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(X4) | v4_pre_topc(sK1,sK0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    ~r2_hidden(sK3,sK1)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f133,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ~v4_pre_topc(sK1,sK0) | ~r2_hidden(sK3,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (31585)------------------------------
% 0.21/0.50  % (31585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (31585)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (31585)Memory used [KB]: 1279
% 0.21/0.50  % (31585)Time elapsed: 0.062 s
% 0.21/0.50  % (31585)------------------------------
% 0.21/0.50  % (31585)------------------------------
% 0.21/0.50  % (31576)Success in time 0.134 s
%------------------------------------------------------------------------------
