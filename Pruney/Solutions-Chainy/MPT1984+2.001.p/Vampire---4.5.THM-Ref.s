%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 351 expanded)
%              Number of leaves         :    6 (  79 expanded)
%              Depth                    :    9
%              Number of atoms          :  270 (3941 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f70,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f29,f18,f27,f28,f23,f20,f19,f25,f26,f24,f55,f48,f22,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
      | v2_struct_0(X0)
      | v1_xboole_0(X3)
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
      | ~ r2_hidden(X1,X3)
      | r1_waybel_7(X0,X3,sK4(X0,X2,X3)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( r1_waybel_7(X0,X3,X4)
                      & r2_hidden(X4,X2)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_hidden(X1,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                  | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
                  | v1_xboole_0(X3) )
              | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( r1_waybel_7(X0,X3,X4)
                      & r2_hidden(X4,X2)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_hidden(X1,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                  | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
                  | v1_xboole_0(X3) )
              | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
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
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
             => ( r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                      & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                      & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                      & v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
                      & ~ v1_xboole_0(X3) )
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r1_waybel_7(X0,X3,X4)
                                & r2_hidden(X4,X2) ) )
                        & r2_hidden(X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_7)).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r2_waybel_7(X0,X3,X4)
                      | ~ r2_hidden(X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                  & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0)))
                  & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              & r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r2_waybel_7(X0,X3,X4)
                      | ~ r2_hidden(X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                  & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0)))
                  & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              & r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
               => ( r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                        & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0)))
                        & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                        & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ~ ( r2_waybel_7(X0,X3,X4)
                                  & r2_hidden(X4,X2) ) )
                          & r2_hidden(X1,X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
             => ( r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                      & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0)))
                      & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                      & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                      & ~ v1_xboole_0(X3) )
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r2_waybel_7(X0,X3,X4)
                                & r2_hidden(X4,X2) ) )
                        & r2_hidden(X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_waybel_7)).

fof(f48,plain,(
    v1_subset_1(sK3,u1_struct_0(k3_yellow_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f18,f32,f36,f34,f33,f30,f21,f20,f19,f22,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ v3_waybel_7(X1,X0)
      | v1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
          | ~ v3_waybel_7(X1,X0)
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
          | ~ v3_waybel_7(X1,X0)
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_waybel_7(X1,X0)
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & v1_subset_1(X1,u1_struct_0(X0))
              & ~ v1_xboole_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_waybel_7)).

fof(f21,plain,(
    v3_waybel_7(sK3,k3_yellow_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] : ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_yellow_1)).

fof(f33,plain,(
    ! [X0] : v4_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_1)).

fof(f32,plain,(
    ! [X0] : v3_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f55,plain,(
    ~ r1_waybel_7(sK0,sK3,sK4(sK0,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f29,f28,f27,f18,f21,f20,f19,f22,f54,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
      | ~ v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | r2_waybel_7(X0,X1,X2)
      | ~ r1_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_7(X0,X1,X2)
            <=> r2_waybel_7(X0,X1,X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
          | ~ v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_7(X0,X1,X2)
            <=> r2_waybel_7(X0,X1,X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
          | ~ v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
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
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
            & v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( r1_waybel_7(X0,X1,X2)
            <=> r2_waybel_7(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_7)).

fof(f54,plain,(
    ~ r2_waybel_7(sK0,sK3,sK4(sK0,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f49,f53,f17])).

fof(f17,plain,(
    ! [X4] :
      ( ~ r2_waybel_7(sK0,sK3,X4)
      | ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f53,plain,(
    m1_subset_1(sK4(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f29,f18,f27,f28,f23,f20,f19,f25,f24,f26,f48,f22,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
      | v2_struct_0(X0)
      | v1_xboole_0(X3)
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
      | ~ r2_hidden(X1,X3)
      | m1_subset_1(sK4(X0,X2,X3),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f49,plain,(
    r2_hidden(sK4(sK0,sK2,sK3),sK2) ),
    inference(unit_resulting_resolution,[],[f27,f18,f29,f28,f23,f20,f19,f25,f24,f26,f48,f22,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
      | v2_struct_0(X0)
      | v1_xboole_0(X3)
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
      | ~ r2_hidden(X1,X3)
      | r2_hidden(sK4(X0,X2,X3),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f24,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(u1_pre_topc(sK0)))) ),
    inference(cnf_transformation,[],[f10])).

fof(f26,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(u1_pre_topc(sK0)))) ),
    inference(cnf_transformation,[],[f10])).

fof(f25,plain,(
    r1_waybel_3(k2_yellow_1(u1_pre_topc(sK0)),sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f19,plain,(
    v2_waybel_0(sK3,k3_yellow_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f20,plain,(
    v13_waybel_0(sK3,k3_yellow_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f23,plain,(
    r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f28,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f18,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:34:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (7831)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.45  % (7842)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.45  % (7833)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.46  % (7842)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f29,f18,f27,f28,f23,f20,f19,f25,f26,f24,f55,f48,f22,f40])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) | v2_struct_0(X0) | v1_xboole_0(X3) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0)))) | ~v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) | ~v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) | ~r2_hidden(X1,X3) | r1_waybel_7(X0,X3,sK4(X0,X2,X3))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (? [X4] : (r1_waybel_7(X0,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) | ~v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0)))) | v1_xboole_0(X3)) | ~r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((? [X4] : ((r1_waybel_7(X0,X3,X4) & r2_hidden(X4,X2)) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X1,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) | ~v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0)))) | v1_xboole_0(X3))) | ~r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) => (r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0)))) & ~v1_xboole_0(X3)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r1_waybel_7(X0,X3,X4) & r2_hidden(X4,X2))) & r2_hidden(X1,X3)))))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_7)).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK0)))))),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (~r2_waybel_7(X0,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) & r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((! [X4] : ((~r2_waybel_7(X0,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X1,X3)) & (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & ~v1_xboole_0(X3))) & r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,negated_conjecture,(
% 0.21/0.46    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) => (r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_waybel_7(X0,X3,X4) & r2_hidden(X4,X2))) & r2_hidden(X1,X3)))))))),
% 0.21/0.46    inference(negated_conjecture,[],[f7])).
% 0.21/0.46  fof(f7,conjecture,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) => (r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_waybel_7(X0,X3,X4) & r2_hidden(X4,X2))) & r2_hidden(X1,X3)))))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_waybel_7)).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    v1_subset_1(sK3,u1_struct_0(k3_yellow_1(u1_struct_0(sK0))))),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f18,f32,f36,f34,f33,f30,f21,f20,f19,f22,f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | v1_xboole_0(X1) | ~v2_waybel_0(X1,X0) | ~v13_waybel_0(X1,X0) | ~v3_waybel_7(X1,X0) | v1_subset_1(X1,u1_struct_0(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)) | ~v3_waybel_7(X1,X0) | ~v13_waybel_0(X1,X0) | ~v2_waybel_0(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)) | (~v3_waybel_7(X1,X0) | ~v13_waybel_0(X1,X0) | ~v2_waybel_0(X1,X0) | v1_xboole_0(X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_waybel_7(X1,X0) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_waybel_7)).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    v3_waybel_7(sK3,k3_yellow_1(u1_struct_0(sK0)))),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X0] : (~v2_struct_0(k3_yellow_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : (v5_orders_2(k3_yellow_1(X0)) & v4_orders_2(k3_yellow_1(X0)) & v3_orders_2(k3_yellow_1(X0)) & v1_orders_2(k3_yellow_1(X0)) & ~v2_struct_0(k3_yellow_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_yellow_1)).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X0] : (v4_orders_2(k3_yellow_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X0] : (v5_orders_2(k3_yellow_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X0] : (l1_orders_2(k3_yellow_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : (l1_orders_2(k3_yellow_1(X0)) & v1_orders_2(k3_yellow_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_1)).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X0] : (v3_orders_2(k3_yellow_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    ~r1_waybel_7(sK0,sK3,sK4(sK0,sK2,sK3))),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f29,f28,f27,f18,f21,f20,f19,f22,f54,f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0))) | ~v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0))) | ~v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0))) | v2_struct_0(X0) | r2_waybel_7(X0,X1,X2) | ~r1_waybel_7(X0,X1,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_7(X0,X1,X2) <=> r2_waybel_7(X0,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) | ~v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0))) | ~v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_7(X0,X1,X2) <=> r2_waybel_7(X0,X1,X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) | ~v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0))) | ~v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) & v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0))) & v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ! [X2] : (r1_waybel_7(X0,X1,X2) <=> r2_waybel_7(X0,X1,X2))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_7)).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    ~r2_waybel_7(sK0,sK3,sK4(sK0,sK2,sK3))),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f49,f53,f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ( ! [X4] : (~r2_waybel_7(sK0,sK3,X4) | ~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    m1_subset_1(sK4(sK0,sK2,sK3),u1_struct_0(sK0))),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f29,f18,f27,f28,f23,f20,f19,f25,f24,f26,f48,f22,f38])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) | v2_struct_0(X0) | v1_xboole_0(X3) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0)))) | ~v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) | ~v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) | ~r2_hidden(X1,X3) | m1_subset_1(sK4(X0,X2,X3),u1_struct_0(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    r2_hidden(sK4(sK0,sK2,sK3),sK2)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f27,f18,f29,f28,f23,f20,f19,f25,f24,f26,f48,f22,f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) | v2_struct_0(X0) | v1_xboole_0(X3) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0)))) | ~v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) | ~v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) | ~r2_hidden(X1,X3) | r2_hidden(sK4(X0,X2,X3),X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(u1_pre_topc(sK0))))),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(u1_pre_topc(sK0))))),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    r1_waybel_3(k2_yellow_1(u1_pre_topc(sK0)),sK1,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    v2_waybel_0(sK3,k3_yellow_1(u1_struct_0(sK0)))),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    v13_waybel_0(sK3,k3_yellow_1(u1_struct_0(sK0)))),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    r2_hidden(sK1,sK3)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    v2_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ~v2_struct_0(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ~v1_xboole_0(sK3)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    l1_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (7842)------------------------------
% 0.21/0.46  % (7842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (7842)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (7842)Memory used [KB]: 895
% 0.21/0.46  % (7842)Time elapsed: 0.028 s
% 0.21/0.46  % (7842)------------------------------
% 0.21/0.46  % (7842)------------------------------
% 0.21/0.46  % (7824)Success in time 0.1 s
%------------------------------------------------------------------------------
