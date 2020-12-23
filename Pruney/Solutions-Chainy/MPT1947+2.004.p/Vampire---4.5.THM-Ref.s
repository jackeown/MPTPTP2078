%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 265 expanded)
%              Number of leaves         :    8 (  47 expanded)
%              Depth                    :   31
%              Number of atoms          :  522 (2005 expanded)
%              Number of equality atoms :   25 ( 165 expanded)
%              Maximal formula depth    :   18 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f170,plain,(
    $false ),
    inference(subsumption_resolution,[],[f169,f28])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1)
          & l1_waybel_0(X1,X0)
          & v1_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1)
          & l1_waybel_0(X1,X0)
          & v1_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v1_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => k11_yellow_6(X0,X1) = k4_yellow_6(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => k11_yellow_6(X0,X1) = k4_yellow_6(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_yellow_6)).

fof(f169,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f168,f26])).

fof(f26,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f168,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f167,f25])).

fof(f25,plain,(
    v1_yellow_6(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f167,plain,
    ( ~ v1_yellow_6(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f166,f24])).

fof(f24,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f166,plain,
    ( ~ v7_waybel_0(sK1)
    | ~ v1_yellow_6(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f165,f23])).

fof(f23,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f165,plain,
    ( ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v1_yellow_6(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f164,f22])).

fof(f22,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f164,plain,
    ( v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v1_yellow_6(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f163,f31])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f163,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v1_yellow_6(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f162,f29])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f162,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v1_yellow_6(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f161,f92])).

fof(f92,plain,(
    r2_hidden(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f90,f48])).

fof(f48,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f40,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f90,plain,(
    ! [X1] :
      ( ~ r1_tarski(u1_struct_0(sK0),X1)
      | r2_hidden(k4_yellow_6(sK0,sK1),X1) ) ),
    inference(subsumption_resolution,[],[f89,f29])).

fof(f89,plain,(
    ! [X1] :
      ( r2_hidden(k4_yellow_6(sK0,sK1),X1)
      | ~ r1_tarski(u1_struct_0(sK0),X1)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f88,f28])).

fof(f88,plain,(
    ! [X1] :
      ( r2_hidden(k4_yellow_6(sK0,sK1),X1)
      | ~ r1_tarski(u1_struct_0(sK0),X1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f87,f26])).

fof(f87,plain,(
    ! [X1] :
      ( r2_hidden(k4_yellow_6(sK0,sK1),X1)
      | ~ r1_tarski(u1_struct_0(sK0),X1)
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f86,f24])).

fof(f86,plain,(
    ! [X1] :
      ( r2_hidden(k4_yellow_6(sK0,sK1),X1)
      | ~ r1_tarski(u1_struct_0(sK0),X1)
      | ~ v7_waybel_0(sK1)
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f85,f23])).

fof(f85,plain,(
    ! [X1] :
      ( r2_hidden(k4_yellow_6(sK0,sK1),X1)
      | ~ r1_tarski(u1_struct_0(sK0),X1)
      | ~ v4_orders_2(sK1)
      | ~ v7_waybel_0(sK1)
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f84,f22])).

fof(f84,plain,(
    ! [X1] :
      ( r2_hidden(k4_yellow_6(sK0,sK1),X1)
      | ~ r1_tarski(u1_struct_0(sK0),X1)
      | v2_struct_0(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v7_waybel_0(sK1)
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f83,f31])).

fof(f83,plain,(
    ! [X1] :
      ( r2_hidden(k4_yellow_6(sK0,sK1),X1)
      | ~ r1_tarski(u1_struct_0(sK0),X1)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v7_waybel_0(sK1)
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f81,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f37,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).

fof(f81,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k10_yellow_6(sK0,sK1),X1)
      | r2_hidden(k4_yellow_6(sK0,sK1),X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f79,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f79,plain,(
    ! [X0] :
      ( r2_hidden(k4_yellow_6(sK0,sK1),X0)
      | ~ r1_tarski(k10_yellow_6(sK0,sK1),X0) ) ),
    inference(subsumption_resolution,[],[f78,f28])).

fof(f78,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | r2_hidden(k4_yellow_6(sK0,sK1),X0)
      | ~ r1_tarski(k10_yellow_6(sK0,sK1),X0) ) ),
    inference(subsumption_resolution,[],[f77,f26])).

fof(f77,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK0)
      | r2_hidden(k4_yellow_6(sK0,sK1),X0)
      | ~ r1_tarski(k10_yellow_6(sK0,sK1),X0) ) ),
    inference(subsumption_resolution,[],[f76,f31])).

fof(f76,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK0)
      | r2_hidden(k4_yellow_6(sK0,sK1),X0)
      | ~ r1_tarski(k10_yellow_6(sK0,sK1),X0) ) ),
    inference(subsumption_resolution,[],[f75,f29])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK0)
      | r2_hidden(k4_yellow_6(sK0,sK1),X0)
      | ~ r1_tarski(k10_yellow_6(sK0,sK1),X0) ) ),
    inference(resolution,[],[f74,f25])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_yellow_6(sK1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_waybel_0(sK1,X0)
      | v2_struct_0(X0)
      | r2_hidden(k4_yellow_6(X0,sK1),X1)
      | ~ r1_tarski(k10_yellow_6(X0,sK1),X1) ) ),
    inference(subsumption_resolution,[],[f73,f23])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_orders_2(sK1)
      | ~ v2_pre_topc(X0)
      | ~ v1_yellow_6(sK1,X0)
      | ~ l1_waybel_0(sK1,X0)
      | v2_struct_0(X0)
      | r2_hidden(k4_yellow_6(X0,sK1),X1)
      | ~ r1_tarski(k10_yellow_6(X0,sK1),X1) ) ),
    inference(subsumption_resolution,[],[f72,f22])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v2_pre_topc(X0)
      | ~ v1_yellow_6(sK1,X0)
      | ~ l1_waybel_0(sK1,X0)
      | v2_struct_0(X0)
      | r2_hidden(k4_yellow_6(X0,sK1),X1)
      | ~ r1_tarski(k10_yellow_6(X0,sK1),X1) ) ),
    inference(resolution,[],[f71,f24])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v2_pre_topc(X0)
      | ~ v1_yellow_6(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | r2_hidden(k4_yellow_6(X0,X1),X2)
      | ~ r1_tarski(k10_yellow_6(X0,X1),X2) ) ),
    inference(resolution,[],[f35,f38])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ v1_yellow_6(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
          | ~ l1_waybel_0(X1,X0)
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
          | ~ l1_waybel_0(X1,X0)
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_6)).

fof(f161,plain,
    ( ~ r2_hidden(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v1_yellow_6(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f157,f27])).

fof(f27,plain,(
    k11_yellow_6(sK0,sK1) != k4_yellow_6(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f157,plain,
    ( k11_yellow_6(sK0,sK1) = k4_yellow_6(sK0,sK1)
    | ~ r2_hidden(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v1_yellow_6(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f153,f35])).

fof(f153,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k10_yellow_6(sK0,sK1))
      | k11_yellow_6(sK0,sK1) = X0
      | ~ r2_hidden(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f152,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f152,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k10_yellow_6(sK0,sK1))
      | k11_yellow_6(sK0,sK1) = X0 ) ),
    inference(subsumption_resolution,[],[f151,f23])).

fof(f151,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k10_yellow_6(sK0,sK1))
      | k11_yellow_6(sK0,sK1) = X0
      | ~ v4_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f150,f26])).

fof(f150,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k10_yellow_6(sK0,sK1))
      | k11_yellow_6(sK0,sK1) = X0
      | ~ v4_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f149,f22])).

fof(f149,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ l1_waybel_0(sK1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k10_yellow_6(sK0,sK1))
      | k11_yellow_6(sK0,sK1) = X0
      | ~ v4_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f148,f24])).

fof(f148,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK1)
      | v2_struct_0(sK1)
      | ~ l1_waybel_0(sK1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k10_yellow_6(sK0,sK1))
      | k11_yellow_6(sK0,sK1) = X0
      | ~ v4_orders_2(sK1) ) ),
    inference(resolution,[],[f147,f25])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ v1_yellow_6(X0,sK0)
      | ~ v7_waybel_0(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
      | k11_yellow_6(sK0,X0) = X1
      | ~ v4_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f146,f28])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(X0)
      | ~ v7_waybel_0(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
      | k11_yellow_6(sK0,X0) = X1
      | ~ v1_yellow_6(X0,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f145,f31])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(X0)
      | ~ v7_waybel_0(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
      | k11_yellow_6(sK0,X0) = X1
      | ~ l1_pre_topc(sK0)
      | ~ v1_yellow_6(X0,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f144,f29])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(X0)
      | ~ v7_waybel_0(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
      | k11_yellow_6(sK0,X0) = X1
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_yellow_6(X0,sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(X0)
      | ~ v7_waybel_0(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
      | k11_yellow_6(sK0,X0) = X1
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ l1_waybel_0(X0,sK0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(X0)
      | ~ v7_waybel_0(X0)
      | ~ v1_yellow_6(X0,sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f142,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v3_yellow_6(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ v1_yellow_6(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1)
          | ~ l1_waybel_0(X1,X0) )
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
          ( l1_waybel_0(X1,X0)
         => ( ( v1_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ( v3_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_yellow_6)).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ v3_yellow_6(X0,sK0)
      | ~ v4_orders_2(X0)
      | ~ v7_waybel_0(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
      | k11_yellow_6(sK0,X0) = X1 ) ),
    inference(subsumption_resolution,[],[f141,f31])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(X0)
      | ~ v7_waybel_0(X0)
      | ~ v3_yellow_6(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
      | k11_yellow_6(sK0,X0) = X1 ) ),
    inference(subsumption_resolution,[],[f140,f28])).

fof(f140,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(X0)
      | ~ v7_waybel_0(X0)
      | ~ v3_yellow_6(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
      | k11_yellow_6(sK0,X0) = X1 ) ),
    inference(subsumption_resolution,[],[f139,f29])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(X0)
      | ~ v7_waybel_0(X0)
      | ~ v3_yellow_6(X0,sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
      | k11_yellow_6(sK0,X0) = X1 ) ),
    inference(resolution,[],[f32,f30])).

fof(f30,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ v3_yellow_6(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
      | k11_yellow_6(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k11_yellow_6(X0,X1) = X2
              <=> r2_hidden(X2,k10_yellow_6(X0,X1)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k11_yellow_6(X0,X1) = X2
              <=> r2_hidden(X2,k10_yellow_6(X0,X1)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k11_yellow_6(X0,X1) = X2
              <=> r2_hidden(X2,k10_yellow_6(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_yellow_6)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:57:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (10951)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (10953)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (10960)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (10951)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (10952)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (10969)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (10968)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (10961)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (10949)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (10959)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.55  % (10967)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.29/0.55  % (10967)Refutation not found, incomplete strategy% (10967)------------------------------
% 1.29/0.55  % (10967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (10967)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (10967)Memory used [KB]: 10746
% 1.29/0.55  % (10967)Time elapsed: 0.136 s
% 1.29/0.55  % (10967)------------------------------
% 1.29/0.55  % (10967)------------------------------
% 1.29/0.55  % SZS output start Proof for theBenchmark
% 1.29/0.55  fof(f170,plain,(
% 1.29/0.55    $false),
% 1.29/0.55    inference(subsumption_resolution,[],[f169,f28])).
% 1.29/0.55  fof(f28,plain,(
% 1.29/0.55    ~v2_struct_0(sK0)),
% 1.29/0.55    inference(cnf_transformation,[],[f11])).
% 1.29/0.55  fof(f11,plain,(
% 1.29/0.55    ? [X0] : (? [X1] : (k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1) & l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.29/0.55    inference(flattening,[],[f10])).
% 1.29/0.55  fof(f10,plain,(
% 1.29/0.55    ? [X0] : (? [X1] : (k11_yellow_6(X0,X1) != k4_yellow_6(X0,X1) & (l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.29/0.55    inference(ennf_transformation,[],[f9])).
% 1.29/0.55  fof(f9,negated_conjecture,(
% 1.29/0.55    ~! [X0] : ((l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => k11_yellow_6(X0,X1) = k4_yellow_6(X0,X1)))),
% 1.29/0.55    inference(negated_conjecture,[],[f8])).
% 1.29/0.55  fof(f8,conjecture,(
% 1.29/0.55    ! [X0] : ((l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => k11_yellow_6(X0,X1) = k4_yellow_6(X0,X1)))),
% 1.29/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_yellow_6)).
% 1.29/0.55  fof(f169,plain,(
% 1.29/0.55    v2_struct_0(sK0)),
% 1.29/0.55    inference(subsumption_resolution,[],[f168,f26])).
% 1.29/0.55  fof(f26,plain,(
% 1.29/0.55    l1_waybel_0(sK1,sK0)),
% 1.29/0.55    inference(cnf_transformation,[],[f11])).
% 1.29/0.55  fof(f168,plain,(
% 1.29/0.55    ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0)),
% 1.29/0.55    inference(subsumption_resolution,[],[f167,f25])).
% 1.29/0.55  fof(f25,plain,(
% 1.29/0.55    v1_yellow_6(sK1,sK0)),
% 1.29/0.55    inference(cnf_transformation,[],[f11])).
% 1.29/0.55  fof(f167,plain,(
% 1.29/0.55    ~v1_yellow_6(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0)),
% 1.29/0.55    inference(subsumption_resolution,[],[f166,f24])).
% 1.29/0.55  fof(f24,plain,(
% 1.29/0.55    v7_waybel_0(sK1)),
% 1.29/0.55    inference(cnf_transformation,[],[f11])).
% 1.29/0.55  fof(f166,plain,(
% 1.29/0.55    ~v7_waybel_0(sK1) | ~v1_yellow_6(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0)),
% 1.29/0.55    inference(subsumption_resolution,[],[f165,f23])).
% 1.29/0.55  fof(f23,plain,(
% 1.29/0.55    v4_orders_2(sK1)),
% 1.29/0.55    inference(cnf_transformation,[],[f11])).
% 1.29/0.55  fof(f165,plain,(
% 1.29/0.55    ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v1_yellow_6(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0)),
% 1.29/0.55    inference(subsumption_resolution,[],[f164,f22])).
% 1.29/0.55  fof(f22,plain,(
% 1.29/0.55    ~v2_struct_0(sK1)),
% 1.29/0.55    inference(cnf_transformation,[],[f11])).
% 1.29/0.55  fof(f164,plain,(
% 1.29/0.55    v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v1_yellow_6(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0)),
% 1.29/0.55    inference(subsumption_resolution,[],[f163,f31])).
% 1.29/0.56  fof(f31,plain,(
% 1.29/0.56    l1_pre_topc(sK0)),
% 1.29/0.56    inference(cnf_transformation,[],[f11])).
% 1.29/0.56  fof(f163,plain,(
% 1.29/0.56    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v1_yellow_6(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0)),
% 1.29/0.56    inference(subsumption_resolution,[],[f162,f29])).
% 1.29/0.56  fof(f29,plain,(
% 1.29/0.56    v2_pre_topc(sK0)),
% 1.29/0.56    inference(cnf_transformation,[],[f11])).
% 1.29/0.56  fof(f162,plain,(
% 1.29/0.56    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v1_yellow_6(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0)),
% 1.29/0.56    inference(subsumption_resolution,[],[f161,f92])).
% 1.29/0.56  fof(f92,plain,(
% 1.29/0.56    r2_hidden(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))),
% 1.29/0.56    inference(resolution,[],[f90,f48])).
% 1.29/0.56  fof(f48,plain,(
% 1.29/0.56    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.29/0.56    inference(duplicate_literal_removal,[],[f47])).
% 1.29/0.56  fof(f47,plain,(
% 1.29/0.56    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.29/0.56    inference(resolution,[],[f40,f39])).
% 1.29/0.56  fof(f39,plain,(
% 1.29/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f21])).
% 1.29/0.56  fof(f21,plain,(
% 1.29/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.29/0.56    inference(ennf_transformation,[],[f1])).
% 1.29/0.56  fof(f1,axiom,(
% 1.29/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.29/0.56  fof(f40,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f21])).
% 1.29/0.56  fof(f90,plain,(
% 1.29/0.56    ( ! [X1] : (~r1_tarski(u1_struct_0(sK0),X1) | r2_hidden(k4_yellow_6(sK0,sK1),X1)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f89,f29])).
% 1.29/0.56  fof(f89,plain,(
% 1.29/0.56    ( ! [X1] : (r2_hidden(k4_yellow_6(sK0,sK1),X1) | ~r1_tarski(u1_struct_0(sK0),X1) | ~v2_pre_topc(sK0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f88,f28])).
% 1.29/0.56  fof(f88,plain,(
% 1.29/0.56    ( ! [X1] : (r2_hidden(k4_yellow_6(sK0,sK1),X1) | ~r1_tarski(u1_struct_0(sK0),X1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f87,f26])).
% 1.29/0.56  fof(f87,plain,(
% 1.29/0.56    ( ! [X1] : (r2_hidden(k4_yellow_6(sK0,sK1),X1) | ~r1_tarski(u1_struct_0(sK0),X1) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f86,f24])).
% 1.29/0.56  fof(f86,plain,(
% 1.29/0.56    ( ! [X1] : (r2_hidden(k4_yellow_6(sK0,sK1),X1) | ~r1_tarski(u1_struct_0(sK0),X1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f85,f23])).
% 1.29/0.56  fof(f85,plain,(
% 1.29/0.56    ( ! [X1] : (r2_hidden(k4_yellow_6(sK0,sK1),X1) | ~r1_tarski(u1_struct_0(sK0),X1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f84,f22])).
% 1.29/0.56  fof(f84,plain,(
% 1.29/0.56    ( ! [X1] : (r2_hidden(k4_yellow_6(sK0,sK1),X1) | ~r1_tarski(u1_struct_0(sK0),X1) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f83,f31])).
% 1.29/0.56  fof(f83,plain,(
% 1.29/0.56    ( ! [X1] : (r2_hidden(k4_yellow_6(sK0,sK1),X1) | ~r1_tarski(u1_struct_0(sK0),X1) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0)) )),
% 1.29/0.56    inference(resolution,[],[f81,f62])).
% 1.29/0.56  fof(f62,plain,(
% 1.29/0.56    ( ! [X0,X1] : (r1_tarski(k10_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0)) )),
% 1.29/0.56    inference(resolution,[],[f37,f42])).
% 1.29/0.56  fof(f42,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f3])).
% 1.29/0.56  fof(f3,axiom,(
% 1.29/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.29/0.56  fof(f37,plain,(
% 1.29/0.56    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f20])).
% 1.29/0.56  fof(f20,plain,(
% 1.29/0.56    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.29/0.56    inference(flattening,[],[f19])).
% 1.29/0.56  fof(f19,plain,(
% 1.29/0.56    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.29/0.56    inference(ennf_transformation,[],[f6])).
% 1.29/0.56  fof(f6,axiom,(
% 1.29/0.56    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).
% 1.29/0.56  fof(f81,plain,(
% 1.29/0.56    ( ! [X2,X1] : (~r1_tarski(k10_yellow_6(sK0,sK1),X1) | r2_hidden(k4_yellow_6(sK0,sK1),X2) | ~r1_tarski(X1,X2)) )),
% 1.29/0.56    inference(resolution,[],[f79,f38])).
% 1.29/0.56  fof(f38,plain,(
% 1.29/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f21])).
% 1.29/0.56  fof(f79,plain,(
% 1.29/0.56    ( ! [X0] : (r2_hidden(k4_yellow_6(sK0,sK1),X0) | ~r1_tarski(k10_yellow_6(sK0,sK1),X0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f78,f28])).
% 1.29/0.56  fof(f78,plain,(
% 1.29/0.56    ( ! [X0] : (v2_struct_0(sK0) | r2_hidden(k4_yellow_6(sK0,sK1),X0) | ~r1_tarski(k10_yellow_6(sK0,sK1),X0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f77,f26])).
% 1.29/0.56  fof(f77,plain,(
% 1.29/0.56    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0) | r2_hidden(k4_yellow_6(sK0,sK1),X0) | ~r1_tarski(k10_yellow_6(sK0,sK1),X0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f76,f31])).
% 1.29/0.56  fof(f76,plain,(
% 1.29/0.56    ( ! [X0] : (~l1_pre_topc(sK0) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0) | r2_hidden(k4_yellow_6(sK0,sK1),X0) | ~r1_tarski(k10_yellow_6(sK0,sK1),X0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f75,f29])).
% 1.29/0.56  fof(f75,plain,(
% 1.29/0.56    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0) | r2_hidden(k4_yellow_6(sK0,sK1),X0) | ~r1_tarski(k10_yellow_6(sK0,sK1),X0)) )),
% 1.29/0.56    inference(resolution,[],[f74,f25])).
% 1.29/0.56  fof(f74,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~v1_yellow_6(sK1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_waybel_0(sK1,X0) | v2_struct_0(X0) | r2_hidden(k4_yellow_6(X0,sK1),X1) | ~r1_tarski(k10_yellow_6(X0,sK1),X1)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f73,f23])).
% 1.29/0.56  fof(f73,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_orders_2(sK1) | ~v2_pre_topc(X0) | ~v1_yellow_6(sK1,X0) | ~l1_waybel_0(sK1,X0) | v2_struct_0(X0) | r2_hidden(k4_yellow_6(X0,sK1),X1) | ~r1_tarski(k10_yellow_6(X0,sK1),X1)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f72,f22])).
% 1.29/0.56  fof(f72,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v2_pre_topc(X0) | ~v1_yellow_6(sK1,X0) | ~l1_waybel_0(sK1,X0) | v2_struct_0(X0) | r2_hidden(k4_yellow_6(X0,sK1),X1) | ~r1_tarski(k10_yellow_6(X0,sK1),X1)) )),
% 1.29/0.56    inference(resolution,[],[f71,f24])).
% 1.29/0.56  fof(f71,plain,(
% 1.29/0.56    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v2_pre_topc(X0) | ~v1_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0) | r2_hidden(k4_yellow_6(X0,X1),X2) | ~r1_tarski(k10_yellow_6(X0,X1),X2)) )),
% 1.29/0.56    inference(resolution,[],[f35,f38])).
% 1.29/0.56  fof(f35,plain,(
% 1.29/0.56    ( ! [X0,X1] : (r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~v1_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f17])).
% 1.29/0.56  fof(f17,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : (r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.29/0.56    inference(flattening,[],[f16])).
% 1.29/0.56  fof(f16,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : (r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.29/0.56    inference(ennf_transformation,[],[f7])).
% 1.29/0.56  fof(f7,axiom,(
% 1.29/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_6)).
% 1.29/0.56  fof(f161,plain,(
% 1.29/0.56    ~r2_hidden(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v1_yellow_6(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0)),
% 1.29/0.56    inference(subsumption_resolution,[],[f157,f27])).
% 1.29/0.56  fof(f27,plain,(
% 1.29/0.56    k11_yellow_6(sK0,sK1) != k4_yellow_6(sK0,sK1)),
% 1.29/0.56    inference(cnf_transformation,[],[f11])).
% 1.29/0.56  fof(f157,plain,(
% 1.29/0.56    k11_yellow_6(sK0,sK1) = k4_yellow_6(sK0,sK1) | ~r2_hidden(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v1_yellow_6(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0)),
% 1.29/0.56    inference(resolution,[],[f153,f35])).
% 1.29/0.56  fof(f153,plain,(
% 1.29/0.56    ( ! [X0] : (~r2_hidden(X0,k10_yellow_6(sK0,sK1)) | k11_yellow_6(sK0,sK1) = X0 | ~r2_hidden(X0,u1_struct_0(sK0))) )),
% 1.29/0.56    inference(resolution,[],[f152,f36])).
% 1.29/0.56  fof(f36,plain,(
% 1.29/0.56    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f18])).
% 1.29/0.56  fof(f18,plain,(
% 1.29/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.29/0.56    inference(ennf_transformation,[],[f2])).
% 1.29/0.56  fof(f2,axiom,(
% 1.29/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.29/0.56  fof(f152,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k10_yellow_6(sK0,sK1)) | k11_yellow_6(sK0,sK1) = X0) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f151,f23])).
% 1.29/0.56  fof(f151,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k10_yellow_6(sK0,sK1)) | k11_yellow_6(sK0,sK1) = X0 | ~v4_orders_2(sK1)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f150,f26])).
% 1.29/0.56  fof(f150,plain,(
% 1.29/0.56    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k10_yellow_6(sK0,sK1)) | k11_yellow_6(sK0,sK1) = X0 | ~v4_orders_2(sK1)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f149,f22])).
% 1.29/0.56  fof(f149,plain,(
% 1.29/0.56    ( ! [X0] : (v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k10_yellow_6(sK0,sK1)) | k11_yellow_6(sK0,sK1) = X0 | ~v4_orders_2(sK1)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f148,f24])).
% 1.29/0.56  fof(f148,plain,(
% 1.29/0.56    ( ! [X0] : (~v7_waybel_0(sK1) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k10_yellow_6(sK0,sK1)) | k11_yellow_6(sK0,sK1) = X0 | ~v4_orders_2(sK1)) )),
% 1.29/0.56    inference(resolution,[],[f147,f25])).
% 1.29/0.56  fof(f147,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~v1_yellow_6(X0,sK0) | ~v7_waybel_0(X0) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,k10_yellow_6(sK0,X0)) | k11_yellow_6(sK0,X0) = X1 | ~v4_orders_2(X0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f146,f28])).
% 1.29/0.56  fof(f146,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~v4_orders_2(X0) | ~v7_waybel_0(X0) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,k10_yellow_6(sK0,X0)) | k11_yellow_6(sK0,X0) = X1 | ~v1_yellow_6(X0,sK0) | v2_struct_0(sK0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f145,f31])).
% 1.29/0.56  fof(f145,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~v4_orders_2(X0) | ~v7_waybel_0(X0) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,k10_yellow_6(sK0,X0)) | k11_yellow_6(sK0,X0) = X1 | ~l1_pre_topc(sK0) | ~v1_yellow_6(X0,sK0) | v2_struct_0(sK0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f144,f29])).
% 1.29/0.56  fof(f144,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~v4_orders_2(X0) | ~v7_waybel_0(X0) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,k10_yellow_6(sK0,X0)) | k11_yellow_6(sK0,X0) = X1 | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_yellow_6(X0,sK0) | v2_struct_0(sK0)) )),
% 1.29/0.56    inference(duplicate_literal_removal,[],[f143])).
% 1.29/0.56  fof(f143,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~v4_orders_2(X0) | ~v7_waybel_0(X0) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,k10_yellow_6(sK0,X0)) | k11_yellow_6(sK0,X0) = X1 | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~l1_waybel_0(X0,sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~v1_yellow_6(X0,sK0) | v2_struct_0(sK0)) )),
% 1.29/0.56    inference(resolution,[],[f142,f34])).
% 1.29/0.56  fof(f34,plain,(
% 1.29/0.56    ( ! [X0,X1] : (v3_yellow_6(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~v1_yellow_6(X1,X0) | v2_struct_0(X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f15])).
% 1.29/0.56  fof(f15,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.29/0.56    inference(flattening,[],[f14])).
% 1.29/0.56  fof(f14,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | (~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_waybel_0(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.29/0.56    inference(ennf_transformation,[],[f4])).
% 1.29/0.56  fof(f4,axiom,(
% 1.29/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (l1_waybel_0(X1,X0) => ((v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)))))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_yellow_6)).
% 1.29/0.56  fof(f142,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~v3_yellow_6(X0,sK0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,k10_yellow_6(sK0,X0)) | k11_yellow_6(sK0,X0) = X1) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f141,f31])).
% 1.29/0.56  fof(f141,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~v3_yellow_6(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,k10_yellow_6(sK0,X0)) | k11_yellow_6(sK0,X0) = X1) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f140,f28])).
% 1.29/0.56  fof(f140,plain,(
% 1.29/0.56    ( ! [X0,X1] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~v3_yellow_6(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,k10_yellow_6(sK0,X0)) | k11_yellow_6(sK0,X0) = X1) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f139,f29])).
% 1.29/0.56  fof(f139,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~v3_yellow_6(X0,sK0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,k10_yellow_6(sK0,X0)) | k11_yellow_6(sK0,X0) = X1) )),
% 1.29/0.56    inference(resolution,[],[f32,f30])).
% 1.29/0.56  fof(f30,plain,(
% 1.29/0.56    v8_pre_topc(sK0)),
% 1.29/0.56    inference(cnf_transformation,[],[f11])).
% 1.29/0.56  fof(f32,plain,(
% 1.29/0.56    ( ! [X2,X0,X1] : (~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | k11_yellow_6(X0,X1) = X2) )),
% 1.29/0.56    inference(cnf_transformation,[],[f13])).
% 1.29/0.56  fof(f13,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : (! [X2] : ((k11_yellow_6(X0,X1) = X2 <=> r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.29/0.56    inference(flattening,[],[f12])).
% 1.29/0.56  fof(f12,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : (! [X2] : ((k11_yellow_6(X0,X1) = X2 <=> r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.29/0.56    inference(ennf_transformation,[],[f5])).
% 1.29/0.56  fof(f5,axiom,(
% 1.29/0.56    ! [X0] : ((l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k11_yellow_6(X0,X1) = X2 <=> r2_hidden(X2,k10_yellow_6(X0,X1))))))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_yellow_6)).
% 1.29/0.56  % SZS output end Proof for theBenchmark
% 1.29/0.56  % (10951)------------------------------
% 1.29/0.56  % (10951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.56  % (10951)Termination reason: Refutation
% 1.29/0.56  
% 1.29/0.56  % (10951)Memory used [KB]: 6396
% 1.29/0.56  % (10951)Time elapsed: 0.121 s
% 1.29/0.56  % (10951)------------------------------
% 1.29/0.56  % (10951)------------------------------
% 1.29/0.56  % (10973)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.29/0.56  % (10948)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.56  % (10944)Success in time 0.194 s
%------------------------------------------------------------------------------
