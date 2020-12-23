%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  148 (1080 expanded)
%              Number of leaves         :   13 ( 201 expanded)
%              Depth                    :   30
%              Number of atoms          :  763 (9446 expanded)
%              Number of equality atoms :   58 (  58 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f417,plain,(
    $false ),
    inference(subsumption_resolution,[],[f415,f41])).

fof(f41,plain,(
    ~ r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))
              & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v3_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_waybel_9(X0)
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
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))
              & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v3_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_waybel_9(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_waybel_9(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v3_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
                 => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)
               => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_waybel_9)).

fof(f415,plain,(
    r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) ),
    inference(backward_demodulation,[],[f366,f414])).

fof(f414,plain,(
    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f412,f154])).

fof(f154,plain,(
    ~ v2_struct_0(sK0) ),
    inference(resolution,[],[f102,f108])).

fof(f108,plain,(
    l1_orders_2(sK0) ),
    inference(resolution,[],[f54,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_waybel_9(X0)
      | l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

fof(f54,plain,(
    l1_waybel_9(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f102,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_struct_0(sK0) ),
    inference(resolution,[],[f52,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f52,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f412,plain,
    ( k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f395,f124])).

fof(f124,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f110,f59])).

fof(f59,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f110,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f108,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f395,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) ),
    inference(forward_demodulation,[],[f391,f332])).

fof(f332,plain,(
    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) ),
    inference(forward_demodulation,[],[f328,f314])).

fof(f314,plain,(
    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f309,f171])).

fof(f171,plain,(
    m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f136,f154])).

fof(f136,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f135,f45])).

fof(f45,plain,(
    v3_yellow_6(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f135,plain,
    ( v2_struct_0(sK0)
    | ~ v3_yellow_6(sK1,sK0)
    | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f134,f44])).

fof(f44,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f134,plain,
    ( v2_struct_0(sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f133,f43])).

fof(f43,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f133,plain,
    ( v2_struct_0(sK0)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f132,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f132,plain,
    ( v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f131,f107])).

fof(f107,plain,(
    l1_pre_topc(sK0) ),
    inference(resolution,[],[f54,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_waybel_9(X0)
      | l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f131,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f130,f48])).

fof(f48,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f130,plain,
    ( v2_struct_0(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f127,f47])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f127,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f46,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ v3_yellow_6(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v3_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v3_yellow_6(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_yellow_6)).

fof(f46,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f309,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k12_lattice3(sK0,sK2,X0) = k11_lattice3(sK0,sK2,X0) ) ),
    inference(resolution,[],[f307,f39])).

fof(f39,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f307,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k12_lattice3(sK0,X0,X1) = k11_lattice3(sK0,X0,X1) ) ),
    inference(resolution,[],[f105,f108])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k12_lattice3(sK0,X0,X1) = k11_lattice3(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f103,f51])).

fof(f51,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k12_lattice3(sK0,X0,X1) = k11_lattice3(sK0,X0,X1) ) ),
    inference(resolution,[],[f53,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f53,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f328,plain,(
    k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f321,f171])).

fof(f321,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X0) = k11_lattice3(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f317,f154])).

fof(f317,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X0) = k11_lattice3(sK0,sK2,X0) ) ),
    inference(resolution,[],[f123,f39])).

fof(f123,plain,(
    ! [X12,X11] :
      ( ~ m1_subset_1(X11,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X12,u1_struct_0(sK0))
      | k11_lattice3(sK0,X11,X12) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X11),X12) ) ),
    inference(subsumption_resolution,[],[f122,f117])).

fof(f117,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | m1_subset_1(k4_waybel_1(sK0,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f108,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k4_waybel_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_1)).

fof(f122,plain,(
    ! [X12,X11] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ m1_subset_1(k4_waybel_1(sK0,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ m1_subset_1(X12,u1_struct_0(sK0))
      | k11_lattice3(sK0,X11,X12) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X11),X12) ) ),
    inference(subsumption_resolution,[],[f121,f116])).

fof(f116,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | v1_funct_2(k4_waybel_1(sK0,X6),u1_struct_0(sK0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f108,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f121,plain,(
    ! [X12,X11] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ v1_funct_2(k4_waybel_1(sK0,X11),u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(k4_waybel_1(sK0,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ m1_subset_1(X12,u1_struct_0(sK0))
      | k11_lattice3(sK0,X11,X12) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X11),X12) ) ),
    inference(subsumption_resolution,[],[f120,f115])).

fof(f115,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | v1_funct_1(k4_waybel_1(sK0,X5)) ) ),
    inference(resolution,[],[f108,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_funct_1(k4_waybel_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f120,plain,(
    ! [X12,X11] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ v1_funct_1(k4_waybel_1(sK0,X11))
      | ~ v1_funct_2(k4_waybel_1(sK0,X11),u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(k4_waybel_1(sK0,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ m1_subset_1(X12,u1_struct_0(sK0))
      | k11_lattice3(sK0,X11,X12) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X11),X12) ) ),
    inference(resolution,[],[f108,f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v1_funct_1(k4_waybel_1(X0,X1))
      | ~ v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
      | ~ m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X3) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3)
      | k4_waybel_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_waybel_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_waybel_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( k4_waybel_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_waybel_1)).

fof(f391,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f246,f171])).

fof(f246,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X0) = k1_funct_1(k4_waybel_1(sK0,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f245,f211])).

fof(f211,plain,(
    v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f207,f154])).

fof(f207,plain,
    ( v2_struct_0(sK0)
    | v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f116,f39])).

fof(f245,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(sK0))
      | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X0) = k1_funct_1(k4_waybel_1(sK0,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f240,f189])).

fof(f189,plain,(
    v1_funct_1(k4_waybel_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f185,f154])).

fof(f185,plain,
    ( v2_struct_0(sK0)
    | v1_funct_1(k4_waybel_1(sK0,sK2)) ),
    inference(resolution,[],[f115,f39])).

fof(f240,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(sK0))
      | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
      | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X0) = k1_funct_1(k4_waybel_1(sK0,sK2),X0) ) ),
    inference(resolution,[],[f233,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f233,plain,(
    m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f229,f154])).

fof(f229,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f117,f39])).

fof(f366,plain,(
    r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) ),
    inference(backward_demodulation,[],[f284,f365])).

fof(f365,plain,(
    k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f363,f154])).

fof(f363,plain,
    ( k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f355,f124])).

fof(f355,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f350,f171])).

fof(f350,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | k1_funct_1(k4_waybel_1(sK0,sK2),X2) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),X2) ) ),
    inference(subsumption_resolution,[],[f349,f211])).

fof(f349,plain,(
    ! [X2] :
      ( ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k1_funct_1(k4_waybel_1(sK0,sK2),X2) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),X2) ) ),
    inference(subsumption_resolution,[],[f348,f189])).

fof(f348,plain,(
    ! [X2] :
      ( ~ v1_funct_1(k4_waybel_1(sK0,sK2))
      | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k1_funct_1(k4_waybel_1(sK0,sK2),X2) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),X2) ) ),
    inference(subsumption_resolution,[],[f346,f154])).

fof(f346,plain,(
    ! [X2] :
      ( v2_struct_0(sK0)
      | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
      | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k1_funct_1(k4_waybel_1(sK0,sK2),X2) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),X2) ) ),
    inference(resolution,[],[f119,f233])).

fof(f119,plain,(
    ! [X10,X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,u1_struct_0(sK0))))
      | v2_struct_0(sK0)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,X8,u1_struct_0(sK0))
      | v1_xboole_0(X8)
      | ~ m1_subset_1(X10,X8)
      | k1_funct_1(X9,X10) = k2_yellow_6(X8,sK0,X9,X10) ) ),
    inference(resolution,[],[f108,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
      | ~ m1_subset_1(X3,X0)
      | k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
      | ~ v1_funct_2(X2,X0,u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
      | ~ v1_funct_2(X2,X0,u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
        & v1_funct_2(X2,X0,u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_yellow_6)).

fof(f284,plain,(
    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) ),
    inference(subsumption_resolution,[],[f283,f40])).

fof(f40,plain,(
    v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f283,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) ),
    inference(subsumption_resolution,[],[f282,f233])).

fof(f282,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) ),
    inference(subsumption_resolution,[],[f281,f211])).

fof(f281,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) ),
    inference(subsumption_resolution,[],[f280,f189])).

fof(f280,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) ),
    inference(subsumption_resolution,[],[f279,f46])).

fof(f279,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) ),
    inference(subsumption_resolution,[],[f278,f45])).

fof(f278,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ v3_yellow_6(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) ),
    inference(subsumption_resolution,[],[f277,f44])).

fof(f277,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ v7_waybel_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) ),
    inference(subsumption_resolution,[],[f276,f43])).

fof(f276,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) ),
    inference(subsumption_resolution,[],[f275,f42])).

fof(f275,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) ),
    inference(subsumption_resolution,[],[f274,f54])).

fof(f274,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ l1_waybel_9(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) ),
    inference(subsumption_resolution,[],[f273,f53])).

fof(f273,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ v2_lattice3(sK0)
    | ~ l1_waybel_9(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) ),
    inference(subsumption_resolution,[],[f272,f52])).

fof(f272,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ v1_lattice3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ l1_waybel_9(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) ),
    inference(subsumption_resolution,[],[f271,f51])).

fof(f271,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ l1_waybel_9(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) ),
    inference(subsumption_resolution,[],[f270,f50])).

fof(f50,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f270,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ l1_waybel_9(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) ),
    inference(subsumption_resolution,[],[f269,f49])).

fof(f49,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f269,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ l1_waybel_9(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) ),
    inference(subsumption_resolution,[],[f268,f48])).

fof(f268,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ v8_pre_topc(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ l1_waybel_9(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) ),
    inference(subsumption_resolution,[],[f267,f47])).

fof(f267,plain,
    ( r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ l1_waybel_9(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) ),
    inference(superposition,[],[f64,f263])).

fof(f263,plain,(
    k3_waybel_2(sK0,sK2,sK1) = k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f259,f154])).

fof(f259,plain,
    ( v2_struct_0(sK0)
    | k3_waybel_2(sK0,sK2,sK1) = k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1) ),
    inference(resolution,[],[f138,f39])).

fof(f138,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,X0),sK1) = k3_waybel_2(sK0,X0,sK1) ) ),
    inference(subsumption_resolution,[],[f137,f42])).

fof(f137,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,X0),sK1) = k3_waybel_2(sK0,X0,sK1) ) ),
    inference(subsumption_resolution,[],[f129,f108])).

fof(f129,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,X0),sK1) = k3_waybel_2(sK0,X0,sK1) ) ),
    inference(resolution,[],[f46,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_waybel_9)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ v3_yellow_6(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ v5_pre_topc(X2,X0,X0)
      | r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1)))
              | ~ v5_pre_topc(X2,X0,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
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
              ( r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1)))
              | ~ v5_pre_topc(X2,X0,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v3_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v3_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X0)
               => r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_waybel_9)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:01:01 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (10980)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (10980)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % (10981)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (10973)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (10967)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (10975)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (10970)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f417,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f415,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ~r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) & m1_subset_1(X2,u1_struct_0(X0))) & (l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))))))),
% 0.22/0.49    inference(negated_conjecture,[],[f13])).
% 0.22/0.49  fof(f13,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_waybel_9)).
% 0.22/0.49  fof(f415,plain,(
% 0.22/0.49    r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))),
% 0.22/0.49    inference(backward_demodulation,[],[f366,f414])).
% 0.22/0.49  fof(f414,plain,(
% 0.22/0.49    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f412,f154])).
% 0.22/0.49  fof(f154,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(resolution,[],[f102,f108])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    l1_orders_2(sK0)),
% 0.22/0.49    inference(resolution,[],[f54,f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_waybel_9(X0) | l1_orders_2(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    l1_waybel_9(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    ~l1_orders_2(sK0) | ~v2_struct_0(sK0)),
% 0.22/0.49    inference(resolution,[],[f52,f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.22/0.49    inference(flattening,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    v1_lattice3(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f412,plain,(
% 0.22/0.49    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) | v2_struct_0(sK0)),
% 0.22/0.49    inference(resolution,[],[f395,f124])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    ~v1_xboole_0(u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.22/0.49    inference(resolution,[],[f110,f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    l1_struct_0(sK0)),
% 0.22/0.49    inference(resolution,[],[f108,f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.22/0.49  fof(f395,plain,(
% 0.22/0.49    v1_xboole_0(u1_struct_0(sK0)) | k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))),
% 0.22/0.49    inference(forward_demodulation,[],[f391,f332])).
% 0.22/0.49  fof(f332,plain,(
% 0.22/0.49    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))),
% 0.22/0.49    inference(forward_demodulation,[],[f328,f314])).
% 0.22/0.49  fof(f314,plain,(
% 0.22/0.49    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1))),
% 0.22/0.49    inference(resolution,[],[f309,f171])).
% 0.22/0.49  fof(f171,plain,(
% 0.22/0.49    m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.49    inference(resolution,[],[f136,f154])).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    v2_struct_0(sK0) | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.49    inference(subsumption_resolution,[],[f135,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    v3_yellow_6(sK1,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~v3_yellow_6(sK1,sK0) | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.49    inference(subsumption_resolution,[],[f134,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    v7_waybel_0(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.49    inference(subsumption_resolution,[],[f133,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    v4_orders_2(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.49    inference(subsumption_resolution,[],[f132,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ~v2_struct_0(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    v2_struct_0(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.49    inference(subsumption_resolution,[],[f131,f107])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    l1_pre_topc(sK0)),
% 0.22/0.49    inference(resolution,[],[f54,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_waybel_9(X0) | l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.49    inference(subsumption_resolution,[],[f130,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    v8_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~v8_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.49    inference(subsumption_resolution,[],[f127,f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    v2_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.49    inference(resolution,[],[f46,f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_yellow_6)).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    l1_waybel_0(sK1,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f309,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k12_lattice3(sK0,sK2,X0) = k11_lattice3(sK0,sK2,X0)) )),
% 0.22/0.49    inference(resolution,[],[f307,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f307,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k12_lattice3(sK0,X0,X1) = k11_lattice3(sK0,X0,X1)) )),
% 0.22/0.49    inference(resolution,[],[f105,f108])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k12_lattice3(sK0,X0,X1) = k11_lattice3(sK0,X0,X1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f103,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    v5_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k12_lattice3(sK0,X0,X1) = k11_lattice3(sK0,X0,X1)) )),
% 0.22/0.49    inference(resolution,[],[f53,f69])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.22/0.49    inference(flattening,[],[f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    v2_lattice3(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f328,plain,(
% 0.22/0.49    k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))),
% 0.22/0.49    inference(resolution,[],[f321,f171])).
% 0.22/0.49  fof(f321,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X0) = k11_lattice3(sK0,sK2,X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f317,f154])).
% 0.22/0.49  fof(f317,plain,(
% 0.22/0.49    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X0) = k11_lattice3(sK0,sK2,X0)) )),
% 0.22/0.49    inference(resolution,[],[f123,f39])).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    ( ! [X12,X11] : (~m1_subset_1(X11,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_subset_1(X12,u1_struct_0(sK0)) | k11_lattice3(sK0,X11,X12) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X11),X12)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f122,f117])).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    ( ! [X7] : (~m1_subset_1(X7,u1_struct_0(sK0)) | v2_struct_0(sK0) | m1_subset_1(k4_waybel_1(sK0,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) )),
% 0.22/0.49    inference(resolution,[],[f108,f68])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_1)).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    ( ! [X12,X11] : (v2_struct_0(sK0) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_subset_1(X12,u1_struct_0(sK0)) | k11_lattice3(sK0,X11,X12) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X11),X12)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f121,f116])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    ( ! [X6] : (~m1_subset_1(X6,u1_struct_0(sK0)) | v2_struct_0(sK0) | v1_funct_2(k4_waybel_1(sK0,X6),u1_struct_0(sK0),u1_struct_0(sK0))) )),
% 0.22/0.49    inference(resolution,[],[f108,f67])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    ( ! [X12,X11] : (v2_struct_0(sK0) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~v1_funct_2(k4_waybel_1(sK0,X11),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_subset_1(X12,u1_struct_0(sK0)) | k11_lattice3(sK0,X11,X12) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X11),X12)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f120,f115])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | v2_struct_0(sK0) | v1_funct_1(k4_waybel_1(sK0,X5))) )),
% 0.22/0.49    inference(resolution,[],[f108,f66])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v1_funct_1(k4_waybel_1(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    ( ! [X12,X11] : (v2_struct_0(sK0) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,X11)) | ~v1_funct_2(k4_waybel_1(sK0,X11),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_subset_1(X12,u1_struct_0(sK0)) | k11_lattice3(sK0,X11,X12) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,X11),X12)) )),
% 0.22/0.49    inference(resolution,[],[f108,f72])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_funct_1(k4_waybel_1(X0,X1)) | ~v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~m1_subset_1(X3,u1_struct_0(X0)) | k11_lattice3(X0,X1,X3) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X3)) )),
% 0.22/0.49    inference(equality_resolution,[],[f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~m1_subset_1(X3,u1_struct_0(X0)) | k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | k4_waybel_1(X0,X1) != X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(X2)) => (k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_waybel_1)).
% 0.22/0.49  fof(f391,plain,(
% 0.22/0.49    v1_xboole_0(u1_struct_0(sK0)) | k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))),
% 0.22/0.49    inference(resolution,[],[f246,f171])).
% 0.22/0.49  fof(f246,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X0) = k1_funct_1(k4_waybel_1(sK0,sK2),X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f245,f211])).
% 0.22/0.49  fof(f211,plain,(
% 0.22/0.49    v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.22/0.49    inference(subsumption_resolution,[],[f207,f154])).
% 0.22/0.49  fof(f207,plain,(
% 0.22/0.49    v2_struct_0(sK0) | v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.22/0.49    inference(resolution,[],[f116,f39])).
% 0.22/0.49  fof(f245,plain,(
% 0.22/0.49    ( ! [X0] : (v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X0) = k1_funct_1(k4_waybel_1(sK0,sK2),X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f240,f189])).
% 0.22/0.49  fof(f189,plain,(
% 0.22/0.49    v1_funct_1(k4_waybel_1(sK0,sK2))),
% 0.22/0.49    inference(subsumption_resolution,[],[f185,f154])).
% 0.22/0.49  fof(f185,plain,(
% 0.22/0.49    v2_struct_0(sK0) | v1_funct_1(k4_waybel_1(sK0,sK2))),
% 0.22/0.49    inference(resolution,[],[f115,f39])).
% 0.22/0.49  fof(f240,plain,(
% 0.22/0.49    ( ! [X0] : (v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X0) = k1_funct_1(k4_waybel_1(sK0,sK2),X0)) )),
% 0.22/0.49    inference(resolution,[],[f233,f71])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.22/0.49    inference(flattening,[],[f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.22/0.49  fof(f233,plain,(
% 0.22/0.49    m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f229,f154])).
% 0.22/0.49  fof(f229,plain,(
% 0.22/0.49    v2_struct_0(sK0) | m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.22/0.49    inference(resolution,[],[f117,f39])).
% 0.22/0.49  fof(f366,plain,(
% 0.22/0.49    r2_hidden(k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))),
% 0.22/0.49    inference(backward_demodulation,[],[f284,f365])).
% 0.22/0.49  fof(f365,plain,(
% 0.22/0.49    k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f363,f154])).
% 0.22/0.49  fof(f363,plain,(
% 0.22/0.49    k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) | v2_struct_0(sK0)),
% 0.22/0.49    inference(resolution,[],[f355,f124])).
% 0.22/0.49  fof(f355,plain,(
% 0.22/0.49    v1_xboole_0(u1_struct_0(sK0)) | k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))),
% 0.22/0.49    inference(resolution,[],[f350,f171])).
% 0.22/0.49  fof(f350,plain,(
% 0.22/0.49    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | k1_funct_1(k4_waybel_1(sK0,sK2),X2) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),X2)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f349,f211])).
% 0.22/0.49  fof(f349,plain,(
% 0.22/0.49    ( ! [X2] : (~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k1_funct_1(k4_waybel_1(sK0,sK2),X2) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),X2)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f348,f189])).
% 0.22/0.49  fof(f348,plain,(
% 0.22/0.49    ( ! [X2] : (~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k1_funct_1(k4_waybel_1(sK0,sK2),X2) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),X2)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f346,f154])).
% 0.22/0.49  fof(f346,plain,(
% 0.22/0.49    ( ! [X2] : (v2_struct_0(sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k1_funct_1(k4_waybel_1(sK0,sK2),X2) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),X2)) )),
% 0.22/0.49    inference(resolution,[],[f119,f233])).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    ( ! [X10,X8,X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,u1_struct_0(sK0)))) | v2_struct_0(sK0) | ~v1_funct_1(X9) | ~v1_funct_2(X9,X8,u1_struct_0(sK0)) | v1_xboole_0(X8) | ~m1_subset_1(X10,X8) | k1_funct_1(X9,X10) = k2_yellow_6(X8,sK0,X9,X10)) )),
% 0.22/0.49    inference(resolution,[],[f108,f70])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | v2_struct_0(X1) | ~l1_orders_2(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~m1_subset_1(X3,X0) | k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | v2_struct_0(X1) | v1_xboole_0(X0))),
% 0.22/0.49    inference(flattening,[],[f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | v2_struct_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) & v1_funct_2(X2,X0,u1_struct_0(X1)) & v1_funct_1(X2) & l1_orders_2(X1) & ~v2_struct_0(X1) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_yellow_6)).
% 0.22/0.49  fof(f284,plain,(
% 0.22/0.49    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f283,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f283,plain,(
% 0.22/0.49    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f282,f233])).
% 0.22/0.49  fof(f282,plain,(
% 0.22/0.49    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f281,f211])).
% 0.22/0.49  fof(f281,plain,(
% 0.22/0.49    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f280,f189])).
% 0.22/0.49  fof(f280,plain,(
% 0.22/0.49    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f279,f46])).
% 0.22/0.49  fof(f279,plain,(
% 0.22/0.49    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~l1_waybel_0(sK1,sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f278,f45])).
% 0.22/0.49  fof(f278,plain,(
% 0.22/0.49    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~v3_yellow_6(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f277,f44])).
% 0.22/0.49  fof(f277,plain,(
% 0.22/0.49    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f276,f43])).
% 0.22/0.49  fof(f276,plain,(
% 0.22/0.49    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f275,f42])).
% 0.22/0.49  fof(f275,plain,(
% 0.22/0.49    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f274,f54])).
% 0.22/0.49  fof(f274,plain,(
% 0.22/0.49    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~l1_waybel_9(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f273,f53])).
% 0.22/0.49  fof(f273,plain,(
% 0.22/0.49    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~v2_lattice3(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f272,f52])).
% 0.22/0.49  fof(f272,plain,(
% 0.22/0.49    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f271,f51])).
% 0.22/0.49  fof(f271,plain,(
% 0.22/0.49    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f270,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    v4_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f270,plain,(
% 0.22/0.49    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f269,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    v3_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f269,plain,(
% 0.22/0.49    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f268,f48])).
% 0.22/0.49  fof(f268,plain,(
% 0.22/0.49    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~v8_pre_topc(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f267,f47])).
% 0.22/0.49  fof(f267,plain,(
% 0.22/0.49    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) | ~v2_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)),
% 0.22/0.49    inference(superposition,[],[f64,f263])).
% 0.22/0.49  fof(f263,plain,(
% 0.22/0.49    k3_waybel_2(sK0,sK2,sK1) = k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f259,f154])).
% 0.22/0.49  fof(f259,plain,(
% 0.22/0.49    v2_struct_0(sK0) | k3_waybel_2(sK0,sK2,sK1) = k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)),
% 0.22/0.49    inference(resolution,[],[f138,f39])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,X0),sK1) = k3_waybel_2(sK0,X0,sK1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f137,f42])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    ( ! [X0] : (v2_struct_0(sK0) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,X0),sK1) = k3_waybel_2(sK0,X0,sK1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f129,f108])).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    ( ! [X0] : (v2_struct_0(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,X0),sK1) = k3_waybel_2(sK0,X0,sK1)) )),
% 0.22/0.49    inference(resolution,[],[f46,f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_waybel_9)).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X0) | r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) | ~v5_pre_topc(X2,X0,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) | ~v5_pre_topc(X2,X0,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X0) => r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1)))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_waybel_9)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (10980)------------------------------
% 0.22/0.49  % (10980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (10980)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (10980)Memory used [KB]: 1791
% 0.22/0.49  % (10980)Time elapsed: 0.036 s
% 0.22/0.49  % (10980)------------------------------
% 0.22/0.49  % (10980)------------------------------
% 0.22/0.50  % (10966)Success in time 0.132 s
%------------------------------------------------------------------------------
