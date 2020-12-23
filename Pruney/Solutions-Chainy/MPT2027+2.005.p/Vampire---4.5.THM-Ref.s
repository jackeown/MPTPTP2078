%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  149 (1087 expanded)
%              Number of leaves         :   13 ( 202 expanded)
%              Depth                    :   25
%              Number of atoms          :  751 (9500 expanded)
%              Number of equality atoms :   61 (  61 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f288,plain,(
    $false ),
    inference(subsumption_resolution,[],[f287,f41])).

% (24822)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (24830)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
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

fof(f287,plain,(
    r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) ),
    inference(backward_demodulation,[],[f173,f286])).

fof(f286,plain,(
    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f285,f78])).

fof(f78,plain,(
    ~ v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f77,f76])).

fof(f76,plain,(
    l1_orders_2(sK0) ),
    inference(resolution,[],[f57,f54])).

fof(f54,plain,(
    l1_waybel_9(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_waybel_9(X0)
      | l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f77,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_struct_0(sK0) ),
    inference(resolution,[],[f58,f52])).

fof(f52,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
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

fof(f285,plain,
    ( k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f284,f79])).

fof(f79,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f75,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f75,plain,(
    l1_pre_topc(sK0) ),
    inference(resolution,[],[f56,f54])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_waybel_9(X0)
      | l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f284,plain,
    ( k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f223,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f223,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) ),
    inference(backward_demodulation,[],[f196,f222])).

fof(f222,plain,(
    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f221,f78])).

fof(f221,plain,
    ( k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f220,f79])).

fof(f220,plain,
    ( k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f204,f59])).

fof(f204,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) ),
    inference(forward_demodulation,[],[f202,f167])).

fof(f167,plain,(
    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) ),
    inference(forward_demodulation,[],[f165,f161])).

fof(f161,plain,(
    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f92,f105])).

fof(f105,plain,(
    m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f104,f78])).

fof(f104,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f103,f45])).

fof(f45,plain,(
    v3_yellow_6(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f103,plain,
    ( ~ v3_yellow_6(sK1,sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f102,f44])).

fof(f44,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f102,plain,
    ( ~ v7_waybel_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f101,f43])).

fof(f43,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f101,plain,
    ( ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f100,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f100,plain,
    ( v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f99,f75])).

fof(f99,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f98,f48])).

fof(f48,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f98,plain,
    ( ~ v8_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f97,f47])).

% (24820)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f97,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v3_yellow_6(sK1,sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f65,f46])).

fof(f46,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ v3_yellow_6(X1,X0)
      | v2_struct_0(X0)
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

fof(f92,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k12_lattice3(sK0,sK2,X0) = k11_lattice3(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f91,f51])).

fof(f51,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v5_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k12_lattice3(sK0,sK2,X0) = k11_lattice3(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f90,f76])).

fof(f90,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k12_lattice3(sK0,sK2,X0) = k11_lattice3(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f89,f53])).

fof(f53,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k12_lattice3(sK0,sK2,X0) = k11_lattice3(sK0,sK2,X0) ) ),
    inference(resolution,[],[f69,f39])).

fof(f39,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
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

fof(f165,plain,(
    k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f109,f105])).

fof(f109,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k11_lattice3(sK0,sK2,X0) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f108,f82])).

fof(f82,plain,(
    v1_funct_1(k4_waybel_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f81,f78])).

fof(f81,plain,
    ( v2_struct_0(sK0)
    | v1_funct_1(k4_waybel_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f80,f76])).

fof(f80,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k4_waybel_1(sK0,sK2)) ),
    inference(resolution,[],[f66,f39])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | v1_funct_1(k4_waybel_1(X0,X1)) ) ),
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

fof(f108,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k4_waybel_1(sK0,sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k11_lattice3(sK0,sK2,X0) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f107,f78])).

fof(f107,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k11_lattice3(sK0,sK2,X0) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f106,f76])).

fof(f106,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k11_lattice3(sK0,sK2,X0) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X0) ) ),
    inference(resolution,[],[f74,f39])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_funct_1(k4_waybel_1(X0,X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X3) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X3) ) ),
    inference(subsumption_resolution,[],[f73,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v1_funct_1(k4_waybel_1(X0,X1))
      | ~ v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X3) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X3) ) ),
    inference(subsumption_resolution,[],[f72,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f202,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f159,f105])).

fof(f159,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X1) = k1_funct_1(k4_waybel_1(sK0,sK2),X1) ) ),
    inference(subsumption_resolution,[],[f158,f85])).

fof(f85,plain,(
    v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f84,f78])).

fof(f84,plain,
    ( v2_struct_0(sK0)
    | v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f83,f76])).

fof(f83,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f67,f39])).

fof(f158,plain,(
    ! [X1] :
      ( ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X1) = k1_funct_1(k4_waybel_1(sK0,sK2),X1) ) ),
    inference(subsumption_resolution,[],[f153,f82])).

% (24835)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (24817)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% (24832)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% (24819)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% (24827)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% (24821)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% (24836)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% (24829)Refutation not found, incomplete strategy% (24829)------------------------------
% (24829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24829)Termination reason: Refutation not found, incomplete strategy

% (24829)Memory used [KB]: 6140
% (24829)Time elapsed: 0.002 s
% (24829)------------------------------
% (24829)------------------------------
fof(f153,plain,(
    ! [X1] :
      ( ~ v1_funct_1(k4_waybel_1(sK0,sK2))
      | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X1) = k1_funct_1(k4_waybel_1(sK0,sK2),X1) ) ),
    inference(resolution,[],[f88,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X0)
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

fof(f88,plain,(
    m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f87,f78])).

fof(f87,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f86,f76])).

fof(f86,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f68,f39])).

fof(f196,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f157,f105])).

fof(f157,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | k1_funct_1(k4_waybel_1(sK0,sK2),X0) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f156,f85])).

fof(f156,plain,(
    ! [X0] :
      ( ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_funct_1(k4_waybel_1(sK0,sK2),X0) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f155,f82])).

fof(f155,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k4_waybel_1(sK0,sK2))
      | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_funct_1(k4_waybel_1(sK0,sK2),X0) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f154,f76])).

fof(f154,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
      | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_funct_1(k4_waybel_1(sK0,sK2),X0) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f152,f78])).

fof(f152,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
      | ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_funct_1(k4_waybel_1(sK0,sK2),X0) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),X0) ) ),
    inference(resolution,[],[f88,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1))))
      | v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,u1_struct_0(X1))
      | v1_xboole_0(X0)
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

fof(f173,plain,(
    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1))) ),
    inference(forward_demodulation,[],[f172,f162])).

fof(f162,plain,(
    k3_waybel_2(sK0,sK2,sK1) = k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1) ),
    inference(resolution,[],[f96,f39])).

fof(f96,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,X0),sK1) = k3_waybel_2(sK0,X0,sK1) ) ),
    inference(subsumption_resolution,[],[f95,f78])).

fof(f95,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,X0),sK1) = k3_waybel_2(sK0,X0,sK1) ) ),
    inference(subsumption_resolution,[],[f94,f42])).

fof(f94,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,X0),sK1) = k3_waybel_2(sK0,X0,sK1) ) ),
    inference(subsumption_resolution,[],[f93,f76])).

fof(f93,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,X0),sK1) = k3_waybel_2(sK0,X0,sK1) ) ),
    inference(resolution,[],[f63,f46])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
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

fof(f172,plain,(
    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) ),
    inference(subsumption_resolution,[],[f171,f40])).

fof(f40,plain,(
    v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f171,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)
    | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) ),
    inference(subsumption_resolution,[],[f170,f82])).

fof(f170,plain,
    ( ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)
    | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) ),
    inference(subsumption_resolution,[],[f169,f85])).

fof(f169,plain,
    ( ~ v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_waybel_1(sK0,sK2))
    | ~ v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)
    | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1))) ),
    inference(resolution,[],[f128,f88])).

fof(f128,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | ~ v5_pre_topc(X0,sK0,sK0)
      | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) ) ),
    inference(subsumption_resolution,[],[f127,f47])).

fof(f127,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v5_pre_topc(X0,sK0,sK0)
      | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) ) ),
    inference(subsumption_resolution,[],[f126,f45])).

% (24824)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f126,plain,(
    ! [X0] :
      ( ~ v3_yellow_6(sK1,sK0)
      | ~ v2_pre_topc(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v5_pre_topc(X0,sK0,sK0)
      | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) ) ),
    inference(subsumption_resolution,[],[f125,f44])).

fof(f125,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK1)
      | ~ v3_yellow_6(sK1,sK0)
      | ~ v2_pre_topc(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v5_pre_topc(X0,sK0,sK0)
      | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) ) ),
    inference(subsumption_resolution,[],[f124,f43])).

fof(f124,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK1)
      | ~ v7_waybel_0(sK1)
      | ~ v3_yellow_6(sK1,sK0)
      | ~ v2_pre_topc(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v5_pre_topc(X0,sK0,sK0)
      | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) ) ),
    inference(subsumption_resolution,[],[f123,f42])).

fof(f123,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v7_waybel_0(sK1)
      | ~ v3_yellow_6(sK1,sK0)
      | ~ v2_pre_topc(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v5_pre_topc(X0,sK0,sK0)
      | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) ) ),
    inference(subsumption_resolution,[],[f122,f54])).

fof(f122,plain,(
    ! [X0] :
      ( ~ l1_waybel_9(sK0)
      | v2_struct_0(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v7_waybel_0(sK1)
      | ~ v3_yellow_6(sK1,sK0)
      | ~ v2_pre_topc(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v5_pre_topc(X0,sK0,sK0)
      | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) ) ),
    inference(subsumption_resolution,[],[f121,f53])).

fof(f121,plain,(
    ! [X0] :
      ( ~ v2_lattice3(sK0)
      | ~ l1_waybel_9(sK0)
      | v2_struct_0(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v7_waybel_0(sK1)
      | ~ v3_yellow_6(sK1,sK0)
      | ~ v2_pre_topc(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v5_pre_topc(X0,sK0,sK0)
      | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) ) ),
    inference(subsumption_resolution,[],[f120,f52])).

fof(f120,plain,(
    ! [X0] :
      ( ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_waybel_9(sK0)
      | v2_struct_0(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v7_waybel_0(sK1)
      | ~ v3_yellow_6(sK1,sK0)
      | ~ v2_pre_topc(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v5_pre_topc(X0,sK0,sK0)
      | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) ) ),
    inference(subsumption_resolution,[],[f119,f51])).

fof(f119,plain,(
    ! [X0] :
      ( ~ v5_orders_2(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_waybel_9(sK0)
      | v2_struct_0(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v7_waybel_0(sK1)
      | ~ v3_yellow_6(sK1,sK0)
      | ~ v2_pre_topc(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v5_pre_topc(X0,sK0,sK0)
      | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) ) ),
    inference(subsumption_resolution,[],[f118,f50])).

fof(f50,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_waybel_9(sK0)
      | v2_struct_0(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v7_waybel_0(sK1)
      | ~ v3_yellow_6(sK1,sK0)
      | ~ v2_pre_topc(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v5_pre_topc(X0,sK0,sK0)
      | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) ) ),
    inference(subsumption_resolution,[],[f117,f49])).

fof(f49,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f117,plain,(
    ! [X0] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_lattice3(sK0)
      | ~ l1_waybel_9(sK0)
      | v2_struct_0(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v7_waybel_0(sK1)
      | ~ v3_yellow_6(sK1,sK0)
      | ~ v2_pre_topc(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v5_pre_topc(X0,sK0,sK0)
      | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) ) ),
    inference(subsumption_resolution,[],[f116,f48])).

fof(f116,plain,(
    ! [X0] :
      ( ~ v8_pre_topc(sK0)
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
      | ~ v2_pre_topc(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | ~ v5_pre_topc(X0,sK0,sK0)
      | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1))) ) ),
    inference(resolution,[],[f64,f46])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
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
      | ~ v2_pre_topc(X0)
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

% (24837)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% (24828)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (24833)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (24823)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (24825)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.52  % (24831)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.52  % (24826)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.52  % (24818)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (24834)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.52  % (24818)Refutation not found, incomplete strategy% (24818)------------------------------
% 0.22/0.52  % (24818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (24818)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (24818)Memory used [KB]: 10618
% 0.22/0.52  % (24818)Time elapsed: 0.078 s
% 0.22/0.52  % (24818)------------------------------
% 0.22/0.52  % (24818)------------------------------
% 0.22/0.52  % (24829)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (24834)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f288,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f287,f41])).
% 0.22/0.52  % (24822)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (24830)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ~r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) & m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1))) & v5_pre_topc(k4_waybel_1(X0,X2),X0,X0)) & m1_subset_1(X2,u1_struct_0(X0))) & (l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f13])).
% 0.22/0.53  fof(f13,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (v5_pre_topc(k4_waybel_1(X0,X2),X0,X0) => r2_hidden(k12_lattice3(X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k3_waybel_2(X0,X2,X1)))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_waybel_9)).
% 0.22/0.53  fof(f287,plain,(
% 0.22/0.53    r2_hidden(k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))),
% 0.22/0.53    inference(backward_demodulation,[],[f173,f286])).
% 0.22/0.53  fof(f286,plain,(
% 0.22/0.53    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))),
% 0.22/0.53    inference(subsumption_resolution,[],[f285,f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ~v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f77,f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    l1_orders_2(sK0)),
% 0.22/0.53    inference(resolution,[],[f57,f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    l1_waybel_9(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_waybel_9(X0) | l1_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ~l1_orders_2(sK0) | ~v2_struct_0(sK0)),
% 0.22/0.53    inference(resolution,[],[f58,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    v1_lattice3(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_lattice3(X0) | ~l1_orders_2(X0) | ~v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(flattening,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.22/0.53  fof(f285,plain,(
% 0.22/0.53    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f284,f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    l1_struct_0(sK0)),
% 0.22/0.53    inference(resolution,[],[f75,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(resolution,[],[f56,f54])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_waybel_9(X0) | l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f284,plain,(
% 0.22/0.53    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(resolution,[],[f223,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.53  fof(f223,plain,(
% 0.22/0.53    v1_xboole_0(u1_struct_0(sK0)) | k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))),
% 0.22/0.53    inference(backward_demodulation,[],[f196,f222])).
% 0.22/0.53  fof(f222,plain,(
% 0.22/0.53    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))),
% 0.22/0.53    inference(subsumption_resolution,[],[f221,f78])).
% 0.22/0.53  fof(f221,plain,(
% 0.22/0.53    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f220,f79])).
% 0.22/0.53  fof(f220,plain,(
% 0.22/0.53    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(resolution,[],[f204,f59])).
% 0.22/0.53  fof(f204,plain,(
% 0.22/0.53    v1_xboole_0(u1_struct_0(sK0)) | k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))),
% 0.22/0.53    inference(forward_demodulation,[],[f202,f167])).
% 0.22/0.53  fof(f167,plain,(
% 0.22/0.53    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))),
% 0.22/0.53    inference(forward_demodulation,[],[f165,f161])).
% 0.22/0.53  fof(f161,plain,(
% 0.22/0.53    k12_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1))),
% 0.22/0.53    inference(resolution,[],[f92,f105])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f104,f78])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    v2_struct_0(sK0) | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f103,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    v3_yellow_6(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    ~v3_yellow_6(sK1,sK0) | v2_struct_0(sK0) | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f102,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    v7_waybel_0(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | v2_struct_0(sK0) | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f101,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    v4_orders_2(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | v2_struct_0(sK0) | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f100,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ~v2_struct_0(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | v2_struct_0(sK0) | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f99,f75])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | v2_struct_0(sK0) | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f98,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    v8_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    ~v8_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | v2_struct_0(sK0) | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f97,f47])).
% 0.22/0.53  % (24820)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    v2_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    ~v2_pre_topc(sK0) | ~v8_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | v2_struct_0(sK0) | m1_subset_1(k11_yellow_6(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.53    inference(resolution,[],[f65,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    l1_waybel_0(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~l1_waybel_0(X1,X0) | ~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~v3_yellow_6(X1,X0) | v2_struct_0(X0) | m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v8_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k11_yellow_6(X0,X1),u1_struct_0(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_yellow_6)).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k12_lattice3(sK0,sK2,X0) = k11_lattice3(sK0,sK2,X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f91,f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    v5_orders_2(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    ( ! [X0] : (~v5_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k12_lattice3(sK0,sK2,X0) = k11_lattice3(sK0,sK2,X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f90,f76])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k12_lattice3(sK0,sK2,X0) = k11_lattice3(sK0,sK2,X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f89,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    v2_lattice3(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    ( ! [X0] : (~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k12_lattice3(sK0,sK2,X0) = k11_lattice3(sK0,sK2,X0)) )),
% 0.22/0.53    inference(resolution,[],[f69,f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.22/0.53    inference(flattening,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    k11_lattice3(sK0,sK2,k11_yellow_6(sK0,sK1)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))),
% 0.22/0.53    inference(resolution,[],[f109,f105])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k11_lattice3(sK0,sK2,X0) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f108,f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    v1_funct_1(k4_waybel_1(sK0,sK2))),
% 0.22/0.53    inference(subsumption_resolution,[],[f81,f78])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    v2_struct_0(sK0) | v1_funct_1(k4_waybel_1(sK0,sK2))),
% 0.22/0.53    inference(subsumption_resolution,[],[f80,f76])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ~l1_orders_2(sK0) | v2_struct_0(sK0) | v1_funct_1(k4_waybel_1(sK0,sK2))),
% 0.22/0.53    inference(resolution,[],[f66,f39])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0) | v1_funct_1(k4_waybel_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(k4_waybel_1(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_1)).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k11_lattice3(sK0,sK2,X0) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f107,f78])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    ( ! [X0] : (v2_struct_0(sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k11_lattice3(sK0,sK2,X0) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f106,f76])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_orders_2(sK0) | v2_struct_0(sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k11_lattice3(sK0,sK2,X0) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X0)) )),
% 0.22/0.53    inference(resolution,[],[f74,f39])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~v1_funct_1(k4_waybel_1(X0,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k11_lattice3(X0,X1,X3) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X3)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f73,f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0) | v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_funct_1(k4_waybel_1(X0,X1)) | ~v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k11_lattice3(X0,X1,X3) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X3)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f72,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0) | m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_funct_1(k4_waybel_1(X0,X1)) | ~v1_funct_2(k4_waybel_1(X0,X1),u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(k4_waybel_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~m1_subset_1(X3,u1_struct_0(X0)) | k11_lattice3(X0,X1,X3) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),k4_waybel_1(X0,X1),X3)) )),
% 0.22/0.53    inference(equality_resolution,[],[f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~m1_subset_1(X3,u1_struct_0(X0)) | k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | k4_waybel_1(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(X2)) => (k4_waybel_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k3_funct_2(u1_struct_0(X0),u1_struct_0(X0),X2,X3) = k11_lattice3(X0,X1,X3))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_waybel_1)).
% 0.22/0.53  fof(f202,plain,(
% 0.22/0.53    v1_xboole_0(u1_struct_0(sK0)) | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))),
% 0.22/0.53    inference(resolution,[],[f159,f105])).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X1) = k1_funct_1(k4_waybel_1(sK0,sK2),X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f158,f85])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f84,f78])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    v2_struct_0(sK0) | v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f83,f76])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    ~l1_orders_2(sK0) | v2_struct_0(sK0) | v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.22/0.53    inference(resolution,[],[f67,f39])).
% 0.22/0.53  fof(f158,plain,(
% 0.22/0.53    ( ! [X1] : (~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X1) = k1_funct_1(k4_waybel_1(sK0,sK2),X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f153,f82])).
% 0.22/0.53  % (24835)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.53  % (24817)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (24832)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.53  % (24819)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.54  % (24827)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.54  % (24821)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.54  % (24836)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.54  % (24829)Refutation not found, incomplete strategy% (24829)------------------------------
% 0.22/0.54  % (24829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (24829)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (24829)Memory used [KB]: 6140
% 0.22/0.54  % (24829)Time elapsed: 0.002 s
% 0.22/0.54  % (24829)------------------------------
% 0.22/0.54  % (24829)------------------------------
% 1.48/0.54  fof(f153,plain,(
% 1.48/0.54    ( ! [X1] : (~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k4_waybel_1(sK0,sK2),X1) = k1_funct_1(k4_waybel_1(sK0,sK2),X1)) )),
% 1.48/0.54    inference(resolution,[],[f88,f71])).
% 1.48/0.54  fof(f71,plain,(
% 1.48/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 1.48/0.54    inference(cnf_transformation,[],[f38])).
% 1.48/0.54  fof(f38,plain,(
% 1.48/0.54    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.48/0.54    inference(flattening,[],[f37])).
% 1.48/0.54  fof(f37,plain,(
% 1.48/0.54    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.48/0.54    inference(ennf_transformation,[],[f1])).
% 1.48/0.54  fof(f1,axiom,(
% 1.48/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 1.48/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 1.48/0.54  fof(f88,plain,(
% 1.48/0.54    m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 1.48/0.54    inference(subsumption_resolution,[],[f87,f78])).
% 1.48/0.54  fof(f87,plain,(
% 1.48/0.54    v2_struct_0(sK0) | m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 1.48/0.54    inference(subsumption_resolution,[],[f86,f76])).
% 1.48/0.54  fof(f86,plain,(
% 1.48/0.54    ~l1_orders_2(sK0) | v2_struct_0(sK0) | m1_subset_1(k4_waybel_1(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 1.48/0.54    inference(resolution,[],[f68,f39])).
% 1.48/0.54  fof(f196,plain,(
% 1.48/0.54    v1_xboole_0(u1_struct_0(sK0)) | k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)) = k1_funct_1(k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1))),
% 1.48/0.54    inference(resolution,[],[f157,f105])).
% 1.48/0.54  fof(f157,plain,(
% 1.48/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | k1_funct_1(k4_waybel_1(sK0,sK2),X0) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),X0)) )),
% 1.48/0.54    inference(subsumption_resolution,[],[f156,f85])).
% 1.48/0.54  fof(f156,plain,(
% 1.48/0.54    ( ! [X0] : (~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_funct_1(k4_waybel_1(sK0,sK2),X0) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),X0)) )),
% 1.48/0.54    inference(subsumption_resolution,[],[f155,f82])).
% 1.48/0.54  fof(f155,plain,(
% 1.48/0.54    ( ! [X0] : (~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_funct_1(k4_waybel_1(sK0,sK2),X0) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),X0)) )),
% 1.48/0.54    inference(subsumption_resolution,[],[f154,f76])).
% 1.48/0.54  fof(f154,plain,(
% 1.48/0.54    ( ! [X0] : (~l1_orders_2(sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_funct_1(k4_waybel_1(sK0,sK2),X0) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),X0)) )),
% 1.48/0.54    inference(subsumption_resolution,[],[f152,f78])).
% 1.48/0.54  fof(f152,plain,(
% 1.48/0.54    ( ! [X0] : (v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_funct_1(k4_waybel_1(sK0,sK2),X0) = k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),X0)) )),
% 1.48/0.54    inference(resolution,[],[f88,f70])).
% 1.48/0.54  fof(f70,plain,(
% 1.48/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | v2_struct_0(X1) | ~l1_orders_2(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | v1_xboole_0(X0) | ~m1_subset_1(X3,X0) | k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3)) )),
% 1.48/0.54    inference(cnf_transformation,[],[f36])).
% 1.48/0.54  fof(f36,plain,(
% 1.48/0.54    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | v2_struct_0(X1) | v1_xboole_0(X0))),
% 1.48/0.54    inference(flattening,[],[f35])).
% 1.48/0.54  fof(f35,plain,(
% 1.48/0.54    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) | ~v1_funct_2(X2,X0,u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | v2_struct_0(X1) | v1_xboole_0(X0)))),
% 1.48/0.54    inference(ennf_transformation,[],[f7])).
% 1.48/0.54  fof(f7,axiom,(
% 1.48/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(X1)))) & v1_funct_2(X2,X0,u1_struct_0(X1)) & v1_funct_1(X2) & l1_orders_2(X1) & ~v2_struct_0(X1) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k2_yellow_6(X0,X1,X2,X3))),
% 1.48/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_yellow_6)).
% 1.48/0.54  fof(f173,plain,(
% 1.48/0.54    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k3_waybel_2(sK0,sK2,sK1)))),
% 1.48/0.54    inference(forward_demodulation,[],[f172,f162])).
% 1.48/0.54  fof(f162,plain,(
% 1.48/0.54    k3_waybel_2(sK0,sK2,sK1) = k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)),
% 1.48/0.54    inference(resolution,[],[f96,f39])).
% 1.48/0.54  fof(f96,plain,(
% 1.48/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,X0),sK1) = k3_waybel_2(sK0,X0,sK1)) )),
% 1.48/0.54    inference(subsumption_resolution,[],[f95,f78])).
% 1.48/0.54  fof(f95,plain,(
% 1.48/0.54    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,X0),sK1) = k3_waybel_2(sK0,X0,sK1)) )),
% 1.48/0.54    inference(subsumption_resolution,[],[f94,f42])).
% 1.48/0.54  fof(f94,plain,(
% 1.48/0.54    ( ! [X0] : (v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,X0),sK1) = k3_waybel_2(sK0,X0,sK1)) )),
% 1.48/0.54    inference(subsumption_resolution,[],[f93,f76])).
% 1.48/0.54  fof(f93,plain,(
% 1.48/0.54    ( ! [X0] : (~l1_orders_2(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,X0),sK1) = k3_waybel_2(sK0,X0,sK1)) )),
% 1.48/0.54    inference(resolution,[],[f63,f46])).
% 1.48/0.54  fof(f63,plain,(
% 1.48/0.54    ( ! [X2,X0,X1] : (~l1_waybel_0(X1,X0) | ~l1_orders_2(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1)) )),
% 1.48/0.54    inference(cnf_transformation,[],[f26])).
% 1.48/0.54  fof(f26,plain,(
% 1.48/0.54    ! [X0] : (! [X1] : (! [X2] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.48/0.54    inference(flattening,[],[f25])).
% 1.48/0.54  fof(f25,plain,(
% 1.48/0.54    ! [X0] : (! [X1] : (! [X2] : (k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 1.48/0.54    inference(ennf_transformation,[],[f11])).
% 1.48/0.54  fof(f11,axiom,(
% 1.48/0.54    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k6_waybel_9(X0,X0,k4_waybel_1(X0,X2),X1) = k3_waybel_2(X0,X2,X1))))),
% 1.48/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_waybel_9)).
% 1.48/0.54  fof(f172,plain,(
% 1.48/0.54    r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))),
% 1.48/0.54    inference(subsumption_resolution,[],[f171,f40])).
% 1.48/0.54  fof(f40,plain,(
% 1.48/0.54    v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0)),
% 1.48/0.54    inference(cnf_transformation,[],[f16])).
% 1.48/0.54  fof(f171,plain,(
% 1.48/0.54    ~v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))),
% 1.48/0.54    inference(subsumption_resolution,[],[f170,f82])).
% 1.48/0.54  fof(f170,plain,(
% 1.48/0.54    ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))),
% 1.48/0.54    inference(subsumption_resolution,[],[f169,f85])).
% 1.48/0.54  fof(f169,plain,(
% 1.48/0.54    ~v1_funct_2(k4_waybel_1(sK0,sK2),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k4_waybel_1(sK0,sK2)) | ~v5_pre_topc(k4_waybel_1(sK0,sK2),sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,k4_waybel_1(sK0,sK2),k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,k4_waybel_1(sK0,sK2),sK1)))),
% 1.48/0.54    inference(resolution,[],[f128,f88])).
% 1.48/0.54  fof(f128,plain,(
% 1.48/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~v5_pre_topc(X0,sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))) )),
% 1.48/0.54    inference(subsumption_resolution,[],[f127,f47])).
% 1.48/0.54  fof(f127,plain,(
% 1.48/0.54    ( ! [X0] : (~v2_pre_topc(sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(X0,sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))) )),
% 1.48/0.54    inference(subsumption_resolution,[],[f126,f45])).
% 1.48/0.54  % (24824)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.48/0.54  fof(f126,plain,(
% 1.48/0.54    ( ! [X0] : (~v3_yellow_6(sK1,sK0) | ~v2_pre_topc(sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(X0,sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))) )),
% 1.48/0.54    inference(subsumption_resolution,[],[f125,f44])).
% 1.48/0.54  fof(f125,plain,(
% 1.48/0.54    ( ! [X0] : (~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~v2_pre_topc(sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(X0,sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))) )),
% 1.48/0.54    inference(subsumption_resolution,[],[f124,f43])).
% 1.48/0.54  fof(f124,plain,(
% 1.48/0.54    ( ! [X0] : (~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~v2_pre_topc(sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(X0,sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))) )),
% 1.48/0.54    inference(subsumption_resolution,[],[f123,f42])).
% 1.48/0.54  fof(f123,plain,(
% 1.48/0.54    ( ! [X0] : (v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~v2_pre_topc(sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(X0,sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))) )),
% 1.48/0.54    inference(subsumption_resolution,[],[f122,f54])).
% 1.48/0.54  fof(f122,plain,(
% 1.48/0.54    ( ! [X0] : (~l1_waybel_9(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~v2_pre_topc(sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(X0,sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))) )),
% 1.48/0.54    inference(subsumption_resolution,[],[f121,f53])).
% 1.48/0.54  fof(f121,plain,(
% 1.48/0.54    ( ! [X0] : (~v2_lattice3(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~v2_pre_topc(sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(X0,sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))) )),
% 1.48/0.54    inference(subsumption_resolution,[],[f120,f52])).
% 1.48/0.54  fof(f120,plain,(
% 1.48/0.54    ( ! [X0] : (~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~v2_pre_topc(sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(X0,sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))) )),
% 1.48/0.54    inference(subsumption_resolution,[],[f119,f51])).
% 1.48/0.54  fof(f119,plain,(
% 1.48/0.54    ( ! [X0] : (~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~v2_pre_topc(sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(X0,sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))) )),
% 1.48/0.54    inference(subsumption_resolution,[],[f118,f50])).
% 1.48/0.54  fof(f50,plain,(
% 1.48/0.54    v4_orders_2(sK0)),
% 1.48/0.54    inference(cnf_transformation,[],[f16])).
% 1.48/0.54  fof(f118,plain,(
% 1.48/0.54    ( ! [X0] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~v2_pre_topc(sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(X0,sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))) )),
% 1.48/0.54    inference(subsumption_resolution,[],[f117,f49])).
% 1.48/0.54  fof(f49,plain,(
% 1.48/0.54    v3_orders_2(sK0)),
% 1.48/0.54    inference(cnf_transformation,[],[f16])).
% 1.48/0.54  fof(f117,plain,(
% 1.48/0.54    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~v2_pre_topc(sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(X0,sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))) )),
% 1.48/0.54    inference(subsumption_resolution,[],[f116,f48])).
% 1.48/0.54  fof(f116,plain,(
% 1.48/0.54    ( ! [X0] : (~v8_pre_topc(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~v3_yellow_6(sK1,sK0) | ~v2_pre_topc(sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v5_pre_topc(X0,sK0,sK0) | r2_hidden(k2_yellow_6(u1_struct_0(sK0),sK0,X0,k11_yellow_6(sK0,sK1)),k10_yellow_6(sK0,k6_waybel_9(sK0,sK0,X0,sK1)))) )),
% 1.48/0.54    inference(resolution,[],[f64,f46])).
% 1.48/0.54  fof(f64,plain,(
% 1.48/0.54    ( ! [X2,X0,X1] : (~l1_waybel_0(X1,X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~v3_yellow_6(X1,X0) | ~v2_pre_topc(X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X0) | r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1)))) )),
% 1.48/0.54    inference(cnf_transformation,[],[f28])).
% 1.48/0.54  fof(f28,plain,(
% 1.48/0.54    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) | ~v5_pre_topc(X2,X0,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.48/0.54    inference(flattening,[],[f27])).
% 1.48/0.54  fof(f27,plain,(
% 1.48/0.54    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1))) | ~v5_pre_topc(X2,X0,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_waybel_0(X1,X0) | ~v3_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.48/0.54    inference(ennf_transformation,[],[f12])).
% 1.48/0.54  % (24837)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.48/0.54  % (24828)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.48/0.55  % (24833)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.48/0.55  fof(f12,axiom,(
% 1.48/0.55    ! [X0] : ((l1_waybel_9(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v3_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X0) => r2_hidden(k2_yellow_6(u1_struct_0(X0),X0,X2,k11_yellow_6(X0,X1)),k10_yellow_6(X0,k6_waybel_9(X0,X0,X2,X1)))))))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_waybel_9)).
% 1.48/0.55  % SZS output end Proof for theBenchmark
% 1.48/0.55  % (24834)------------------------------
% 1.48/0.55  % (24834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (24834)Termination reason: Refutation
% 1.48/0.55  
% 1.48/0.55  % (24834)Memory used [KB]: 1918
% 1.48/0.55  % (24834)Time elapsed: 0.093 s
% 1.48/0.55  % (24834)------------------------------
% 1.48/0.55  % (24834)------------------------------
% 1.48/0.55  % (24816)Success in time 0.189 s
%------------------------------------------------------------------------------
