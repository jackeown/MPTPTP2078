%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 242 expanded)
%              Number of leaves         :   30 ( 117 expanded)
%              Depth                    :   13
%              Number of atoms          :  589 (1582 expanded)
%              Number of equality atoms :   63 (  67 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f171,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f80,f84,f88,f92,f96,f100,f104,f121,f128,f142,f150,f152,f158,f161,f165,f168,f170])).

fof(f170,plain,
    ( spl5_11
    | ~ spl5_10
    | ~ spl5_9
    | spl5_8
    | ~ spl5_5
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f169,f65,f78,f90,f94,f98,f102])).

fof(f102,plain,
    ( spl5_11
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f98,plain,
    ( spl5_10
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f94,plain,
    ( spl5_9
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f90,plain,
    ( spl5_8
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f78,plain,
    ( spl5_5
  <=> l1_waybel_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f65,plain,
    ( spl5_1
  <=> v2_struct_0(k3_waybel_2(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f169,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f66,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_waybel_2(X0,X1,X2))
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_waybel_2(X0,X1,X2)) )
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_waybel_2(X0,X1,X2)) )
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_waybel_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_waybel_2)).

fof(f66,plain,
    ( v2_struct_0(k3_waybel_2(sK0,sK1,sK2))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f168,plain,
    ( spl5_11
    | ~ spl5_10
    | ~ spl5_9
    | spl5_8
    | ~ spl5_6
    | ~ spl5_5
    | spl5_3 ),
    inference(avatar_split_clause,[],[f166,f71,f78,f82,f90,f94,f98,f102])).

fof(f82,plain,
    ( spl5_6
  <=> v7_waybel_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f71,plain,
    ( spl5_3
  <=> v7_waybel_0(k3_waybel_2(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f166,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | ~ v7_waybel_0(sK2)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(resolution,[],[f72,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_waybel_2(X0,X1,X2))
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_waybel_2(X0,X1,X2))
        & v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) )
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_waybel_2(X0,X1,X2))
        & v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) )
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(X2,X0)
        & v7_waybel_0(X2)
        & ~ v2_struct_0(X2)
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_waybel_2(X0,X1,X2))
        & v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_waybel_2)).

fof(f72,plain,
    ( ~ v7_waybel_0(k3_waybel_2(sK0,sK1,sK2))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f165,plain,
    ( spl5_11
    | ~ spl5_10
    | ~ spl5_9
    | spl5_8
    | ~ spl5_5
    | spl5_4 ),
    inference(avatar_split_clause,[],[f164,f74,f78,f90,f94,f98,f102])).

fof(f74,plain,
    ( spl5_4
  <=> l1_waybel_0(k3_waybel_2(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f164,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl5_4 ),
    inference(resolution,[],[f75,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
        & v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) )
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
        & v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) )
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
        & v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_waybel_2)).

fof(f75,plain,
    ( ~ l1_waybel_0(k3_waybel_2(sK0,sK1,sK2),sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f161,plain,
    ( ~ spl5_17
    | ~ spl5_5
    | spl5_18 ),
    inference(avatar_split_clause,[],[f160,f155,f78,f148])).

fof(f148,plain,
    ( spl5_17
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f155,plain,
    ( spl5_18
  <=> l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f160,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl5_5
    | spl5_18 ),
    inference(resolution,[],[f159,f79])).

fof(f79,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK2,X0)
        | ~ l1_struct_0(X0) )
    | spl5_18 ),
    inference(resolution,[],[f156,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f156,plain,
    ( ~ l1_orders_2(sK2)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f155])).

fof(f158,plain,
    ( spl5_8
    | ~ spl5_18
    | ~ spl5_7
    | spl5_16 ),
    inference(avatar_split_clause,[],[f153,f140,f86,f155,f90])).

fof(f86,plain,
    ( spl5_7
  <=> v4_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f140,plain,
    ( spl5_16
  <=> v4_orders_2(g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f153,plain,
    ( ~ v4_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl5_16 ),
    inference(resolution,[],[f141,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v4_orders_2(X0)
          | ~ v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) )
        & ( v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))
          | ~ v4_orders_2(X0) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v4_orders_2(X0)
      <=> v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v4_orders_2(X0)
      <=> v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_orders_2(X0)
      <=> v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l16_yellow_6)).

fof(f141,plain,
    ( ~ v4_orders_2(g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)))
    | spl5_16 ),
    inference(avatar_component_clause,[],[f140])).

fof(f152,plain,
    ( ~ spl5_10
    | spl5_17 ),
    inference(avatar_split_clause,[],[f151,f148,f98])).

fof(f151,plain,
    ( ~ l1_orders_2(sK0)
    | spl5_17 ),
    inference(resolution,[],[f149,f44])).

fof(f44,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f149,plain,
    ( ~ l1_struct_0(sK0)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f148])).

fof(f150,plain,
    ( spl5_11
    | ~ spl5_10
    | ~ spl5_9
    | spl5_8
    | ~ spl5_5
    | ~ spl5_17
    | spl5_15 ),
    inference(avatar_split_clause,[],[f144,f136,f148,f78,f90,f94,f98,f102])).

fof(f136,plain,
    ( spl5_15
  <=> l1_orders_2(k3_waybel_2(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f144,plain,
    ( ~ l1_struct_0(sK0)
    | ~ l1_waybel_0(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl5_15 ),
    inference(resolution,[],[f143,f58])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(k3_waybel_2(sK0,sK1,sK2),X0)
        | ~ l1_struct_0(X0) )
    | spl5_15 ),
    inference(resolution,[],[f137,f43])).

fof(f137,plain,
    ( ~ l1_orders_2(k3_waybel_2(sK0,sK1,sK2))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f136])).

fof(f142,plain,
    ( spl5_1
    | ~ spl5_15
    | spl5_2
    | ~ spl5_16
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f133,f126,f140,f68,f136,f65])).

fof(f68,plain,
    ( spl5_2
  <=> v4_orders_2(k3_waybel_2(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f126,plain,
    ( spl5_13
  <=> g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(k3_waybel_2(sK0,sK1,sK2)),u1_orders_2(k3_waybel_2(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f133,plain,
    ( ~ v4_orders_2(g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)))
    | v4_orders_2(k3_waybel_2(sK0,sK1,sK2))
    | ~ l1_orders_2(k3_waybel_2(sK0,sK1,sK2))
    | v2_struct_0(k3_waybel_2(sK0,sK1,sK2))
    | ~ spl5_13 ),
    inference(superposition,[],[f46,f127])).

fof(f127,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(k3_waybel_2(sK0,sK1,sK2)),u1_orders_2(k3_waybel_2(sK0,sK1,sK2)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f126])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))
      | v4_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f128,plain,
    ( spl5_8
    | spl5_13
    | ~ spl5_5
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f122,f119,f78,f126,f90])).

fof(f119,plain,
    ( spl5_12
  <=> ! [X0] :
        ( ~ l1_waybel_0(X0,sK0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_waybel_2(sK0,sK1,X0)),u1_orders_2(k3_waybel_2(sK0,sK1,X0)))
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f122,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(k3_waybel_2(sK0,sK1,sK2)),u1_orders_2(k3_waybel_2(sK0,sK1,sK2)))
    | v2_struct_0(sK2)
    | ~ spl5_5
    | ~ spl5_12 ),
    inference(resolution,[],[f120,f79])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_waybel_2(sK0,sK1,X0)),u1_orders_2(k3_waybel_2(sK0,sK1,X0)))
        | v2_struct_0(X0) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f121,plain,
    ( spl5_11
    | ~ spl5_10
    | spl5_12
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f115,f94,f119,f98,f102])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_waybel_2(sK0,sK1,X0)),u1_orders_2(k3_waybel_2(sK0,sK1,X0)))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_9 ),
    inference(resolution,[],[f109,f95])).

fof(f95,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f94])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(k3_waybel_2(X0,X1,X2)),u1_orders_2(k3_waybel_2(X0,X1,X2)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f105,f58])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(k3_waybel_2(X0,X1,X2)),u1_orders_2(k3_waybel_2(X0,X1,X2)))
      | ~ l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f63,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(k3_waybel_2(X0,X1,X2)),u1_orders_2(k3_waybel_2(X0,X1,X2)))
      | ~ l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
      | ~ v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
      | k3_waybel_2(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_waybel_2(X0,X1,X2) = X3
                      | ( ! [X5] :
                            ( k11_lattice3(X0,X1,X5) != k1_funct_1(u1_waybel_0(X0,X3),sK3(X0,X1,X2,X3))
                            | k1_funct_1(u1_waybel_0(X0,X2),sK3(X0,X1,X2,X3)) != X5
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X3)) )
                      | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                    & ( ( ! [X6] :
                            ( ( k1_funct_1(u1_waybel_0(X0,X3),X6) = k11_lattice3(X0,X1,sK4(X0,X1,X2,X3,X6))
                              & k1_funct_1(u1_waybel_0(X0,X2),X6) = sK4(X0,X1,X2,X3,X6)
                              & m1_subset_1(sK4(X0,X1,X2,X3,X6),u1_struct_0(X0)) )
                            | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                        & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                      | k3_waybel_2(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ l1_waybel_0(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f33,f32])).

fof(f32,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(u1_waybel_0(X0,X3),X4) != k11_lattice3(X0,X1,X5)
              | k1_funct_1(u1_waybel_0(X0,X2),X4) != X5
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & m1_subset_1(X4,u1_struct_0(X3)) )
     => ( ! [X5] :
            ( k11_lattice3(X0,X1,X5) != k1_funct_1(u1_waybel_0(X0,X3),sK3(X0,X1,X2,X3))
            | k1_funct_1(u1_waybel_0(X0,X2),sK3(X0,X1,X2,X3)) != X5
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X6,X3,X2,X1,X0] :
      ( ? [X7] :
          ( k1_funct_1(u1_waybel_0(X0,X3),X6) = k11_lattice3(X0,X1,X7)
          & k1_funct_1(u1_waybel_0(X0,X2),X6) = X7
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( k1_funct_1(u1_waybel_0(X0,X3),X6) = k11_lattice3(X0,X1,sK4(X0,X1,X2,X3,X6))
        & k1_funct_1(u1_waybel_0(X0,X2),X6) = sK4(X0,X1,X2,X3,X6)
        & m1_subset_1(sK4(X0,X1,X2,X3,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_waybel_2(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ! [X5] :
                              ( k1_funct_1(u1_waybel_0(X0,X3),X4) != k11_lattice3(X0,X1,X5)
                              | k1_funct_1(u1_waybel_0(X0,X2),X4) != X5
                              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                          & m1_subset_1(X4,u1_struct_0(X3)) )
                      | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                    & ( ( ! [X6] :
                            ( ? [X7] :
                                ( k1_funct_1(u1_waybel_0(X0,X3),X6) = k11_lattice3(X0,X1,X7)
                                & k1_funct_1(u1_waybel_0(X0,X2),X6) = X7
                                & m1_subset_1(X7,u1_struct_0(X0)) )
                            | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                        & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                      | k3_waybel_2(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ l1_waybel_0(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_waybel_2(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ! [X5] :
                              ( k1_funct_1(u1_waybel_0(X0,X3),X4) != k11_lattice3(X0,X1,X5)
                              | k1_funct_1(u1_waybel_0(X0,X2),X4) != X5
                              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                          & m1_subset_1(X4,u1_struct_0(X3)) )
                      | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                    & ( ( ! [X4] :
                            ( ? [X5] :
                                ( k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5)
                                & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5
                                & m1_subset_1(X5,u1_struct_0(X0)) )
                            | ~ m1_subset_1(X4,u1_struct_0(X3)) )
                        & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                      | k3_waybel_2(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ l1_waybel_0(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_waybel_2(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ! [X5] :
                              ( k1_funct_1(u1_waybel_0(X0,X3),X4) != k11_lattice3(X0,X1,X5)
                              | k1_funct_1(u1_waybel_0(X0,X2),X4) != X5
                              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                          & m1_subset_1(X4,u1_struct_0(X3)) )
                      | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                    & ( ( ! [X4] :
                            ( ? [X5] :
                                ( k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5)
                                & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5
                                & m1_subset_1(X5,u1_struct_0(X0)) )
                            | ~ m1_subset_1(X4,u1_struct_0(X3)) )
                        & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                      | k3_waybel_2(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ l1_waybel_0(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k3_waybel_2(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( ? [X5] :
                              ( k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5)
                              & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5
                              & m1_subset_1(X5,u1_struct_0(X0)) )
                          | ~ m1_subset_1(X4,u1_struct_0(X3)) )
                      & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ l1_waybel_0(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k3_waybel_2(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( ? [X5] :
                              ( k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5)
                              & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5
                              & m1_subset_1(X5,u1_struct_0(X0)) )
                          | ~ m1_subset_1(X4,u1_struct_0(X3)) )
                      & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ l1_waybel_0(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( l1_waybel_0(X3,X0)
                    & v6_waybel_0(X3,X0) )
                 => ( k3_waybel_2(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X3))
                         => ? [X5] :
                              ( k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5)
                              & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5
                              & m1_subset_1(X5,u1_struct_0(X0)) ) )
                      & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_waybel_2)).

fof(f104,plain,(
    ~ spl5_11 ),
    inference(avatar_split_clause,[],[f35,f102])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ l1_waybel_0(k3_waybel_2(sK0,sK1,sK2),sK0)
      | ~ v7_waybel_0(k3_waybel_2(sK0,sK1,sK2))
      | ~ v4_orders_2(k3_waybel_2(sK0,sK1,sK2))
      | v2_struct_0(k3_waybel_2(sK0,sK1,sK2)) )
    & l1_waybel_0(sK2,sK0)
    & v7_waybel_0(sK2)
    & v4_orders_2(sK2)
    & ~ v2_struct_0(sK2)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
                  | ~ v7_waybel_0(k3_waybel_2(X0,X1,X2))
                  | ~ v4_orders_2(k3_waybel_2(X0,X1,X2))
                  | v2_struct_0(k3_waybel_2(X0,X1,X2)) )
                & l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ l1_waybel_0(k3_waybel_2(sK0,X1,X2),sK0)
                | ~ v7_waybel_0(k3_waybel_2(sK0,X1,X2))
                | ~ v4_orders_2(k3_waybel_2(sK0,X1,X2))
                | v2_struct_0(k3_waybel_2(sK0,X1,X2)) )
              & l1_waybel_0(X2,sK0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ l1_waybel_0(k3_waybel_2(sK0,X1,X2),sK0)
              | ~ v7_waybel_0(k3_waybel_2(sK0,X1,X2))
              | ~ v4_orders_2(k3_waybel_2(sK0,X1,X2))
              | v2_struct_0(k3_waybel_2(sK0,X1,X2)) )
            & l1_waybel_0(X2,sK0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ l1_waybel_0(k3_waybel_2(sK0,sK1,X2),sK0)
            | ~ v7_waybel_0(k3_waybel_2(sK0,sK1,X2))
            | ~ v4_orders_2(k3_waybel_2(sK0,sK1,X2))
            | v2_struct_0(k3_waybel_2(sK0,sK1,X2)) )
          & l1_waybel_0(X2,sK0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ( ~ l1_waybel_0(k3_waybel_2(sK0,sK1,X2),sK0)
          | ~ v7_waybel_0(k3_waybel_2(sK0,sK1,X2))
          | ~ v4_orders_2(k3_waybel_2(sK0,sK1,X2))
          | v2_struct_0(k3_waybel_2(sK0,sK1,X2)) )
        & l1_waybel_0(X2,sK0)
        & v7_waybel_0(X2)
        & v4_orders_2(X2)
        & ~ v2_struct_0(X2) )
   => ( ( ~ l1_waybel_0(k3_waybel_2(sK0,sK1,sK2),sK0)
        | ~ v7_waybel_0(k3_waybel_2(sK0,sK1,sK2))
        | ~ v4_orders_2(k3_waybel_2(sK0,sK1,sK2))
        | v2_struct_0(k3_waybel_2(sK0,sK1,sK2)) )
      & l1_waybel_0(sK2,sK0)
      & v7_waybel_0(sK2)
      & v4_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
                | ~ v7_waybel_0(k3_waybel_2(X0,X1,X2))
                | ~ v4_orders_2(k3_waybel_2(X0,X1,X2))
                | v2_struct_0(k3_waybel_2(X0,X1,X2)) )
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
                | ~ v7_waybel_0(k3_waybel_2(X0,X1,X2))
                | ~ v4_orders_2(k3_waybel_2(X0,X1,X2))
                | v2_struct_0(k3_waybel_2(X0,X1,X2)) )
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( l1_waybel_0(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ( l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
                  & v7_waybel_0(k3_waybel_2(X0,X1,X2))
                  & v4_orders_2(k3_waybel_2(X0,X1,X2))
                  & ~ v2_struct_0(k3_waybel_2(X0,X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
                & v7_waybel_0(k3_waybel_2(X0,X1,X2))
                & v4_orders_2(k3_waybel_2(X0,X1,X2))
                & ~ v2_struct_0(k3_waybel_2(X0,X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_9)).

fof(f100,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f36,f98])).

fof(f36,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f96,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f37,f94])).

fof(f37,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f92,plain,(
    ~ spl5_8 ),
    inference(avatar_split_clause,[],[f38,f90])).

fof(f38,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f88,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f39,f86])).

fof(f39,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f40,f82])).

fof(f40,plain,(
    v7_waybel_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f80,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f41,f78])).

fof(f41,plain,(
    l1_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f42,f74,f71,f68,f65])).

fof(f42,plain,
    ( ~ l1_waybel_0(k3_waybel_2(sK0,sK1,sK2),sK0)
    | ~ v7_waybel_0(k3_waybel_2(sK0,sK1,sK2))
    | ~ v4_orders_2(k3_waybel_2(sK0,sK1,sK2))
    | v2_struct_0(k3_waybel_2(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:48:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (27932)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.47  % (27927)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (27927)Refutation not found, incomplete strategy% (27927)------------------------------
% 0.22/0.47  % (27927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (27932)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (27943)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.48  % (27927)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (27927)Memory used [KB]: 10618
% 0.22/0.48  % (27927)Time elapsed: 0.060 s
% 0.22/0.48  % (27927)------------------------------
% 0.22/0.48  % (27927)------------------------------
% 0.22/0.48  % (27940)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f171,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f76,f80,f84,f88,f92,f96,f100,f104,f121,f128,f142,f150,f152,f158,f161,f165,f168,f170])).
% 0.22/0.48  fof(f170,plain,(
% 0.22/0.48    spl5_11 | ~spl5_10 | ~spl5_9 | spl5_8 | ~spl5_5 | ~spl5_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f169,f65,f78,f90,f94,f98,f102])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    spl5_11 <=> v2_struct_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    spl5_10 <=> l1_orders_2(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    spl5_9 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    spl5_8 <=> v2_struct_0(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    spl5_5 <=> l1_waybel_0(sK2,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    spl5_1 <=> v2_struct_0(k3_waybel_2(sK0,sK1,sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.48  fof(f169,plain,(
% 0.22/0.48    ~l1_waybel_0(sK2,sK0) | v2_struct_0(sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~spl5_1),
% 0.22/0.48    inference(resolution,[],[f66,f55])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v2_struct_0(k3_waybel_2(X0,X1,X2)) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) & ~v2_struct_0(k3_waybel_2(X0,X1,X2))) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) & ~v2_struct_0(k3_waybel_2(X0,X1,X2))) | (~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((l1_waybel_0(X2,X0) & ~v2_struct_0(X2) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) & ~v2_struct_0(k3_waybel_2(X0,X1,X2))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_waybel_2)).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    v2_struct_0(k3_waybel_2(sK0,sK1,sK2)) | ~spl5_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f65])).
% 0.22/0.48  fof(f168,plain,(
% 0.22/0.48    spl5_11 | ~spl5_10 | ~spl5_9 | spl5_8 | ~spl5_6 | ~spl5_5 | spl5_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f166,f71,f78,f82,f90,f94,f98,f102])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    spl5_6 <=> v7_waybel_0(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    spl5_3 <=> v7_waybel_0(k3_waybel_2(sK0,sK1,sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.48  fof(f166,plain,(
% 0.22/0.48    ~l1_waybel_0(sK2,sK0) | ~v7_waybel_0(sK2) | v2_struct_0(sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | spl5_3),
% 0.22/0.48    inference(resolution,[],[f72,f54])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (v7_waybel_0(k3_waybel_2(X0,X1,X2)) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((v7_waybel_0(k3_waybel_2(X0,X1,X2)) & v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)) | ~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((v7_waybel_0(k3_waybel_2(X0,X1,X2)) & v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)) | (~l1_waybel_0(X2,X0) | ~v7_waybel_0(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & ~v2_struct_0(X2) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_waybel_2(X0,X1,X2)) & v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_waybel_2)).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ~v7_waybel_0(k3_waybel_2(sK0,sK1,sK2)) | spl5_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f71])).
% 0.22/0.48  fof(f165,plain,(
% 0.22/0.48    spl5_11 | ~spl5_10 | ~spl5_9 | spl5_8 | ~spl5_5 | spl5_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f164,f74,f78,f90,f94,f98,f102])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    spl5_4 <=> l1_waybel_0(k3_waybel_2(sK0,sK1,sK2),sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.48  fof(f164,plain,(
% 0.22/0.48    ~l1_waybel_0(sK2,sK0) | v2_struct_0(sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | spl5_4),
% 0.22/0.48    inference(resolution,[],[f75,f58])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (l1_waybel_0(k3_waybel_2(X0,X1,X2),X0) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((l1_waybel_0(k3_waybel_2(X0,X1,X2),X0) & v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((l1_waybel_0(k3_waybel_2(X0,X1,X2),X0) & v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)) | (~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((l1_waybel_0(X2,X0) & ~v2_struct_0(X2) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_waybel_2(X0,X1,X2),X0) & v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_waybel_2)).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    ~l1_waybel_0(k3_waybel_2(sK0,sK1,sK2),sK0) | spl5_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f74])).
% 0.22/0.48  fof(f161,plain,(
% 0.22/0.48    ~spl5_17 | ~spl5_5 | spl5_18),
% 0.22/0.48    inference(avatar_split_clause,[],[f160,f155,f78,f148])).
% 0.22/0.48  fof(f148,plain,(
% 0.22/0.48    spl5_17 <=> l1_struct_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.22/0.48  fof(f155,plain,(
% 0.22/0.48    spl5_18 <=> l1_orders_2(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.22/0.48  fof(f160,plain,(
% 0.22/0.48    ~l1_struct_0(sK0) | (~spl5_5 | spl5_18)),
% 0.22/0.48    inference(resolution,[],[f159,f79])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    l1_waybel_0(sK2,sK0) | ~spl5_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f78])).
% 0.22/0.48  fof(f159,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_waybel_0(sK2,X0) | ~l1_struct_0(X0)) ) | spl5_18),
% 0.22/0.48    inference(resolution,[],[f156,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X0,X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 0.22/0.48  fof(f156,plain,(
% 0.22/0.48    ~l1_orders_2(sK2) | spl5_18),
% 0.22/0.48    inference(avatar_component_clause,[],[f155])).
% 0.22/0.48  fof(f158,plain,(
% 0.22/0.48    spl5_8 | ~spl5_18 | ~spl5_7 | spl5_16),
% 0.22/0.48    inference(avatar_split_clause,[],[f153,f140,f86,f155,f90])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    spl5_7 <=> v4_orders_2(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.48  fof(f140,plain,(
% 0.22/0.48    spl5_16 <=> v4_orders_2(g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.22/0.48  fof(f153,plain,(
% 0.22/0.48    ~v4_orders_2(sK2) | ~l1_orders_2(sK2) | v2_struct_0(sK2) | spl5_16),
% 0.22/0.48    inference(resolution,[],[f141,f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0] : (v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) | ~v4_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0] : (((v4_orders_2(X0) | ~v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) & (v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) | ~v4_orders_2(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : ((v4_orders_2(X0) <=> v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0] : ((v4_orders_2(X0) <=> v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => (v4_orders_2(X0) <=> v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l16_yellow_6)).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    ~v4_orders_2(g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))) | spl5_16),
% 0.22/0.48    inference(avatar_component_clause,[],[f140])).
% 0.22/0.48  fof(f152,plain,(
% 0.22/0.48    ~spl5_10 | spl5_17),
% 0.22/0.48    inference(avatar_split_clause,[],[f151,f148,f98])).
% 0.22/0.48  fof(f151,plain,(
% 0.22/0.48    ~l1_orders_2(sK0) | spl5_17),
% 0.22/0.48    inference(resolution,[],[f149,f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.22/0.48  fof(f149,plain,(
% 0.22/0.48    ~l1_struct_0(sK0) | spl5_17),
% 0.22/0.48    inference(avatar_component_clause,[],[f148])).
% 0.22/0.48  fof(f150,plain,(
% 0.22/0.48    spl5_11 | ~spl5_10 | ~spl5_9 | spl5_8 | ~spl5_5 | ~spl5_17 | spl5_15),
% 0.22/0.48    inference(avatar_split_clause,[],[f144,f136,f148,f78,f90,f94,f98,f102])).
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    spl5_15 <=> l1_orders_2(k3_waybel_2(sK0,sK1,sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.22/0.48  fof(f144,plain,(
% 0.22/0.48    ~l1_struct_0(sK0) | ~l1_waybel_0(sK2,sK0) | v2_struct_0(sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | spl5_15),
% 0.22/0.48    inference(resolution,[],[f143,f58])).
% 0.22/0.48  fof(f143,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_waybel_0(k3_waybel_2(sK0,sK1,sK2),X0) | ~l1_struct_0(X0)) ) | spl5_15),
% 0.22/0.48    inference(resolution,[],[f137,f43])).
% 0.22/0.48  fof(f137,plain,(
% 0.22/0.48    ~l1_orders_2(k3_waybel_2(sK0,sK1,sK2)) | spl5_15),
% 0.22/0.48    inference(avatar_component_clause,[],[f136])).
% 0.22/0.48  fof(f142,plain,(
% 0.22/0.48    spl5_1 | ~spl5_15 | spl5_2 | ~spl5_16 | ~spl5_13),
% 0.22/0.48    inference(avatar_split_clause,[],[f133,f126,f140,f68,f136,f65])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    spl5_2 <=> v4_orders_2(k3_waybel_2(sK0,sK1,sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    spl5_13 <=> g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(k3_waybel_2(sK0,sK1,sK2)),u1_orders_2(k3_waybel_2(sK0,sK1,sK2)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    ~v4_orders_2(g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))) | v4_orders_2(k3_waybel_2(sK0,sK1,sK2)) | ~l1_orders_2(k3_waybel_2(sK0,sK1,sK2)) | v2_struct_0(k3_waybel_2(sK0,sK1,sK2)) | ~spl5_13),
% 0.22/0.48    inference(superposition,[],[f46,f127])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(k3_waybel_2(sK0,sK1,sK2)),u1_orders_2(k3_waybel_2(sK0,sK1,sK2))) | ~spl5_13),
% 0.22/0.48    inference(avatar_component_clause,[],[f126])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X0] : (~v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) | v4_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    spl5_8 | spl5_13 | ~spl5_5 | ~spl5_12),
% 0.22/0.48    inference(avatar_split_clause,[],[f122,f119,f78,f126,f90])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    spl5_12 <=> ! [X0] : (~l1_waybel_0(X0,sK0) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_waybel_2(sK0,sK1,X0)),u1_orders_2(k3_waybel_2(sK0,sK1,X0))) | v2_struct_0(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(k3_waybel_2(sK0,sK1,sK2)),u1_orders_2(k3_waybel_2(sK0,sK1,sK2))) | v2_struct_0(sK2) | (~spl5_5 | ~spl5_12)),
% 0.22/0.48    inference(resolution,[],[f120,f79])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_waybel_0(X0,sK0) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_waybel_2(sK0,sK1,X0)),u1_orders_2(k3_waybel_2(sK0,sK1,X0))) | v2_struct_0(X0)) ) | ~spl5_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f119])).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    spl5_11 | ~spl5_10 | spl5_12 | ~spl5_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f115,f94,f119,f98,f102])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_waybel_0(X0,sK0) | v2_struct_0(X0) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_waybel_2(sK0,sK1,X0)),u1_orders_2(k3_waybel_2(sK0,sK1,X0))) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_9),
% 0.22/0.48    inference(resolution,[],[f109,f95])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f94])).
% 0.22/0.48  fof(f109,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(k3_waybel_2(X0,X1,X2)),u1_orders_2(k3_waybel_2(X0,X1,X2))) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f105,f58])).
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(k3_waybel_2(X0,X1,X2)),u1_orders_2(k3_waybel_2(X0,X1,X2))) | ~l1_waybel_0(k3_waybel_2(X0,X1,X2),X0) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f63,f56])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(k3_waybel_2(X0,X1,X2)),u1_orders_2(k3_waybel_2(X0,X1,X2))) | ~l1_waybel_0(k3_waybel_2(X0,X1,X2),X0) | ~v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(equality_resolution,[],[f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) | k3_waybel_2(X0,X1,X2) != X3 | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k3_waybel_2(X0,X1,X2) = X3 | (! [X5] : (k11_lattice3(X0,X1,X5) != k1_funct_1(u1_waybel_0(X0,X3),sK3(X0,X1,X2,X3)) | k1_funct_1(u1_waybel_0(X0,X2),sK3(X0,X1,X2,X3)) != X5 | ~m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X3))) | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) & ((! [X6] : ((k1_funct_1(u1_waybel_0(X0,X3),X6) = k11_lattice3(X0,X1,sK4(X0,X1,X2,X3,X6)) & k1_funct_1(u1_waybel_0(X0,X2),X6) = sK4(X0,X1,X2,X3,X6) & m1_subset_1(sK4(X0,X1,X2,X3,X6),u1_struct_0(X0))) | ~m1_subset_1(X6,u1_struct_0(X3))) & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) | k3_waybel_2(X0,X1,X2) != X3)) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f33,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ! [X3,X2,X1,X0] : (? [X4] : (! [X5] : (k1_funct_1(u1_waybel_0(X0,X3),X4) != k11_lattice3(X0,X1,X5) | k1_funct_1(u1_waybel_0(X0,X2),X4) != X5 | ~m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X3))) => (! [X5] : (k11_lattice3(X0,X1,X5) != k1_funct_1(u1_waybel_0(X0,X3),sK3(X0,X1,X2,X3)) | k1_funct_1(u1_waybel_0(X0,X2),sK3(X0,X1,X2,X3)) != X5 | ~m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X3))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ! [X6,X3,X2,X1,X0] : (? [X7] : (k1_funct_1(u1_waybel_0(X0,X3),X6) = k11_lattice3(X0,X1,X7) & k1_funct_1(u1_waybel_0(X0,X2),X6) = X7 & m1_subset_1(X7,u1_struct_0(X0))) => (k1_funct_1(u1_waybel_0(X0,X3),X6) = k11_lattice3(X0,X1,sK4(X0,X1,X2,X3,X6)) & k1_funct_1(u1_waybel_0(X0,X2),X6) = sK4(X0,X1,X2,X3,X6) & m1_subset_1(sK4(X0,X1,X2,X3,X6),u1_struct_0(X0))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k3_waybel_2(X0,X1,X2) = X3 | ? [X4] : (! [X5] : (k1_funct_1(u1_waybel_0(X0,X3),X4) != k11_lattice3(X0,X1,X5) | k1_funct_1(u1_waybel_0(X0,X2),X4) != X5 | ~m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X3))) | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) & ((! [X6] : (? [X7] : (k1_funct_1(u1_waybel_0(X0,X3),X6) = k11_lattice3(X0,X1,X7) & k1_funct_1(u1_waybel_0(X0,X2),X6) = X7 & m1_subset_1(X7,u1_struct_0(X0))) | ~m1_subset_1(X6,u1_struct_0(X3))) & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) | k3_waybel_2(X0,X1,X2) != X3)) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(rectify,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k3_waybel_2(X0,X1,X2) = X3 | ? [X4] : (! [X5] : (k1_funct_1(u1_waybel_0(X0,X3),X4) != k11_lattice3(X0,X1,X5) | k1_funct_1(u1_waybel_0(X0,X2),X4) != X5 | ~m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X3))) | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) & ((! [X4] : (? [X5] : (k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5) & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X3))) & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) | k3_waybel_2(X0,X1,X2) != X3)) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k3_waybel_2(X0,X1,X2) = X3 | (? [X4] : (! [X5] : (k1_funct_1(u1_waybel_0(X0,X3),X4) != k11_lattice3(X0,X1,X5) | k1_funct_1(u1_waybel_0(X0,X2),X4) != X5 | ~m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X3))) | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)))) & ((! [X4] : (? [X5] : (k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5) & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X3))) & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) | k3_waybel_2(X0,X1,X2) != X3)) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k3_waybel_2(X0,X1,X2) = X3 <=> (! [X4] : (? [X5] : (k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5) & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X3))) & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)))) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k3_waybel_2(X0,X1,X2) = X3 <=> (! [X4] : (? [X5] : (k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5) & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X3))) & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)))) | (~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0))) | (~l1_waybel_0(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((l1_waybel_0(X3,X0) & v6_waybel_0(X3,X0)) => (k3_waybel_2(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X3)) => ? [X5] : (k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5) & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5 & m1_subset_1(X5,u1_struct_0(X0)))) & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))))))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_waybel_2)).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    ~spl5_11),
% 0.22/0.48    inference(avatar_split_clause,[],[f35,f102])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ~v2_struct_0(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    (((~l1_waybel_0(k3_waybel_2(sK0,sK1,sK2),sK0) | ~v7_waybel_0(k3_waybel_2(sK0,sK1,sK2)) | ~v4_orders_2(k3_waybel_2(sK0,sK1,sK2)) | v2_struct_0(k3_waybel_2(sK0,sK1,sK2))) & l1_waybel_0(sK2,sK0) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f26,f25,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : ((~l1_waybel_0(k3_waybel_2(X0,X1,X2),X0) | ~v7_waybel_0(k3_waybel_2(X0,X1,X2)) | ~v4_orders_2(k3_waybel_2(X0,X1,X2)) | v2_struct_0(k3_waybel_2(X0,X1,X2))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~l1_waybel_0(k3_waybel_2(sK0,X1,X2),sK0) | ~v7_waybel_0(k3_waybel_2(sK0,X1,X2)) | ~v4_orders_2(k3_waybel_2(sK0,X1,X2)) | v2_struct_0(k3_waybel_2(sK0,X1,X2))) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ? [X1] : (? [X2] : ((~l1_waybel_0(k3_waybel_2(sK0,X1,X2),sK0) | ~v7_waybel_0(k3_waybel_2(sK0,X1,X2)) | ~v4_orders_2(k3_waybel_2(sK0,X1,X2)) | v2_struct_0(k3_waybel_2(sK0,X1,X2))) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~l1_waybel_0(k3_waybel_2(sK0,sK1,X2),sK0) | ~v7_waybel_0(k3_waybel_2(sK0,sK1,X2)) | ~v4_orders_2(k3_waybel_2(sK0,sK1,X2)) | v2_struct_0(k3_waybel_2(sK0,sK1,X2))) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ? [X2] : ((~l1_waybel_0(k3_waybel_2(sK0,sK1,X2),sK0) | ~v7_waybel_0(k3_waybel_2(sK0,sK1,X2)) | ~v4_orders_2(k3_waybel_2(sK0,sK1,X2)) | v2_struct_0(k3_waybel_2(sK0,sK1,X2))) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((~l1_waybel_0(k3_waybel_2(sK0,sK1,sK2),sK0) | ~v7_waybel_0(k3_waybel_2(sK0,sK1,sK2)) | ~v4_orders_2(k3_waybel_2(sK0,sK1,sK2)) | v2_struct_0(k3_waybel_2(sK0,sK1,sK2))) & l1_waybel_0(sK2,sK0) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : ((~l1_waybel_0(k3_waybel_2(X0,X1,X2),X0) | ~v7_waybel_0(k3_waybel_2(X0,X1,X2)) | ~v4_orders_2(k3_waybel_2(X0,X1,X2)) | v2_struct_0(k3_waybel_2(X0,X1,X2))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : ((~l1_waybel_0(k3_waybel_2(X0,X1,X2),X0) | ~v7_waybel_0(k3_waybel_2(X0,X1,X2)) | ~v4_orders_2(k3_waybel_2(X0,X1,X2)) | v2_struct_0(k3_waybel_2(X0,X1,X2))) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (l1_waybel_0(k3_waybel_2(X0,X1,X2),X0) & v7_waybel_0(k3_waybel_2(X0,X1,X2)) & v4_orders_2(k3_waybel_2(X0,X1,X2)) & ~v2_struct_0(k3_waybel_2(X0,X1,X2))))))),
% 0.22/0.48    inference(negated_conjecture,[],[f8])).
% 0.22/0.48  fof(f8,conjecture,(
% 0.22/0.48    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (l1_waybel_0(k3_waybel_2(X0,X1,X2),X0) & v7_waybel_0(k3_waybel_2(X0,X1,X2)) & v4_orders_2(k3_waybel_2(X0,X1,X2)) & ~v2_struct_0(k3_waybel_2(X0,X1,X2))))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_9)).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    spl5_10),
% 0.22/0.48    inference(avatar_split_clause,[],[f36,f98])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    l1_orders_2(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    spl5_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f37,f94])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    ~spl5_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f38,f90])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ~v2_struct_0(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    spl5_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f39,f86])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    v4_orders_2(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    spl5_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f40,f82])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    v7_waybel_0(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    spl5_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f41,f78])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    l1_waybel_0(sK2,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f42,f74,f71,f68,f65])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ~l1_waybel_0(k3_waybel_2(sK0,sK1,sK2),sK0) | ~v7_waybel_0(k3_waybel_2(sK0,sK1,sK2)) | ~v4_orders_2(k3_waybel_2(sK0,sK1,sK2)) | v2_struct_0(k3_waybel_2(sK0,sK1,sK2))),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (27932)------------------------------
% 0.22/0.48  % (27932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (27932)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (27932)Memory used [KB]: 10746
% 0.22/0.48  % (27932)Time elapsed: 0.067 s
% 0.22/0.48  % (27932)------------------------------
% 0.22/0.48  % (27932)------------------------------
% 0.22/0.49  % (27925)Success in time 0.124 s
%------------------------------------------------------------------------------
