%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:49 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 294 expanded)
%              Number of leaves         :   27 (  97 expanded)
%              Depth                    :   18
%              Number of atoms          :  643 (1498 expanded)
%              Number of equality atoms :   37 ( 126 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f353,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f71,f81,f86,f91,f96,f110,f119,f126,f131,f267,f281,f324,f333,f337,f339,f348,f352])).

fof(f352,plain,
    ( spl6_1
    | spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_20 ),
    inference(avatar_contradiction_clause,[],[f351])).

fof(f351,plain,
    ( $false
    | spl6_1
    | spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f350,f60])).

fof(f60,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl6_1
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f350,plain,
    ( v2_struct_0(sK2)
    | spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f349,f85])).

fof(f85,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl6_6
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f349,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_20 ),
    inference(resolution,[],[f315,f172])).

fof(f172,plain,
    ( ! [X1] :
        ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,X1))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1) )
    | spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f170,f65])).

fof(f65,plain,
    ( ~ v2_struct_0(sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl6_2
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f170,plain,
    ( ! [X1] :
        ( v2_struct_0(sK1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ v2_struct_0(k2_tsep_1(sK0,sK1,X1)) )
    | spl6_3
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(resolution,[],[f168,f95])).

fof(f95,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl6_8
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ v2_struct_0(k2_tsep_1(sK0,X0,X1)) )
    | spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f103,f80])).

fof(f80,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl6_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ v2_struct_0(k2_tsep_1(sK0,X0,X1)) )
    | spl6_3 ),
    inference(resolution,[],[f70,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

% (8733)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% (8746)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% (8750)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (8748)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% (8749)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f70,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl6_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f315,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f313])).

fof(f313,plain,
    ( spl6_20
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f348,plain,
    ( spl6_1
    | spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | spl6_23 ),
    inference(avatar_contradiction_clause,[],[f347])).

fof(f347,plain,
    ( $false
    | spl6_1
    | spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | spl6_23 ),
    inference(subsumption_resolution,[],[f346,f65])).

fof(f346,plain,
    ( v2_struct_0(sK1)
    | spl6_1
    | spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | spl6_23 ),
    inference(subsumption_resolution,[],[f345,f85])).

fof(f345,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK1)
    | spl6_1
    | spl6_3
    | ~ spl6_5
    | ~ spl6_8
    | spl6_23 ),
    inference(subsumption_resolution,[],[f344,f60])).

fof(f344,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK1)
    | spl6_3
    | ~ spl6_5
    | ~ spl6_8
    | spl6_23 ),
    inference(subsumption_resolution,[],[f343,f95])).

fof(f343,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK1)
    | spl6_3
    | ~ spl6_5
    | spl6_23 ),
    inference(subsumption_resolution,[],[f342,f80])).

fof(f342,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK1)
    | spl6_3
    | ~ spl6_5
    | spl6_23 ),
    inference(resolution,[],[f340,f223])).

fof(f223,plain,
    ( ! [X4,X5] :
        ( m1_pre_topc(k2_tsep_1(sK0,X4,X5),sK0)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X4) )
    | spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f105,f80])).

fof(f105,plain,
    ( ! [X4,X5] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | m1_pre_topc(k2_tsep_1(sK0,X4,X5),sK0) )
    | spl6_3 ),
    inference(resolution,[],[f70,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f340,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
        | ~ l1_pre_topc(X0) )
    | spl6_23 ),
    inference(resolution,[],[f332,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f332,plain,
    ( ~ l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | spl6_23 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl6_23
  <=> l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f339,plain,
    ( spl6_12
    | ~ spl6_19
    | spl6_22 ),
    inference(avatar_contradiction_clause,[],[f338])).

fof(f338,plain,
    ( $false
    | spl6_12
    | ~ spl6_19
    | spl6_22 ),
    inference(subsumption_resolution,[],[f335,f280])).

fof(f280,plain,
    ( m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl6_19
  <=> m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f335,plain,
    ( ~ m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | spl6_12
    | spl6_22 ),
    inference(resolution,[],[f323,f186])).

fof(f186,plain,
    ( ! [X5] :
        ( v1_xboole_0(k3_xboole_0(X5,u1_struct_0(sK2)))
        | ~ m1_subset_1(sK3,k3_xboole_0(X5,u1_struct_0(sK2))) )
    | spl6_12 ),
    inference(resolution,[],[f151,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f151,plain,
    ( ! [X1] : ~ r2_hidden(sK3,k3_xboole_0(X1,u1_struct_0(sK2)))
    | spl6_12 ),
    inference(resolution,[],[f133,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f133,plain,
    ( ! [X1] : ~ sP5(sK3,u1_struct_0(sK2),X1)
    | spl6_12 ),
    inference(resolution,[],[f125,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f125,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl6_12
  <=> r2_hidden(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f323,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | spl6_22 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl6_22
  <=> v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f337,plain,
    ( spl6_13
    | ~ spl6_19
    | spl6_22 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | spl6_13
    | ~ spl6_19
    | spl6_22 ),
    inference(subsumption_resolution,[],[f334,f280])).

fof(f334,plain,
    ( ~ m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | spl6_13
    | spl6_22 ),
    inference(resolution,[],[f323,f191])).

fof(f191,plain,
    ( ! [X5] :
        ( v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),X5))
        | ~ m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),X5)) )
    | spl6_13 ),
    inference(resolution,[],[f154,f41])).

fof(f154,plain,
    ( ! [X1] : ~ r2_hidden(sK3,k3_xboole_0(u1_struct_0(sK1),X1))
    | spl6_13 ),
    inference(resolution,[],[f135,f55])).

fof(f135,plain,
    ( ! [X0] : ~ sP5(sK3,X0,u1_struct_0(sK1))
    | spl6_13 ),
    inference(resolution,[],[f130,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f130,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK1))
    | spl6_13 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl6_13
  <=> r2_hidden(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f333,plain,
    ( ~ spl6_23
    | spl6_21 ),
    inference(avatar_split_clause,[],[f328,f317,f330])).

fof(f317,plain,
    ( spl6_21
  <=> l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f328,plain,
    ( ~ l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | spl6_21 ),
    inference(resolution,[],[f319,f35])).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f319,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | spl6_21 ),
    inference(avatar_component_clause,[],[f317])).

fof(f324,plain,
    ( spl6_20
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f276,f264,f321,f317,f313])).

fof(f264,plain,
    ( spl6_18
  <=> u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f276,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl6_18 ),
    inference(superposition,[],[f37,f266])).

fof(f266,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f264])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f281,plain,
    ( spl6_19
    | ~ spl6_9
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f272,f264,f107,f278])).

fof(f107,plain,
    ( spl6_9
  <=> m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f272,plain,
    ( m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl6_9
    | ~ spl6_18 ),
    inference(superposition,[],[f109,f266])).

fof(f109,plain,
    ( m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f267,plain,
    ( spl6_18
    | spl6_1
    | spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f258,f93,f88,f83,f78,f68,f63,f58,f264])).

fof(f88,plain,
    ( spl6_7
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f258,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl6_1
    | spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f257,f95])).

fof(f257,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl6_1
    | spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(subsumption_resolution,[],[f256,f65])).

fof(f256,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl6_1
    | spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(subsumption_resolution,[],[f255,f85])).

fof(f255,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl6_1
    | spl6_3
    | ~ spl6_5
    | spl6_7 ),
    inference(subsumption_resolution,[],[f254,f60])).

fof(f254,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl6_3
    | ~ spl6_5
    | spl6_7 ),
    inference(resolution,[],[f249,f90])).

fof(f90,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f249,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(X0,X1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1)) )
    | spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f208,f223])).

fof(f208,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
        | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1)) )
    | spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f207,f168])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,X1)
        | v2_struct_0(k2_tsep_1(sK0,X0,X1))
        | ~ m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
        | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1)) )
    | spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f206,f70])).

fof(f206,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,X1)
        | v2_struct_0(k2_tsep_1(sK0,X0,X1))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
        | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1)) )
    | spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f205,f80])).

fof(f205,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | r1_tsep_1(X0,X1)
        | v2_struct_0(k2_tsep_1(sK0,X0,X1))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
        | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1)) )
    | spl6_3
    | ~ spl6_5 ),
    inference(duplicate_literal_removal,[],[f204])).

fof(f204,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | r1_tsep_1(X0,X1)
        | v2_struct_0(k2_tsep_1(sK0,X0,X1))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
        | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1)) )
    | spl6_3
    | ~ spl6_5 ),
    inference(resolution,[],[f203,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | r1_tsep_1(X1,X2)
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | r1_tsep_1(X1,X2)
      | v2_struct_0(X3)
      | ~ v1_pre_topc(X3)
      | ~ m1_pre_topc(X3,X0)
      | u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k2_tsep_1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).

fof(f203,plain,
    ( ! [X2,X3] :
        ( v1_pre_topc(k2_tsep_1(sK0,X2,X3))
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X2) )
    | spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f104,f80])).

fof(f104,plain,
    ( ! [X2,X3] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | v1_pre_topc(k2_tsep_1(sK0,X2,X3)) )
    | spl6_3 ),
    inference(resolution,[],[f70,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v1_pre_topc(k2_tsep_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f131,plain,
    ( ~ spl6_13
    | spl6_11 ),
    inference(avatar_split_clause,[],[f121,f116,f128])).

fof(f116,plain,
    ( spl6_11
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f121,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK1))
    | spl6_11 ),
    inference(resolution,[],[f118,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f118,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f126,plain,
    ( ~ spl6_12
    | spl6_10 ),
    inference(avatar_split_clause,[],[f120,f112,f123])).

fof(f112,plain,
    ( spl6_10
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f120,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | spl6_10 ),
    inference(resolution,[],[f114,f40])).

fof(f114,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f112])).

fof(f119,plain,
    ( ~ spl6_10
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f53,f116,f112])).

fof(f53,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4] :
      ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | sK3 != X4 ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK1))
      | sK3 != X5
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | sK3 != X4 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X5] :
                            ( X3 = X5
                            & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                   => ( ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X2)) )
                      & ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tmap_1)).

fof(f110,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f26,f107])).

fof(f26,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f13])).

fof(f96,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f31,f93])).

fof(f31,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f91,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f29,f88])).

fof(f29,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f86,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f28,f83])).

fof(f28,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f81,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f34,f78])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f71,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f32,f68])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f66,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f30,f63])).

fof(f30,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f27,f58])).

fof(f27,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:33:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (8736)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.52  % (8734)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.52  % (8747)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.52  % (8742)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.52  % (8739)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.34/0.54  % (8744)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.55  % (8737)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.60/0.56  % (8751)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.60/0.56  % (8732)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.60/0.56  % (8735)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.60/0.56  % (8752)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.60/0.57  % (8752)Refutation not found, incomplete strategy% (8752)------------------------------
% 1.60/0.57  % (8752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.57  % (8752)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.57  
% 1.60/0.57  % (8752)Memory used [KB]: 10618
% 1.60/0.57  % (8752)Time elapsed: 0.133 s
% 1.60/0.57  % (8752)------------------------------
% 1.60/0.57  % (8752)------------------------------
% 1.60/0.57  % (8745)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.60/0.57  % (8738)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 1.60/0.57  % (8735)Refutation found. Thanks to Tanya!
% 1.60/0.57  % SZS status Theorem for theBenchmark
% 1.60/0.57  % SZS output start Proof for theBenchmark
% 1.60/0.57  fof(f353,plain,(
% 1.60/0.57    $false),
% 1.60/0.57    inference(avatar_sat_refutation,[],[f61,f66,f71,f81,f86,f91,f96,f110,f119,f126,f131,f267,f281,f324,f333,f337,f339,f348,f352])).
% 1.60/0.57  fof(f352,plain,(
% 1.60/0.57    spl6_1 | spl6_2 | spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_8 | ~spl6_20),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f351])).
% 1.60/0.57  fof(f351,plain,(
% 1.60/0.57    $false | (spl6_1 | spl6_2 | spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_8 | ~spl6_20)),
% 1.60/0.57    inference(subsumption_resolution,[],[f350,f60])).
% 1.60/0.57  fof(f60,plain,(
% 1.60/0.57    ~v2_struct_0(sK2) | spl6_1),
% 1.60/0.57    inference(avatar_component_clause,[],[f58])).
% 1.60/0.57  fof(f58,plain,(
% 1.60/0.57    spl6_1 <=> v2_struct_0(sK2)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.60/0.57  fof(f350,plain,(
% 1.60/0.57    v2_struct_0(sK2) | (spl6_2 | spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_8 | ~spl6_20)),
% 1.60/0.57    inference(subsumption_resolution,[],[f349,f85])).
% 1.60/0.57  fof(f85,plain,(
% 1.60/0.57    m1_pre_topc(sK2,sK0) | ~spl6_6),
% 1.60/0.57    inference(avatar_component_clause,[],[f83])).
% 1.60/0.57  fof(f83,plain,(
% 1.60/0.57    spl6_6 <=> m1_pre_topc(sK2,sK0)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.60/0.57  fof(f349,plain,(
% 1.60/0.57    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | (spl6_2 | spl6_3 | ~spl6_5 | ~spl6_8 | ~spl6_20)),
% 1.60/0.57    inference(resolution,[],[f315,f172])).
% 1.60/0.57  fof(f172,plain,(
% 1.60/0.57    ( ! [X1] : (~v2_struct_0(k2_tsep_1(sK0,sK1,X1)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1)) ) | (spl6_2 | spl6_3 | ~spl6_5 | ~spl6_8)),
% 1.60/0.57    inference(subsumption_resolution,[],[f170,f65])).
% 1.60/0.57  fof(f65,plain,(
% 1.60/0.57    ~v2_struct_0(sK1) | spl6_2),
% 1.60/0.57    inference(avatar_component_clause,[],[f63])).
% 1.60/0.57  fof(f63,plain,(
% 1.60/0.57    spl6_2 <=> v2_struct_0(sK1)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.60/0.57  fof(f170,plain,(
% 1.60/0.57    ( ! [X1] : (v2_struct_0(sK1) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~v2_struct_0(k2_tsep_1(sK0,sK1,X1))) ) | (spl6_3 | ~spl6_5 | ~spl6_8)),
% 1.60/0.57    inference(resolution,[],[f168,f95])).
% 1.60/0.57  fof(f95,plain,(
% 1.60/0.57    m1_pre_topc(sK1,sK0) | ~spl6_8),
% 1.60/0.57    inference(avatar_component_clause,[],[f93])).
% 1.60/0.57  fof(f93,plain,(
% 1.60/0.57    spl6_8 <=> m1_pre_topc(sK1,sK0)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.60/0.57  fof(f168,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~v2_struct_0(k2_tsep_1(sK0,X0,X1))) ) | (spl6_3 | ~spl6_5)),
% 1.60/0.57    inference(subsumption_resolution,[],[f103,f80])).
% 1.60/0.57  fof(f80,plain,(
% 1.60/0.57    l1_pre_topc(sK0) | ~spl6_5),
% 1.60/0.57    inference(avatar_component_clause,[],[f78])).
% 1.60/0.57  fof(f78,plain,(
% 1.60/0.57    spl6_5 <=> l1_pre_topc(sK0)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.60/0.57  fof(f103,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~v2_struct_0(k2_tsep_1(sK0,X0,X1))) ) | spl6_3),
% 1.60/0.57    inference(resolution,[],[f70,f42])).
% 1.60/0.57  fof(f42,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~v2_struct_0(k2_tsep_1(X0,X1,X2))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f24])).
% 1.60/0.57  fof(f24,plain,(
% 1.60/0.57    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.60/0.57    inference(flattening,[],[f23])).
% 1.60/0.58  % (8733)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.60/0.58  % (8746)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 1.60/0.58  % (8750)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.60/0.58  % (8748)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.60/0.59  % (8749)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.60/0.59  fof(f23,plain,(
% 1.60/0.59    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.60/0.59    inference(ennf_transformation,[],[f8])).
% 1.60/0.59  fof(f8,axiom,(
% 1.60/0.59    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 1.60/0.59  fof(f70,plain,(
% 1.60/0.59    ~v2_struct_0(sK0) | spl6_3),
% 1.60/0.59    inference(avatar_component_clause,[],[f68])).
% 1.60/0.59  fof(f68,plain,(
% 1.60/0.59    spl6_3 <=> v2_struct_0(sK0)),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.60/0.59  fof(f315,plain,(
% 1.60/0.59    v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~spl6_20),
% 1.60/0.59    inference(avatar_component_clause,[],[f313])).
% 1.60/0.59  fof(f313,plain,(
% 1.60/0.59    spl6_20 <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2))),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.60/0.59  fof(f348,plain,(
% 1.60/0.59    spl6_1 | spl6_2 | spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_8 | spl6_23),
% 1.60/0.59    inference(avatar_contradiction_clause,[],[f347])).
% 1.60/0.59  fof(f347,plain,(
% 1.60/0.59    $false | (spl6_1 | spl6_2 | spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_8 | spl6_23)),
% 1.60/0.59    inference(subsumption_resolution,[],[f346,f65])).
% 1.60/0.59  fof(f346,plain,(
% 1.60/0.59    v2_struct_0(sK1) | (spl6_1 | spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_8 | spl6_23)),
% 1.60/0.59    inference(subsumption_resolution,[],[f345,f85])).
% 1.60/0.59  fof(f345,plain,(
% 1.60/0.59    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK1) | (spl6_1 | spl6_3 | ~spl6_5 | ~spl6_8 | spl6_23)),
% 1.60/0.59    inference(subsumption_resolution,[],[f344,f60])).
% 1.60/0.59  fof(f344,plain,(
% 1.60/0.59    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK1) | (spl6_3 | ~spl6_5 | ~spl6_8 | spl6_23)),
% 1.60/0.59    inference(subsumption_resolution,[],[f343,f95])).
% 1.60/0.59  fof(f343,plain,(
% 1.60/0.59    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK1) | (spl6_3 | ~spl6_5 | spl6_23)),
% 1.60/0.59    inference(subsumption_resolution,[],[f342,f80])).
% 1.60/0.59  fof(f342,plain,(
% 1.60/0.59    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK1) | (spl6_3 | ~spl6_5 | spl6_23)),
% 1.60/0.59    inference(resolution,[],[f340,f223])).
% 1.60/0.59  fof(f223,plain,(
% 1.60/0.59    ( ! [X4,X5] : (m1_pre_topc(k2_tsep_1(sK0,X4,X5),sK0) | ~m1_pre_topc(X4,sK0) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X4)) ) | (spl6_3 | ~spl6_5)),
% 1.60/0.59    inference(subsumption_resolution,[],[f105,f80])).
% 1.60/0.59  fof(f105,plain,(
% 1.60/0.59    ( ! [X4,X5] : (~l1_pre_topc(sK0) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK0) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK0) | m1_pre_topc(k2_tsep_1(sK0,X4,X5),sK0)) ) | spl6_3),
% 1.60/0.59    inference(resolution,[],[f70,f44])).
% 1.60/0.59  fof(f44,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f24])).
% 1.60/0.59  fof(f340,plain,(
% 1.60/0.59    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) | ~l1_pre_topc(X0)) ) | spl6_23),
% 1.60/0.59    inference(resolution,[],[f332,f36])).
% 1.60/0.59  fof(f36,plain,(
% 1.60/0.59    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f15])).
% 1.60/0.59  fof(f15,plain,(
% 1.60/0.59    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.60/0.59    inference(ennf_transformation,[],[f5])).
% 1.60/0.59  fof(f5,axiom,(
% 1.60/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.60/0.59  fof(f332,plain,(
% 1.60/0.59    ~l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | spl6_23),
% 1.60/0.59    inference(avatar_component_clause,[],[f330])).
% 1.60/0.59  fof(f330,plain,(
% 1.60/0.59    spl6_23 <=> l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.60/0.59  fof(f339,plain,(
% 1.60/0.59    spl6_12 | ~spl6_19 | spl6_22),
% 1.60/0.59    inference(avatar_contradiction_clause,[],[f338])).
% 1.60/0.59  fof(f338,plain,(
% 1.60/0.59    $false | (spl6_12 | ~spl6_19 | spl6_22)),
% 1.60/0.59    inference(subsumption_resolution,[],[f335,f280])).
% 1.60/0.59  fof(f280,plain,(
% 1.60/0.59    m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~spl6_19),
% 1.60/0.59    inference(avatar_component_clause,[],[f278])).
% 1.60/0.59  fof(f278,plain,(
% 1.60/0.59    spl6_19 <=> m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.60/0.59  fof(f335,plain,(
% 1.60/0.59    ~m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | (spl6_12 | spl6_22)),
% 1.60/0.59    inference(resolution,[],[f323,f186])).
% 1.60/0.59  fof(f186,plain,(
% 1.60/0.59    ( ! [X5] : (v1_xboole_0(k3_xboole_0(X5,u1_struct_0(sK2))) | ~m1_subset_1(sK3,k3_xboole_0(X5,u1_struct_0(sK2)))) ) | spl6_12),
% 1.60/0.59    inference(resolution,[],[f151,f41])).
% 1.60/0.59  fof(f41,plain,(
% 1.60/0.59    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f22])).
% 1.60/0.59  fof(f22,plain,(
% 1.60/0.59    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.60/0.59    inference(flattening,[],[f21])).
% 1.60/0.59  fof(f21,plain,(
% 1.60/0.59    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.60/0.59    inference(ennf_transformation,[],[f3])).
% 1.60/0.59  fof(f3,axiom,(
% 1.60/0.59    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.60/0.59  fof(f151,plain,(
% 1.60/0.59    ( ! [X1] : (~r2_hidden(sK3,k3_xboole_0(X1,u1_struct_0(sK2)))) ) | spl6_12),
% 1.60/0.59    inference(resolution,[],[f133,f55])).
% 1.60/0.59  fof(f55,plain,(
% 1.60/0.59    ( ! [X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 1.60/0.59    inference(equality_resolution,[],[f49])).
% 1.60/0.59  fof(f49,plain,(
% 1.60/0.59    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.60/0.59    inference(cnf_transformation,[],[f1])).
% 1.60/0.59  fof(f1,axiom,(
% 1.60/0.59    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.60/0.59  fof(f133,plain,(
% 1.60/0.59    ( ! [X1] : (~sP5(sK3,u1_struct_0(sK2),X1)) ) | spl6_12),
% 1.60/0.59    inference(resolution,[],[f125,f47])).
% 1.60/0.59  fof(f47,plain,(
% 1.60/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~sP5(X3,X1,X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f1])).
% 1.60/0.59  fof(f125,plain,(
% 1.60/0.59    ~r2_hidden(sK3,u1_struct_0(sK2)) | spl6_12),
% 1.60/0.59    inference(avatar_component_clause,[],[f123])).
% 1.60/0.59  fof(f123,plain,(
% 1.60/0.59    spl6_12 <=> r2_hidden(sK3,u1_struct_0(sK2))),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.60/0.59  fof(f323,plain,(
% 1.60/0.59    ~v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | spl6_22),
% 1.60/0.59    inference(avatar_component_clause,[],[f321])).
% 1.60/0.59  fof(f321,plain,(
% 1.60/0.59    spl6_22 <=> v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.60/0.59  fof(f337,plain,(
% 1.60/0.59    spl6_13 | ~spl6_19 | spl6_22),
% 1.60/0.59    inference(avatar_contradiction_clause,[],[f336])).
% 1.60/0.59  fof(f336,plain,(
% 1.60/0.59    $false | (spl6_13 | ~spl6_19 | spl6_22)),
% 1.60/0.59    inference(subsumption_resolution,[],[f334,f280])).
% 1.60/0.59  fof(f334,plain,(
% 1.60/0.59    ~m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | (spl6_13 | spl6_22)),
% 1.60/0.59    inference(resolution,[],[f323,f191])).
% 1.60/0.59  fof(f191,plain,(
% 1.60/0.59    ( ! [X5] : (v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),X5)) | ~m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),X5))) ) | spl6_13),
% 1.60/0.59    inference(resolution,[],[f154,f41])).
% 1.60/0.59  fof(f154,plain,(
% 1.60/0.59    ( ! [X1] : (~r2_hidden(sK3,k3_xboole_0(u1_struct_0(sK1),X1))) ) | spl6_13),
% 1.60/0.59    inference(resolution,[],[f135,f55])).
% 1.60/0.59  fof(f135,plain,(
% 1.60/0.59    ( ! [X0] : (~sP5(sK3,X0,u1_struct_0(sK1))) ) | spl6_13),
% 1.60/0.59    inference(resolution,[],[f130,f46])).
% 1.60/0.59  fof(f46,plain,(
% 1.60/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~sP5(X3,X1,X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f1])).
% 1.60/0.59  fof(f130,plain,(
% 1.60/0.59    ~r2_hidden(sK3,u1_struct_0(sK1)) | spl6_13),
% 1.60/0.59    inference(avatar_component_clause,[],[f128])).
% 1.60/0.59  fof(f128,plain,(
% 1.60/0.59    spl6_13 <=> r2_hidden(sK3,u1_struct_0(sK1))),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.60/0.59  fof(f333,plain,(
% 1.60/0.59    ~spl6_23 | spl6_21),
% 1.60/0.59    inference(avatar_split_clause,[],[f328,f317,f330])).
% 1.60/0.59  fof(f317,plain,(
% 1.60/0.59    spl6_21 <=> l1_struct_0(k2_tsep_1(sK0,sK1,sK2))),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.60/0.59  fof(f328,plain,(
% 1.60/0.59    ~l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | spl6_21),
% 1.60/0.59    inference(resolution,[],[f319,f35])).
% 1.60/0.59  fof(f35,plain,(
% 1.60/0.59    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f14])).
% 1.60/0.59  fof(f14,plain,(
% 1.60/0.59    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.60/0.59    inference(ennf_transformation,[],[f4])).
% 1.60/0.59  fof(f4,axiom,(
% 1.60/0.59    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.60/0.59  fof(f319,plain,(
% 1.60/0.59    ~l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | spl6_21),
% 1.60/0.59    inference(avatar_component_clause,[],[f317])).
% 1.60/0.59  fof(f324,plain,(
% 1.60/0.59    spl6_20 | ~spl6_21 | ~spl6_22 | ~spl6_18),
% 1.60/0.59    inference(avatar_split_clause,[],[f276,f264,f321,f317,f313])).
% 1.60/0.59  fof(f264,plain,(
% 1.60/0.59    spl6_18 <=> u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.60/0.59  fof(f276,plain,(
% 1.60/0.59    ~v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~spl6_18),
% 1.60/0.59    inference(superposition,[],[f37,f266])).
% 1.60/0.59  fof(f266,plain,(
% 1.60/0.59    u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | ~spl6_18),
% 1.60/0.59    inference(avatar_component_clause,[],[f264])).
% 1.60/0.59  fof(f37,plain,(
% 1.60/0.59    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f17])).
% 1.60/0.59  fof(f17,plain,(
% 1.60/0.59    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.60/0.59    inference(flattening,[],[f16])).
% 1.60/0.59  fof(f16,plain,(
% 1.60/0.59    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.60/0.59    inference(ennf_transformation,[],[f6])).
% 1.60/0.59  fof(f6,axiom,(
% 1.60/0.59    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.60/0.59  fof(f281,plain,(
% 1.60/0.59    spl6_19 | ~spl6_9 | ~spl6_18),
% 1.60/0.59    inference(avatar_split_clause,[],[f272,f264,f107,f278])).
% 1.60/0.59  fof(f107,plain,(
% 1.60/0.59    spl6_9 <=> m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.60/0.59  fof(f272,plain,(
% 1.60/0.59    m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | (~spl6_9 | ~spl6_18)),
% 1.60/0.59    inference(superposition,[],[f109,f266])).
% 1.60/0.59  fof(f109,plain,(
% 1.60/0.59    m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) | ~spl6_9),
% 1.60/0.59    inference(avatar_component_clause,[],[f107])).
% 1.60/0.59  fof(f267,plain,(
% 1.60/0.59    spl6_18 | spl6_1 | spl6_2 | spl6_3 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_8),
% 1.60/0.59    inference(avatar_split_clause,[],[f258,f93,f88,f83,f78,f68,f63,f58,f264])).
% 1.60/0.59  fof(f88,plain,(
% 1.60/0.59    spl6_7 <=> r1_tsep_1(sK1,sK2)),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.60/0.59  fof(f258,plain,(
% 1.60/0.59    u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | (spl6_1 | spl6_2 | spl6_3 | ~spl6_5 | ~spl6_6 | spl6_7 | ~spl6_8)),
% 1.60/0.59    inference(subsumption_resolution,[],[f257,f95])).
% 1.60/0.59  fof(f257,plain,(
% 1.60/0.59    ~m1_pre_topc(sK1,sK0) | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | (spl6_1 | spl6_2 | spl6_3 | ~spl6_5 | ~spl6_6 | spl6_7)),
% 1.60/0.59    inference(subsumption_resolution,[],[f256,f65])).
% 1.60/0.59  fof(f256,plain,(
% 1.60/0.59    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | (spl6_1 | spl6_3 | ~spl6_5 | ~spl6_6 | spl6_7)),
% 1.60/0.59    inference(subsumption_resolution,[],[f255,f85])).
% 1.60/0.59  fof(f255,plain,(
% 1.60/0.59    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | (spl6_1 | spl6_3 | ~spl6_5 | spl6_7)),
% 1.60/0.59    inference(subsumption_resolution,[],[f254,f60])).
% 1.60/0.59  fof(f254,plain,(
% 1.60/0.59    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | (spl6_3 | ~spl6_5 | spl6_7)),
% 1.60/0.59    inference(resolution,[],[f249,f90])).
% 1.60/0.59  fof(f90,plain,(
% 1.60/0.59    ~r1_tsep_1(sK1,sK2) | spl6_7),
% 1.60/0.59    inference(avatar_component_clause,[],[f88])).
% 1.60/0.59  fof(f249,plain,(
% 1.60/0.59    ( ! [X0,X1] : (r1_tsep_1(X0,X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1))) ) | (spl6_3 | ~spl6_5)),
% 1.60/0.59    inference(subsumption_resolution,[],[f208,f223])).
% 1.60/0.59  fof(f208,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,X1) | ~m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0) | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1))) ) | (spl6_3 | ~spl6_5)),
% 1.60/0.59    inference(subsumption_resolution,[],[f207,f168])).
% 1.60/0.59  fof(f207,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,X1) | v2_struct_0(k2_tsep_1(sK0,X0,X1)) | ~m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0) | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1))) ) | (spl6_3 | ~spl6_5)),
% 1.60/0.59    inference(subsumption_resolution,[],[f206,f70])).
% 1.60/0.59  fof(f206,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,X1) | v2_struct_0(k2_tsep_1(sK0,X0,X1)) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0) | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1))) ) | (spl6_3 | ~spl6_5)),
% 1.60/0.59    inference(subsumption_resolution,[],[f205,f80])).
% 1.60/0.59  fof(f205,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | r1_tsep_1(X0,X1) | v2_struct_0(k2_tsep_1(sK0,X0,X1)) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0) | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1))) ) | (spl6_3 | ~spl6_5)),
% 1.60/0.59    inference(duplicate_literal_removal,[],[f204])).
% 1.60/0.59  fof(f204,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | r1_tsep_1(X0,X1) | v2_struct_0(k2_tsep_1(sK0,X0,X1)) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0) | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1))) ) | (spl6_3 | ~spl6_5)),
% 1.60/0.59    inference(resolution,[],[f203,f54])).
% 1.60/0.59  fof(f54,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | r1_tsep_1(X1,X2) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | v2_struct_0(X0) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))) )),
% 1.60/0.59    inference(equality_resolution,[],[f39])).
% 1.60/0.59  fof(f39,plain,(
% 1.60/0.59    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | r1_tsep_1(X1,X2) | v2_struct_0(X3) | ~v1_pre_topc(X3) | ~m1_pre_topc(X3,X0) | u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3) )),
% 1.60/0.59    inference(cnf_transformation,[],[f19])).
% 1.60/0.59  fof(f19,plain,(
% 1.60/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.60/0.59    inference(flattening,[],[f18])).
% 1.60/0.59  fof(f18,plain,(
% 1.60/0.59    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.60/0.59    inference(ennf_transformation,[],[f7])).
% 1.60/0.59  fof(f7,axiom,(
% 1.60/0.59    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))))))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).
% 1.60/0.59  fof(f203,plain,(
% 1.60/0.59    ( ! [X2,X3] : (v1_pre_topc(k2_tsep_1(sK0,X2,X3)) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X2)) ) | (spl6_3 | ~spl6_5)),
% 1.60/0.59    inference(subsumption_resolution,[],[f104,f80])).
% 1.60/0.59  fof(f104,plain,(
% 1.60/0.59    ( ! [X2,X3] : (~l1_pre_topc(sK0) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK0) | v1_pre_topc(k2_tsep_1(sK0,X2,X3))) ) | spl6_3),
% 1.60/0.59    inference(resolution,[],[f70,f43])).
% 1.60/0.59  fof(f43,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v1_pre_topc(k2_tsep_1(X0,X1,X2))) )),
% 1.60/0.59    inference(cnf_transformation,[],[f24])).
% 1.60/0.59  fof(f131,plain,(
% 1.60/0.59    ~spl6_13 | spl6_11),
% 1.60/0.59    inference(avatar_split_clause,[],[f121,f116,f128])).
% 1.60/0.59  fof(f116,plain,(
% 1.60/0.59    spl6_11 <=> m1_subset_1(sK3,u1_struct_0(sK1))),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.60/0.59  fof(f121,plain,(
% 1.60/0.59    ~r2_hidden(sK3,u1_struct_0(sK1)) | spl6_11),
% 1.60/0.59    inference(resolution,[],[f118,f40])).
% 1.60/0.59  fof(f40,plain,(
% 1.60/0.59    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f20])).
% 1.60/0.59  fof(f20,plain,(
% 1.60/0.59    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.60/0.59    inference(ennf_transformation,[],[f2])).
% 1.60/0.59  fof(f2,axiom,(
% 1.60/0.59    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.60/0.59  fof(f118,plain,(
% 1.60/0.59    ~m1_subset_1(sK3,u1_struct_0(sK1)) | spl6_11),
% 1.60/0.59    inference(avatar_component_clause,[],[f116])).
% 1.60/0.59  fof(f126,plain,(
% 1.60/0.59    ~spl6_12 | spl6_10),
% 1.60/0.59    inference(avatar_split_clause,[],[f120,f112,f123])).
% 1.60/0.59  fof(f112,plain,(
% 1.60/0.59    spl6_10 <=> m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.60/0.59  fof(f120,plain,(
% 1.60/0.59    ~r2_hidden(sK3,u1_struct_0(sK2)) | spl6_10),
% 1.60/0.59    inference(resolution,[],[f114,f40])).
% 1.60/0.59  fof(f114,plain,(
% 1.60/0.59    ~m1_subset_1(sK3,u1_struct_0(sK2)) | spl6_10),
% 1.60/0.59    inference(avatar_component_clause,[],[f112])).
% 1.60/0.59  fof(f119,plain,(
% 1.60/0.59    ~spl6_10 | ~spl6_11),
% 1.60/0.59    inference(avatar_split_clause,[],[f53,f116,f112])).
% 1.60/0.59  fof(f53,plain,(
% 1.60/0.59    ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.60/0.59    inference(equality_resolution,[],[f52])).
% 1.60/0.59  fof(f52,plain,(
% 1.60/0.59    ( ! [X4] : (~m1_subset_1(sK3,u1_struct_0(sK1)) | ~m1_subset_1(X4,u1_struct_0(sK2)) | sK3 != X4) )),
% 1.60/0.59    inference(equality_resolution,[],[f25])).
% 1.60/0.59  fof(f25,plain,(
% 1.60/0.59    ( ! [X4,X5] : (~m1_subset_1(X5,u1_struct_0(sK1)) | sK3 != X5 | ~m1_subset_1(X4,u1_struct_0(sK2)) | sK3 != X4) )),
% 1.60/0.59    inference(cnf_transformation,[],[f13])).
% 1.60/0.59  fof(f13,plain,(
% 1.60/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.60/0.59    inference(flattening,[],[f12])).
% 1.60/0.59  fof(f12,plain,(
% 1.60/0.59    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.60/0.59    inference(ennf_transformation,[],[f11])).
% 1.60/0.59  fof(f11,plain,(
% 1.60/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X5] : (X3 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))))))),
% 1.60/0.59    inference(rectify,[],[f10])).
% 1.60/0.59  fof(f10,negated_conjecture,(
% 1.60/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 1.60/0.59    inference(negated_conjecture,[],[f9])).
% 1.60/0.59  fof(f9,conjecture,(
% 1.60/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tmap_1)).
% 1.60/0.59  fof(f110,plain,(
% 1.60/0.59    spl6_9),
% 1.60/0.59    inference(avatar_split_clause,[],[f26,f107])).
% 1.60/0.59  fof(f26,plain,(
% 1.60/0.59    m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))),
% 1.60/0.59    inference(cnf_transformation,[],[f13])).
% 1.60/0.59  fof(f96,plain,(
% 1.60/0.59    spl6_8),
% 1.60/0.59    inference(avatar_split_clause,[],[f31,f93])).
% 1.60/0.59  fof(f31,plain,(
% 1.60/0.59    m1_pre_topc(sK1,sK0)),
% 1.60/0.59    inference(cnf_transformation,[],[f13])).
% 1.60/0.59  fof(f91,plain,(
% 1.60/0.59    ~spl6_7),
% 1.60/0.59    inference(avatar_split_clause,[],[f29,f88])).
% 1.60/0.59  fof(f29,plain,(
% 1.60/0.59    ~r1_tsep_1(sK1,sK2)),
% 1.60/0.59    inference(cnf_transformation,[],[f13])).
% 1.60/0.59  fof(f86,plain,(
% 1.60/0.59    spl6_6),
% 1.60/0.59    inference(avatar_split_clause,[],[f28,f83])).
% 1.60/0.59  fof(f28,plain,(
% 1.60/0.59    m1_pre_topc(sK2,sK0)),
% 1.60/0.59    inference(cnf_transformation,[],[f13])).
% 1.60/0.59  fof(f81,plain,(
% 1.60/0.59    spl6_5),
% 1.60/0.59    inference(avatar_split_clause,[],[f34,f78])).
% 1.60/0.59  fof(f34,plain,(
% 1.60/0.59    l1_pre_topc(sK0)),
% 1.60/0.59    inference(cnf_transformation,[],[f13])).
% 1.60/0.59  fof(f71,plain,(
% 1.60/0.59    ~spl6_3),
% 1.60/0.59    inference(avatar_split_clause,[],[f32,f68])).
% 1.60/0.59  fof(f32,plain,(
% 1.60/0.59    ~v2_struct_0(sK0)),
% 1.60/0.59    inference(cnf_transformation,[],[f13])).
% 1.60/0.59  fof(f66,plain,(
% 1.60/0.59    ~spl6_2),
% 1.60/0.59    inference(avatar_split_clause,[],[f30,f63])).
% 1.60/0.59  fof(f30,plain,(
% 1.60/0.59    ~v2_struct_0(sK1)),
% 1.60/0.59    inference(cnf_transformation,[],[f13])).
% 1.60/0.59  fof(f61,plain,(
% 1.60/0.59    ~spl6_1),
% 1.60/0.59    inference(avatar_split_clause,[],[f27,f58])).
% 1.60/0.59  fof(f27,plain,(
% 1.60/0.59    ~v2_struct_0(sK2)),
% 1.60/0.59    inference(cnf_transformation,[],[f13])).
% 1.60/0.59  % SZS output end Proof for theBenchmark
% 1.60/0.59  % (8735)------------------------------
% 1.60/0.59  % (8735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.59  % (8735)Termination reason: Refutation
% 1.60/0.59  
% 1.60/0.59  % (8735)Memory used [KB]: 10746
% 1.60/0.59  % (8735)Time elapsed: 0.140 s
% 1.60/0.59  % (8735)------------------------------
% 1.60/0.59  % (8735)------------------------------
% 1.60/0.59  % (8731)Success in time 0.231 s
%------------------------------------------------------------------------------
