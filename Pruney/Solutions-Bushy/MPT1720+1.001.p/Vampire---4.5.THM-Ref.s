%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1720+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:25 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 201 expanded)
%              Number of leaves         :   16 (  55 expanded)
%              Depth                    :   34
%              Number of atoms          :  610 (1320 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f52,f57,f62,f67,f72,f77,f82,f87,f92,f102,f148])).

fof(f148,plain,
    ( spl4_1
    | spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl4_1
    | spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | spl4_12 ),
    inference(subsumption_resolution,[],[f146,f71])).

fof(f71,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl4_7
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f146,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | spl4_1
    | spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | spl4_12 ),
    inference(subsumption_resolution,[],[f145,f51])).

fof(f51,plain,
    ( ~ v2_struct_0(sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl4_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

% (7577)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% (7584)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f145,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | spl4_1
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | spl4_12 ),
    inference(subsumption_resolution,[],[f144,f76])).

fof(f76,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl4_8
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f144,plain,
    ( ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | spl4_1
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | spl4_12 ),
    inference(subsumption_resolution,[],[f143,f81])).

fof(f81,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_9
  <=> m1_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f143,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | spl4_1
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | spl4_12 ),
    inference(subsumption_resolution,[],[f142,f86])).

fof(f86,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_10
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f142,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | spl4_1
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_11
    | spl4_12 ),
    inference(subsumption_resolution,[],[f141,f41])).

fof(f41,plain,
    ( ~ v2_struct_0(sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl4_1
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f141,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_11
    | spl4_12 ),
    inference(subsumption_resolution,[],[f140,f91])).

fof(f91,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_11
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f140,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_12 ),
    inference(resolution,[],[f139,f101])).

fof(f101,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_12
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f139,plain,
    ( ! [X2,X0,X1] :
        ( m1_pre_topc(k1_tsep_1(sK0,X0,X1),X2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(X0,X2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0) )
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f138,f97])).

fof(f97,plain,
    ( ! [X2,X3] :
        ( m1_pre_topc(k1_tsep_1(sK0,X2,X3),sK0)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X2) )
    | spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f95,f56])).

fof(f56,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl4_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f95,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | m1_pre_topc(k1_tsep_1(sK0,X2,X3),sK0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f66,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f66,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl4_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f138,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
        | m1_pre_topc(k1_tsep_1(sK0,X0,X1),X2)
        | ~ m1_pre_topc(X1,sK0) )
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f137,f66])).

fof(f137,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(X0,X2)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
        | m1_pre_topc(k1_tsep_1(sK0,X0,X1),X2)
        | ~ m1_pre_topc(X1,sK0) )
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(X0,X2)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
        | ~ m1_pre_topc(X2,sK0)
        | m1_pre_topc(k1_tsep_1(sK0,X0,X1),X2)
        | ~ m1_pre_topc(X1,sK0) )
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(resolution,[],[f124,f61])).

fof(f61,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl4_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f124,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ v2_pre_topc(X7)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X6,sK0)
        | ~ m1_pre_topc(X4,X6)
        | ~ m1_pre_topc(X5,X6)
        | ~ l1_pre_topc(X7)
        | ~ m1_pre_topc(k1_tsep_1(sK0,X5,X4),X7)
        | ~ m1_pre_topc(X6,X7)
        | m1_pre_topc(k1_tsep_1(sK0,X5,X4),X6)
        | ~ m1_pre_topc(X4,sK0) )
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(resolution,[],[f120,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X1,X2)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f120,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),u1_struct_0(X2))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(X0,X2) )
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),u1_struct_0(X2))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(X0,sK0) )
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(resolution,[],[f118,f103])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f93,f66])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,X1)
        | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) )
    | ~ spl4_5 ),
    inference(resolution,[],[f61,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f118,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
        | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),u1_struct_0(X2))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X1,X2) )
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),u1_struct_0(X2))
        | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X1,X2)
        | ~ m1_pre_topc(X1,sK0) )
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(resolution,[],[f115,f103])).

fof(f115,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_tarski(u1_struct_0(X5),X6)
        | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X4,X5)),X6)
        | ~ r1_tarski(u1_struct_0(X4),X6)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X5) )
    | spl4_4
    | ~ spl4_6 ),
    inference(superposition,[],[f36,f113])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0) )
    | spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f112,f56])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0))
        | v2_struct_0(sK0) )
    | spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f111,f66])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl4_4
    | ~ spl4_6 ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK0) )
    | spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f109,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(k1_tsep_1(sK0,X0,X1))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1)) )
    | spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f108,f97])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(k1_tsep_1(sK0,X0,X1))
        | ~ m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
        | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1)) )
    | spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f107,f56])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(k1_tsep_1(sK0,X0,X1))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
        | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1)) )
    | spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f106,f66])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(k1_tsep_1(sK0,X0,X1))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
        | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1)) )
    | spl4_4
    | ~ spl4_6 ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,
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
        | v2_struct_0(k1_tsep_1(sK0,X0,X1))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
        | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1)) )
    | spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f96,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ v1_pre_topc(X3)
      | ~ m1_pre_topc(X3,X0)
      | u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k1_tsep_1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

fof(f96,plain,
    ( ! [X0,X1] :
        ( v1_pre_topc(k1_tsep_1(sK0,X0,X1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0) )
    | spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f94,f56])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v1_pre_topc(k1_tsep_1(sK0,X0,X1)) )
    | ~ spl4_6 ),
    inference(resolution,[],[f66,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v1_pre_topc(k1_tsep_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f102,plain,(
    ~ spl4_12 ),
    inference(avatar_split_clause,[],[f21,f99])).

fof(f21,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
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
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
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
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ( m1_pre_topc(X3,X2)
                        & m1_pre_topc(X1,X2) )
                     => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ( m1_pre_topc(X3,X2)
                      & m1_pre_topc(X1,X2) )
                   => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tmap_1)).

fof(f92,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f25,f89])).

fof(f25,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f87,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f23,f84])).

fof(f23,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f82,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f20,f79])).

fof(f20,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f77,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f19,f74])).

fof(f19,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f72,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f18,f69])).

fof(f18,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f67,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f28,f64])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f62,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f27,f59])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f57,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f26,f54])).

fof(f26,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f52,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f24,f49])).

fof(f24,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f17,f39])).

fof(f17,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
