%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 240 expanded)
%              Number of leaves         :   21 (  81 expanded)
%              Depth                    :   21
%              Number of atoms          :  605 (1371 expanded)
%              Number of equality atoms :   25 (  27 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f252,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f60,f65,f70,f75,f80,f90,f95,f100,f110,f131,f152,f225,f245,f251])).

fof(f251,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_12
    | spl4_23 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_12
    | spl4_23 ),
    inference(subsumption_resolution,[],[f249,f99])).

fof(f99,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_12
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f249,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_23 ),
    inference(subsumption_resolution,[],[f248,f79])).

fof(f79,plain,
    ( m1_pre_topc(sK1,sK3)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl4_8
  <=> m1_pre_topc(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f248,plain,
    ( ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | spl4_23 ),
    inference(subsumption_resolution,[],[f246,f74])).

fof(f74,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl4_7
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f246,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl4_5
    | ~ spl4_6
    | spl4_23 ),
    inference(resolution,[],[f244,f111])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f101,f69])).

fof(f69,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl4_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,X1)
        | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) )
    | ~ spl4_5 ),
    inference(resolution,[],[f64,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f64,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl4_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f244,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl4_23
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f245,plain,
    ( ~ spl4_23
    | spl4_22 ),
    inference(avatar_split_clause,[],[f236,f222,f242])).

fof(f222,plain,
    ( spl4_22
  <=> r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f236,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3))
    | spl4_22 ),
    inference(resolution,[],[f230,f35])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f230,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK3)) )
    | spl4_22 ),
    inference(resolution,[],[f224,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f224,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(sK3))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f222])).

fof(f225,plain,
    ( ~ spl4_22
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | spl4_13
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f215,f140,f128,f107,f72,f67,f62,f222])).

fof(f107,plain,
    ( spl4_13
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f128,plain,
    ( spl4_14
  <=> k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f140,plain,
    ( spl4_15
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f215,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(sK3))
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | spl4_13
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f211,f74])).

fof(f211,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(sK3))
    | ~ spl4_5
    | ~ spl4_6
    | spl4_13
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(resolution,[],[f167,f109])).

fof(f109,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f107])).

fof(f167,plain,
    ( ! [X0] :
        ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(X0)) )
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f166,f141])).

fof(f141,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f140])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
        | ~ m1_pre_topc(X0,sK0)
        | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
        | ~ r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(X0)) )
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f165,f69])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
        | ~ m1_pre_topc(X0,sK0)
        | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
        | ~ r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(X0)) )
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(resolution,[],[f135,f64])).

fof(f135,plain,
    ( ! [X10,X9] :
        ( ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X10)
        | ~ m1_pre_topc(X9,X10)
        | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X9)
        | ~ r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(X9)) )
    | ~ spl4_14 ),
    inference(superposition,[],[f34,f130])).

fof(f130,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f128])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X1,X2)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f152,plain,
    ( spl4_2
    | spl4_3
    | spl4_4
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | spl4_15 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl4_2
    | spl4_3
    | spl4_4
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | spl4_15 ),
    inference(subsumption_resolution,[],[f150,f54])).

fof(f54,plain,
    ( ~ v2_struct_0(sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl4_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f150,plain,
    ( v2_struct_0(sK1)
    | spl4_2
    | spl4_4
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | spl4_15 ),
    inference(subsumption_resolution,[],[f149,f94])).

fof(f94,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_11
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f149,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK1)
    | spl4_2
    | spl4_4
    | ~ spl4_6
    | ~ spl4_12
    | spl4_15 ),
    inference(subsumption_resolution,[],[f148,f49])).

fof(f49,plain,
    ( ~ v2_struct_0(sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl4_2
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f148,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK1)
    | spl4_4
    | ~ spl4_6
    | ~ spl4_12
    | spl4_15 ),
    inference(subsumption_resolution,[],[f147,f99])).

fof(f147,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK1)
    | spl4_4
    | ~ spl4_6
    | spl4_15 ),
    inference(resolution,[],[f142,f105])).

fof(f105,plain,
    ( ! [X2,X3] :
        ( m1_pre_topc(k2_tsep_1(sK0,X2,X3),sK0)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X2) )
    | spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f103,f59])).

fof(f59,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl4_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f103,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | m1_pre_topc(k2_tsep_1(sK0,X2,X3),sK0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f69,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f142,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f140])).

fof(f131,plain,
    ( spl4_14
    | spl4_2
    | spl4_3
    | spl4_4
    | ~ spl4_6
    | spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f126,f97,f92,f87,f67,f57,f52,f47,f128])).

fof(f87,plain,
    ( spl4_10
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f126,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | spl4_2
    | spl4_3
    | spl4_4
    | ~ spl4_6
    | spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f125,f99])).

fof(f125,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | spl4_2
    | spl4_3
    | spl4_4
    | ~ spl4_6
    | spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f124,f49])).

fof(f124,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | spl4_3
    | spl4_4
    | ~ spl4_6
    | spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f123,f54])).

fof(f123,plain,
    ( v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | spl4_4
    | ~ spl4_6
    | spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f122,f94])).

fof(f122,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | spl4_4
    | ~ spl4_6
    | spl4_10 ),
    inference(resolution,[],[f121,f89])).

fof(f89,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f87])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k2_tsep_1(sK0,X1,X0)) )
    | spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f120,f59])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | r1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X1,sK0)
        | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k2_tsep_1(sK0,X1,X0))
        | v2_struct_0(sK0) )
    | spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f119,f69])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | r1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X1,sK0)
        | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k2_tsep_1(sK0,X1,X0))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl4_4
    | ~ spl4_6 ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | r1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X1,sK0)
        | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k2_tsep_1(sK0,X1,X0))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK0) )
    | spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f117,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(k2_tsep_1(sK0,X0,X1))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X0,sK0)
        | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1)) )
    | spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f116,f105])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,X1)
        | v2_struct_0(k2_tsep_1(sK0,X0,X1))
        | ~ m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
        | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1)) )
    | spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f115,f59])).

fof(f115,plain,
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
    | spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f114,f69])).

fof(f114,plain,
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
    | spl4_4
    | ~ spl4_6 ),
    inference(duplicate_literal_removal,[],[f113])).

fof(f113,plain,
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
    | spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f104,f40])).

fof(f40,plain,(
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
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
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
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).

fof(f104,plain,
    ( ! [X0,X1] :
        ( v1_pre_topc(k2_tsep_1(sK0,X0,X1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0) )
    | spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f102,f59])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v1_pre_topc(k2_tsep_1(sK0,X0,X1)) )
    | ~ spl4_6 ),
    inference(resolution,[],[f69,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v1_pre_topc(k2_tsep_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f110,plain,(
    ~ spl4_13 ),
    inference(avatar_split_clause,[],[f23,f107])).

fof(f23,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
                   => ( ( m1_pre_topc(X2,X3)
                        & m1_pre_topc(X1,X3) )
                     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                        | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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
                 => ( ( m1_pre_topc(X2,X3)
                      & m1_pre_topc(X1,X3) )
                   => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                      | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tmap_1)).

fof(f100,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f27,f97])).

fof(f27,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f95,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f25,f92])).

fof(f25,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f90,plain,(
    ~ spl4_10 ),
    inference(avatar_split_clause,[],[f22,f87])).

fof(f22,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f80,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f20,f77])).

fof(f20,plain,(
    m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f19,f72])).

fof(f19,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f70,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f30,f67])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f65,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f29,f62])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f60,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f28,f57])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f55,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f26,f52])).

fof(f26,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f50,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f24,f47])).

fof(f24,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:06:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (28192)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.45  % (28184)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.46  % (28184)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f252,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f50,f55,f60,f65,f70,f75,f80,f90,f95,f100,f110,f131,f152,f225,f245,f251])).
% 0.21/0.46  fof(f251,plain,(
% 0.21/0.46    ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_12 | spl4_23),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f250])).
% 0.21/0.46  fof(f250,plain,(
% 0.21/0.46    $false | (~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_12 | spl4_23)),
% 0.21/0.46    inference(subsumption_resolution,[],[f249,f99])).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    m1_pre_topc(sK1,sK0) | ~spl4_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f97])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    spl4_12 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.46  fof(f249,plain,(
% 0.21/0.46    ~m1_pre_topc(sK1,sK0) | (~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | spl4_23)),
% 0.21/0.46    inference(subsumption_resolution,[],[f248,f79])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    m1_pre_topc(sK1,sK3) | ~spl4_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f77])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    spl4_8 <=> m1_pre_topc(sK1,sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.46  fof(f248,plain,(
% 0.21/0.46    ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK1,sK0) | (~spl4_5 | ~spl4_6 | ~spl4_7 | spl4_23)),
% 0.21/0.46    inference(subsumption_resolution,[],[f246,f74])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    m1_pre_topc(sK3,sK0) | ~spl4_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f72])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    spl4_7 <=> m1_pre_topc(sK3,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.46  fof(f246,plain,(
% 0.21/0.46    ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK1,sK0) | (~spl4_5 | ~spl4_6 | spl4_23)),
% 0.21/0.46    inference(resolution,[],[f244,f111])).
% 0.21/0.46  fof(f111,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,sK0)) ) | (~spl4_5 | ~spl4_6)),
% 0.21/0.46    inference(subsumption_resolution,[],[f101,f69])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    l1_pre_topc(sK0) | ~spl4_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f67])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    spl4_6 <=> l1_pre_topc(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,X1) | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))) ) | ~spl4_5),
% 0.21/0.46    inference(resolution,[],[f64,f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    v2_pre_topc(sK0) | ~spl4_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f62])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    spl4_5 <=> v2_pre_topc(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.46  fof(f244,plain,(
% 0.21/0.46    ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) | spl4_23),
% 0.21/0.46    inference(avatar_component_clause,[],[f242])).
% 0.21/0.46  fof(f242,plain,(
% 0.21/0.46    spl4_23 <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.46  fof(f245,plain,(
% 0.21/0.46    ~spl4_23 | spl4_22),
% 0.21/0.46    inference(avatar_split_clause,[],[f236,f222,f242])).
% 0.21/0.46  fof(f222,plain,(
% 0.21/0.46    spl4_22 <=> r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(sK3))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.46  fof(f236,plain,(
% 0.21/0.46    ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) | spl4_22),
% 0.21/0.46    inference(resolution,[],[f230,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.46  fof(f230,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),X0) | ~r1_tarski(X0,u1_struct_0(sK3))) ) | spl4_22),
% 0.21/0.46    inference(resolution,[],[f224,f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.46  fof(f224,plain,(
% 0.21/0.46    ~r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(sK3)) | spl4_22),
% 0.21/0.46    inference(avatar_component_clause,[],[f222])).
% 0.21/0.46  fof(f225,plain,(
% 0.21/0.46    ~spl4_22 | ~spl4_5 | ~spl4_6 | ~spl4_7 | spl4_13 | ~spl4_14 | ~spl4_15),
% 0.21/0.46    inference(avatar_split_clause,[],[f215,f140,f128,f107,f72,f67,f62,f222])).
% 0.21/0.46  fof(f107,plain,(
% 0.21/0.46    spl4_13 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    spl4_14 <=> k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    spl4_15 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.47  fof(f215,plain,(
% 0.21/0.47    ~r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(sK3)) | (~spl4_5 | ~spl4_6 | ~spl4_7 | spl4_13 | ~spl4_14 | ~spl4_15)),
% 0.21/0.47    inference(subsumption_resolution,[],[f211,f74])).
% 0.21/0.47  fof(f211,plain,(
% 0.21/0.47    ~m1_pre_topc(sK3,sK0) | ~r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(sK3)) | (~spl4_5 | ~spl4_6 | spl4_13 | ~spl4_14 | ~spl4_15)),
% 0.21/0.47    inference(resolution,[],[f167,f109])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) | spl4_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f107])).
% 0.21/0.47  fof(f167,plain,(
% 0.21/0.47    ( ! [X0] : (m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) | ~m1_pre_topc(X0,sK0) | ~r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(X0))) ) | (~spl4_5 | ~spl4_6 | ~spl4_14 | ~spl4_15)),
% 0.21/0.47    inference(subsumption_resolution,[],[f166,f141])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | ~spl4_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f140])).
% 0.21/0.47  fof(f166,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | ~m1_pre_topc(X0,sK0) | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) | ~r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(X0))) ) | (~spl4_5 | ~spl4_6 | ~spl4_14)),
% 0.21/0.47    inference(subsumption_resolution,[],[f165,f69])).
% 0.21/0.47  fof(f165,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | ~m1_pre_topc(X0,sK0) | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) | ~r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(X0))) ) | (~spl4_5 | ~spl4_14)),
% 0.21/0.47    inference(resolution,[],[f135,f64])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    ( ! [X10,X9] : (~v2_pre_topc(X10) | ~l1_pre_topc(X10) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X10) | ~m1_pre_topc(X9,X10) | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X9) | ~r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),u1_struct_0(X9))) ) | ~spl4_14),
% 0.21/0.47    inference(superposition,[],[f34,f130])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~spl4_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f128])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X1,X2) | ~v2_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    spl4_2 | spl4_3 | spl4_4 | ~spl4_6 | ~spl4_11 | ~spl4_12 | spl4_15),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f151])).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    $false | (spl4_2 | spl4_3 | spl4_4 | ~spl4_6 | ~spl4_11 | ~spl4_12 | spl4_15)),
% 0.21/0.47    inference(subsumption_resolution,[],[f150,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ~v2_struct_0(sK1) | spl4_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl4_3 <=> v2_struct_0(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    v2_struct_0(sK1) | (spl4_2 | spl4_4 | ~spl4_6 | ~spl4_11 | ~spl4_12 | spl4_15)),
% 0.21/0.47    inference(subsumption_resolution,[],[f149,f94])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    m1_pre_topc(sK2,sK0) | ~spl4_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f92])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    spl4_11 <=> m1_pre_topc(sK2,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK1) | (spl4_2 | spl4_4 | ~spl4_6 | ~spl4_12 | spl4_15)),
% 0.21/0.47    inference(subsumption_resolution,[],[f148,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ~v2_struct_0(sK2) | spl4_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    spl4_2 <=> v2_struct_0(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.47  fof(f148,plain,(
% 0.21/0.47    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK1) | (spl4_4 | ~spl4_6 | ~spl4_12 | spl4_15)),
% 0.21/0.47    inference(subsumption_resolution,[],[f147,f99])).
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK1) | (spl4_4 | ~spl4_6 | spl4_15)),
% 0.21/0.47    inference(resolution,[],[f142,f105])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    ( ! [X2,X3] : (m1_pre_topc(k2_tsep_1(sK0,X2,X3),sK0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X2)) ) | (spl4_4 | ~spl4_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f103,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ~v2_struct_0(sK0) | spl4_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f57])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    spl4_4 <=> v2_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    ( ! [X2,X3] : (v2_struct_0(sK0) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK0) | m1_pre_topc(k2_tsep_1(sK0,X2,X3),sK0)) ) | ~spl4_6),
% 0.21/0.47    inference(resolution,[],[f69,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | spl4_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f140])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    spl4_14 | spl4_2 | spl4_3 | spl4_4 | ~spl4_6 | spl4_10 | ~spl4_11 | ~spl4_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f126,f97,f92,f87,f67,f57,f52,f47,f128])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    spl4_10 <=> r1_tsep_1(sK1,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | (spl4_2 | spl4_3 | spl4_4 | ~spl4_6 | spl4_10 | ~spl4_11 | ~spl4_12)),
% 0.21/0.47    inference(subsumption_resolution,[],[f125,f99])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    ~m1_pre_topc(sK1,sK0) | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | (spl4_2 | spl4_3 | spl4_4 | ~spl4_6 | spl4_10 | ~spl4_11)),
% 0.21/0.47    inference(subsumption_resolution,[],[f124,f49])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | (spl4_3 | spl4_4 | ~spl4_6 | spl4_10 | ~spl4_11)),
% 0.21/0.47    inference(subsumption_resolution,[],[f123,f54])).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    v2_struct_0(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | (spl4_4 | ~spl4_6 | spl4_10 | ~spl4_11)),
% 0.21/0.47    inference(subsumption_resolution,[],[f122,f94])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | (spl4_4 | ~spl4_6 | spl4_10)),
% 0.21/0.47    inference(resolution,[],[f121,f89])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    ~r1_tsep_1(sK1,sK2) | spl4_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f87])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k2_tsep_1(sK0,X1,X0))) ) | (spl4_4 | ~spl4_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f120,f59])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | r1_tsep_1(X1,X0) | ~m1_pre_topc(X1,sK0) | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k2_tsep_1(sK0,X1,X0)) | v2_struct_0(sK0)) ) | (spl4_4 | ~spl4_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f119,f69])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | r1_tsep_1(X1,X0) | ~m1_pre_topc(X1,sK0) | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k2_tsep_1(sK0,X1,X0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl4_4 | ~spl4_6)),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f118])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | r1_tsep_1(X1,X0) | ~m1_pre_topc(X1,sK0) | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k2_tsep_1(sK0,X1,X0)) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0)) ) | (spl4_4 | ~spl4_6)),
% 0.21/0.47    inference(resolution,[],[f117,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v2_struct_0(k2_tsep_1(sK0,X0,X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,X1) | ~m1_pre_topc(X0,sK0) | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1))) ) | (spl4_4 | ~spl4_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f116,f105])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,X1) | v2_struct_0(k2_tsep_1(sK0,X0,X1)) | ~m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0) | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1))) ) | (spl4_4 | ~spl4_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f115,f59])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,X1) | v2_struct_0(k2_tsep_1(sK0,X0,X1)) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0) | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1))) ) | (spl4_4 | ~spl4_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f114,f69])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | r1_tsep_1(X0,X1) | v2_struct_0(k2_tsep_1(sK0,X0,X1)) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0) | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1))) ) | (spl4_4 | ~spl4_6)),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f113])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | r1_tsep_1(X0,X1) | v2_struct_0(k2_tsep_1(sK0,X0,X1)) | v2_struct_0(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0) | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1))) ) | (spl4_4 | ~spl4_6)),
% 0.21/0.47    inference(resolution,[],[f104,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | r1_tsep_1(X1,X2) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | v2_struct_0(X0) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))) )),
% 0.21/0.47    inference(equality_resolution,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | r1_tsep_1(X1,X2) | v2_struct_0(X3) | ~v1_pre_topc(X3) | ~m1_pre_topc(X3,X0) | u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_pre_topc(k2_tsep_1(sK0,X0,X1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X0)) ) | (spl4_4 | ~spl4_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f102,f59])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v1_pre_topc(k2_tsep_1(sK0,X0,X1))) ) | ~spl4_6),
% 0.21/0.47    inference(resolution,[],[f69,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v1_pre_topc(k2_tsep_1(X0,X1,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    ~spl4_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f23,f107])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f6])).
% 0.21/0.47  fof(f6,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tmap_1)).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    spl4_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f97])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    m1_pre_topc(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    spl4_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f92])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    m1_pre_topc(sK2,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ~spl4_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f22,f87])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ~r1_tsep_1(sK1,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    spl4_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f20,f77])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    m1_pre_topc(sK1,sK3)),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    spl4_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f19,f72])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    m1_pre_topc(sK3,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    spl4_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f30,f67])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl4_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f29,f62])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    v2_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ~spl4_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f28,f57])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ~spl4_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f52])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ~v2_struct_0(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ~spl4_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f47])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ~v2_struct_0(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (28184)------------------------------
% 0.21/0.47  % (28184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (28184)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (28184)Memory used [KB]: 10746
% 0.21/0.47  % (28184)Time elapsed: 0.065 s
% 0.21/0.47  % (28184)------------------------------
% 0.21/0.47  % (28184)------------------------------
% 0.21/0.47  % (28177)Success in time 0.113 s
%------------------------------------------------------------------------------
