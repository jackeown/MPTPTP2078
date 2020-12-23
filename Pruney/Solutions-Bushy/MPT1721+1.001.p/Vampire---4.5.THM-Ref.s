%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1721+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 283 expanded)
%              Number of leaves         :   36 ( 116 expanded)
%              Depth                    :   10
%              Number of atoms          :  715 (1586 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f236,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f55,f59,f63,f67,f71,f75,f83,f87,f91,f95,f99,f103,f108,f112,f116,f120,f124,f128,f134,f138,f147,f162,f166,f175,f179,f185,f213,f226,f234])).

fof(f234,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_18
    | spl4_35 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_18
    | spl4_35 ),
    inference(unit_resulting_resolution,[],[f62,f66,f70,f90,f74,f225,f115])).

fof(f115,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_pre_topc(X1,X2)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl4_18
  <=> ! [X1,X0,X2] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_pre_topc(X1,X2)
        | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f225,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3))
    | spl4_35 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl4_35
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f74,plain,
    ( m1_pre_topc(sK1,sK3)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_8
  <=> m1_pre_topc(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f90,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_12
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f70,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl4_7
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f66,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f62,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl4_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f226,plain,
    ( ~ spl4_35
    | ~ spl4_17
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f215,f211,f110,f224])).

fof(f110,plain,
    ( spl4_17
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f211,plain,
    ( spl4_33
  <=> ! [X1] :
        ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),X1)
        | ~ r1_tarski(X1,u1_struct_0(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f215,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl4_17
    | ~ spl4_33 ),
    inference(resolution,[],[f212,f111])).

fof(f111,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f110])).

fof(f212,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),X1)
        | ~ r1_tarski(X1,u1_struct_0(sK3)) )
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f211])).

fof(f213,plain,
    ( spl4_33
    | spl4_2
    | spl4_3
    | spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_29
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f194,f183,f177,f89,f85,f81,f53,f49,f211])).

fof(f49,plain,
    ( spl4_2
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f53,plain,
    ( spl4_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f81,plain,
    ( spl4_10
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f85,plain,
    ( spl4_11
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f177,plain,
    ( spl4_29
  <=> ! [X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK3))
        | ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f183,plain,
    ( spl4_30
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | r1_tsep_1(X0,X1)
        | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f194,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)),X1)
        | ~ r1_tarski(X1,u1_struct_0(sK3)) )
    | spl4_2
    | spl4_3
    | spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_29
    | ~ spl4_30 ),
    inference(backward_demodulation,[],[f178,f192])).

fof(f192,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl4_2
    | spl4_3
    | spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f191,f54])).

fof(f54,plain,
    ( ~ v2_struct_0(sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f191,plain,
    ( v2_struct_0(sK1)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl4_2
    | spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f190,f86])).

fof(f86,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f85])).

fof(f190,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK1)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl4_2
    | spl4_10
    | ~ spl4_12
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f189,f50])).

fof(f50,plain,
    ( ~ v2_struct_0(sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f189,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK1)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl4_10
    | ~ spl4_12
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f188,f90])).

fof(f188,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK1)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl4_10
    | ~ spl4_30 ),
    inference(resolution,[],[f184,f82])).

fof(f82,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f81])).

fof(f184,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1)) )
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f183])).

fof(f178,plain,
    ( ! [X1] :
        ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),X1)
        | ~ r1_tarski(X1,u1_struct_0(sK3)) )
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f177])).

fof(f185,plain,
    ( spl4_30
    | spl4_4
    | ~ spl4_6
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f181,f173,f65,f57,f183])).

fof(f57,plain,
    ( spl4_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f173,plain,
    ( spl4_28
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | r1_tsep_1(X1,X2)
        | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f181,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | r1_tsep_1(X0,X1)
        | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1)) )
    | spl4_4
    | ~ spl4_6
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f180,f58])).

fof(f58,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f180,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | r1_tsep_1(X0,X1)
        | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1)) )
    | ~ spl4_6
    | ~ spl4_28 ),
    inference(resolution,[],[f174,f66])).

fof(f174,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | r1_tsep_1(X1,X2)
        | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f173])).

fof(f179,plain,
    ( spl4_29
    | ~ spl4_16
    | spl4_24 ),
    inference(avatar_split_clause,[],[f171,f142,f106,f177])).

fof(f106,plain,
    ( spl4_16
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f142,plain,
    ( spl4_24
  <=> r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f171,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK3))
        | ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),X1) )
    | ~ spl4_16
    | spl4_24 ),
    inference(resolution,[],[f143,f107])).

fof(f107,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f106])).

fof(f143,plain,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f142])).

fof(f175,plain,
    ( spl4_28
    | ~ spl4_20
    | ~ spl4_21
    | ~ spl4_22
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f169,f164,f132,f126,f122,f173])).

fof(f122,plain,
    ( spl4_20
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f126,plain,
    ( spl4_21
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v1_pre_topc(k2_tsep_1(X0,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f132,plain,
    ( spl4_22
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f164,plain,
    ( spl4_27
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | r1_tsep_1(X1,X2)
        | v2_struct_0(k2_tsep_1(X0,X1,X2))
        | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
        | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f169,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | r1_tsep_1(X1,X2)
        | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) )
    | ~ spl4_20
    | ~ spl4_21
    | ~ spl4_22
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f168,f133])).

fof(f133,plain,
    ( ! [X2,X0,X1] :
        ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X0) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f132])).

fof(f168,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | r1_tsep_1(X1,X2)
        | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) )
    | ~ spl4_20
    | ~ spl4_21
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f167,f127])).

fof(f127,plain,
    ( ! [X2,X0,X1] :
        ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X0) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f126])).

fof(f167,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | r1_tsep_1(X1,X2)
        | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
        | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) )
    | ~ spl4_20
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f165,f123])).

fof(f123,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X0) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f122])).

fof(f165,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | r1_tsep_1(X1,X2)
        | v2_struct_0(k2_tsep_1(X0,X1,X2))
        | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
        | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f164])).

fof(f166,plain,(
    spl4_27 ),
    inference(avatar_split_clause,[],[f43,f164])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | r1_tsep_1(X1,X2)
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
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
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).

fof(f162,plain,
    ( spl4_2
    | spl4_3
    | spl4_4
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_22
    | spl4_25 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl4_2
    | spl4_3
    | spl4_4
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_22
    | spl4_25 ),
    inference(subsumption_resolution,[],[f160,f58])).

fof(f160,plain,
    ( v2_struct_0(sK0)
    | spl4_2
    | spl4_3
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_22
    | spl4_25 ),
    inference(subsumption_resolution,[],[f159,f86])).

fof(f159,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl4_2
    | spl4_3
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_22
    | spl4_25 ),
    inference(subsumption_resolution,[],[f158,f50])).

fof(f158,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_22
    | spl4_25 ),
    inference(subsumption_resolution,[],[f157,f90])).

fof(f157,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_22
    | spl4_25 ),
    inference(subsumption_resolution,[],[f156,f54])).

fof(f156,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl4_6
    | ~ spl4_22
    | spl4_25 ),
    inference(subsumption_resolution,[],[f153,f66])).

fof(f153,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl4_22
    | spl4_25 ),
    inference(resolution,[],[f146,f133])).

fof(f146,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | spl4_25 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl4_25
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f147,plain,
    ( ~ spl4_24
    | ~ spl4_25
    | ~ spl4_7
    | spl4_13
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f140,f136,f93,f69,f145,f142])).

fof(f93,plain,
    ( spl4_13
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f136,plain,
    ( spl4_23
  <=> ! [X1,X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | m1_pre_topc(X0,X1)
        | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f140,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
    | ~ spl4_7
    | spl4_13
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f139,f70])).

fof(f139,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
    | spl4_13
    | ~ spl4_23 ),
    inference(resolution,[],[f137,f94])).

fof(f94,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f93])).

fof(f137,plain,
    ( ! [X0,X1] :
        ( m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f136])).

fof(f138,plain,
    ( spl4_23
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f130,f118,f65,f61,f136])).

fof(f118,plain,
    ( spl4_19
  <=> ! [X1,X0,X2] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(X2,X0)
        | m1_pre_topc(X1,X2)
        | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | m1_pre_topc(X0,X1)
        | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) )
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f129,f66])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | m1_pre_topc(X0,X1)
        | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) )
    | ~ spl4_5
    | ~ spl4_19 ),
    inference(resolution,[],[f119,f62])).

fof(f119,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(X2,X0)
        | m1_pre_topc(X1,X2)
        | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f118])).

fof(f134,plain,(
    spl4_22 ),
    inference(avatar_split_clause,[],[f41,f132])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f128,plain,(
    spl4_21 ),
    inference(avatar_split_clause,[],[f40,f126])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v1_pre_topc(k2_tsep_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f124,plain,(
    spl4_20 ),
    inference(avatar_split_clause,[],[f39,f122])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f120,plain,(
    spl4_19 ),
    inference(avatar_split_clause,[],[f36,f118])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f116,plain,(
    spl4_18 ),
    inference(avatar_split_clause,[],[f35,f114])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f112,plain,
    ( spl4_17
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f104,f101,f97,f110])).

fof(f97,plain,
    ( spl4_14
  <=> ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f101,plain,
    ( spl4_15
  <=> ! [X1,X0,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f104,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(superposition,[],[f102,f98])).

fof(f98,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f97])).

fof(f102,plain,
    ( ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f101])).

fof(f108,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f42,f106])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f103,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f38,f101])).

fof(f38,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

fof(f99,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f37,f97])).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f95,plain,(
    ~ spl4_13 ),
    inference(avatar_split_clause,[],[f25,f93])).

fof(f25,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tmap_1)).

fof(f91,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f29,f89])).

fof(f29,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f87,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f27,f85])).

fof(f27,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f83,plain,(
    ~ spl4_10 ),
    inference(avatar_split_clause,[],[f24,f81])).

fof(f24,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f75,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f22,f73])).

fof(f22,plain,(
    m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f71,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f21,f69])).

fof(f21,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f67,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f32,f65])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f63,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f31,f61])).

fof(f31,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f59,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f30,f57])).

fof(f30,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f28,f53])).

fof(f28,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f51,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f26,f49])).

fof(f26,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
