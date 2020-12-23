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
% DateTime   : Thu Dec  3 13:10:39 EST 2020

% Result     : Theorem 3.27s
% Output     : Refutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  449 (3137 expanded)
%              Number of leaves         :   93 (1477 expanded)
%              Depth                    :   29
%              Number of atoms          : 2721 (11932 expanded)
%              Number of equality atoms :  293 (1274 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8317,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f99,f104,f109,f114,f119,f124,f130,f136,f142,f148,f154,f160,f168,f173,f178,f192,f197,f202,f216,f221,f226,f231,f236,f256,f261,f266,f295,f300,f305,f338,f343,f348,f371,f376,f381,f411,f416,f421,f1236,f1241,f1246,f1251,f1256,f1261,f1266,f1271,f1276,f1281,f1286,f5078,f5083,f5088,f5093,f5098,f5103,f5108,f5119,f5124,f5129,f8260,f8265,f8270,f8275,f8280,f8285,f8290,f8295,f8300,f8305,f8310,f8314,f8316])).

fof(f8316,plain,
    ( spl9_1
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_23
    | ~ spl9_38
    | spl9_66 ),
    inference(avatar_contradiction_clause,[],[f8315])).

fof(f8315,plain,
    ( $false
    | spl9_1
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_23
    | ~ spl9_38
    | spl9_66 ),
    inference(subsumption_resolution,[],[f8311,f559])).

fof(f559,plain,
    ( m1_subset_1(k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_23 ),
    inference(unit_resulting_resolution,[],[f93,f147,f129,f118,f230,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(f230,plain,
    ( m1_subset_1(k3_lattices(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl9_23
  <=> m1_subset_1(k3_lattices(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f118,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl9_6
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f129,plain,
    ( l1_lattices(sK0)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl9_8
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f147,plain,
    ( v6_lattices(sK0)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl9_11
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f93,plain,
    ( ~ v2_struct_0(sK0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl9_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f8311,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_38
    | spl9_66 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f415,f8284,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(f8284,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)),k4_lattices(sK0,sK1,sK3)) != k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)))
    | spl9_66 ),
    inference(avatar_component_clause,[],[f8282])).

fof(f8282,plain,
    ( spl9_66
  <=> k3_lattices(sK0,k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)),k4_lattices(sK0,sK1,sK3)) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).

fof(f415,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f413])).

fof(f413,plain,
    ( spl9_38
  <=> m1_subset_1(k4_lattices(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f135,plain,
    ( l2_lattices(sK0)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl9_9
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f141,plain,
    ( v4_lattices(sK0)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl9_10
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f8314,plain,
    ( spl9_1
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_23
    | ~ spl9_38
    | spl9_66 ),
    inference(avatar_contradiction_clause,[],[f8313])).

fof(f8313,plain,
    ( $false
    | spl9_1
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_23
    | ~ spl9_38
    | spl9_66 ),
    inference(subsumption_resolution,[],[f8312,f559])).

fof(f8312,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_38
    | spl9_66 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f415,f8284,f86])).

fof(f8310,plain,
    ( spl9_71
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f398,f145,f127,f121,f111,f91,f8307])).

fof(f8307,plain,
    ( spl9_71
  <=> k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_71])])).

fof(f111,plain,
    ( spl9_5
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f121,plain,
    ( spl9_7
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f398,plain,
    ( k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK3,sK1)
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(backward_demodulation,[],[f351,f392])).

fof(f392,plain,
    ( k4_lattices(sK0,sK3,sK1) = k4_lattices(sK0,sK1,sK3)
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f93,f147,f129,f113,f123,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f123,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f113,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f351,plain,
    ( k4_lattices(sK0,sK3,sK1) = k2_lattices(sK0,sK3,sK1)
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f93,f147,f129,f123,f113,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f8305,plain,
    ( spl9_70
    | spl9_1
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f396,f145,f127,f121,f116,f91,f8302])).

fof(f8302,plain,
    ( spl9_70
  <=> k4_lattices(sK0,sK2,sK3) = k2_lattices(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_70])])).

fof(f396,plain,
    ( k4_lattices(sK0,sK2,sK3) = k2_lattices(sK0,sK3,sK2)
    | spl9_1
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(backward_demodulation,[],[f354,f393])).

fof(f393,plain,
    ( k4_lattices(sK0,sK2,sK3) = k4_lattices(sK0,sK3,sK2)
    | spl9_1
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f93,f147,f129,f118,f123,f89])).

fof(f354,plain,
    ( k4_lattices(sK0,sK3,sK2) = k2_lattices(sK0,sK3,sK2)
    | spl9_1
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f93,f147,f129,f123,f118,f88])).

fof(f8300,plain,
    ( spl9_69
    | spl9_1
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f393,f145,f127,f121,f116,f91,f8297])).

fof(f8297,plain,
    ( spl9_69
  <=> k4_lattices(sK0,sK2,sK3) = k4_lattices(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_69])])).

fof(f8295,plain,
    ( spl9_68
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f392,f145,f127,f121,f111,f91,f8292])).

fof(f8292,plain,
    ( spl9_68
  <=> k4_lattices(sK0,sK3,sK1) = k4_lattices(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).

fof(f8290,plain,
    ( spl9_67
    | spl9_1
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f389,f145,f127,f116,f111,f91,f8287])).

fof(f8287,plain,
    ( spl9_67
  <=> k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_67])])).

fof(f389,plain,
    ( k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1)
    | spl9_1
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f93,f147,f129,f113,f118,f89])).

fof(f8285,plain,
    ( ~ spl9_66
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_23
    | ~ spl9_25
    | ~ spl9_27
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_45
    | ~ spl9_47
    | spl9_56 ),
    inference(avatar_split_clause,[],[f7794,f5100,f1268,f1258,f1243,f413,f263,f253,f228,f157,f151,f145,f139,f133,f127,f121,f116,f111,f106,f101,f96,f91,f8282])).

fof(f96,plain,
    ( spl9_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f101,plain,
    ( spl9_3
  <=> v11_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f106,plain,
    ( spl9_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f151,plain,
    ( spl9_12
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f157,plain,
    ( spl9_13
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f253,plain,
    ( spl9_25
  <=> sK3 = k2_lattices(sK0,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f263,plain,
    ( spl9_27
  <=> sK1 = k2_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f1243,plain,
    ( spl9_42
  <=> k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f1258,plain,
    ( spl9_45
  <=> sK1 = k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).

fof(f1268,plain,
    ( spl9_47
  <=> k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).

fof(f5100,plain,
    ( spl9_56
  <=> k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)),k3_lattices(sK0,sK1,sK3)) = k3_lattices(sK0,k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)),k4_lattices(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f7794,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)),k4_lattices(sK0,sK1,sK3)) != k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_23
    | ~ spl9_25
    | ~ spl9_27
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_45
    | ~ spl9_47
    | spl9_56 ),
    inference(backward_demodulation,[],[f5970,f7793])).

fof(f7793,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3))) = k4_lattices(sK0,k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK3)),k3_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_23
    | ~ spl9_25
    | ~ spl9_27
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_45 ),
    inference(forward_demodulation,[],[f7792,f951])).

fof(f951,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK2) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f118,f415,f86])).

fof(f7792,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3))) = k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK2),k3_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_23
    | ~ spl9_25
    | ~ spl9_27
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_45 ),
    inference(forward_demodulation,[],[f5278,f3760])).

fof(f3760,plain,
    ( k3_lattices(sK0,sK1,sK3) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_23
    | ~ spl9_25
    | ~ spl9_27
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_45 ),
    inference(backward_demodulation,[],[f946,f3757])).

fof(f3757,plain,
    ( k3_lattices(sK0,sK1,sK3) = k3_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_23
    | ~ spl9_25
    | ~ spl9_27
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_45 ),
    inference(forward_demodulation,[],[f3756,f1035])).

fof(f1035,plain,
    ( k3_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13
    | ~ spl9_23
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f898,f930])).

fof(f930,plain,
    ( k1_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) = k3_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_23
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f230,f415,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f898,plain,
    ( k3_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k1_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_13
    | ~ spl9_23
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f93,f108,f159,f230,f415,f75])).

fof(f75,plain,(
    ! [X4,X0,X3] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),sK5(X0)))
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f48,f50,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),sK5(X0)))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

fof(f159,plain,
    ( v9_lattices(sK0)
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f157])).

fof(f108,plain,
    ( l3_lattices(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f3756,plain,
    ( k3_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_23
    | ~ spl9_25
    | ~ spl9_27
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_45 ),
    inference(forward_demodulation,[],[f3755,f930])).

fof(f3755,plain,
    ( k1_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k1_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_23
    | ~ spl9_25
    | ~ spl9_27
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_45 ),
    inference(forward_demodulation,[],[f3754,f614])).

fof(f614,plain,
    ( k3_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_23 ),
    inference(backward_demodulation,[],[f606,f613])).

fof(f613,plain,
    ( k3_lattices(sK0,sK1,sK3) = k3_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_23 ),
    inference(backward_demodulation,[],[f537,f510])).

fof(f510,plain,
    ( k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_23 ),
    inference(unit_resulting_resolution,[],[f93,f147,f153,f159,f108,f230,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattices)).

fof(f153,plain,
    ( v8_lattices(sK0)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f151])).

fof(f537,plain,
    ( k1_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3)) = k3_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_23 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f230,f230,f85])).

fof(f606,plain,
    ( k3_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3)))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13
    | ~ spl9_23 ),
    inference(forward_demodulation,[],[f517,f537])).

fof(f517,plain,
    ( k3_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k1_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3)))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_13
    | ~ spl9_23 ),
    inference(unit_resulting_resolution,[],[f93,f108,f159,f230,f230,f75])).

fof(f3754,plain,
    ( k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k1_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3))) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3)),k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_23
    | ~ spl9_25
    | ~ spl9_27
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_45 ),
    inference(forward_demodulation,[],[f1621,f2164])).

fof(f2164,plain,
    ( k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_23
    | ~ spl9_25
    | ~ spl9_27
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_45 ),
    inference(backward_demodulation,[],[f978,f2161])).

fof(f2161,plain,
    ( k4_lattices(sK0,sK1,sK3) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_23
    | ~ spl9_25
    | ~ spl9_27
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_45 ),
    inference(forward_demodulation,[],[f2160,f888])).

fof(f888,plain,
    ( k4_lattices(sK0,sK1,sK3) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f93,f147,f153,f159,f108,f415,f74])).

fof(f2160,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_23
    | ~ spl9_25
    | ~ spl9_27
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_45 ),
    inference(forward_demodulation,[],[f2159,f1006])).

fof(f1006,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) = k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_23
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f970,f994])).

fof(f994,plain,
    ( k4_lattices(sK0,k4_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3)) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_23
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f93,f147,f129,f230,f415,f89])).

fof(f970,plain,
    ( k4_lattices(sK0,k4_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3)) = k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_23
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f93,f147,f129,f230,f415,f88])).

fof(f2159,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) = k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_27
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_45 ),
    inference(forward_demodulation,[],[f2158,f1245])).

fof(f1245,plain,
    ( k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK1,sK3)
    | ~ spl9_42 ),
    inference(avatar_component_clause,[],[f1243])).

fof(f2158,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) = k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),k1_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_27
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_45 ),
    inference(forward_demodulation,[],[f2157,f2143])).

fof(f2143,plain,
    ( k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK1)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_27
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_45 ),
    inference(backward_demodulation,[],[f1039,f2142])).

fof(f2142,plain,
    ( sK1 = k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_27
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_45 ),
    inference(forward_demodulation,[],[f2141,f1260])).

fof(f1260,plain,
    ( sK1 = k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK3))
    | ~ spl9_45 ),
    inference(avatar_component_clause,[],[f1258])).

fof(f2141,plain,
    ( k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK3)) = k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_27
    | ~ spl9_38
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f2140,f1245])).

fof(f2140,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK3)) = k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_27
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f2139,f934])).

fof(f934,plain,
    ( k1_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK3)) = k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_5
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f113,f415,f85])).

fof(f2139,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f2138,f265])).

fof(f265,plain,
    ( sK1 = k2_lattices(sK0,sK1,sK1)
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f263])).

fof(f2138,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK1,sK1),k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(forward_demodulation,[],[f1995,f355])).

fof(f355,plain,
    ( k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,sK3)
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f93,f147,f129,f113,f123,f88])).

fof(f1995,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK1,sK1),k2_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7 ),
    inference(unit_resulting_resolution,[],[f93,f108,f103,f113,f113,f123,f79])).

fof(f79,plain,(
    ! [X6,X4,X0,X5] :
      ( ~ v11_lattices(X0)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ( k2_lattices(X0,sK6(X0),k1_lattices(X0,sK7(X0),sK8(X0))) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),k2_lattices(X0,sK6(X0),sK8(X0)))
            & m1_subset_1(sK8(X0),u1_struct_0(X0))
            & m1_subset_1(sK7(X0),u1_struct_0(X0))
            & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6))
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f53,f56,f55,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k2_lattices(X0,sK6(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK6(X0),X2),k2_lattices(X0,sK6(X0),X3))
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k2_lattices(X0,sK6(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK6(X0),X2),k2_lattices(X0,sK6(X0),X3))
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k2_lattices(X0,sK6(X0),k1_lattices(X0,sK7(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),k2_lattices(X0,sK6(X0),X3))
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X3] :
          ( k2_lattices(X0,sK6(X0),k1_lattices(X0,sK7(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),k2_lattices(X0,sK6(X0),X3))
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK6(X0),k1_lattices(X0,sK7(X0),sK8(X0))) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),k2_lattices(X0,sK6(X0),sK8(X0)))
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6))
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ! [X3] :
                      ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v11_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_lattices)).

fof(f103,plain,
    ( v11_lattices(sK0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f1039,plain,
    ( k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK3)))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f894,f1017])).

fof(f1017,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK1) = k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_5
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f926,f950])).

fof(f950,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK1) = k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_5
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f113,f415,f86])).

fof(f926,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK1) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK1)
    | spl9_1
    | ~ spl9_5
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f113,f415,f85])).

fof(f894,plain,
    ( k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK1))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_13
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f93,f108,f159,f113,f415,f75])).

fof(f2157,plain,
    ( k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK1),k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f1993,f2115])).

fof(f2115,plain,
    ( k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK3)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_42 ),
    inference(backward_demodulation,[],[f1037,f2114])).

fof(f2114,plain,
    ( sK3 = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f2113,f321])).

fof(f321,plain,
    ( sK3 = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13 ),
    inference(backward_demodulation,[],[f285,f314])).

fof(f314,plain,
    ( k3_lattices(sK0,sK3,sK1) = k3_lattices(sK0,sK1,sK3)
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f113,f123,f86])).

fof(f285,plain,
    ( sK3 = k2_lattices(sK0,sK3,k3_lattices(sK0,sK3,sK1))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13 ),
    inference(backward_demodulation,[],[f239,f269])).

fof(f269,plain,
    ( k3_lattices(sK0,sK3,sK1) = k1_lattices(sK0,sK3,sK1)
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f123,f113,f85])).

fof(f239,plain,
    ( sK3 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,sK1))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f93,f108,f159,f123,f113,f75])).

fof(f2113,plain,
    ( k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK3)) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f2112,f1015])).

fof(f1015,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK3) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f928,f952])).

fof(f952,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK3) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f123,f415,f86])).

fof(f928,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK3) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK3)
    | spl9_1
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f123,f415,f85])).

fof(f2112,plain,
    ( k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK3)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f2111,f1245])).

fof(f2111,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK3) = k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_25 ),
    inference(forward_demodulation,[],[f2110,f398])).

fof(f2110,plain,
    ( k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),sK3)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_25 ),
    inference(forward_demodulation,[],[f1997,f255])).

fof(f255,plain,
    ( sK3 = k2_lattices(sK0,sK3,sK3)
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f253])).

fof(f1997,plain,
    ( k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7 ),
    inference(unit_resulting_resolution,[],[f93,f108,f103,f123,f113,f123,f79])).

fof(f1037,plain,
    ( k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK3)))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f896,f1015])).

fof(f896,plain,
    ( k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK3))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_13
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f93,f108,f159,f123,f415,f75])).

fof(f1993,plain,
    ( k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK1),k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f93,f108,f103,f415,f113,f123,f79])).

fof(f978,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_23
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f93,f147,f129,f230,f415,f88])).

fof(f1621,plain,
    ( k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k1_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3))) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3)),k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_23
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f93,f108,f103,f230,f230,f415,f79])).

fof(f946,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3)) = k3_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_23
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f230,f415,f86])).

fof(f5278,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3))) = k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK2),k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_23
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f93,f98,f103,f108,f415,f118,f230,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v11_lattices(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v11_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_lattices)).

fof(f98,plain,
    ( v10_lattices(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f5970,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)),k4_lattices(sK0,sK1,sK3)) != k4_lattices(sK0,k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK3)),k3_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_47
    | spl9_56 ),
    inference(backward_demodulation,[],[f5102,f5938])).

fof(f5938,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_47 ),
    inference(forward_demodulation,[],[f5839,f1270])).

fof(f1270,plain,
    ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1)
    | ~ spl9_47 ),
    inference(avatar_component_clause,[],[f1268])).

fof(f5839,plain,
    ( k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK3)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK1),k3_lattices(sK0,sK2,sK3))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7 ),
    inference(unit_resulting_resolution,[],[f93,f98,f103,f108,f118,f113,f123,f73])).

fof(f5102,plain,
    ( k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)),k3_lattices(sK0,sK1,sK3)) != k3_lattices(sK0,k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)),k4_lattices(sK0,sK1,sK3))
    | spl9_56 ),
    inference(avatar_component_clause,[],[f5100])).

fof(f8280,plain,
    ( spl9_65
    | spl9_1
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f356,f145,f127,f121,f116,f91,f8277])).

fof(f8277,plain,
    ( spl9_65
  <=> k4_lattices(sK0,sK2,sK3) = k2_lattices(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_65])])).

fof(f356,plain,
    ( k4_lattices(sK0,sK2,sK3) = k2_lattices(sK0,sK2,sK3)
    | spl9_1
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f93,f147,f129,f118,f123,f88])).

fof(f8275,plain,
    ( spl9_64
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f355,f145,f127,f121,f111,f91,f8272])).

fof(f8272,plain,
    ( spl9_64
  <=> k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).

fof(f8270,plain,
    ( spl9_63
    | spl9_1
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f352,f145,f127,f116,f111,f91,f8267])).

fof(f8267,plain,
    ( spl9_63
  <=> k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_63])])).

fof(f352,plain,
    ( k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2)
    | spl9_1
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f93,f147,f129,f113,f118,f88])).

fof(f8265,plain,
    ( spl9_62
    | spl9_1
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f326,f139,f133,f116,f111,f91,f8262])).

fof(f8262,plain,
    ( spl9_62
  <=> k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f326,plain,
    ( k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK2,sK1)
    | spl9_1
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(backward_demodulation,[],[f268,f311])).

fof(f311,plain,
    ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1)
    | spl9_1
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f113,f118,f86])).

fof(f268,plain,
    ( k3_lattices(sK0,sK2,sK1) = k1_lattices(sK0,sK2,sK1)
    | spl9_1
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f118,f113,f85])).

fof(f8260,plain,
    ( spl9_61
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f325,f157,f139,f133,f116,f111,f106,f91,f8257])).

fof(f8257,plain,
    ( spl9_61
  <=> sK2 = k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_61])])).

fof(f325,plain,
    ( sK2 = k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13 ),
    inference(backward_demodulation,[],[f286,f311])).

fof(f286,plain,
    ( sK2 = k2_lattices(sK0,sK2,k3_lattices(sK0,sK2,sK1))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13 ),
    inference(backward_demodulation,[],[f238,f268])).

fof(f238,plain,
    ( sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK1))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f93,f108,f159,f118,f113,f75])).

fof(f5129,plain,
    ( spl9_60
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f322,f139,f133,f121,f111,f91,f5126])).

fof(f5126,plain,
    ( spl9_60
  <=> k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).

fof(f322,plain,
    ( k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK3,sK1)
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(backward_demodulation,[],[f269,f314])).

fof(f5124,plain,
    ( spl9_59
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f321,f157,f139,f133,f121,f111,f106,f91,f5121])).

fof(f5121,plain,
    ( spl9_59
  <=> sK3 = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).

fof(f5119,plain,
    ( spl9_58
    | spl9_1
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f319,f139,f133,f121,f116,f91,f5116])).

fof(f5116,plain,
    ( spl9_58
  <=> k3_lattices(sK0,sK2,sK3) = k1_lattices(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).

fof(f319,plain,
    ( k3_lattices(sK0,sK2,sK3) = k1_lattices(sK0,sK3,sK2)
    | spl9_1
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(backward_demodulation,[],[f272,f315])).

fof(f315,plain,
    ( k3_lattices(sK0,sK2,sK3) = k3_lattices(sK0,sK3,sK2)
    | spl9_1
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f118,f123,f86])).

fof(f272,plain,
    ( k3_lattices(sK0,sK3,sK2) = k1_lattices(sK0,sK3,sK2)
    | spl9_1
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f123,f118,f85])).

fof(f5108,plain,
    ( spl9_57
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_27
    | ~ spl9_37
    | ~ spl9_41
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f2506,f1263,f1238,f408,f263,f145,f139,f133,f127,f116,f111,f106,f101,f91,f5105])).

fof(f5105,plain,
    ( spl9_57
  <=> sK1 = k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_57])])).

fof(f408,plain,
    ( spl9_37
  <=> m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f1238,plain,
    ( spl9_41
  <=> k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).

fof(f1263,plain,
    ( spl9_46
  <=> sK1 = k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f2506,plain,
    ( sK1 = k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK2))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_27
    | ~ spl9_37
    | ~ spl9_41
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f2505,f1265])).

fof(f1265,plain,
    ( sK1 = k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2))
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f1263])).

fof(f2505,plain,
    ( k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK2))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_27
    | ~ spl9_37
    | ~ spl9_41 ),
    inference(forward_demodulation,[],[f2504,f1240])).

fof(f1240,plain,
    ( k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2)
    | ~ spl9_41 ),
    inference(avatar_component_clause,[],[f1238])).

fof(f2504,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK2))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_27
    | ~ spl9_37 ),
    inference(forward_demodulation,[],[f2503,f786])).

fof(f786,plain,
    ( k1_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK2))
    | spl9_1
    | ~ spl9_5
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_37 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f113,f410,f85])).

fof(f410,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f408])).

fof(f2503,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK2))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f2502,f265])).

fof(f2502,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,sK1,sK1),k4_lattices(sK0,sK1,sK2))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(forward_demodulation,[],[f1914,f352])).

fof(f1914,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,sK1,sK1),k2_lattices(sK0,sK1,sK2))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f93,f108,f103,f113,f113,f118,f79])).

fof(f5103,plain,
    ( ~ spl9_56
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_23
    | ~ spl9_37
    | ~ spl9_39
    | spl9_40
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f2137,f1243,f1233,f418,f408,f228,f145,f139,f133,f127,f121,f116,f111,f106,f101,f91,f5100])).

fof(f418,plain,
    ( spl9_39
  <=> m1_subset_1(k4_lattices(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f1233,plain,
    ( spl9_40
  <=> k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)),k3_lattices(sK0,sK1,sK3)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)),k4_lattices(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f2137,plain,
    ( k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)),k3_lattices(sK0,sK1,sK3)) != k3_lattices(sK0,k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)),k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_23
    | ~ spl9_37
    | ~ spl9_39
    | spl9_40
    | ~ spl9_42 ),
    inference(backward_demodulation,[],[f1235,f2131])).

fof(f2131,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)) = k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_23
    | ~ spl9_37
    | ~ spl9_39
    | ~ spl9_42 ),
    inference(backward_demodulation,[],[f1099,f2130])).

fof(f2130,plain,
    ( k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_23
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f2129,f569])).

fof(f569,plain,
    ( k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)) = k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_23 ),
    inference(unit_resulting_resolution,[],[f93,f147,f129,f118,f230,f88])).

fof(f2129,plain,
    ( k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f2128,f1245])).

fof(f2128,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)) = k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(forward_demodulation,[],[f2127,f401])).

fof(f401,plain,
    ( k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK2,sK1)
    | spl9_1
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(backward_demodulation,[],[f350,f389])).

fof(f350,plain,
    ( k4_lattices(sK0,sK2,sK1) = k2_lattices(sK0,sK2,sK1)
    | spl9_1
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f93,f147,f129,f118,f113,f88])).

fof(f2127,plain,
    ( k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),k4_lattices(sK0,sK2,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(forward_demodulation,[],[f1996,f356])).

fof(f1996,plain,
    ( k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),k2_lattices(sK0,sK2,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7 ),
    inference(unit_resulting_resolution,[],[f93,f108,f103,f118,f113,f123,f79])).

fof(f1099,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3))
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_37
    | ~ spl9_39 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f410,f420,f85])).

fof(f420,plain,
    ( m1_subset_1(k4_lattices(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl9_39 ),
    inference(avatar_component_clause,[],[f418])).

fof(f1235,plain,
    ( k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)),k3_lattices(sK0,sK1,sK3)) != k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)),k4_lattices(sK0,sK1,sK3))
    | spl9_40 ),
    inference(avatar_component_clause,[],[f1233])).

fof(f5098,plain,
    ( spl9_55
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_26
    | ~ spl9_37
    | ~ spl9_41 ),
    inference(avatar_split_clause,[],[f2477,f1238,f408,f258,f157,f145,f139,f133,f127,f116,f111,f106,f101,f91,f5095])).

fof(f5095,plain,
    ( spl9_55
  <=> sK2 = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_55])])).

fof(f258,plain,
    ( spl9_26
  <=> sK2 = k2_lattices(sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f2477,plain,
    ( sK2 = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_26
    | ~ spl9_37
    | ~ spl9_41 ),
    inference(forward_demodulation,[],[f2476,f325])).

fof(f2476,plain,
    ( k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_26
    | ~ spl9_37
    | ~ spl9_41 ),
    inference(forward_demodulation,[],[f2475,f858])).

fof(f858,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2))
    | spl9_1
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_37 ),
    inference(forward_demodulation,[],[f780,f801])).

fof(f801,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2))
    | spl9_1
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_37 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f118,f410,f86])).

fof(f780,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)
    | spl9_1
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_37 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f118,f410,f85])).

fof(f2475,plain,
    ( k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_26
    | ~ spl9_41 ),
    inference(forward_demodulation,[],[f2474,f1240])).

fof(f2474,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f2473,f401])).

fof(f2473,plain,
    ( k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK2)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f1915,f260])).

fof(f260,plain,
    ( sK2 = k2_lattices(sK0,sK2,sK2)
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f258])).

fof(f1915,plain,
    ( k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),k2_lattices(sK0,sK2,sK2))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f93,f108,f103,f118,f113,f118,f79])).

fof(f5093,plain,
    ( spl9_54
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_27
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_45 ),
    inference(avatar_split_clause,[],[f2142,f1258,f1243,f413,f263,f145,f139,f133,f127,f121,f111,f106,f101,f91,f5090])).

fof(f5090,plain,
    ( spl9_54
  <=> sK1 = k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

fof(f5088,plain,
    ( spl9_53
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_25
    | ~ spl9_38
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f2114,f1243,f413,f253,f157,f145,f139,f133,f127,f121,f111,f106,f101,f91,f5085])).

fof(f5085,plain,
    ( spl9_53
  <=> sK3 = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_53])])).

fof(f5083,plain,
    ( spl9_52
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_26
    | ~ spl9_39
    | ~ spl9_43
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f2061,f1253,f1248,f418,f258,f145,f139,f133,f127,f121,f116,f106,f101,f91,f5080])).

fof(f5080,plain,
    ( spl9_52
  <=> sK2 = k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).

fof(f1248,plain,
    ( spl9_43
  <=> k3_lattices(sK0,sK2,sK3) = k1_lattices(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).

fof(f1253,plain,
    ( spl9_44
  <=> sK2 = k2_lattices(sK0,sK2,k3_lattices(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f2061,plain,
    ( sK2 = k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_26
    | ~ spl9_39
    | ~ spl9_43
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f2060,f1255])).

fof(f1255,plain,
    ( sK2 = k2_lattices(sK0,sK2,k3_lattices(sK0,sK2,sK3))
    | ~ spl9_44 ),
    inference(avatar_component_clause,[],[f1253])).

fof(f2060,plain,
    ( k2_lattices(sK0,sK2,k3_lattices(sK0,sK2,sK3)) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_26
    | ~ spl9_39
    | ~ spl9_43 ),
    inference(forward_demodulation,[],[f2059,f1250])).

fof(f1250,plain,
    ( k3_lattices(sK0,sK2,sK3) = k1_lattices(sK0,sK2,sK3)
    | ~ spl9_43 ),
    inference(avatar_component_clause,[],[f1248])).

fof(f2059,plain,
    ( k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK3)) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_26
    | ~ spl9_39 ),
    inference(forward_demodulation,[],[f2058,f1103])).

fof(f1103,plain,
    ( k1_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK3)) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK3))
    | spl9_1
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_39 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f118,f420,f85])).

fof(f2058,plain,
    ( k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f2057,f260])).

fof(f2057,plain,
    ( k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK2),k4_lattices(sK0,sK2,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(forward_demodulation,[],[f2005,f356])).

fof(f2005,plain,
    ( k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK2),k2_lattices(sK0,sK2,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7 ),
    inference(unit_resulting_resolution,[],[f93,f108,f103,f118,f118,f123,f79])).

fof(f5078,plain,
    ( spl9_51
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_39
    | ~ spl9_43
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f2045,f1283,f1248,f418,f253,f145,f139,f133,f127,f121,f116,f106,f101,f91,f5075])).

fof(f5075,plain,
    ( spl9_51
  <=> sK3 = k3_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).

fof(f1283,plain,
    ( spl9_50
  <=> sK3 = k2_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).

fof(f2045,plain,
    ( sK3 = k3_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_39
    | ~ spl9_43
    | ~ spl9_50 ),
    inference(forward_demodulation,[],[f2044,f1285])).

fof(f1285,plain,
    ( sK3 = k2_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3))
    | ~ spl9_50 ),
    inference(avatar_component_clause,[],[f1283])).

fof(f2044,plain,
    ( k2_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3)) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_39
    | ~ spl9_43 ),
    inference(forward_demodulation,[],[f2043,f1193])).

fof(f1193,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),sK3) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK3))
    | spl9_1
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_39 ),
    inference(forward_demodulation,[],[f1095,f1122])).

fof(f1122,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK2,sK3),sK3) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK3))
    | spl9_1
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_39 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f123,f420,f86])).

fof(f1095,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),sK3) = k3_lattices(sK0,k4_lattices(sK0,sK2,sK3),sK3)
    | spl9_1
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_39 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f123,f420,f85])).

fof(f2043,plain,
    ( k2_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),sK3)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_43 ),
    inference(forward_demodulation,[],[f2042,f1250])).

fof(f2042,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),sK3) = k2_lattices(sK0,sK3,k1_lattices(sK0,sK2,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_25 ),
    inference(forward_demodulation,[],[f2041,f396])).

fof(f2041,plain,
    ( k2_lattices(sK0,sK3,k1_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),sK3)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_25 ),
    inference(forward_demodulation,[],[f2006,f255])).

fof(f2006,plain,
    ( k2_lattices(sK0,sK3,k1_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k2_lattices(sK0,sK3,sK3))
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7 ),
    inference(unit_resulting_resolution,[],[f93,f108,f103,f123,f118,f123,f79])).

fof(f1286,plain,
    ( spl9_50
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f318,f157,f139,f133,f121,f116,f106,f91,f1283])).

fof(f318,plain,
    ( sK3 = k2_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13 ),
    inference(backward_demodulation,[],[f281,f315])).

fof(f281,plain,
    ( sK3 = k2_lattices(sK0,sK3,k3_lattices(sK0,sK3,sK2))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13 ),
    inference(backward_demodulation,[],[f242,f272])).

fof(f242,plain,
    ( sK3 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,sK2))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f93,f108,f159,f123,f118,f75])).

fof(f1281,plain,
    ( spl9_49
    | spl9_1
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f315,f139,f133,f121,f116,f91,f1278])).

fof(f1278,plain,
    ( spl9_49
  <=> k3_lattices(sK0,sK2,sK3) = k3_lattices(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f1276,plain,
    ( spl9_48
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f314,f139,f133,f121,f111,f91,f1273])).

fof(f1273,plain,
    ( spl9_48
  <=> k3_lattices(sK0,sK3,sK1) = k3_lattices(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f1271,plain,
    ( spl9_47
    | spl9_1
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f311,f139,f133,f116,f111,f91,f1268])).

fof(f1266,plain,
    ( spl9_46
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f284,f157,f139,f133,f116,f111,f106,f91,f1263])).

fof(f284,plain,
    ( sK1 = k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13 ),
    inference(backward_demodulation,[],[f240,f270])).

fof(f270,plain,
    ( k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2)
    | spl9_1
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f113,f118,f85])).

fof(f240,plain,
    ( sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f93,f108,f159,f113,f118,f75])).

fof(f1261,plain,
    ( spl9_45
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f280,f157,f139,f133,f121,f111,f106,f91,f1258])).

fof(f280,plain,
    ( sK1 = k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13 ),
    inference(backward_demodulation,[],[f243,f273])).

fof(f273,plain,
    ( k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK1,sK3)
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f113,f123,f85])).

fof(f243,plain,
    ( sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f93,f108,f159,f113,f123,f75])).

fof(f1256,plain,
    ( spl9_44
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f279,f157,f139,f133,f121,f116,f106,f91,f1253])).

fof(f279,plain,
    ( sK2 = k2_lattices(sK0,sK2,k3_lattices(sK0,sK2,sK3))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13 ),
    inference(backward_demodulation,[],[f244,f274])).

fof(f274,plain,
    ( k3_lattices(sK0,sK2,sK3) = k1_lattices(sK0,sK2,sK3)
    | spl9_1
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f118,f123,f85])).

fof(f244,plain,
    ( sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK3))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f93,f108,f159,f118,f123,f75])).

fof(f1251,plain,
    ( spl9_43
    | spl9_1
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f274,f139,f133,f121,f116,f91,f1248])).

fof(f1246,plain,
    ( spl9_42
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f273,f139,f133,f121,f111,f91,f1243])).

fof(f1241,plain,
    ( spl9_41
    | spl9_1
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f270,f139,f133,f116,f111,f91,f1238])).

fof(f1236,plain,
    ( ~ spl9_40
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f400,f145,f139,f133,f127,f121,f111,f91,f1233])).

fof(f400,plain,
    ( k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)),k3_lattices(sK0,sK1,sK3)) != k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)),k4_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11 ),
    inference(backward_demodulation,[],[f324,f392])).

fof(f324,plain,
    ( k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)),k4_lattices(sK0,sK3,sK1)) != k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)),k3_lattices(sK0,sK1,sK3))
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(backward_demodulation,[],[f65,f314])).

fof(f65,plain,(
    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)),k3_lattices(sK0,sK3,sK1)) != k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)),k4_lattices(sK0,sK3,sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)),k3_lattices(sK0,sK3,sK1)) != k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)),k4_lattices(sK0,sK3,sK1))
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v11_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f45,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1)) != k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1))
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v11_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,X2),k3_lattices(sK0,X2,X3)),k3_lattices(sK0,X3,X1)) != k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,X2),k4_lattices(sK0,X2,X3)),k4_lattices(sK0,X3,X1))
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v11_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,X2),k3_lattices(sK0,X2,X3)),k3_lattices(sK0,X3,X1)) != k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,X2),k4_lattices(sK0,X2,X3)),k4_lattices(sK0,X3,X1))
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,X2),k3_lattices(sK0,X2,X3)),k3_lattices(sK0,X3,sK1)) != k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,X2),k4_lattices(sK0,X2,X3)),k4_lattices(sK0,X3,sK1))
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,X2),k3_lattices(sK0,X2,X3)),k3_lattices(sK0,X3,sK1)) != k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,X2),k4_lattices(sK0,X2,X3)),k4_lattices(sK0,X3,sK1))
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,X3)),k3_lattices(sK0,X3,sK1)) != k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,X3)),k4_lattices(sK0,X3,sK1))
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X3] :
        ( k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,X3)),k3_lattices(sK0,X3,sK1)) != k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,X3)),k4_lattices(sK0,X3,sK1))
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)),k3_lattices(sK0,sK3,sK1)) != k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)),k4_lattices(sK0,sK3,sK1))
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1)) != k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1))
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v11_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1)) != k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1))
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v11_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v11_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1)) = k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v11_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1)) = k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattices)).

fof(f421,plain,
    ( spl9_39
    | spl9_1
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f210,f145,f127,f121,f116,f91,f418])).

fof(f210,plain,
    ( m1_subset_1(k4_lattices(sK0,sK2,sK3),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f93,f147,f129,f118,f123,f87])).

fof(f416,plain,
    ( spl9_38
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f209,f145,f127,f121,f111,f91,f413])).

fof(f209,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK3),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f93,f147,f129,f113,f123,f87])).

fof(f411,plain,
    ( spl9_37
    | spl9_1
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f206,f145,f127,f116,f111,f91,f408])).

fof(f206,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f93,f147,f129,f113,f118,f87])).

fof(f381,plain,
    ( spl9_36
    | spl9_1
    | ~ spl9_5
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_27 ),
    inference(avatar_split_clause,[],[f363,f263,f145,f127,f111,f91,f378])).

fof(f378,plain,
    ( spl9_36
  <=> sK1 = k4_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f363,plain,
    ( sK1 = k4_lattices(sK0,sK1,sK1)
    | spl9_1
    | ~ spl9_5
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f349,f265])).

fof(f349,plain,
    ( k4_lattices(sK0,sK1,sK1) = k2_lattices(sK0,sK1,sK1)
    | spl9_1
    | ~ spl9_5
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f93,f147,f129,f113,f113,f88])).

fof(f376,plain,
    ( spl9_35
    | spl9_1
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f361,f258,f145,f127,f116,f91,f373])).

fof(f373,plain,
    ( spl9_35
  <=> sK2 = k4_lattices(sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f361,plain,
    ( sK2 = k4_lattices(sK0,sK2,sK2)
    | spl9_1
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f353,f260])).

fof(f353,plain,
    ( k4_lattices(sK0,sK2,sK2) = k2_lattices(sK0,sK2,sK2)
    | spl9_1
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f93,f147,f129,f118,f118,f88])).

fof(f371,plain,
    ( spl9_34
    | spl9_1
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f359,f253,f145,f127,f121,f91,f368])).

fof(f368,plain,
    ( spl9_34
  <=> sK3 = k4_lattices(sK0,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f359,plain,
    ( sK3 = k4_lattices(sK0,sK3,sK3)
    | spl9_1
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_25 ),
    inference(forward_demodulation,[],[f357,f255])).

fof(f357,plain,
    ( k4_lattices(sK0,sK3,sK3) = k2_lattices(sK0,sK3,sK3)
    | spl9_1
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f93,f147,f129,f123,f123,f88])).

fof(f348,plain,
    ( spl9_33
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f205,f145,f127,f121,f111,f91,f345])).

fof(f345,plain,
    ( spl9_33
  <=> m1_subset_1(k4_lattices(sK0,sK3,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f205,plain,
    ( m1_subset_1(k4_lattices(sK0,sK3,sK1),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f93,f147,f129,f123,f113,f87])).

fof(f343,plain,
    ( spl9_32
    | spl9_1
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f204,f145,f127,f116,f111,f91,f340])).

fof(f340,plain,
    ( spl9_32
  <=> m1_subset_1(k4_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f204,plain,
    ( m1_subset_1(k4_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f93,f147,f129,f118,f113,f87])).

fof(f338,plain,
    ( spl9_31
    | spl9_1
    | ~ spl9_5
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f203,f145,f127,f111,f91,f335])).

fof(f335,plain,
    ( spl9_31
  <=> m1_subset_1(k4_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f203,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_5
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f93,f147,f129,f113,f113,f87])).

fof(f305,plain,
    ( spl9_30
    | spl9_1
    | ~ spl9_5
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f287,f165,f139,f133,f111,f91,f302])).

fof(f302,plain,
    ( spl9_30
  <=> sK1 = k3_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f165,plain,
    ( spl9_14
  <=> sK1 = k1_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f287,plain,
    ( sK1 = k3_lattices(sK0,sK1,sK1)
    | spl9_1
    | ~ spl9_5
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_14 ),
    inference(forward_demodulation,[],[f267,f167])).

fof(f167,plain,
    ( sK1 = k1_lattices(sK0,sK1,sK1)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f165])).

fof(f267,plain,
    ( k1_lattices(sK0,sK1,sK1) = k3_lattices(sK0,sK1,sK1)
    | spl9_1
    | ~ spl9_5
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f113,f113,f85])).

fof(f300,plain,
    ( spl9_29
    | spl9_1
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f282,f170,f139,f133,f116,f91,f297])).

fof(f297,plain,
    ( spl9_29
  <=> sK2 = k3_lattices(sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f170,plain,
    ( spl9_15
  <=> sK2 = k1_lattices(sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f282,plain,
    ( sK2 = k3_lattices(sK0,sK2,sK2)
    | spl9_1
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_15 ),
    inference(forward_demodulation,[],[f271,f172])).

fof(f172,plain,
    ( sK2 = k1_lattices(sK0,sK2,sK2)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f170])).

fof(f271,plain,
    ( k1_lattices(sK0,sK2,sK2) = k3_lattices(sK0,sK2,sK2)
    | spl9_1
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f118,f118,f85])).

fof(f295,plain,
    ( spl9_28
    | spl9_1
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f277,f175,f139,f133,f121,f91,f292])).

fof(f292,plain,
    ( spl9_28
  <=> sK3 = k3_lattices(sK0,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f175,plain,
    ( spl9_16
  <=> sK3 = k1_lattices(sK0,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f277,plain,
    ( sK3 = k3_lattices(sK0,sK3,sK3)
    | spl9_1
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_16 ),
    inference(forward_demodulation,[],[f275,f177])).

fof(f177,plain,
    ( sK3 = k1_lattices(sK0,sK3,sK3)
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f175])).

fof(f275,plain,
    ( k1_lattices(sK0,sK3,sK3) = k3_lattices(sK0,sK3,sK3)
    | spl9_1
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f123,f123,f85])).

fof(f266,plain,
    ( spl9_27
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_13
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f249,f165,f157,f111,f106,f91,f263])).

fof(f249,plain,
    ( sK1 = k2_lattices(sK0,sK1,sK1)
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_13
    | ~ spl9_14 ),
    inference(forward_demodulation,[],[f237,f167])).

fof(f237,plain,
    ( sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f93,f108,f159,f113,f113,f75])).

fof(f261,plain,
    ( spl9_26
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f248,f170,f157,f116,f106,f91,f258])).

fof(f248,plain,
    ( sK2 = k2_lattices(sK0,sK2,sK2)
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_13
    | ~ spl9_15 ),
    inference(forward_demodulation,[],[f241,f172])).

fof(f241,plain,
    ( sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK2))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f93,f108,f159,f118,f118,f75])).

fof(f256,plain,
    ( spl9_25
    | spl9_1
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_13
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f247,f175,f157,f121,f106,f91,f253])).

fof(f247,plain,
    ( sK3 = k2_lattices(sK0,sK3,sK3)
    | spl9_1
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_13
    | ~ spl9_16 ),
    inference(forward_demodulation,[],[f245,f177])).

fof(f245,plain,
    ( sK3 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,sK3))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f93,f108,f159,f123,f123,f75])).

fof(f236,plain,
    ( spl9_24
    | spl9_1
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f186,f139,f133,f121,f116,f91,f233])).

fof(f233,plain,
    ( spl9_24
  <=> m1_subset_1(k3_lattices(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f186,plain,
    ( m1_subset_1(k3_lattices(sK0,sK2,sK3),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f118,f123,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_lattices)).

fof(f231,plain,
    ( spl9_23
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f185,f139,f133,f121,f111,f91,f228])).

fof(f185,plain,
    ( m1_subset_1(k3_lattices(sK0,sK1,sK3),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f113,f123,f84])).

fof(f226,plain,
    ( spl9_22
    | spl9_1
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f184,f139,f133,f121,f116,f91,f223])).

fof(f223,plain,
    ( spl9_22
  <=> m1_subset_1(k3_lattices(sK0,sK3,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f184,plain,
    ( m1_subset_1(k3_lattices(sK0,sK3,sK2),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f123,f118,f84])).

fof(f221,plain,
    ( spl9_21
    | spl9_1
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f183,f139,f133,f116,f91,f218])).

fof(f218,plain,
    ( spl9_21
  <=> m1_subset_1(k3_lattices(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f183,plain,
    ( m1_subset_1(k3_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f118,f118,f84])).

fof(f216,plain,
    ( spl9_20
    | spl9_1
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f182,f139,f133,f116,f111,f91,f213])).

fof(f213,plain,
    ( spl9_20
  <=> m1_subset_1(k3_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f182,plain,
    ( m1_subset_1(k3_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f113,f118,f84])).

fof(f202,plain,
    ( spl9_19
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f181,f139,f133,f121,f111,f91,f199])).

fof(f199,plain,
    ( spl9_19
  <=> m1_subset_1(k3_lattices(sK0,sK3,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f181,plain,
    ( m1_subset_1(k3_lattices(sK0,sK3,sK1),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f123,f113,f84])).

fof(f197,plain,
    ( spl9_18
    | spl9_1
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f180,f139,f133,f116,f111,f91,f194])).

fof(f194,plain,
    ( spl9_18
  <=> m1_subset_1(k3_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f180,plain,
    ( m1_subset_1(k3_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f118,f113,f84])).

fof(f192,plain,
    ( spl9_17
    | spl9_1
    | ~ spl9_5
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f179,f139,f133,f111,f91,f189])).

fof(f189,plain,
    ( spl9_17
  <=> m1_subset_1(k3_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f179,plain,
    ( m1_subset_1(k3_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_5
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f93,f141,f135,f113,f113,f84])).

fof(f178,plain,
    ( spl9_16
    | spl9_1
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f163,f157,f151,f145,f121,f106,f91,f175])).

fof(f163,plain,
    ( sK3 = k1_lattices(sK0,sK3,sK3)
    | spl9_1
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f93,f147,f153,f159,f108,f123,f74])).

fof(f173,plain,
    ( spl9_15
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f162,f157,f151,f145,f116,f106,f91,f170])).

fof(f162,plain,
    ( sK2 = k1_lattices(sK0,sK2,sK2)
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f93,f147,f153,f159,f108,f118,f74])).

fof(f168,plain,
    ( spl9_14
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f161,f157,f151,f145,f111,f106,f91,f165])).

fof(f161,plain,
    ( sK1 = k1_lattices(sK0,sK1,sK1)
    | spl9_1
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f93,f147,f153,f159,f108,f113,f74])).

fof(f160,plain,
    ( spl9_13
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f155,f106,f96,f91,f157])).

fof(f155,plain,
    ( v9_lattices(sK0)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f108,f93,f98,f72])).

fof(f72,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f154,plain,
    ( spl9_12
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f149,f106,f96,f91,f151])).

fof(f149,plain,
    ( v8_lattices(sK0)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f108,f93,f98,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f148,plain,
    ( spl9_11
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f143,f106,f96,f91,f145])).

fof(f143,plain,
    ( v6_lattices(sK0)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f108,f93,f98,f70])).

fof(f70,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f142,plain,
    ( spl9_10
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f137,f106,f96,f91,f139])).

fof(f137,plain,
    ( v4_lattices(sK0)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f108,f93,f98,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f136,plain,
    ( spl9_9
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f131,f106,f133])).

fof(f131,plain,
    ( l2_lattices(sK0)
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f108,f67])).

fof(f67,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f130,plain,
    ( spl9_8
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f125,f106,f127])).

fof(f125,plain,
    ( l1_lattices(sK0)
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f108,f66])).

fof(f66,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f124,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f64,f121])).

fof(f64,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f119,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f63,f116])).

fof(f63,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f114,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f62,f111])).

fof(f62,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f109,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f61,f106])).

fof(f61,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f104,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f60,f101])).

fof(f60,plain,(
    v11_lattices(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f99,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f59,f96])).

fof(f59,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f94,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f58,f91])).

fof(f58,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:21:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (9762)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.49  % (9747)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.49  % (9751)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.49  % (9757)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.49  % (9756)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.50  % (9748)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (9746)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (9765)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.50  % (9759)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.50  % (9758)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (9750)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (9767)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (9749)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (9763)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.51  % (9749)Refutation not found, incomplete strategy% (9749)------------------------------
% 0.21/0.51  % (9749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9749)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (9749)Memory used [KB]: 10618
% 0.21/0.51  % (9749)Time elapsed: 0.095 s
% 0.21/0.51  % (9749)------------------------------
% 0.21/0.51  % (9749)------------------------------
% 0.21/0.51  % (9761)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (9766)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.52  % (9754)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.52  % (9769)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.52  % (9755)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.53  % (9754)Refutation not found, incomplete strategy% (9754)------------------------------
% 0.21/0.53  % (9754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (9754)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (9754)Memory used [KB]: 10874
% 0.21/0.53  % (9754)Time elapsed: 0.114 s
% 0.21/0.53  % (9754)------------------------------
% 0.21/0.53  % (9754)------------------------------
% 0.21/0.53  % (9768)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.53  % (9753)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (9752)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.53  % (9764)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.53  % (9760)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.54  % (9769)Refutation not found, incomplete strategy% (9769)------------------------------
% 0.21/0.54  % (9769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (9769)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (9769)Memory used [KB]: 10618
% 0.21/0.54  % (9769)Time elapsed: 0.103 s
% 0.21/0.54  % (9769)------------------------------
% 0.21/0.54  % (9769)------------------------------
% 0.21/0.54  % (9756)Refutation not found, incomplete strategy% (9756)------------------------------
% 0.21/0.54  % (9756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (9756)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (9756)Memory used [KB]: 11257
% 0.21/0.54  % (9756)Time elapsed: 0.117 s
% 0.21/0.54  % (9756)------------------------------
% 0.21/0.54  % (9756)------------------------------
% 0.21/0.54  % (9762)Refutation not found, incomplete strategy% (9762)------------------------------
% 0.21/0.54  % (9762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (9762)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (9762)Memory used [KB]: 3326
% 0.21/0.54  % (9762)Time elapsed: 0.090 s
% 0.21/0.54  % (9762)------------------------------
% 0.21/0.54  % (9762)------------------------------
% 1.66/0.57  % (9753)Refutation not found, incomplete strategy% (9753)------------------------------
% 1.66/0.57  % (9753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.57  % (9753)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.57  
% 1.66/0.57  % (9753)Memory used [KB]: 8187
% 1.66/0.57  % (9753)Time elapsed: 0.146 s
% 1.66/0.57  % (9753)------------------------------
% 1.66/0.57  % (9753)------------------------------
% 2.10/0.65  % (9768)Refutation not found, incomplete strategy% (9768)------------------------------
% 2.10/0.65  % (9768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.65  % (9768)Termination reason: Refutation not found, incomplete strategy
% 2.10/0.65  
% 2.10/0.65  % (9768)Memory used [KB]: 1663
% 2.10/0.65  % (9768)Time elapsed: 0.205 s
% 2.10/0.65  % (9768)------------------------------
% 2.10/0.65  % (9768)------------------------------
% 2.93/0.75  % (9764)Refutation not found, incomplete strategy% (9764)------------------------------
% 2.93/0.75  % (9764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.93/0.75  % (9764)Termination reason: Refutation not found, incomplete strategy
% 2.93/0.75  
% 2.93/0.75  % (9764)Memory used [KB]: 6524
% 2.93/0.75  % (9764)Time elapsed: 0.332 s
% 2.93/0.75  % (9764)------------------------------
% 2.93/0.75  % (9764)------------------------------
% 3.27/0.83  % (9746)Refutation found. Thanks to Tanya!
% 3.27/0.83  % SZS status Theorem for theBenchmark
% 3.27/0.83  % SZS output start Proof for theBenchmark
% 3.27/0.83  fof(f8317,plain,(
% 3.27/0.83    $false),
% 3.27/0.83    inference(avatar_sat_refutation,[],[f94,f99,f104,f109,f114,f119,f124,f130,f136,f142,f148,f154,f160,f168,f173,f178,f192,f197,f202,f216,f221,f226,f231,f236,f256,f261,f266,f295,f300,f305,f338,f343,f348,f371,f376,f381,f411,f416,f421,f1236,f1241,f1246,f1251,f1256,f1261,f1266,f1271,f1276,f1281,f1286,f5078,f5083,f5088,f5093,f5098,f5103,f5108,f5119,f5124,f5129,f8260,f8265,f8270,f8275,f8280,f8285,f8290,f8295,f8300,f8305,f8310,f8314,f8316])).
% 3.85/0.84  fof(f8316,plain,(
% 3.85/0.84    spl9_1 | ~spl9_6 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_23 | ~spl9_38 | spl9_66),
% 3.85/0.84    inference(avatar_contradiction_clause,[],[f8315])).
% 3.85/0.84  fof(f8315,plain,(
% 3.85/0.84    $false | (spl9_1 | ~spl9_6 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_23 | ~spl9_38 | spl9_66)),
% 3.85/0.84    inference(subsumption_resolution,[],[f8311,f559])).
% 3.85/0.84  fof(f559,plain,(
% 3.85/0.84    m1_subset_1(k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)),u1_struct_0(sK0)) | (spl9_1 | ~spl9_6 | ~spl9_8 | ~spl9_11 | ~spl9_23)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f147,f129,f118,f230,f87])).
% 3.85/0.84  fof(f87,plain,(
% 3.85/0.84    ( ! [X2,X0,X1] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.85/0.84    inference(cnf_transformation,[],[f37])).
% 3.85/0.84  fof(f37,plain,(
% 3.85/0.84    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.85/0.84    inference(flattening,[],[f36])).
% 3.85/0.84  fof(f36,plain,(
% 3.85/0.84    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.85/0.84    inference(ennf_transformation,[],[f7])).
% 3.85/0.84  fof(f7,axiom,(
% 3.85/0.84    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 3.85/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).
% 3.85/0.84  fof(f230,plain,(
% 3.85/0.84    m1_subset_1(k3_lattices(sK0,sK1,sK3),u1_struct_0(sK0)) | ~spl9_23),
% 3.85/0.84    inference(avatar_component_clause,[],[f228])).
% 3.85/0.84  fof(f228,plain,(
% 3.85/0.84    spl9_23 <=> m1_subset_1(k3_lattices(sK0,sK1,sK3),u1_struct_0(sK0))),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 3.85/0.84  fof(f118,plain,(
% 3.85/0.84    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl9_6),
% 3.85/0.84    inference(avatar_component_clause,[],[f116])).
% 3.85/0.84  fof(f116,plain,(
% 3.85/0.84    spl9_6 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 3.85/0.84  fof(f129,plain,(
% 3.85/0.84    l1_lattices(sK0) | ~spl9_8),
% 3.85/0.84    inference(avatar_component_clause,[],[f127])).
% 3.85/0.84  fof(f127,plain,(
% 3.85/0.84    spl9_8 <=> l1_lattices(sK0)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 3.85/0.84  fof(f147,plain,(
% 3.85/0.84    v6_lattices(sK0) | ~spl9_11),
% 3.85/0.84    inference(avatar_component_clause,[],[f145])).
% 3.85/0.84  fof(f145,plain,(
% 3.85/0.84    spl9_11 <=> v6_lattices(sK0)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 3.85/0.84  fof(f93,plain,(
% 3.85/0.84    ~v2_struct_0(sK0) | spl9_1),
% 3.85/0.84    inference(avatar_component_clause,[],[f91])).
% 3.85/0.84  fof(f91,plain,(
% 3.85/0.84    spl9_1 <=> v2_struct_0(sK0)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 3.85/0.84  fof(f8311,plain,(
% 3.85/0.84    ~m1_subset_1(k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)),u1_struct_0(sK0)) | (spl9_1 | ~spl9_9 | ~spl9_10 | ~spl9_38 | spl9_66)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f141,f135,f415,f8284,f86])).
% 3.85/0.84  fof(f86,plain,(
% 3.85/0.84    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)) )),
% 3.85/0.84    inference(cnf_transformation,[],[f35])).
% 3.85/0.84  fof(f35,plain,(
% 3.85/0.84    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 3.85/0.84    inference(flattening,[],[f34])).
% 3.85/0.84  fof(f34,plain,(
% 3.85/0.84    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 3.85/0.84    inference(ennf_transformation,[],[f2])).
% 3.85/0.84  fof(f2,axiom,(
% 3.85/0.84    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 3.85/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).
% 3.85/0.84  fof(f8284,plain,(
% 3.85/0.84    k3_lattices(sK0,k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)),k4_lattices(sK0,sK1,sK3)) != k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3))) | spl9_66),
% 3.85/0.84    inference(avatar_component_clause,[],[f8282])).
% 3.85/0.84  fof(f8282,plain,(
% 3.85/0.84    spl9_66 <=> k3_lattices(sK0,k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)),k4_lattices(sK0,sK1,sK3)) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)))),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).
% 3.85/0.84  fof(f415,plain,(
% 3.85/0.84    m1_subset_1(k4_lattices(sK0,sK1,sK3),u1_struct_0(sK0)) | ~spl9_38),
% 3.85/0.84    inference(avatar_component_clause,[],[f413])).
% 3.85/0.84  fof(f413,plain,(
% 3.85/0.84    spl9_38 <=> m1_subset_1(k4_lattices(sK0,sK1,sK3),u1_struct_0(sK0))),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).
% 3.85/0.84  fof(f135,plain,(
% 3.85/0.84    l2_lattices(sK0) | ~spl9_9),
% 3.85/0.84    inference(avatar_component_clause,[],[f133])).
% 3.85/0.84  fof(f133,plain,(
% 3.85/0.84    spl9_9 <=> l2_lattices(sK0)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 3.85/0.84  fof(f141,plain,(
% 3.85/0.84    v4_lattices(sK0) | ~spl9_10),
% 3.85/0.84    inference(avatar_component_clause,[],[f139])).
% 3.85/0.84  fof(f139,plain,(
% 3.85/0.84    spl9_10 <=> v4_lattices(sK0)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 3.85/0.84  fof(f8314,plain,(
% 3.85/0.84    spl9_1 | ~spl9_6 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_23 | ~spl9_38 | spl9_66),
% 3.85/0.84    inference(avatar_contradiction_clause,[],[f8313])).
% 3.85/0.84  fof(f8313,plain,(
% 3.85/0.84    $false | (spl9_1 | ~spl9_6 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_23 | ~spl9_38 | spl9_66)),
% 3.85/0.84    inference(subsumption_resolution,[],[f8312,f559])).
% 3.85/0.84  fof(f8312,plain,(
% 3.85/0.84    ~m1_subset_1(k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)),u1_struct_0(sK0)) | (spl9_1 | ~spl9_9 | ~spl9_10 | ~spl9_38 | spl9_66)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f141,f135,f415,f8284,f86])).
% 3.85/0.84  fof(f8310,plain,(
% 3.85/0.84    spl9_71 | spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_11),
% 3.85/0.84    inference(avatar_split_clause,[],[f398,f145,f127,f121,f111,f91,f8307])).
% 3.85/0.84  fof(f8307,plain,(
% 3.85/0.84    spl9_71 <=> k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK3,sK1)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_71])])).
% 3.85/0.84  fof(f111,plain,(
% 3.85/0.84    spl9_5 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 3.85/0.84  fof(f121,plain,(
% 3.85/0.84    spl9_7 <=> m1_subset_1(sK3,u1_struct_0(sK0))),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 3.85/0.84  fof(f398,plain,(
% 3.85/0.84    k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK3,sK1) | (spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_11)),
% 3.85/0.84    inference(backward_demodulation,[],[f351,f392])).
% 3.85/0.84  fof(f392,plain,(
% 3.85/0.84    k4_lattices(sK0,sK3,sK1) = k4_lattices(sK0,sK1,sK3) | (spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_11)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f147,f129,f113,f123,f89])).
% 3.85/0.84  fof(f89,plain,(
% 3.85/0.84    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)) )),
% 3.85/0.84    inference(cnf_transformation,[],[f41])).
% 3.85/0.84  fof(f41,plain,(
% 3.85/0.84    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.85/0.84    inference(flattening,[],[f40])).
% 3.85/0.84  fof(f40,plain,(
% 3.85/0.84    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.85/0.84    inference(ennf_transformation,[],[f3])).
% 3.85/0.84  fof(f3,axiom,(
% 3.85/0.84    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 3.85/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).
% 3.85/0.84  fof(f123,plain,(
% 3.85/0.84    m1_subset_1(sK3,u1_struct_0(sK0)) | ~spl9_7),
% 3.85/0.84    inference(avatar_component_clause,[],[f121])).
% 3.85/0.84  fof(f113,plain,(
% 3.85/0.84    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl9_5),
% 3.85/0.84    inference(avatar_component_clause,[],[f111])).
% 3.85/0.84  fof(f351,plain,(
% 3.85/0.84    k4_lattices(sK0,sK3,sK1) = k2_lattices(sK0,sK3,sK1) | (spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_11)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f147,f129,f123,f113,f88])).
% 3.85/0.84  fof(f88,plain,(
% 3.85/0.84    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)) )),
% 3.85/0.84    inference(cnf_transformation,[],[f39])).
% 3.85/0.84  fof(f39,plain,(
% 3.85/0.84    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.85/0.84    inference(flattening,[],[f38])).
% 3.85/0.84  fof(f38,plain,(
% 3.85/0.84    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.85/0.84    inference(ennf_transformation,[],[f10])).
% 3.85/0.84  fof(f10,axiom,(
% 3.85/0.84    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 3.85/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 3.85/0.84  fof(f8305,plain,(
% 3.85/0.84    spl9_70 | spl9_1 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11),
% 3.85/0.84    inference(avatar_split_clause,[],[f396,f145,f127,f121,f116,f91,f8302])).
% 3.85/0.84  fof(f8302,plain,(
% 3.85/0.84    spl9_70 <=> k4_lattices(sK0,sK2,sK3) = k2_lattices(sK0,sK3,sK2)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_70])])).
% 3.85/0.84  fof(f396,plain,(
% 3.85/0.84    k4_lattices(sK0,sK2,sK3) = k2_lattices(sK0,sK3,sK2) | (spl9_1 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11)),
% 3.85/0.84    inference(backward_demodulation,[],[f354,f393])).
% 3.85/0.84  fof(f393,plain,(
% 3.85/0.84    k4_lattices(sK0,sK2,sK3) = k4_lattices(sK0,sK3,sK2) | (spl9_1 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f147,f129,f118,f123,f89])).
% 3.85/0.84  fof(f354,plain,(
% 3.85/0.84    k4_lattices(sK0,sK3,sK2) = k2_lattices(sK0,sK3,sK2) | (spl9_1 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f147,f129,f123,f118,f88])).
% 3.85/0.84  fof(f8300,plain,(
% 3.85/0.84    spl9_69 | spl9_1 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11),
% 3.85/0.84    inference(avatar_split_clause,[],[f393,f145,f127,f121,f116,f91,f8297])).
% 3.85/0.84  fof(f8297,plain,(
% 3.85/0.84    spl9_69 <=> k4_lattices(sK0,sK2,sK3) = k4_lattices(sK0,sK3,sK2)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_69])])).
% 3.85/0.84  fof(f8295,plain,(
% 3.85/0.84    spl9_68 | spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_11),
% 3.85/0.84    inference(avatar_split_clause,[],[f392,f145,f127,f121,f111,f91,f8292])).
% 3.85/0.84  fof(f8292,plain,(
% 3.85/0.84    spl9_68 <=> k4_lattices(sK0,sK3,sK1) = k4_lattices(sK0,sK1,sK3)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).
% 3.85/0.84  fof(f8290,plain,(
% 3.85/0.84    spl9_67 | spl9_1 | ~spl9_5 | ~spl9_6 | ~spl9_8 | ~spl9_11),
% 3.85/0.84    inference(avatar_split_clause,[],[f389,f145,f127,f116,f111,f91,f8287])).
% 3.85/0.84  fof(f8287,plain,(
% 3.85/0.84    spl9_67 <=> k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_67])])).
% 3.85/0.84  fof(f389,plain,(
% 3.85/0.84    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1) | (spl9_1 | ~spl9_5 | ~spl9_6 | ~spl9_8 | ~spl9_11)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f147,f129,f113,f118,f89])).
% 3.85/0.84  fof(f8285,plain,(
% 3.85/0.84    ~spl9_66 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_23 | ~spl9_25 | ~spl9_27 | ~spl9_38 | ~spl9_42 | ~spl9_45 | ~spl9_47 | spl9_56),
% 3.85/0.84    inference(avatar_split_clause,[],[f7794,f5100,f1268,f1258,f1243,f413,f263,f253,f228,f157,f151,f145,f139,f133,f127,f121,f116,f111,f106,f101,f96,f91,f8282])).
% 3.85/0.84  fof(f96,plain,(
% 3.85/0.84    spl9_2 <=> v10_lattices(sK0)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 3.85/0.84  fof(f101,plain,(
% 3.85/0.84    spl9_3 <=> v11_lattices(sK0)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 3.85/0.84  fof(f106,plain,(
% 3.85/0.84    spl9_4 <=> l3_lattices(sK0)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 3.85/0.84  fof(f151,plain,(
% 3.85/0.84    spl9_12 <=> v8_lattices(sK0)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 3.85/0.84  fof(f157,plain,(
% 3.85/0.84    spl9_13 <=> v9_lattices(sK0)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 3.85/0.84  fof(f253,plain,(
% 3.85/0.84    spl9_25 <=> sK3 = k2_lattices(sK0,sK3,sK3)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 3.85/0.84  fof(f263,plain,(
% 3.85/0.84    spl9_27 <=> sK1 = k2_lattices(sK0,sK1,sK1)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 3.85/0.84  fof(f1243,plain,(
% 3.85/0.84    spl9_42 <=> k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK1,sK3)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).
% 3.85/0.84  fof(f1258,plain,(
% 3.85/0.84    spl9_45 <=> sK1 = k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK3))),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).
% 3.85/0.84  fof(f1268,plain,(
% 3.85/0.84    spl9_47 <=> k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).
% 3.85/0.84  fof(f5100,plain,(
% 3.85/0.84    spl9_56 <=> k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)),k3_lattices(sK0,sK1,sK3)) = k3_lattices(sK0,k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)),k4_lattices(sK0,sK1,sK3))),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).
% 3.85/0.84  fof(f7794,plain,(
% 3.85/0.84    k3_lattices(sK0,k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)),k4_lattices(sK0,sK1,sK3)) != k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_23 | ~spl9_25 | ~spl9_27 | ~spl9_38 | ~spl9_42 | ~spl9_45 | ~spl9_47 | spl9_56)),
% 3.85/0.84    inference(backward_demodulation,[],[f5970,f7793])).
% 3.85/0.84  fof(f7793,plain,(
% 3.85/0.84    k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3))) = k4_lattices(sK0,k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK3)),k3_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_23 | ~spl9_25 | ~spl9_27 | ~spl9_38 | ~spl9_42 | ~spl9_45)),
% 3.85/0.84    inference(forward_demodulation,[],[f7792,f951])).
% 3.85/0.84  fof(f951,plain,(
% 3.85/0.84    k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK2) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_6 | ~spl9_9 | ~spl9_10 | ~spl9_38)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f141,f135,f118,f415,f86])).
% 3.85/0.84  fof(f7792,plain,(
% 3.85/0.84    k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3))) = k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK2),k3_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_23 | ~spl9_25 | ~spl9_27 | ~spl9_38 | ~spl9_42 | ~spl9_45)),
% 3.85/0.84    inference(forward_demodulation,[],[f5278,f3760])).
% 3.85/0.84  fof(f3760,plain,(
% 3.85/0.84    k3_lattices(sK0,sK1,sK3) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_23 | ~spl9_25 | ~spl9_27 | ~spl9_38 | ~spl9_42 | ~spl9_45)),
% 3.85/0.84    inference(backward_demodulation,[],[f946,f3757])).
% 3.85/0.84  fof(f3757,plain,(
% 3.85/0.84    k3_lattices(sK0,sK1,sK3) = k3_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_23 | ~spl9_25 | ~spl9_27 | ~spl9_38 | ~spl9_42 | ~spl9_45)),
% 3.85/0.84    inference(forward_demodulation,[],[f3756,f1035])).
% 3.85/0.84  fof(f1035,plain,(
% 3.85/0.84    k3_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3))) | (spl9_1 | ~spl9_4 | ~spl9_9 | ~spl9_10 | ~spl9_13 | ~spl9_23 | ~spl9_38)),
% 3.85/0.84    inference(forward_demodulation,[],[f898,f930])).
% 3.85/0.84  fof(f930,plain,(
% 3.85/0.84    k1_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) = k3_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_9 | ~spl9_10 | ~spl9_23 | ~spl9_38)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f141,f135,f230,f415,f85])).
% 3.85/0.84  fof(f85,plain,(
% 3.85/0.84    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)) )),
% 3.85/0.84    inference(cnf_transformation,[],[f33])).
% 3.85/0.84  fof(f33,plain,(
% 3.85/0.84    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 3.85/0.84    inference(flattening,[],[f32])).
% 3.85/0.84  fof(f32,plain,(
% 3.85/0.84    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 3.85/0.84    inference(ennf_transformation,[],[f9])).
% 3.85/0.84  fof(f9,axiom,(
% 3.85/0.84    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 3.85/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 3.85/0.84  fof(f898,plain,(
% 3.85/0.84    k3_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k1_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3))) | (spl9_1 | ~spl9_4 | ~spl9_13 | ~spl9_23 | ~spl9_38)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f108,f159,f230,f415,f75])).
% 3.85/0.84  fof(f75,plain,(
% 3.85/0.84    ( ! [X4,X0,X3] : (v2_struct_0(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v9_lattices(X0) | ~l3_lattices(X0) | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3) )),
% 3.85/0.84    inference(cnf_transformation,[],[f51])).
% 3.85/0.84  fof(f51,plain,(
% 3.85/0.84    ! [X0] : (((v9_lattices(X0) | ((sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),sK5(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.85/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f48,f50,f49])).
% 3.85/0.84  fof(f49,plain,(
% 3.85/0.84    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 3.85/0.84    introduced(choice_axiom,[])).
% 3.85/0.84  fof(f50,plain,(
% 3.85/0.84    ! [X0] : (? [X2] : (sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => (sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),sK5(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 3.85/0.84    introduced(choice_axiom,[])).
% 3.85/0.84  fof(f48,plain,(
% 3.85/0.84    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.85/0.84    inference(rectify,[],[f47])).
% 3.85/0.84  fof(f47,plain,(
% 3.85/0.84    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.85/0.84    inference(nnf_transformation,[],[f27])).
% 3.85/0.84  fof(f27,plain,(
% 3.85/0.84    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.85/0.84    inference(flattening,[],[f26])).
% 3.85/0.84  fof(f26,plain,(
% 3.85/0.84    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.85/0.84    inference(ennf_transformation,[],[f5])).
% 3.85/0.84  fof(f5,axiom,(
% 3.85/0.84    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 3.85/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).
% 3.85/0.84  fof(f159,plain,(
% 3.85/0.84    v9_lattices(sK0) | ~spl9_13),
% 3.85/0.84    inference(avatar_component_clause,[],[f157])).
% 3.85/0.84  fof(f108,plain,(
% 3.85/0.84    l3_lattices(sK0) | ~spl9_4),
% 3.85/0.84    inference(avatar_component_clause,[],[f106])).
% 3.85/0.84  fof(f3756,plain,(
% 3.85/0.84    k3_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3))) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_23 | ~spl9_25 | ~spl9_27 | ~spl9_38 | ~spl9_42 | ~spl9_45)),
% 3.85/0.84    inference(forward_demodulation,[],[f3755,f930])).
% 3.85/0.84  fof(f3755,plain,(
% 3.85/0.84    k1_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k1_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3))) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_23 | ~spl9_25 | ~spl9_27 | ~spl9_38 | ~spl9_42 | ~spl9_45)),
% 3.85/0.84    inference(forward_demodulation,[],[f3754,f614])).
% 3.85/0.84  fof(f614,plain,(
% 3.85/0.84    k3_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_4 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_23)),
% 3.85/0.84    inference(backward_demodulation,[],[f606,f613])).
% 3.85/0.84  fof(f613,plain,(
% 3.85/0.84    k3_lattices(sK0,sK1,sK3) = k3_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_4 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_23)),
% 3.85/0.84    inference(backward_demodulation,[],[f537,f510])).
% 3.85/0.84  fof(f510,plain,(
% 3.85/0.84    k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_4 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_23)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f147,f153,f159,f108,f230,f74])).
% 3.85/0.84  fof(f74,plain,(
% 3.85/0.84    ( ! [X0,X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.85/0.84    inference(cnf_transformation,[],[f25])).
% 3.85/0.84  fof(f25,plain,(
% 3.85/0.84    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.85/0.84    inference(flattening,[],[f24])).
% 3.85/0.84  fof(f24,plain,(
% 3.85/0.84    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.85/0.84    inference(ennf_transformation,[],[f11])).
% 3.85/0.84  fof(f11,axiom,(
% 3.85/0.84    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_lattices(X0,X1,X1) = X1))),
% 3.85/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattices)).
% 3.85/0.84  fof(f153,plain,(
% 3.85/0.84    v8_lattices(sK0) | ~spl9_12),
% 3.85/0.84    inference(avatar_component_clause,[],[f151])).
% 3.85/0.84  fof(f537,plain,(
% 3.85/0.84    k1_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3)) = k3_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_9 | ~spl9_10 | ~spl9_23)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f141,f135,f230,f230,f85])).
% 3.85/0.84  fof(f606,plain,(
% 3.85/0.84    k3_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3))) | (spl9_1 | ~spl9_4 | ~spl9_9 | ~spl9_10 | ~spl9_13 | ~spl9_23)),
% 3.85/0.84    inference(forward_demodulation,[],[f517,f537])).
% 3.85/0.84  fof(f517,plain,(
% 3.85/0.84    k3_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k1_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3))) | (spl9_1 | ~spl9_4 | ~spl9_13 | ~spl9_23)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f108,f159,f230,f230,f75])).
% 3.85/0.84  fof(f3754,plain,(
% 3.85/0.84    k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k1_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3))) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3)),k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_23 | ~spl9_25 | ~spl9_27 | ~spl9_38 | ~spl9_42 | ~spl9_45)),
% 3.85/0.84    inference(forward_demodulation,[],[f1621,f2164])).
% 3.85/0.84  fof(f2164,plain,(
% 3.85/0.84    k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_23 | ~spl9_25 | ~spl9_27 | ~spl9_38 | ~spl9_42 | ~spl9_45)),
% 3.85/0.84    inference(backward_demodulation,[],[f978,f2161])).
% 3.85/0.84  fof(f2161,plain,(
% 3.85/0.84    k4_lattices(sK0,sK1,sK3) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_23 | ~spl9_25 | ~spl9_27 | ~spl9_38 | ~spl9_42 | ~spl9_45)),
% 3.85/0.84    inference(forward_demodulation,[],[f2160,f888])).
% 3.85/0.84  fof(f888,plain,(
% 3.85/0.84    k4_lattices(sK0,sK1,sK3) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_4 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_38)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f147,f153,f159,f108,f415,f74])).
% 3.85/0.84  fof(f2160,plain,(
% 3.85/0.84    k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_13 | ~spl9_23 | ~spl9_25 | ~spl9_27 | ~spl9_38 | ~spl9_42 | ~spl9_45)),
% 3.85/0.84    inference(forward_demodulation,[],[f2159,f1006])).
% 3.85/0.84  fof(f1006,plain,(
% 3.85/0.84    k4_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) = k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_8 | ~spl9_11 | ~spl9_23 | ~spl9_38)),
% 3.85/0.84    inference(forward_demodulation,[],[f970,f994])).
% 3.85/0.84  fof(f994,plain,(
% 3.85/0.84    k4_lattices(sK0,k4_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3)) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_8 | ~spl9_11 | ~spl9_23 | ~spl9_38)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f147,f129,f230,f415,f89])).
% 3.85/0.84  fof(f970,plain,(
% 3.85/0.84    k4_lattices(sK0,k4_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3)) = k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_8 | ~spl9_11 | ~spl9_23 | ~spl9_38)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f147,f129,f230,f415,f88])).
% 3.85/0.84  fof(f2159,plain,(
% 3.85/0.84    k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) = k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_13 | ~spl9_25 | ~spl9_27 | ~spl9_38 | ~spl9_42 | ~spl9_45)),
% 3.85/0.84    inference(forward_demodulation,[],[f2158,f1245])).
% 3.85/0.84  fof(f1245,plain,(
% 3.85/0.84    k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK1,sK3) | ~spl9_42),
% 3.85/0.84    inference(avatar_component_clause,[],[f1243])).
% 3.85/0.84  fof(f2158,plain,(
% 3.85/0.84    k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) = k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),k1_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_13 | ~spl9_25 | ~spl9_27 | ~spl9_38 | ~spl9_42 | ~spl9_45)),
% 3.85/0.84    inference(forward_demodulation,[],[f2157,f2143])).
% 3.85/0.84  fof(f2143,plain,(
% 3.85/0.84    k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK1) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_13 | ~spl9_27 | ~spl9_38 | ~spl9_42 | ~spl9_45)),
% 3.85/0.84    inference(backward_demodulation,[],[f1039,f2142])).
% 3.85/0.84  fof(f2142,plain,(
% 3.85/0.84    sK1 = k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_27 | ~spl9_38 | ~spl9_42 | ~spl9_45)),
% 3.85/0.84    inference(forward_demodulation,[],[f2141,f1260])).
% 3.85/0.84  fof(f1260,plain,(
% 3.85/0.84    sK1 = k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK3)) | ~spl9_45),
% 3.85/0.84    inference(avatar_component_clause,[],[f1258])).
% 3.85/0.84  fof(f2141,plain,(
% 3.85/0.84    k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK3)) = k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_27 | ~spl9_38 | ~spl9_42)),
% 3.85/0.84    inference(forward_demodulation,[],[f2140,f1245])).
% 3.85/0.84  fof(f2140,plain,(
% 3.85/0.84    k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK3)) = k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_27 | ~spl9_38)),
% 3.85/0.84    inference(forward_demodulation,[],[f2139,f934])).
% 3.85/0.84  fof(f934,plain,(
% 3.85/0.84    k1_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK3)) = k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_5 | ~spl9_9 | ~spl9_10 | ~spl9_38)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f141,f135,f113,f415,f85])).
% 3.85/0.84  fof(f2139,plain,(
% 3.85/0.84    k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_27)),
% 3.85/0.84    inference(forward_demodulation,[],[f2138,f265])).
% 3.85/0.84  fof(f265,plain,(
% 3.85/0.84    sK1 = k2_lattices(sK0,sK1,sK1) | ~spl9_27),
% 3.85/0.84    inference(avatar_component_clause,[],[f263])).
% 3.85/0.84  fof(f2138,plain,(
% 3.85/0.84    k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK1,sK1),k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_11)),
% 3.85/0.84    inference(forward_demodulation,[],[f1995,f355])).
% 3.85/0.84  fof(f355,plain,(
% 3.85/0.84    k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,sK3) | (spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_11)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f147,f129,f113,f123,f88])).
% 3.85/0.84  fof(f1995,plain,(
% 3.85/0.84    k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK1,sK1),k2_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f108,f103,f113,f113,f123,f79])).
% 3.85/0.84  fof(f79,plain,(
% 3.85/0.84    ( ! [X6,X4,X0,X5] : (~v11_lattices(X0) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.85/0.84    inference(cnf_transformation,[],[f57])).
% 3.85/0.84  fof(f57,plain,(
% 3.85/0.84    ! [X0] : (((v11_lattices(X0) | (((k2_lattices(X0,sK6(X0),k1_lattices(X0,sK7(X0),sK8(X0))) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),k2_lattices(X0,sK6(X0),sK8(X0))) & m1_subset_1(sK8(X0),u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0))) & m1_subset_1(sK6(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.85/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f53,f56,f55,f54])).
% 3.85/0.84  fof(f54,plain,(
% 3.85/0.84    ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k2_lattices(X0,sK6(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK6(X0),X2),k2_lattices(X0,sK6(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK6(X0),u1_struct_0(X0))))),
% 3.85/0.84    introduced(choice_axiom,[])).
% 3.85/0.84  fof(f55,plain,(
% 3.85/0.84    ! [X0] : (? [X2] : (? [X3] : (k2_lattices(X0,sK6(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK6(X0),X2),k2_lattices(X0,sK6(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (k2_lattices(X0,sK6(X0),k1_lattices(X0,sK7(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),k2_lattices(X0,sK6(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0))))),
% 3.85/0.84    introduced(choice_axiom,[])).
% 3.85/0.84  fof(f56,plain,(
% 3.85/0.84    ! [X0] : (? [X3] : (k2_lattices(X0,sK6(X0),k1_lattices(X0,sK7(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),k2_lattices(X0,sK6(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) => (k2_lattices(X0,sK6(X0),k1_lattices(X0,sK7(X0),sK8(X0))) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),k2_lattices(X0,sK6(X0),sK8(X0))) & m1_subset_1(sK8(X0),u1_struct_0(X0))))),
% 3.85/0.84    introduced(choice_axiom,[])).
% 3.85/0.84  fof(f53,plain,(
% 3.85/0.84    ! [X0] : (((v11_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.85/0.84    inference(rectify,[],[f52])).
% 3.85/0.84  fof(f52,plain,(
% 3.85/0.84    ! [X0] : (((v11_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.85/0.84    inference(nnf_transformation,[],[f29])).
% 3.85/0.84  fof(f29,plain,(
% 3.85/0.84    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.85/0.84    inference(flattening,[],[f28])).
% 3.85/0.84  fof(f28,plain,(
% 3.85/0.84    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.85/0.84    inference(ennf_transformation,[],[f4])).
% 3.85/0.84  fof(f4,axiom,(
% 3.85/0.84    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v11_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)))))))),
% 3.85/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_lattices)).
% 3.85/0.84  fof(f103,plain,(
% 3.85/0.84    v11_lattices(sK0) | ~spl9_3),
% 3.85/0.84    inference(avatar_component_clause,[],[f101])).
% 3.85/0.84  fof(f1039,plain,(
% 3.85/0.84    k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK3))) | (spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_9 | ~spl9_10 | ~spl9_13 | ~spl9_38)),
% 3.85/0.84    inference(forward_demodulation,[],[f894,f1017])).
% 3.85/0.84  fof(f1017,plain,(
% 3.85/0.84    k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK1) = k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_5 | ~spl9_9 | ~spl9_10 | ~spl9_38)),
% 3.85/0.84    inference(forward_demodulation,[],[f926,f950])).
% 3.85/0.84  fof(f950,plain,(
% 3.85/0.84    k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK1) = k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_5 | ~spl9_9 | ~spl9_10 | ~spl9_38)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f141,f135,f113,f415,f86])).
% 3.85/0.84  fof(f926,plain,(
% 3.85/0.84    k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK1) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK1) | (spl9_1 | ~spl9_5 | ~spl9_9 | ~spl9_10 | ~spl9_38)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f141,f135,f113,f415,f85])).
% 3.85/0.84  fof(f894,plain,(
% 3.85/0.84    k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK1)) | (spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_13 | ~spl9_38)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f108,f159,f113,f415,f75])).
% 3.85/0.84  fof(f2157,plain,(
% 3.85/0.84    k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK1),k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_13 | ~spl9_25 | ~spl9_38 | ~spl9_42)),
% 3.85/0.84    inference(forward_demodulation,[],[f1993,f2115])).
% 3.85/0.84  fof(f2115,plain,(
% 3.85/0.84    k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK3) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_13 | ~spl9_25 | ~spl9_38 | ~spl9_42)),
% 3.85/0.84    inference(backward_demodulation,[],[f1037,f2114])).
% 3.85/0.84  fof(f2114,plain,(
% 3.85/0.84    sK3 = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_13 | ~spl9_25 | ~spl9_38 | ~spl9_42)),
% 3.85/0.84    inference(forward_demodulation,[],[f2113,f321])).
% 3.85/0.84  fof(f321,plain,(
% 3.85/0.84    sK3 = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_9 | ~spl9_10 | ~spl9_13)),
% 3.85/0.84    inference(backward_demodulation,[],[f285,f314])).
% 3.85/0.84  fof(f314,plain,(
% 3.85/0.84    k3_lattices(sK0,sK3,sK1) = k3_lattices(sK0,sK1,sK3) | (spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_9 | ~spl9_10)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f141,f135,f113,f123,f86])).
% 3.85/0.84  fof(f285,plain,(
% 3.85/0.84    sK3 = k2_lattices(sK0,sK3,k3_lattices(sK0,sK3,sK1)) | (spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_9 | ~spl9_10 | ~spl9_13)),
% 3.85/0.84    inference(backward_demodulation,[],[f239,f269])).
% 3.85/0.84  fof(f269,plain,(
% 3.85/0.84    k3_lattices(sK0,sK3,sK1) = k1_lattices(sK0,sK3,sK1) | (spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_9 | ~spl9_10)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f141,f135,f123,f113,f85])).
% 3.85/0.84  fof(f239,plain,(
% 3.85/0.84    sK3 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,sK1)) | (spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_13)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f108,f159,f123,f113,f75])).
% 3.85/0.84  fof(f2113,plain,(
% 3.85/0.84    k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK3)) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_38 | ~spl9_42)),
% 3.85/0.84    inference(forward_demodulation,[],[f2112,f1015])).
% 3.85/0.84  fof(f1015,plain,(
% 3.85/0.84    k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK3) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_7 | ~spl9_9 | ~spl9_10 | ~spl9_38)),
% 3.85/0.84    inference(forward_demodulation,[],[f928,f952])).
% 3.85/0.84  fof(f952,plain,(
% 3.85/0.84    k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK3) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_7 | ~spl9_9 | ~spl9_10 | ~spl9_38)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f141,f135,f123,f415,f86])).
% 3.85/0.84  fof(f928,plain,(
% 3.85/0.84    k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK3) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK3) | (spl9_1 | ~spl9_7 | ~spl9_9 | ~spl9_10 | ~spl9_38)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f141,f135,f123,f415,f85])).
% 3.85/0.84  fof(f2112,plain,(
% 3.85/0.84    k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK3) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_25 | ~spl9_42)),
% 3.85/0.84    inference(forward_demodulation,[],[f2111,f1245])).
% 3.85/0.84  fof(f2111,plain,(
% 3.85/0.84    k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK3) = k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_25)),
% 3.85/0.84    inference(forward_demodulation,[],[f2110,f398])).
% 3.85/0.84  fof(f2110,plain,(
% 3.85/0.84    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),sK3) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_25)),
% 3.85/0.84    inference(forward_demodulation,[],[f1997,f255])).
% 3.85/0.84  fof(f255,plain,(
% 3.85/0.84    sK3 = k2_lattices(sK0,sK3,sK3) | ~spl9_25),
% 3.85/0.84    inference(avatar_component_clause,[],[f253])).
% 3.85/0.84  fof(f1997,plain,(
% 3.85/0.84    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f108,f103,f123,f113,f123,f79])).
% 3.85/0.84  fof(f1037,plain,(
% 3.85/0.84    k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK3))) | (spl9_1 | ~spl9_4 | ~spl9_7 | ~spl9_9 | ~spl9_10 | ~spl9_13 | ~spl9_38)),
% 3.85/0.84    inference(forward_demodulation,[],[f896,f1015])).
% 3.85/0.84  fof(f896,plain,(
% 3.85/0.84    k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK3)) | (spl9_1 | ~spl9_4 | ~spl9_7 | ~spl9_13 | ~spl9_38)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f108,f159,f123,f415,f75])).
% 3.85/0.84  fof(f1993,plain,(
% 3.85/0.84    k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK1),k2_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_38)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f108,f103,f415,f113,f123,f79])).
% 3.85/0.84  fof(f978,plain,(
% 3.85/0.84    k4_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_8 | ~spl9_11 | ~spl9_23 | ~spl9_38)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f147,f129,f230,f415,f88])).
% 3.85/0.84  fof(f1621,plain,(
% 3.85/0.84    k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k1_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3))) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3)),k2_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3))) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_23 | ~spl9_38)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f108,f103,f230,f230,f415,f79])).
% 3.85/0.84  fof(f946,plain,(
% 3.85/0.84    k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3)) = k3_lattices(sK0,k3_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_9 | ~spl9_10 | ~spl9_23 | ~spl9_38)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f141,f135,f230,f415,f86])).
% 3.85/0.84  fof(f5278,plain,(
% 3.85/0.84    k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3))) = k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK2),k3_lattices(sK0,k4_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK1,sK3))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_23 | ~spl9_38)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f98,f103,f108,f415,f118,f230,f73])).
% 3.85/0.84  fof(f73,plain,(
% 3.85/0.84    ( ! [X2,X0,X3,X1] : (~v11_lattices(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.85/0.84    inference(cnf_transformation,[],[f23])).
% 3.85/0.84  fof(f23,plain,(
% 3.85/0.84    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.85/0.84    inference(flattening,[],[f22])).
% 3.85/0.84  fof(f22,plain,(
% 3.85/0.84    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.85/0.84    inference(ennf_transformation,[],[f12])).
% 3.85/0.84  fof(f12,axiom,(
% 3.85/0.84    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))))))),
% 3.85/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_lattices)).
% 3.85/0.84  fof(f98,plain,(
% 3.85/0.84    v10_lattices(sK0) | ~spl9_2),
% 3.85/0.84    inference(avatar_component_clause,[],[f96])).
% 3.85/0.84  fof(f5970,plain,(
% 3.85/0.84    k3_lattices(sK0,k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)),k4_lattices(sK0,sK1,sK3)) != k4_lattices(sK0,k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK3)),k3_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_47 | spl9_56)),
% 3.85/0.84    inference(backward_demodulation,[],[f5102,f5938])).
% 3.85/0.84  fof(f5938,plain,(
% 3.85/0.84    k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_47)),
% 3.85/0.84    inference(forward_demodulation,[],[f5839,f1270])).
% 3.85/0.84  fof(f1270,plain,(
% 3.85/0.84    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1) | ~spl9_47),
% 3.85/0.84    inference(avatar_component_clause,[],[f1268])).
% 3.85/0.84  fof(f5839,plain,(
% 3.85/0.84    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK3)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK1),k3_lattices(sK0,sK2,sK3)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f98,f103,f108,f118,f113,f123,f73])).
% 3.85/0.84  fof(f5102,plain,(
% 3.85/0.84    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)),k3_lattices(sK0,sK1,sK3)) != k3_lattices(sK0,k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)),k4_lattices(sK0,sK1,sK3)) | spl9_56),
% 3.85/0.84    inference(avatar_component_clause,[],[f5100])).
% 3.85/0.84  fof(f8280,plain,(
% 3.85/0.84    spl9_65 | spl9_1 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11),
% 3.85/0.84    inference(avatar_split_clause,[],[f356,f145,f127,f121,f116,f91,f8277])).
% 3.85/0.84  fof(f8277,plain,(
% 3.85/0.84    spl9_65 <=> k4_lattices(sK0,sK2,sK3) = k2_lattices(sK0,sK2,sK3)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_65])])).
% 3.85/0.84  fof(f356,plain,(
% 3.85/0.84    k4_lattices(sK0,sK2,sK3) = k2_lattices(sK0,sK2,sK3) | (spl9_1 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f147,f129,f118,f123,f88])).
% 3.85/0.84  fof(f8275,plain,(
% 3.85/0.84    spl9_64 | spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_11),
% 3.85/0.84    inference(avatar_split_clause,[],[f355,f145,f127,f121,f111,f91,f8272])).
% 3.85/0.84  fof(f8272,plain,(
% 3.85/0.84    spl9_64 <=> k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,sK3)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).
% 3.85/0.84  fof(f8270,plain,(
% 3.85/0.84    spl9_63 | spl9_1 | ~spl9_5 | ~spl9_6 | ~spl9_8 | ~spl9_11),
% 3.85/0.84    inference(avatar_split_clause,[],[f352,f145,f127,f116,f111,f91,f8267])).
% 3.85/0.84  fof(f8267,plain,(
% 3.85/0.84    spl9_63 <=> k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_63])])).
% 3.85/0.84  fof(f352,plain,(
% 3.85/0.84    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2) | (spl9_1 | ~spl9_5 | ~spl9_6 | ~spl9_8 | ~spl9_11)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f147,f129,f113,f118,f88])).
% 3.85/0.84  fof(f8265,plain,(
% 3.85/0.84    spl9_62 | spl9_1 | ~spl9_5 | ~spl9_6 | ~spl9_9 | ~spl9_10),
% 3.85/0.84    inference(avatar_split_clause,[],[f326,f139,f133,f116,f111,f91,f8262])).
% 3.85/0.84  fof(f8262,plain,(
% 3.85/0.84    spl9_62 <=> k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK2,sK1)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).
% 3.85/0.84  fof(f326,plain,(
% 3.85/0.84    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK2,sK1) | (spl9_1 | ~spl9_5 | ~spl9_6 | ~spl9_9 | ~spl9_10)),
% 3.85/0.84    inference(backward_demodulation,[],[f268,f311])).
% 3.85/0.84  fof(f311,plain,(
% 3.85/0.84    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1) | (spl9_1 | ~spl9_5 | ~spl9_6 | ~spl9_9 | ~spl9_10)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f141,f135,f113,f118,f86])).
% 3.85/0.84  fof(f268,plain,(
% 3.85/0.84    k3_lattices(sK0,sK2,sK1) = k1_lattices(sK0,sK2,sK1) | (spl9_1 | ~spl9_5 | ~spl9_6 | ~spl9_9 | ~spl9_10)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f141,f135,f118,f113,f85])).
% 3.85/0.84  fof(f8260,plain,(
% 3.85/0.84    spl9_61 | spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_9 | ~spl9_10 | ~spl9_13),
% 3.85/0.84    inference(avatar_split_clause,[],[f325,f157,f139,f133,f116,f111,f106,f91,f8257])).
% 3.85/0.84  fof(f8257,plain,(
% 3.85/0.84    spl9_61 <=> sK2 = k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2))),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_61])])).
% 3.85/0.84  fof(f325,plain,(
% 3.85/0.84    sK2 = k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) | (spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_9 | ~spl9_10 | ~spl9_13)),
% 3.85/0.84    inference(backward_demodulation,[],[f286,f311])).
% 3.85/0.84  fof(f286,plain,(
% 3.85/0.84    sK2 = k2_lattices(sK0,sK2,k3_lattices(sK0,sK2,sK1)) | (spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_9 | ~spl9_10 | ~spl9_13)),
% 3.85/0.84    inference(backward_demodulation,[],[f238,f268])).
% 3.85/0.84  fof(f238,plain,(
% 3.85/0.84    sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK1)) | (spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_13)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f108,f159,f118,f113,f75])).
% 3.85/0.84  fof(f5129,plain,(
% 3.85/0.84    spl9_60 | spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_9 | ~spl9_10),
% 3.85/0.84    inference(avatar_split_clause,[],[f322,f139,f133,f121,f111,f91,f5126])).
% 3.85/0.84  fof(f5126,plain,(
% 3.85/0.84    spl9_60 <=> k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK3,sK1)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).
% 3.85/0.84  fof(f322,plain,(
% 3.85/0.84    k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK3,sK1) | (spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_9 | ~spl9_10)),
% 3.85/0.84    inference(backward_demodulation,[],[f269,f314])).
% 3.85/0.84  fof(f5124,plain,(
% 3.85/0.84    spl9_59 | spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_9 | ~spl9_10 | ~spl9_13),
% 3.85/0.84    inference(avatar_split_clause,[],[f321,f157,f139,f133,f121,f111,f106,f91,f5121])).
% 3.85/0.84  fof(f5121,plain,(
% 3.85/0.84    spl9_59 <=> sK3 = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK3))),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).
% 3.85/0.84  fof(f5119,plain,(
% 3.85/0.84    spl9_58 | spl9_1 | ~spl9_6 | ~spl9_7 | ~spl9_9 | ~spl9_10),
% 3.85/0.84    inference(avatar_split_clause,[],[f319,f139,f133,f121,f116,f91,f5116])).
% 3.85/0.84  fof(f5116,plain,(
% 3.85/0.84    spl9_58 <=> k3_lattices(sK0,sK2,sK3) = k1_lattices(sK0,sK3,sK2)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).
% 3.85/0.84  fof(f319,plain,(
% 3.85/0.84    k3_lattices(sK0,sK2,sK3) = k1_lattices(sK0,sK3,sK2) | (spl9_1 | ~spl9_6 | ~spl9_7 | ~spl9_9 | ~spl9_10)),
% 3.85/0.84    inference(backward_demodulation,[],[f272,f315])).
% 3.85/0.84  fof(f315,plain,(
% 3.85/0.84    k3_lattices(sK0,sK2,sK3) = k3_lattices(sK0,sK3,sK2) | (spl9_1 | ~spl9_6 | ~spl9_7 | ~spl9_9 | ~spl9_10)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f141,f135,f118,f123,f86])).
% 3.85/0.84  fof(f272,plain,(
% 3.85/0.84    k3_lattices(sK0,sK3,sK2) = k1_lattices(sK0,sK3,sK2) | (spl9_1 | ~spl9_6 | ~spl9_7 | ~spl9_9 | ~spl9_10)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f141,f135,f123,f118,f85])).
% 3.85/0.84  fof(f5108,plain,(
% 3.85/0.84    spl9_57 | spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_27 | ~spl9_37 | ~spl9_41 | ~spl9_46),
% 3.85/0.84    inference(avatar_split_clause,[],[f2506,f1263,f1238,f408,f263,f145,f139,f133,f127,f116,f111,f106,f101,f91,f5105])).
% 3.85/0.84  fof(f5105,plain,(
% 3.85/0.84    spl9_57 <=> sK1 = k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK2))),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_57])])).
% 3.85/0.84  fof(f408,plain,(
% 3.85/0.84    spl9_37 <=> m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).
% 3.85/0.84  fof(f1238,plain,(
% 3.85/0.84    spl9_41 <=> k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).
% 3.85/0.84  fof(f1263,plain,(
% 3.85/0.84    spl9_46 <=> sK1 = k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2))),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).
% 3.85/0.84  fof(f2506,plain,(
% 3.85/0.84    sK1 = k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK2)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_27 | ~spl9_37 | ~spl9_41 | ~spl9_46)),
% 3.85/0.84    inference(forward_demodulation,[],[f2505,f1265])).
% 3.85/0.84  fof(f1265,plain,(
% 3.85/0.84    sK1 = k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2)) | ~spl9_46),
% 3.85/0.84    inference(avatar_component_clause,[],[f1263])).
% 3.85/0.84  fof(f2505,plain,(
% 3.85/0.84    k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK2)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_27 | ~spl9_37 | ~spl9_41)),
% 3.85/0.84    inference(forward_demodulation,[],[f2504,f1240])).
% 3.85/0.84  fof(f1240,plain,(
% 3.85/0.84    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2) | ~spl9_41),
% 3.85/0.84    inference(avatar_component_clause,[],[f1238])).
% 3.85/0.84  fof(f2504,plain,(
% 3.85/0.84    k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK2)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_27 | ~spl9_37)),
% 3.85/0.84    inference(forward_demodulation,[],[f2503,f786])).
% 3.85/0.84  fof(f786,plain,(
% 3.85/0.84    k1_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK2)) | (spl9_1 | ~spl9_5 | ~spl9_9 | ~spl9_10 | ~spl9_37)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f141,f135,f113,f410,f85])).
% 3.85/0.84  fof(f410,plain,(
% 3.85/0.84    m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | ~spl9_37),
% 3.85/0.84    inference(avatar_component_clause,[],[f408])).
% 3.85/0.84  fof(f2503,plain,(
% 3.85/0.84    k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK2)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_8 | ~spl9_11 | ~spl9_27)),
% 3.85/0.84    inference(forward_demodulation,[],[f2502,f265])).
% 3.85/0.84  fof(f2502,plain,(
% 3.85/0.84    k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,sK1,sK1),k4_lattices(sK0,sK1,sK2)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_8 | ~spl9_11)),
% 3.85/0.84    inference(forward_demodulation,[],[f1914,f352])).
% 3.85/0.84  fof(f1914,plain,(
% 3.85/0.84    k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,sK1,sK1),k2_lattices(sK0,sK1,sK2)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f108,f103,f113,f113,f118,f79])).
% 3.85/0.84  fof(f5103,plain,(
% 3.85/0.84    ~spl9_56 | spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_23 | ~spl9_37 | ~spl9_39 | spl9_40 | ~spl9_42),
% 3.85/0.84    inference(avatar_split_clause,[],[f2137,f1243,f1233,f418,f408,f228,f145,f139,f133,f127,f121,f116,f111,f106,f101,f91,f5100])).
% 3.85/0.84  fof(f418,plain,(
% 3.85/0.84    spl9_39 <=> m1_subset_1(k4_lattices(sK0,sK2,sK3),u1_struct_0(sK0))),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).
% 3.85/0.84  fof(f1233,plain,(
% 3.85/0.84    spl9_40 <=> k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)),k3_lattices(sK0,sK1,sK3)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)),k4_lattices(sK0,sK1,sK3))),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).
% 3.85/0.84  fof(f2137,plain,(
% 3.85/0.84    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)),k3_lattices(sK0,sK1,sK3)) != k3_lattices(sK0,k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)),k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_23 | ~spl9_37 | ~spl9_39 | spl9_40 | ~spl9_42)),
% 3.85/0.84    inference(backward_demodulation,[],[f1235,f2131])).
% 3.85/0.84  fof(f2131,plain,(
% 3.85/0.84    k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)) = k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_23 | ~spl9_37 | ~spl9_39 | ~spl9_42)),
% 3.85/0.84    inference(backward_demodulation,[],[f1099,f2130])).
% 3.85/0.84  fof(f2130,plain,(
% 3.85/0.84    k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_23 | ~spl9_42)),
% 3.85/0.84    inference(forward_demodulation,[],[f2129,f569])).
% 3.85/0.84  fof(f569,plain,(
% 3.85/0.84    k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)) = k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_6 | ~spl9_8 | ~spl9_11 | ~spl9_23)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f147,f129,f118,f230,f88])).
% 3.85/0.84  fof(f2129,plain,(
% 3.85/0.84    k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_42)),
% 3.85/0.84    inference(forward_demodulation,[],[f2128,f1245])).
% 3.85/0.84  fof(f2128,plain,(
% 3.85/0.84    k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)) = k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11)),
% 3.85/0.84    inference(forward_demodulation,[],[f2127,f401])).
% 3.85/0.84  fof(f401,plain,(
% 3.85/0.84    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK2,sK1) | (spl9_1 | ~spl9_5 | ~spl9_6 | ~spl9_8 | ~spl9_11)),
% 3.85/0.84    inference(backward_demodulation,[],[f350,f389])).
% 3.85/0.84  fof(f350,plain,(
% 3.85/0.84    k4_lattices(sK0,sK2,sK1) = k2_lattices(sK0,sK2,sK1) | (spl9_1 | ~spl9_5 | ~spl9_6 | ~spl9_8 | ~spl9_11)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f147,f129,f118,f113,f88])).
% 3.85/0.84  fof(f2127,plain,(
% 3.85/0.84    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),k4_lattices(sK0,sK2,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11)),
% 3.85/0.84    inference(forward_demodulation,[],[f1996,f356])).
% 3.85/0.84  fof(f1996,plain,(
% 3.85/0.84    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),k2_lattices(sK0,sK2,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_7)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f108,f103,f118,f113,f123,f79])).
% 3.85/0.84  fof(f1099,plain,(
% 3.85/0.84    k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)) | (spl9_1 | ~spl9_9 | ~spl9_10 | ~spl9_37 | ~spl9_39)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f141,f135,f410,f420,f85])).
% 3.85/0.84  fof(f420,plain,(
% 3.85/0.84    m1_subset_1(k4_lattices(sK0,sK2,sK3),u1_struct_0(sK0)) | ~spl9_39),
% 3.85/0.84    inference(avatar_component_clause,[],[f418])).
% 3.85/0.84  fof(f1235,plain,(
% 3.85/0.84    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)),k3_lattices(sK0,sK1,sK3)) != k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)),k4_lattices(sK0,sK1,sK3)) | spl9_40),
% 3.85/0.84    inference(avatar_component_clause,[],[f1233])).
% 3.85/0.84  fof(f5098,plain,(
% 3.85/0.84    spl9_55 | spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_13 | ~spl9_26 | ~spl9_37 | ~spl9_41),
% 3.85/0.84    inference(avatar_split_clause,[],[f2477,f1238,f408,f258,f157,f145,f139,f133,f127,f116,f111,f106,f101,f91,f5095])).
% 3.85/0.84  fof(f5095,plain,(
% 3.85/0.84    spl9_55 <=> sK2 = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2))),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_55])])).
% 3.85/0.84  fof(f258,plain,(
% 3.85/0.84    spl9_26 <=> sK2 = k2_lattices(sK0,sK2,sK2)),
% 3.85/0.84    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 3.85/0.84  fof(f2477,plain,(
% 3.85/0.84    sK2 = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_13 | ~spl9_26 | ~spl9_37 | ~spl9_41)),
% 3.85/0.84    inference(forward_demodulation,[],[f2476,f325])).
% 3.85/0.84  fof(f2476,plain,(
% 3.85/0.84    k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_26 | ~spl9_37 | ~spl9_41)),
% 3.85/0.84    inference(forward_demodulation,[],[f2475,f858])).
% 3.85/0.84  fof(f858,plain,(
% 3.85/0.84    k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) | (spl9_1 | ~spl9_6 | ~spl9_9 | ~spl9_10 | ~spl9_37)),
% 3.85/0.84    inference(forward_demodulation,[],[f780,f801])).
% 3.85/0.84  fof(f801,plain,(
% 3.85/0.84    k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) | (spl9_1 | ~spl9_6 | ~spl9_9 | ~spl9_10 | ~spl9_37)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f141,f135,f118,f410,f86])).
% 3.85/0.84  fof(f780,plain,(
% 3.85/0.84    k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) | (spl9_1 | ~spl9_6 | ~spl9_9 | ~spl9_10 | ~spl9_37)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f141,f135,f118,f410,f85])).
% 3.85/0.84  fof(f2475,plain,(
% 3.85/0.84    k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_8 | ~spl9_11 | ~spl9_26 | ~spl9_41)),
% 3.85/0.84    inference(forward_demodulation,[],[f2474,f1240])).
% 3.85/0.84  fof(f2474,plain,(
% 3.85/0.84    k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_8 | ~spl9_11 | ~spl9_26)),
% 3.85/0.84    inference(forward_demodulation,[],[f2473,f401])).
% 3.85/0.84  fof(f2473,plain,(
% 3.85/0.84    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK2) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_26)),
% 3.85/0.84    inference(forward_demodulation,[],[f1915,f260])).
% 3.85/0.84  fof(f260,plain,(
% 3.85/0.84    sK2 = k2_lattices(sK0,sK2,sK2) | ~spl9_26),
% 3.85/0.84    inference(avatar_component_clause,[],[f258])).
% 3.85/0.84  fof(f1915,plain,(
% 3.85/0.84    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),k2_lattices(sK0,sK2,sK2)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_6)),
% 3.85/0.84    inference(unit_resulting_resolution,[],[f93,f108,f103,f118,f113,f118,f79])).
% 3.85/0.85  fof(f5093,plain,(
% 3.85/0.85    spl9_54 | spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_27 | ~spl9_38 | ~spl9_42 | ~spl9_45),
% 3.85/0.85    inference(avatar_split_clause,[],[f2142,f1258,f1243,f413,f263,f145,f139,f133,f127,f121,f111,f106,f101,f91,f5090])).
% 3.85/0.85  fof(f5090,plain,(
% 3.85/0.85    spl9_54 <=> sK1 = k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK3))),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).
% 3.85/0.85  fof(f5088,plain,(
% 3.85/0.85    spl9_53 | spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_13 | ~spl9_25 | ~spl9_38 | ~spl9_42),
% 3.85/0.85    inference(avatar_split_clause,[],[f2114,f1243,f413,f253,f157,f145,f139,f133,f127,f121,f111,f106,f101,f91,f5085])).
% 3.85/0.85  fof(f5085,plain,(
% 3.85/0.85    spl9_53 <=> sK3 = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK3))),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_53])])).
% 3.85/0.85  fof(f5083,plain,(
% 3.85/0.85    spl9_52 | spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_26 | ~spl9_39 | ~spl9_43 | ~spl9_44),
% 3.85/0.85    inference(avatar_split_clause,[],[f2061,f1253,f1248,f418,f258,f145,f139,f133,f127,f121,f116,f106,f101,f91,f5080])).
% 3.85/0.85  fof(f5080,plain,(
% 3.85/0.85    spl9_52 <=> sK2 = k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK3))),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).
% 3.85/0.85  fof(f1248,plain,(
% 3.85/0.85    spl9_43 <=> k3_lattices(sK0,sK2,sK3) = k1_lattices(sK0,sK2,sK3)),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).
% 3.85/0.85  fof(f1253,plain,(
% 3.85/0.85    spl9_44 <=> sK2 = k2_lattices(sK0,sK2,k3_lattices(sK0,sK2,sK3))),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).
% 3.85/0.85  fof(f2061,plain,(
% 3.85/0.85    sK2 = k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_26 | ~spl9_39 | ~spl9_43 | ~spl9_44)),
% 3.85/0.85    inference(forward_demodulation,[],[f2060,f1255])).
% 3.85/0.85  fof(f1255,plain,(
% 3.85/0.85    sK2 = k2_lattices(sK0,sK2,k3_lattices(sK0,sK2,sK3)) | ~spl9_44),
% 3.85/0.85    inference(avatar_component_clause,[],[f1253])).
% 3.85/0.85  fof(f2060,plain,(
% 3.85/0.85    k2_lattices(sK0,sK2,k3_lattices(sK0,sK2,sK3)) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_26 | ~spl9_39 | ~spl9_43)),
% 3.85/0.85    inference(forward_demodulation,[],[f2059,f1250])).
% 3.85/0.85  fof(f1250,plain,(
% 3.85/0.85    k3_lattices(sK0,sK2,sK3) = k1_lattices(sK0,sK2,sK3) | ~spl9_43),
% 3.85/0.85    inference(avatar_component_clause,[],[f1248])).
% 3.85/0.85  fof(f2059,plain,(
% 3.85/0.85    k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK3)) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_26 | ~spl9_39)),
% 3.85/0.85    inference(forward_demodulation,[],[f2058,f1103])).
% 3.85/0.85  fof(f1103,plain,(
% 3.85/0.85    k1_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK3)) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK3)) | (spl9_1 | ~spl9_6 | ~spl9_9 | ~spl9_10 | ~spl9_39)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f141,f135,f118,f420,f85])).
% 3.85/0.85  fof(f2058,plain,(
% 3.85/0.85    k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_26)),
% 3.85/0.85    inference(forward_demodulation,[],[f2057,f260])).
% 3.85/0.85  fof(f2057,plain,(
% 3.85/0.85    k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK2),k4_lattices(sK0,sK2,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11)),
% 3.85/0.85    inference(forward_demodulation,[],[f2005,f356])).
% 3.85/0.85  fof(f2005,plain,(
% 3.85/0.85    k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK2),k2_lattices(sK0,sK2,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_7)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f108,f103,f118,f118,f123,f79])).
% 3.85/0.85  fof(f5078,plain,(
% 3.85/0.85    spl9_51 | spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_39 | ~spl9_43 | ~spl9_50),
% 3.85/0.85    inference(avatar_split_clause,[],[f2045,f1283,f1248,f418,f253,f145,f139,f133,f127,f121,f116,f106,f101,f91,f5075])).
% 3.85/0.85  fof(f5075,plain,(
% 3.85/0.85    spl9_51 <=> sK3 = k3_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK3))),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).
% 3.85/0.85  fof(f1283,plain,(
% 3.85/0.85    spl9_50 <=> sK3 = k2_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3))),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).
% 3.85/0.85  fof(f2045,plain,(
% 3.85/0.85    sK3 = k3_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_39 | ~spl9_43 | ~spl9_50)),
% 3.85/0.85    inference(forward_demodulation,[],[f2044,f1285])).
% 3.85/0.85  fof(f1285,plain,(
% 3.85/0.85    sK3 = k2_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3)) | ~spl9_50),
% 3.85/0.85    inference(avatar_component_clause,[],[f1283])).
% 3.85/0.85  fof(f2044,plain,(
% 3.85/0.85    k2_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3)) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11 | ~spl9_25 | ~spl9_39 | ~spl9_43)),
% 3.85/0.85    inference(forward_demodulation,[],[f2043,f1193])).
% 3.85/0.85  fof(f1193,plain,(
% 3.85/0.85    k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),sK3) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK3)) | (spl9_1 | ~spl9_7 | ~spl9_9 | ~spl9_10 | ~spl9_39)),
% 3.85/0.85    inference(forward_demodulation,[],[f1095,f1122])).
% 3.85/0.85  fof(f1122,plain,(
% 3.85/0.85    k3_lattices(sK0,k4_lattices(sK0,sK2,sK3),sK3) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK3)) | (spl9_1 | ~spl9_7 | ~spl9_9 | ~spl9_10 | ~spl9_39)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f141,f135,f123,f420,f86])).
% 3.85/0.85  fof(f1095,plain,(
% 3.85/0.85    k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),sK3) = k3_lattices(sK0,k4_lattices(sK0,sK2,sK3),sK3) | (spl9_1 | ~spl9_7 | ~spl9_9 | ~spl9_10 | ~spl9_39)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f141,f135,f123,f420,f85])).
% 3.85/0.85  fof(f2043,plain,(
% 3.85/0.85    k2_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),sK3) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_25 | ~spl9_43)),
% 3.85/0.85    inference(forward_demodulation,[],[f2042,f1250])).
% 3.85/0.85  fof(f2042,plain,(
% 3.85/0.85    k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),sK3) = k2_lattices(sK0,sK3,k1_lattices(sK0,sK2,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_25)),
% 3.85/0.85    inference(forward_demodulation,[],[f2041,f396])).
% 3.85/0.85  fof(f2041,plain,(
% 3.85/0.85    k2_lattices(sK0,sK3,k1_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),sK3) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_25)),
% 3.85/0.85    inference(forward_demodulation,[],[f2006,f255])).
% 3.85/0.85  fof(f2006,plain,(
% 3.85/0.85    k2_lattices(sK0,sK3,k1_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k2_lattices(sK0,sK3,sK3)) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_7)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f108,f103,f123,f118,f123,f79])).
% 3.85/0.85  fof(f1286,plain,(
% 3.85/0.85    spl9_50 | spl9_1 | ~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_9 | ~spl9_10 | ~spl9_13),
% 3.85/0.85    inference(avatar_split_clause,[],[f318,f157,f139,f133,f121,f116,f106,f91,f1283])).
% 3.85/0.85  fof(f318,plain,(
% 3.85/0.85    sK3 = k2_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3)) | (spl9_1 | ~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_9 | ~spl9_10 | ~spl9_13)),
% 3.85/0.85    inference(backward_demodulation,[],[f281,f315])).
% 3.85/0.85  fof(f281,plain,(
% 3.85/0.85    sK3 = k2_lattices(sK0,sK3,k3_lattices(sK0,sK3,sK2)) | (spl9_1 | ~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_9 | ~spl9_10 | ~spl9_13)),
% 3.85/0.85    inference(backward_demodulation,[],[f242,f272])).
% 3.85/0.85  fof(f242,plain,(
% 3.85/0.85    sK3 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,sK2)) | (spl9_1 | ~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_13)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f108,f159,f123,f118,f75])).
% 3.85/0.85  fof(f1281,plain,(
% 3.85/0.85    spl9_49 | spl9_1 | ~spl9_6 | ~spl9_7 | ~spl9_9 | ~spl9_10),
% 3.85/0.85    inference(avatar_split_clause,[],[f315,f139,f133,f121,f116,f91,f1278])).
% 3.85/0.85  fof(f1278,plain,(
% 3.85/0.85    spl9_49 <=> k3_lattices(sK0,sK2,sK3) = k3_lattices(sK0,sK3,sK2)),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).
% 3.85/0.85  fof(f1276,plain,(
% 3.85/0.85    spl9_48 | spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_9 | ~spl9_10),
% 3.85/0.85    inference(avatar_split_clause,[],[f314,f139,f133,f121,f111,f91,f1273])).
% 3.85/0.85  fof(f1273,plain,(
% 3.85/0.85    spl9_48 <=> k3_lattices(sK0,sK3,sK1) = k3_lattices(sK0,sK1,sK3)),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).
% 3.85/0.85  fof(f1271,plain,(
% 3.85/0.85    spl9_47 | spl9_1 | ~spl9_5 | ~spl9_6 | ~spl9_9 | ~spl9_10),
% 3.85/0.85    inference(avatar_split_clause,[],[f311,f139,f133,f116,f111,f91,f1268])).
% 3.85/0.85  fof(f1266,plain,(
% 3.85/0.85    spl9_46 | spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_9 | ~spl9_10 | ~spl9_13),
% 3.85/0.85    inference(avatar_split_clause,[],[f284,f157,f139,f133,f116,f111,f106,f91,f1263])).
% 3.85/0.85  fof(f284,plain,(
% 3.85/0.85    sK1 = k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2)) | (spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_9 | ~spl9_10 | ~spl9_13)),
% 3.85/0.85    inference(backward_demodulation,[],[f240,f270])).
% 3.85/0.85  fof(f270,plain,(
% 3.85/0.85    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2) | (spl9_1 | ~spl9_5 | ~spl9_6 | ~spl9_9 | ~spl9_10)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f141,f135,f113,f118,f85])).
% 3.85/0.85  fof(f240,plain,(
% 3.85/0.85    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) | (spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_6 | ~spl9_13)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f108,f159,f113,f118,f75])).
% 3.85/0.85  fof(f1261,plain,(
% 3.85/0.85    spl9_45 | spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_9 | ~spl9_10 | ~spl9_13),
% 3.85/0.85    inference(avatar_split_clause,[],[f280,f157,f139,f133,f121,f111,f106,f91,f1258])).
% 3.85/0.85  fof(f280,plain,(
% 3.85/0.85    sK1 = k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_9 | ~spl9_10 | ~spl9_13)),
% 3.85/0.85    inference(backward_demodulation,[],[f243,f273])).
% 3.85/0.85  fof(f273,plain,(
% 3.85/0.85    k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK1,sK3) | (spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_9 | ~spl9_10)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f141,f135,f113,f123,f85])).
% 3.85/0.85  fof(f243,plain,(
% 3.85/0.85    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_7 | ~spl9_13)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f108,f159,f113,f123,f75])).
% 3.85/0.85  fof(f1256,plain,(
% 3.85/0.85    spl9_44 | spl9_1 | ~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_9 | ~spl9_10 | ~spl9_13),
% 3.85/0.85    inference(avatar_split_clause,[],[f279,f157,f139,f133,f121,f116,f106,f91,f1253])).
% 3.85/0.85  fof(f279,plain,(
% 3.85/0.85    sK2 = k2_lattices(sK0,sK2,k3_lattices(sK0,sK2,sK3)) | (spl9_1 | ~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_9 | ~spl9_10 | ~spl9_13)),
% 3.85/0.85    inference(backward_demodulation,[],[f244,f274])).
% 3.85/0.85  fof(f274,plain,(
% 3.85/0.85    k3_lattices(sK0,sK2,sK3) = k1_lattices(sK0,sK2,sK3) | (spl9_1 | ~spl9_6 | ~spl9_7 | ~spl9_9 | ~spl9_10)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f141,f135,f118,f123,f85])).
% 3.85/0.85  fof(f244,plain,(
% 3.85/0.85    sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK3)) | (spl9_1 | ~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_13)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f108,f159,f118,f123,f75])).
% 3.85/0.85  fof(f1251,plain,(
% 3.85/0.85    spl9_43 | spl9_1 | ~spl9_6 | ~spl9_7 | ~spl9_9 | ~spl9_10),
% 3.85/0.85    inference(avatar_split_clause,[],[f274,f139,f133,f121,f116,f91,f1248])).
% 3.85/0.85  fof(f1246,plain,(
% 3.85/0.85    spl9_42 | spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_9 | ~spl9_10),
% 3.85/0.85    inference(avatar_split_clause,[],[f273,f139,f133,f121,f111,f91,f1243])).
% 3.85/0.85  fof(f1241,plain,(
% 3.85/0.85    spl9_41 | spl9_1 | ~spl9_5 | ~spl9_6 | ~spl9_9 | ~spl9_10),
% 3.85/0.85    inference(avatar_split_clause,[],[f270,f139,f133,f116,f111,f91,f1238])).
% 3.85/0.85  fof(f1236,plain,(
% 3.85/0.85    ~spl9_40 | spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11),
% 3.85/0.85    inference(avatar_split_clause,[],[f400,f145,f139,f133,f127,f121,f111,f91,f1233])).
% 3.85/0.85  fof(f400,plain,(
% 3.85/0.85    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)),k3_lattices(sK0,sK1,sK3)) != k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)),k4_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_9 | ~spl9_10 | ~spl9_11)),
% 3.85/0.85    inference(backward_demodulation,[],[f324,f392])).
% 3.85/0.85  fof(f324,plain,(
% 3.85/0.85    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)),k4_lattices(sK0,sK3,sK1)) != k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)),k3_lattices(sK0,sK1,sK3)) | (spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_9 | ~spl9_10)),
% 3.85/0.85    inference(backward_demodulation,[],[f65,f314])).
% 3.85/0.85  fof(f65,plain,(
% 3.85/0.85    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)),k3_lattices(sK0,sK3,sK1)) != k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)),k4_lattices(sK0,sK3,sK1))),
% 3.85/0.85    inference(cnf_transformation,[],[f46])).
% 3.85/0.85  fof(f46,plain,(
% 3.85/0.85    (((k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)),k3_lattices(sK0,sK3,sK1)) != k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)),k4_lattices(sK0,sK3,sK1)) & m1_subset_1(sK3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v11_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 3.85/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f45,f44,f43,f42])).
% 3.85/0.85  fof(f42,plain,(
% 3.85/0.85    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1)) != k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,X2),k3_lattices(sK0,X2,X3)),k3_lattices(sK0,X3,X1)) != k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,X2),k4_lattices(sK0,X2,X3)),k4_lattices(sK0,X3,X1)) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v11_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 3.85/0.85    introduced(choice_axiom,[])).
% 3.85/0.85  fof(f43,plain,(
% 3.85/0.85    ? [X1] : (? [X2] : (? [X3] : (k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,X2),k3_lattices(sK0,X2,X3)),k3_lattices(sK0,X3,X1)) != k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,X2),k4_lattices(sK0,X2,X3)),k4_lattices(sK0,X3,X1)) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,X2),k3_lattices(sK0,X2,X3)),k3_lattices(sK0,X3,sK1)) != k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,X2),k4_lattices(sK0,X2,X3)),k4_lattices(sK0,X3,sK1)) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 3.85/0.85    introduced(choice_axiom,[])).
% 3.85/0.85  fof(f44,plain,(
% 3.85/0.85    ? [X2] : (? [X3] : (k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,X2),k3_lattices(sK0,X2,X3)),k3_lattices(sK0,X3,sK1)) != k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,X2),k4_lattices(sK0,X2,X3)),k4_lattices(sK0,X3,sK1)) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) => (? [X3] : (k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,X3)),k3_lattices(sK0,X3,sK1)) != k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,X3)),k4_lattices(sK0,X3,sK1)) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 3.85/0.85    introduced(choice_axiom,[])).
% 3.85/0.85  fof(f45,plain,(
% 3.85/0.85    ? [X3] : (k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,X3)),k3_lattices(sK0,X3,sK1)) != k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,X3)),k4_lattices(sK0,X3,sK1)) & m1_subset_1(X3,u1_struct_0(sK0))) => (k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)),k3_lattices(sK0,sK3,sK1)) != k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)),k4_lattices(sK0,sK3,sK1)) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 3.85/0.85    introduced(choice_axiom,[])).
% 3.85/0.85  fof(f18,plain,(
% 3.85/0.85    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1)) != k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.85/0.85    inference(flattening,[],[f17])).
% 3.85/0.85  fof(f17,plain,(
% 3.85/0.85    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1)) != k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.85/0.85    inference(ennf_transformation,[],[f14])).
% 3.85/0.85  fof(f14,negated_conjecture,(
% 3.85/0.85    ~! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1)) = k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1))))))),
% 3.85/0.85    inference(negated_conjecture,[],[f13])).
% 3.85/0.85  fof(f13,conjecture,(
% 3.85/0.85    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1)) = k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1))))))),
% 3.85/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattices)).
% 3.85/0.85  fof(f421,plain,(
% 3.85/0.85    spl9_39 | spl9_1 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11),
% 3.85/0.85    inference(avatar_split_clause,[],[f210,f145,f127,f121,f116,f91,f418])).
% 3.85/0.85  fof(f210,plain,(
% 3.85/0.85    m1_subset_1(k4_lattices(sK0,sK2,sK3),u1_struct_0(sK0)) | (spl9_1 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_11)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f147,f129,f118,f123,f87])).
% 3.85/0.85  fof(f416,plain,(
% 3.85/0.85    spl9_38 | spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_11),
% 3.85/0.85    inference(avatar_split_clause,[],[f209,f145,f127,f121,f111,f91,f413])).
% 3.85/0.85  fof(f209,plain,(
% 3.85/0.85    m1_subset_1(k4_lattices(sK0,sK1,sK3),u1_struct_0(sK0)) | (spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_11)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f147,f129,f113,f123,f87])).
% 3.85/0.85  fof(f411,plain,(
% 3.85/0.85    spl9_37 | spl9_1 | ~spl9_5 | ~spl9_6 | ~spl9_8 | ~spl9_11),
% 3.85/0.85    inference(avatar_split_clause,[],[f206,f145,f127,f116,f111,f91,f408])).
% 3.85/0.85  fof(f206,plain,(
% 3.85/0.85    m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | (spl9_1 | ~spl9_5 | ~spl9_6 | ~spl9_8 | ~spl9_11)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f147,f129,f113,f118,f87])).
% 3.85/0.85  fof(f381,plain,(
% 3.85/0.85    spl9_36 | spl9_1 | ~spl9_5 | ~spl9_8 | ~spl9_11 | ~spl9_27),
% 3.85/0.85    inference(avatar_split_clause,[],[f363,f263,f145,f127,f111,f91,f378])).
% 3.85/0.85  fof(f378,plain,(
% 3.85/0.85    spl9_36 <=> sK1 = k4_lattices(sK0,sK1,sK1)),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).
% 3.85/0.85  fof(f363,plain,(
% 3.85/0.85    sK1 = k4_lattices(sK0,sK1,sK1) | (spl9_1 | ~spl9_5 | ~spl9_8 | ~spl9_11 | ~spl9_27)),
% 3.85/0.85    inference(forward_demodulation,[],[f349,f265])).
% 3.85/0.85  fof(f349,plain,(
% 3.85/0.85    k4_lattices(sK0,sK1,sK1) = k2_lattices(sK0,sK1,sK1) | (spl9_1 | ~spl9_5 | ~spl9_8 | ~spl9_11)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f147,f129,f113,f113,f88])).
% 3.85/0.85  fof(f376,plain,(
% 3.85/0.85    spl9_35 | spl9_1 | ~spl9_6 | ~spl9_8 | ~spl9_11 | ~spl9_26),
% 3.85/0.85    inference(avatar_split_clause,[],[f361,f258,f145,f127,f116,f91,f373])).
% 3.85/0.85  fof(f373,plain,(
% 3.85/0.85    spl9_35 <=> sK2 = k4_lattices(sK0,sK2,sK2)),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).
% 3.85/0.85  fof(f361,plain,(
% 3.85/0.85    sK2 = k4_lattices(sK0,sK2,sK2) | (spl9_1 | ~spl9_6 | ~spl9_8 | ~spl9_11 | ~spl9_26)),
% 3.85/0.85    inference(forward_demodulation,[],[f353,f260])).
% 3.85/0.85  fof(f353,plain,(
% 3.85/0.85    k4_lattices(sK0,sK2,sK2) = k2_lattices(sK0,sK2,sK2) | (spl9_1 | ~spl9_6 | ~spl9_8 | ~spl9_11)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f147,f129,f118,f118,f88])).
% 3.85/0.85  fof(f371,plain,(
% 3.85/0.85    spl9_34 | spl9_1 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_25),
% 3.85/0.85    inference(avatar_split_clause,[],[f359,f253,f145,f127,f121,f91,f368])).
% 3.85/0.85  fof(f368,plain,(
% 3.85/0.85    spl9_34 <=> sK3 = k4_lattices(sK0,sK3,sK3)),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).
% 3.85/0.85  fof(f359,plain,(
% 3.85/0.85    sK3 = k4_lattices(sK0,sK3,sK3) | (spl9_1 | ~spl9_7 | ~spl9_8 | ~spl9_11 | ~spl9_25)),
% 3.85/0.85    inference(forward_demodulation,[],[f357,f255])).
% 3.85/0.85  fof(f357,plain,(
% 3.85/0.85    k4_lattices(sK0,sK3,sK3) = k2_lattices(sK0,sK3,sK3) | (spl9_1 | ~spl9_7 | ~spl9_8 | ~spl9_11)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f147,f129,f123,f123,f88])).
% 3.85/0.85  fof(f348,plain,(
% 3.85/0.85    spl9_33 | spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_11),
% 3.85/0.85    inference(avatar_split_clause,[],[f205,f145,f127,f121,f111,f91,f345])).
% 3.85/0.85  fof(f345,plain,(
% 3.85/0.85    spl9_33 <=> m1_subset_1(k4_lattices(sK0,sK3,sK1),u1_struct_0(sK0))),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).
% 3.85/0.85  fof(f205,plain,(
% 3.85/0.85    m1_subset_1(k4_lattices(sK0,sK3,sK1),u1_struct_0(sK0)) | (spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_8 | ~spl9_11)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f147,f129,f123,f113,f87])).
% 3.85/0.85  fof(f343,plain,(
% 3.85/0.85    spl9_32 | spl9_1 | ~spl9_5 | ~spl9_6 | ~spl9_8 | ~spl9_11),
% 3.85/0.85    inference(avatar_split_clause,[],[f204,f145,f127,f116,f111,f91,f340])).
% 3.85/0.85  fof(f340,plain,(
% 3.85/0.85    spl9_32 <=> m1_subset_1(k4_lattices(sK0,sK2,sK1),u1_struct_0(sK0))),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 3.85/0.85  fof(f204,plain,(
% 3.85/0.85    m1_subset_1(k4_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) | (spl9_1 | ~spl9_5 | ~spl9_6 | ~spl9_8 | ~spl9_11)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f147,f129,f118,f113,f87])).
% 3.85/0.85  fof(f338,plain,(
% 3.85/0.85    spl9_31 | spl9_1 | ~spl9_5 | ~spl9_8 | ~spl9_11),
% 3.85/0.85    inference(avatar_split_clause,[],[f203,f145,f127,f111,f91,f335])).
% 3.85/0.85  fof(f335,plain,(
% 3.85/0.85    spl9_31 <=> m1_subset_1(k4_lattices(sK0,sK1,sK1),u1_struct_0(sK0))),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 3.85/0.85  fof(f203,plain,(
% 3.85/0.85    m1_subset_1(k4_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) | (spl9_1 | ~spl9_5 | ~spl9_8 | ~spl9_11)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f147,f129,f113,f113,f87])).
% 3.85/0.85  fof(f305,plain,(
% 3.85/0.85    spl9_30 | spl9_1 | ~spl9_5 | ~spl9_9 | ~spl9_10 | ~spl9_14),
% 3.85/0.85    inference(avatar_split_clause,[],[f287,f165,f139,f133,f111,f91,f302])).
% 3.85/0.85  fof(f302,plain,(
% 3.85/0.85    spl9_30 <=> sK1 = k3_lattices(sK0,sK1,sK1)),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 3.85/0.85  fof(f165,plain,(
% 3.85/0.85    spl9_14 <=> sK1 = k1_lattices(sK0,sK1,sK1)),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 3.85/0.85  fof(f287,plain,(
% 3.85/0.85    sK1 = k3_lattices(sK0,sK1,sK1) | (spl9_1 | ~spl9_5 | ~spl9_9 | ~spl9_10 | ~spl9_14)),
% 3.85/0.85    inference(forward_demodulation,[],[f267,f167])).
% 3.85/0.85  fof(f167,plain,(
% 3.85/0.85    sK1 = k1_lattices(sK0,sK1,sK1) | ~spl9_14),
% 3.85/0.85    inference(avatar_component_clause,[],[f165])).
% 3.85/0.85  fof(f267,plain,(
% 3.85/0.85    k1_lattices(sK0,sK1,sK1) = k3_lattices(sK0,sK1,sK1) | (spl9_1 | ~spl9_5 | ~spl9_9 | ~spl9_10)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f141,f135,f113,f113,f85])).
% 3.85/0.85  fof(f300,plain,(
% 3.85/0.85    spl9_29 | spl9_1 | ~spl9_6 | ~spl9_9 | ~spl9_10 | ~spl9_15),
% 3.85/0.85    inference(avatar_split_clause,[],[f282,f170,f139,f133,f116,f91,f297])).
% 3.85/0.85  fof(f297,plain,(
% 3.85/0.85    spl9_29 <=> sK2 = k3_lattices(sK0,sK2,sK2)),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 3.85/0.85  fof(f170,plain,(
% 3.85/0.85    spl9_15 <=> sK2 = k1_lattices(sK0,sK2,sK2)),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 3.85/0.85  fof(f282,plain,(
% 3.85/0.85    sK2 = k3_lattices(sK0,sK2,sK2) | (spl9_1 | ~spl9_6 | ~spl9_9 | ~spl9_10 | ~spl9_15)),
% 3.85/0.85    inference(forward_demodulation,[],[f271,f172])).
% 3.85/0.85  fof(f172,plain,(
% 3.85/0.85    sK2 = k1_lattices(sK0,sK2,sK2) | ~spl9_15),
% 3.85/0.85    inference(avatar_component_clause,[],[f170])).
% 3.85/0.85  fof(f271,plain,(
% 3.85/0.85    k1_lattices(sK0,sK2,sK2) = k3_lattices(sK0,sK2,sK2) | (spl9_1 | ~spl9_6 | ~spl9_9 | ~spl9_10)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f141,f135,f118,f118,f85])).
% 3.85/0.85  fof(f295,plain,(
% 3.85/0.85    spl9_28 | spl9_1 | ~spl9_7 | ~spl9_9 | ~spl9_10 | ~spl9_16),
% 3.85/0.85    inference(avatar_split_clause,[],[f277,f175,f139,f133,f121,f91,f292])).
% 3.85/0.85  fof(f292,plain,(
% 3.85/0.85    spl9_28 <=> sK3 = k3_lattices(sK0,sK3,sK3)),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).
% 3.85/0.85  fof(f175,plain,(
% 3.85/0.85    spl9_16 <=> sK3 = k1_lattices(sK0,sK3,sK3)),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 3.85/0.85  fof(f277,plain,(
% 3.85/0.85    sK3 = k3_lattices(sK0,sK3,sK3) | (spl9_1 | ~spl9_7 | ~spl9_9 | ~spl9_10 | ~spl9_16)),
% 3.85/0.85    inference(forward_demodulation,[],[f275,f177])).
% 3.85/0.85  fof(f177,plain,(
% 3.85/0.85    sK3 = k1_lattices(sK0,sK3,sK3) | ~spl9_16),
% 3.85/0.85    inference(avatar_component_clause,[],[f175])).
% 3.85/0.85  fof(f275,plain,(
% 3.85/0.85    k1_lattices(sK0,sK3,sK3) = k3_lattices(sK0,sK3,sK3) | (spl9_1 | ~spl9_7 | ~spl9_9 | ~spl9_10)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f141,f135,f123,f123,f85])).
% 3.85/0.85  fof(f266,plain,(
% 3.85/0.85    spl9_27 | spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_13 | ~spl9_14),
% 3.85/0.85    inference(avatar_split_clause,[],[f249,f165,f157,f111,f106,f91,f263])).
% 3.85/0.85  fof(f249,plain,(
% 3.85/0.85    sK1 = k2_lattices(sK0,sK1,sK1) | (spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_13 | ~spl9_14)),
% 3.85/0.85    inference(forward_demodulation,[],[f237,f167])).
% 3.85/0.85  fof(f237,plain,(
% 3.85/0.85    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) | (spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_13)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f108,f159,f113,f113,f75])).
% 3.85/0.85  fof(f261,plain,(
% 3.85/0.85    spl9_26 | spl9_1 | ~spl9_4 | ~spl9_6 | ~spl9_13 | ~spl9_15),
% 3.85/0.85    inference(avatar_split_clause,[],[f248,f170,f157,f116,f106,f91,f258])).
% 3.85/0.85  fof(f248,plain,(
% 3.85/0.85    sK2 = k2_lattices(sK0,sK2,sK2) | (spl9_1 | ~spl9_4 | ~spl9_6 | ~spl9_13 | ~spl9_15)),
% 3.85/0.85    inference(forward_demodulation,[],[f241,f172])).
% 3.85/0.85  fof(f241,plain,(
% 3.85/0.85    sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK2)) | (spl9_1 | ~spl9_4 | ~spl9_6 | ~spl9_13)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f108,f159,f118,f118,f75])).
% 3.85/0.85  fof(f256,plain,(
% 3.85/0.85    spl9_25 | spl9_1 | ~spl9_4 | ~spl9_7 | ~spl9_13 | ~spl9_16),
% 3.85/0.85    inference(avatar_split_clause,[],[f247,f175,f157,f121,f106,f91,f253])).
% 3.85/0.85  fof(f247,plain,(
% 3.85/0.85    sK3 = k2_lattices(sK0,sK3,sK3) | (spl9_1 | ~spl9_4 | ~spl9_7 | ~spl9_13 | ~spl9_16)),
% 3.85/0.85    inference(forward_demodulation,[],[f245,f177])).
% 3.85/0.85  fof(f245,plain,(
% 3.85/0.85    sK3 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,sK3)) | (spl9_1 | ~spl9_4 | ~spl9_7 | ~spl9_13)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f108,f159,f123,f123,f75])).
% 3.85/0.85  fof(f236,plain,(
% 3.85/0.85    spl9_24 | spl9_1 | ~spl9_6 | ~spl9_7 | ~spl9_9 | ~spl9_10),
% 3.85/0.85    inference(avatar_split_clause,[],[f186,f139,f133,f121,f116,f91,f233])).
% 3.85/0.85  fof(f233,plain,(
% 3.85/0.85    spl9_24 <=> m1_subset_1(k3_lattices(sK0,sK2,sK3),u1_struct_0(sK0))),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 3.85/0.85  fof(f186,plain,(
% 3.85/0.85    m1_subset_1(k3_lattices(sK0,sK2,sK3),u1_struct_0(sK0)) | (spl9_1 | ~spl9_6 | ~spl9_7 | ~spl9_9 | ~spl9_10)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f141,f135,f118,f123,f84])).
% 3.85/0.85  fof(f84,plain,(
% 3.85/0.85    ( ! [X2,X0,X1] : (m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 3.85/0.85    inference(cnf_transformation,[],[f31])).
% 3.85/0.85  fof(f31,plain,(
% 3.85/0.85    ! [X0,X1,X2] : (m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 3.85/0.85    inference(flattening,[],[f30])).
% 3.85/0.85  fof(f30,plain,(
% 3.85/0.85    ! [X0,X1,X2] : (m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 3.85/0.85    inference(ennf_transformation,[],[f6])).
% 3.85/0.85  fof(f6,axiom,(
% 3.85/0.85    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 3.85/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_lattices)).
% 3.85/0.85  fof(f231,plain,(
% 3.85/0.85    spl9_23 | spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_9 | ~spl9_10),
% 3.85/0.85    inference(avatar_split_clause,[],[f185,f139,f133,f121,f111,f91,f228])).
% 3.85/0.85  fof(f185,plain,(
% 3.85/0.85    m1_subset_1(k3_lattices(sK0,sK1,sK3),u1_struct_0(sK0)) | (spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_9 | ~spl9_10)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f141,f135,f113,f123,f84])).
% 3.85/0.85  fof(f226,plain,(
% 3.85/0.85    spl9_22 | spl9_1 | ~spl9_6 | ~spl9_7 | ~spl9_9 | ~spl9_10),
% 3.85/0.85    inference(avatar_split_clause,[],[f184,f139,f133,f121,f116,f91,f223])).
% 3.85/0.85  fof(f223,plain,(
% 3.85/0.85    spl9_22 <=> m1_subset_1(k3_lattices(sK0,sK3,sK2),u1_struct_0(sK0))),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 3.85/0.85  fof(f184,plain,(
% 3.85/0.85    m1_subset_1(k3_lattices(sK0,sK3,sK2),u1_struct_0(sK0)) | (spl9_1 | ~spl9_6 | ~spl9_7 | ~spl9_9 | ~spl9_10)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f141,f135,f123,f118,f84])).
% 3.85/0.85  fof(f221,plain,(
% 3.85/0.85    spl9_21 | spl9_1 | ~spl9_6 | ~spl9_9 | ~spl9_10),
% 3.85/0.85    inference(avatar_split_clause,[],[f183,f139,f133,f116,f91,f218])).
% 3.85/0.85  fof(f218,plain,(
% 3.85/0.85    spl9_21 <=> m1_subset_1(k3_lattices(sK0,sK2,sK2),u1_struct_0(sK0))),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 3.85/0.85  fof(f183,plain,(
% 3.85/0.85    m1_subset_1(k3_lattices(sK0,sK2,sK2),u1_struct_0(sK0)) | (spl9_1 | ~spl9_6 | ~spl9_9 | ~spl9_10)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f141,f135,f118,f118,f84])).
% 3.85/0.85  fof(f216,plain,(
% 3.85/0.85    spl9_20 | spl9_1 | ~spl9_5 | ~spl9_6 | ~spl9_9 | ~spl9_10),
% 3.85/0.85    inference(avatar_split_clause,[],[f182,f139,f133,f116,f111,f91,f213])).
% 3.85/0.85  fof(f213,plain,(
% 3.85/0.85    spl9_20 <=> m1_subset_1(k3_lattices(sK0,sK1,sK2),u1_struct_0(sK0))),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 3.85/0.85  fof(f182,plain,(
% 3.85/0.85    m1_subset_1(k3_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | (spl9_1 | ~spl9_5 | ~spl9_6 | ~spl9_9 | ~spl9_10)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f141,f135,f113,f118,f84])).
% 3.85/0.85  fof(f202,plain,(
% 3.85/0.85    spl9_19 | spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_9 | ~spl9_10),
% 3.85/0.85    inference(avatar_split_clause,[],[f181,f139,f133,f121,f111,f91,f199])).
% 3.85/0.85  fof(f199,plain,(
% 3.85/0.85    spl9_19 <=> m1_subset_1(k3_lattices(sK0,sK3,sK1),u1_struct_0(sK0))),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 3.85/0.85  fof(f181,plain,(
% 3.85/0.85    m1_subset_1(k3_lattices(sK0,sK3,sK1),u1_struct_0(sK0)) | (spl9_1 | ~spl9_5 | ~spl9_7 | ~spl9_9 | ~spl9_10)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f141,f135,f123,f113,f84])).
% 3.85/0.85  fof(f197,plain,(
% 3.85/0.85    spl9_18 | spl9_1 | ~spl9_5 | ~spl9_6 | ~spl9_9 | ~spl9_10),
% 3.85/0.85    inference(avatar_split_clause,[],[f180,f139,f133,f116,f111,f91,f194])).
% 3.85/0.85  fof(f194,plain,(
% 3.85/0.85    spl9_18 <=> m1_subset_1(k3_lattices(sK0,sK2,sK1),u1_struct_0(sK0))),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 3.85/0.85  fof(f180,plain,(
% 3.85/0.85    m1_subset_1(k3_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) | (spl9_1 | ~spl9_5 | ~spl9_6 | ~spl9_9 | ~spl9_10)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f141,f135,f118,f113,f84])).
% 3.85/0.85  fof(f192,plain,(
% 3.85/0.85    spl9_17 | spl9_1 | ~spl9_5 | ~spl9_9 | ~spl9_10),
% 3.85/0.85    inference(avatar_split_clause,[],[f179,f139,f133,f111,f91,f189])).
% 3.85/0.85  fof(f189,plain,(
% 3.85/0.85    spl9_17 <=> m1_subset_1(k3_lattices(sK0,sK1,sK1),u1_struct_0(sK0))),
% 3.85/0.85    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 3.85/0.85  fof(f179,plain,(
% 3.85/0.85    m1_subset_1(k3_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) | (spl9_1 | ~spl9_5 | ~spl9_9 | ~spl9_10)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f141,f135,f113,f113,f84])).
% 3.85/0.85  fof(f178,plain,(
% 3.85/0.85    spl9_16 | spl9_1 | ~spl9_4 | ~spl9_7 | ~spl9_11 | ~spl9_12 | ~spl9_13),
% 3.85/0.85    inference(avatar_split_clause,[],[f163,f157,f151,f145,f121,f106,f91,f175])).
% 3.85/0.85  fof(f163,plain,(
% 3.85/0.85    sK3 = k1_lattices(sK0,sK3,sK3) | (spl9_1 | ~spl9_4 | ~spl9_7 | ~spl9_11 | ~spl9_12 | ~spl9_13)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f147,f153,f159,f108,f123,f74])).
% 3.85/0.85  fof(f173,plain,(
% 3.85/0.85    spl9_15 | spl9_1 | ~spl9_4 | ~spl9_6 | ~spl9_11 | ~spl9_12 | ~spl9_13),
% 3.85/0.85    inference(avatar_split_clause,[],[f162,f157,f151,f145,f116,f106,f91,f170])).
% 3.85/0.85  fof(f162,plain,(
% 3.85/0.85    sK2 = k1_lattices(sK0,sK2,sK2) | (spl9_1 | ~spl9_4 | ~spl9_6 | ~spl9_11 | ~spl9_12 | ~spl9_13)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f147,f153,f159,f108,f118,f74])).
% 3.85/0.85  fof(f168,plain,(
% 3.85/0.85    spl9_14 | spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_11 | ~spl9_12 | ~spl9_13),
% 3.85/0.85    inference(avatar_split_clause,[],[f161,f157,f151,f145,f111,f106,f91,f165])).
% 3.85/0.85  fof(f161,plain,(
% 3.85/0.85    sK1 = k1_lattices(sK0,sK1,sK1) | (spl9_1 | ~spl9_4 | ~spl9_5 | ~spl9_11 | ~spl9_12 | ~spl9_13)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f93,f147,f153,f159,f108,f113,f74])).
% 3.85/0.85  fof(f160,plain,(
% 3.85/0.85    spl9_13 | spl9_1 | ~spl9_2 | ~spl9_4),
% 3.85/0.85    inference(avatar_split_clause,[],[f155,f106,f96,f91,f157])).
% 3.85/0.85  fof(f155,plain,(
% 3.85/0.85    v9_lattices(sK0) | (spl9_1 | ~spl9_2 | ~spl9_4)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f108,f93,f98,f72])).
% 3.85/0.85  fof(f72,plain,(
% 3.85/0.85    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.85/0.85    inference(cnf_transformation,[],[f21])).
% 3.85/0.85  fof(f21,plain,(
% 3.85/0.85    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 3.85/0.85    inference(flattening,[],[f20])).
% 3.85/0.85  fof(f20,plain,(
% 3.85/0.85    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 3.85/0.85    inference(ennf_transformation,[],[f16])).
% 3.85/0.85  fof(f16,plain,(
% 3.85/0.85    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.85/0.85    inference(pure_predicate_removal,[],[f15])).
% 3.85/0.85  fof(f15,plain,(
% 3.85/0.85    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.85/0.85    inference(pure_predicate_removal,[],[f1])).
% 3.85/0.85  fof(f1,axiom,(
% 3.85/0.85    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.85/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 3.85/0.85  fof(f154,plain,(
% 3.85/0.85    spl9_12 | spl9_1 | ~spl9_2 | ~spl9_4),
% 3.85/0.85    inference(avatar_split_clause,[],[f149,f106,f96,f91,f151])).
% 3.85/0.85  fof(f149,plain,(
% 3.85/0.85    v8_lattices(sK0) | (spl9_1 | ~spl9_2 | ~spl9_4)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f108,f93,f98,f71])).
% 3.85/0.85  fof(f71,plain,(
% 3.85/0.85    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.85/0.85    inference(cnf_transformation,[],[f21])).
% 3.85/0.85  fof(f148,plain,(
% 3.85/0.85    spl9_11 | spl9_1 | ~spl9_2 | ~spl9_4),
% 3.85/0.85    inference(avatar_split_clause,[],[f143,f106,f96,f91,f145])).
% 3.85/0.85  fof(f143,plain,(
% 3.85/0.85    v6_lattices(sK0) | (spl9_1 | ~spl9_2 | ~spl9_4)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f108,f93,f98,f70])).
% 3.85/0.85  fof(f70,plain,(
% 3.85/0.85    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.85/0.85    inference(cnf_transformation,[],[f21])).
% 3.85/0.85  fof(f142,plain,(
% 3.85/0.85    spl9_10 | spl9_1 | ~spl9_2 | ~spl9_4),
% 3.85/0.85    inference(avatar_split_clause,[],[f137,f106,f96,f91,f139])).
% 3.85/0.85  fof(f137,plain,(
% 3.85/0.85    v4_lattices(sK0) | (spl9_1 | ~spl9_2 | ~spl9_4)),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f108,f93,f98,f69])).
% 3.85/0.85  fof(f69,plain,(
% 3.85/0.85    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.85/0.85    inference(cnf_transformation,[],[f21])).
% 3.85/0.85  fof(f136,plain,(
% 3.85/0.85    spl9_9 | ~spl9_4),
% 3.85/0.85    inference(avatar_split_clause,[],[f131,f106,f133])).
% 3.85/0.85  fof(f131,plain,(
% 3.85/0.85    l2_lattices(sK0) | ~spl9_4),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f108,f67])).
% 3.85/0.85  fof(f67,plain,(
% 3.85/0.85    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 3.85/0.85    inference(cnf_transformation,[],[f19])).
% 3.85/0.85  fof(f19,plain,(
% 3.85/0.85    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 3.85/0.85    inference(ennf_transformation,[],[f8])).
% 3.85/0.85  fof(f8,axiom,(
% 3.85/0.85    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 3.85/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 3.85/0.85  fof(f130,plain,(
% 3.85/0.85    spl9_8 | ~spl9_4),
% 3.85/0.85    inference(avatar_split_clause,[],[f125,f106,f127])).
% 3.85/0.85  fof(f125,plain,(
% 3.85/0.85    l1_lattices(sK0) | ~spl9_4),
% 3.85/0.85    inference(unit_resulting_resolution,[],[f108,f66])).
% 3.85/0.85  fof(f66,plain,(
% 3.85/0.85    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 3.85/0.85    inference(cnf_transformation,[],[f19])).
% 3.85/0.85  fof(f124,plain,(
% 3.85/0.85    spl9_7),
% 3.85/0.85    inference(avatar_split_clause,[],[f64,f121])).
% 3.85/0.85  fof(f64,plain,(
% 3.85/0.85    m1_subset_1(sK3,u1_struct_0(sK0))),
% 3.85/0.85    inference(cnf_transformation,[],[f46])).
% 3.85/0.85  fof(f119,plain,(
% 3.85/0.85    spl9_6),
% 3.85/0.85    inference(avatar_split_clause,[],[f63,f116])).
% 3.85/0.85  fof(f63,plain,(
% 3.85/0.85    m1_subset_1(sK2,u1_struct_0(sK0))),
% 3.85/0.85    inference(cnf_transformation,[],[f46])).
% 3.85/0.85  fof(f114,plain,(
% 3.85/0.85    spl9_5),
% 3.85/0.85    inference(avatar_split_clause,[],[f62,f111])).
% 3.85/0.85  fof(f62,plain,(
% 3.85/0.85    m1_subset_1(sK1,u1_struct_0(sK0))),
% 3.85/0.85    inference(cnf_transformation,[],[f46])).
% 3.85/0.85  fof(f109,plain,(
% 3.85/0.85    spl9_4),
% 3.85/0.85    inference(avatar_split_clause,[],[f61,f106])).
% 3.85/0.85  fof(f61,plain,(
% 3.85/0.85    l3_lattices(sK0)),
% 3.85/0.85    inference(cnf_transformation,[],[f46])).
% 3.85/0.85  fof(f104,plain,(
% 3.85/0.85    spl9_3),
% 3.85/0.85    inference(avatar_split_clause,[],[f60,f101])).
% 3.85/0.85  fof(f60,plain,(
% 3.85/0.85    v11_lattices(sK0)),
% 3.85/0.85    inference(cnf_transformation,[],[f46])).
% 3.85/0.85  fof(f99,plain,(
% 3.85/0.85    spl9_2),
% 3.85/0.85    inference(avatar_split_clause,[],[f59,f96])).
% 3.85/0.85  fof(f59,plain,(
% 3.85/0.85    v10_lattices(sK0)),
% 3.85/0.85    inference(cnf_transformation,[],[f46])).
% 3.85/0.85  fof(f94,plain,(
% 3.85/0.85    ~spl9_1),
% 3.85/0.85    inference(avatar_split_clause,[],[f58,f91])).
% 3.85/0.85  fof(f58,plain,(
% 3.85/0.85    ~v2_struct_0(sK0)),
% 3.85/0.85    inference(cnf_transformation,[],[f46])).
% 3.85/0.85  % SZS output end Proof for theBenchmark
% 3.85/0.85  % (9746)------------------------------
% 3.85/0.85  % (9746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.85/0.85  % (9746)Termination reason: Refutation
% 3.85/0.85  
% 3.85/0.85  % (9746)Memory used [KB]: 8059
% 3.85/0.85  % (9746)Time elapsed: 0.423 s
% 3.85/0.85  % (9746)------------------------------
% 3.85/0.85  % (9746)------------------------------
% 3.85/0.85  % (9743)Success in time 0.489 s
%------------------------------------------------------------------------------
