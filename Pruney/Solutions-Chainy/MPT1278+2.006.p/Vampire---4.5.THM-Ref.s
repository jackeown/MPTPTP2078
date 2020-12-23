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
% DateTime   : Thu Dec  3 13:12:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 366 expanded)
%              Number of leaves         :   43 ( 161 expanded)
%              Depth                    :   11
%              Number of atoms          :  569 (1118 expanded)
%              Number of equality atoms :  107 ( 203 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (24085)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f1305,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f92,f97,f102,f107,f112,f142,f150,f174,f179,f227,f248,f369,f507,f790,f796,f817,f834,f946,f1062,f1190,f1214,f1273,f1304])).

fof(f1304,plain,
    ( spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_20
    | ~ spl2_113 ),
    inference(avatar_contradiction_clause,[],[f1303])).

fof(f1303,plain,
    ( $false
    | spl2_1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_20
    | ~ spl2_113 ),
    inference(subsumption_resolution,[],[f1302,f81])).

fof(f81,plain,
    ( k1_xboole_0 != sK1
    | spl2_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl2_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1302,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_20
    | ~ spl2_113 ),
    inference(forward_demodulation,[],[f1301,f223])).

fof(f223,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl2_20
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f1301,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_113 ),
    inference(forward_demodulation,[],[f1300,f59])).

fof(f59,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f1300,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_113 ),
    inference(forward_demodulation,[],[f1299,f127])).

fof(f127,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f96,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f96,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f1299,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_113 ),
    inference(subsumption_resolution,[],[f1298,f101])).

fof(f101,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl2_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f1298,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4
    | ~ spl2_113 ),
    inference(subsumption_resolution,[],[f1297,f96])).

fof(f1297,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_113 ),
    inference(superposition,[],[f60,f1272])).

fof(f1272,plain,
    ( k1_xboole_0 = k2_tops_1(sK0,sK1)
    | ~ spl2_113 ),
    inference(avatar_component_clause,[],[f1270])).

fof(f1270,plain,
    ( spl2_113
  <=> k1_xboole_0 = k2_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_113])])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f1273,plain,
    ( spl2_113
    | ~ spl2_104
    | ~ spl2_109 ),
    inference(avatar_split_clause,[],[f1249,f1211,f1059,f1270])).

fof(f1059,plain,
    ( spl2_104
  <=> k2_pre_topc(sK0,k1_xboole_0) = k2_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_104])])).

fof(f1211,plain,
    ( spl2_109
  <=> k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_109])])).

fof(f1249,plain,
    ( k1_xboole_0 = k2_tops_1(sK0,sK1)
    | ~ spl2_104
    | ~ spl2_109 ),
    inference(backward_demodulation,[],[f1061,f1213])).

fof(f1213,plain,
    ( k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)
    | ~ spl2_109 ),
    inference(avatar_component_clause,[],[f1211])).

fof(f1061,plain,
    ( k2_pre_topc(sK0,k1_xboole_0) = k2_tops_1(sK0,sK1)
    | ~ spl2_104 ),
    inference(avatar_component_clause,[],[f1059])).

fof(f1214,plain,
    ( spl2_109
    | ~ spl2_90
    | ~ spl2_108 ),
    inference(avatar_split_clause,[],[f1209,f1187,f811,f1211])).

fof(f811,plain,
    ( spl2_90
  <=> k2_pre_topc(sK0,k1_xboole_0) = k2_tops_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_90])])).

fof(f1187,plain,
    ( spl2_108
  <=> k1_xboole_0 = k2_tops_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_108])])).

fof(f1209,plain,
    ( k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)
    | ~ spl2_90
    | ~ spl2_108 ),
    inference(backward_demodulation,[],[f813,f1189])).

fof(f1189,plain,
    ( k1_xboole_0 = k2_tops_1(sK0,k1_xboole_0)
    | ~ spl2_108 ),
    inference(avatar_component_clause,[],[f1187])).

fof(f813,plain,
    ( k2_pre_topc(sK0,k1_xboole_0) = k2_tops_1(sK0,k1_xboole_0)
    | ~ spl2_90 ),
    inference(avatar_component_clause,[],[f811])).

fof(f1190,plain,
    ( spl2_108
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f1185,f147,f104,f99,f1187])).

fof(f104,plain,
    ( spl2_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f147,plain,
    ( spl2_10
  <=> v4_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f1185,plain,
    ( k1_xboole_0 = k2_tops_1(sK0,k1_xboole_0)
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f1172,f129])).

fof(f129,plain,(
    ! [X0,X1] : k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f128,f115])).

fof(f115,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f73,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f73,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f128,plain,(
    ! [X0,X1] : k7_subset_1(X0,k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(unit_resulting_resolution,[],[f58,f76])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f1172,plain,
    ( k2_tops_1(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k1_xboole_0,k1_tops_1(sK0,k1_xboole_0))
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f106,f101,f149,f58,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f149,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f147])).

fof(f106,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f1062,plain,
    ( spl2_104
    | ~ spl2_88
    | ~ spl2_92
    | ~ spl2_96 ),
    inference(avatar_split_clause,[],[f1057,f928,f831,f784,f1059])).

fof(f784,plain,
    ( spl2_88
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).

fof(f831,plain,
    ( spl2_92
  <=> k2_pre_topc(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_92])])).

fof(f928,plain,
    ( spl2_96
  <=> k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_96])])).

fof(f1057,plain,
    ( k2_pre_topc(sK0,k1_xboole_0) = k2_tops_1(sK0,sK1)
    | ~ spl2_88
    | ~ spl2_92
    | ~ spl2_96 ),
    inference(forward_demodulation,[],[f1029,f833])).

fof(f833,plain,
    ( k2_pre_topc(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl2_92 ),
    inference(avatar_component_clause,[],[f831])).

fof(f1029,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl2_88
    | ~ spl2_96 ),
    inference(backward_demodulation,[],[f786,f930])).

fof(f930,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_xboole_0)
    | ~ spl2_96 ),
    inference(avatar_component_clause,[],[f928])).

fof(f786,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0)
    | ~ spl2_88 ),
    inference(avatar_component_clause,[],[f784])).

fof(f946,plain,
    ( spl2_96
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f945,f241,f99,f94,f89,f928])).

fof(f89,plain,
    ( spl2_3
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f241,plain,
    ( spl2_22
  <=> k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f945,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_xboole_0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f944,f101])).

fof(f944,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f943,f96])).

fof(f943,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f915,f91])).

fof(f91,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f915,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_xboole_0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_22 ),
    inference(superposition,[],[f62,f243])).

fof(f243,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f241])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tops_1)).

fof(f834,plain,
    ( spl2_92
    | ~ spl2_87
    | ~ spl2_90 ),
    inference(avatar_split_clause,[],[f825,f811,f778,f831])).

fof(f778,plain,
    ( spl2_87
  <=> k2_tops_1(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).

fof(f825,plain,
    ( k2_pre_topc(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl2_87
    | ~ spl2_90 ),
    inference(backward_demodulation,[],[f780,f813])).

fof(f780,plain,
    ( k2_tops_1(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl2_87 ),
    inference(avatar_component_clause,[],[f778])).

fof(f817,plain,
    ( spl2_90
    | ~ spl2_13
    | ~ spl2_87 ),
    inference(avatar_split_clause,[],[f816,f778,f171,f811])).

fof(f171,plain,
    ( spl2_13
  <=> m1_subset_1(k2_pre_topc(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f816,plain,
    ( k2_pre_topc(sK0,k1_xboole_0) = k2_tops_1(sK0,k1_xboole_0)
    | ~ spl2_13
    | ~ spl2_87 ),
    inference(forward_demodulation,[],[f815,f59])).

fof(f815,plain,
    ( k2_tops_1(sK0,k1_xboole_0) = k4_xboole_0(k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl2_13
    | ~ spl2_87 ),
    inference(subsumption_resolution,[],[f807,f173])).

fof(f173,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f171])).

fof(f807,plain,
    ( k2_tops_1(sK0,k1_xboole_0) = k4_xboole_0(k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_87 ),
    inference(superposition,[],[f76,f780])).

fof(f796,plain,
    ( spl2_87
    | ~ spl2_5
    | ~ spl2_49 ),
    inference(avatar_split_clause,[],[f795,f486,f99,f778])).

fof(f486,plain,
    ( spl2_49
  <=> k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f795,plain,
    ( k2_tops_1(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl2_5
    | ~ spl2_49 ),
    inference(subsumption_resolution,[],[f794,f101])).

fof(f794,plain,
    ( k2_tops_1(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_49 ),
    inference(subsumption_resolution,[],[f744,f58])).

fof(f744,plain,
    ( k2_tops_1(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_49 ),
    inference(superposition,[],[f61,f488])).

fof(f488,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ spl2_49 ),
    inference(avatar_component_clause,[],[f486])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f790,plain,
    ( spl2_88
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f789,f221,f99,f94,f784])).

fof(f789,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0)
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f788,f101])).

fof(f788,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f742,f96])).

fof(f742,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_20 ),
    inference(superposition,[],[f61,f223])).

fof(f507,plain,
    ( spl2_49
    | ~ spl2_5
    | ~ spl2_14
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f506,f241,f176,f99,f486])).

fof(f176,plain,
    ( spl2_14
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f506,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ spl2_5
    | ~ spl2_14
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f505,f101])).

fof(f505,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_14
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f471,f178])).

fof(f178,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f176])).

fof(f471,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_22 ),
    inference(superposition,[],[f75,f243])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(f369,plain,
    ( spl2_23
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f342,f99,f94,f84,f245])).

fof(f245,plain,
    ( spl2_23
  <=> v2_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f84,plain,
    ( spl2_2
  <=> v3_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f342,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f101,f86,f96,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | ~ v2_tops_1(k2_pre_topc(X0,X1),X0) )
            & ( v2_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v3_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

fof(f86,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f248,plain,
    ( spl2_22
    | ~ spl2_23
    | ~ spl2_5
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f239,f176,f99,f245,f241])).

fof(f239,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl2_5
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f230,f101])).

fof(f230,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_14 ),
    inference(resolution,[],[f178,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f227,plain,
    ( spl2_20
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f226,f136,f99,f94,f221])).

fof(f136,plain,
    ( spl2_9
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f226,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f225,f101])).

fof(f225,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f215,f138])).

fof(f138,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f136])).

fof(f215,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f64,f96])).

fof(f179,plain,
    ( spl2_14
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f163,f99,f94,f176])).

fof(f163,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f101,f96,f74])).

% (24079)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f174,plain,
    ( spl2_13
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f164,f99,f171])).

fof(f164,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f101,f58,f74])).

fof(f150,plain,
    ( spl2_10
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f143,f109,f104,f99,f147])).

fof(f109,plain,
    ( spl2_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f143,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f106,f101,f111,f58,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f111,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f142,plain,
    ( spl2_9
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f141,f99,f94,f84,f136])).

fof(f141,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f140,f101])).

fof(f140,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f133,f86])).

fof(f133,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f63,f96])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tops_1(X1,X0)
      | v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

fof(f112,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f57,f109])).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f107,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f51,f104])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( k1_xboole_0 != sK1
    & v3_tops_1(sK1,sK0)
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f46,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 != X1
            & v3_tops_1(X1,X0)
            & v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,sK0)
          & v3_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( k1_xboole_0 != X1
        & v3_tops_1(X1,sK0)
        & v3_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k1_xboole_0 != sK1
      & v3_tops_1(sK1,sK0)
      & v3_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v3_tops_1(X1,X0)
                & v3_pre_topc(X1,X0) )
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tops_1(X1,X0)
              & v3_pre_topc(X1,X0) )
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).

fof(f102,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f52,f99])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f97,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f53,f94])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f92,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f54,f89])).

fof(f54,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f87,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f55,f84])).

fof(f55,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f82,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f56,f79])).

fof(f56,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:53:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (24089)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.46  % (24074)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (24090)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (24086)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (24074)Refutation not found, incomplete strategy% (24074)------------------------------
% 0.21/0.49  % (24074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (24074)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (24074)Memory used [KB]: 6652
% 0.21/0.49  % (24074)Time elapsed: 0.056 s
% 0.21/0.49  % (24074)------------------------------
% 0.21/0.49  % (24074)------------------------------
% 0.21/0.49  % (24081)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (24080)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (24075)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (24088)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (24087)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (24078)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (24092)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (24076)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (24090)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  % (24085)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  fof(f1305,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f82,f87,f92,f97,f102,f107,f112,f142,f150,f174,f179,f227,f248,f369,f507,f790,f796,f817,f834,f946,f1062,f1190,f1214,f1273,f1304])).
% 0.21/0.51  fof(f1304,plain,(
% 0.21/0.51    spl2_1 | ~spl2_4 | ~spl2_5 | ~spl2_20 | ~spl2_113),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f1303])).
% 0.21/0.51  fof(f1303,plain,(
% 0.21/0.51    $false | (spl2_1 | ~spl2_4 | ~spl2_5 | ~spl2_20 | ~spl2_113)),
% 0.21/0.51    inference(subsumption_resolution,[],[f1302,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    k1_xboole_0 != sK1 | spl2_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    spl2_1 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.51  fof(f1302,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | (~spl2_4 | ~spl2_5 | ~spl2_20 | ~spl2_113)),
% 0.21/0.51    inference(forward_demodulation,[],[f1301,f223])).
% 0.21/0.51  fof(f223,plain,(
% 0.21/0.51    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f221])).
% 0.21/0.51  fof(f221,plain,(
% 0.21/0.51    spl2_20 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.51  fof(f1301,plain,(
% 0.21/0.51    sK1 = k1_tops_1(sK0,sK1) | (~spl2_4 | ~spl2_5 | ~spl2_113)),
% 0.21/0.51    inference(forward_demodulation,[],[f1300,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.51  fof(f1300,plain,(
% 0.21/0.51    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_xboole_0) | (~spl2_4 | ~spl2_5 | ~spl2_113)),
% 0.21/0.51    inference(forward_demodulation,[],[f1299,f127])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) ) | ~spl2_4),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f96,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    spl2_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.51  fof(f1299,plain,(
% 0.21/0.51    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) | (~spl2_4 | ~spl2_5 | ~spl2_113)),
% 0.21/0.51    inference(subsumption_resolution,[],[f1298,f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    l1_pre_topc(sK0) | ~spl2_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f99])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl2_5 <=> l1_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.51  fof(f1298,plain,(
% 0.21/0.51    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) | ~l1_pre_topc(sK0) | (~spl2_4 | ~spl2_113)),
% 0.21/0.51    inference(subsumption_resolution,[],[f1297,f96])).
% 0.21/0.51  fof(f1297,plain,(
% 0.21/0.51    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_113),
% 0.21/0.51    inference(superposition,[],[f60,f1272])).
% 0.21/0.51  fof(f1272,plain,(
% 0.21/0.51    k1_xboole_0 = k2_tops_1(sK0,sK1) | ~spl2_113),
% 0.21/0.51    inference(avatar_component_clause,[],[f1270])).
% 0.21/0.51  fof(f1270,plain,(
% 0.21/0.51    spl2_113 <=> k1_xboole_0 = k2_tops_1(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_113])])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 0.21/0.51  fof(f1273,plain,(
% 0.21/0.51    spl2_113 | ~spl2_104 | ~spl2_109),
% 0.21/0.51    inference(avatar_split_clause,[],[f1249,f1211,f1059,f1270])).
% 0.21/0.51  fof(f1059,plain,(
% 0.21/0.51    spl2_104 <=> k2_pre_topc(sK0,k1_xboole_0) = k2_tops_1(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_104])])).
% 0.21/0.51  fof(f1211,plain,(
% 0.21/0.51    spl2_109 <=> k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_109])])).
% 0.21/0.51  fof(f1249,plain,(
% 0.21/0.51    k1_xboole_0 = k2_tops_1(sK0,sK1) | (~spl2_104 | ~spl2_109)),
% 0.21/0.51    inference(backward_demodulation,[],[f1061,f1213])).
% 0.21/0.51  fof(f1213,plain,(
% 0.21/0.51    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) | ~spl2_109),
% 0.21/0.51    inference(avatar_component_clause,[],[f1211])).
% 0.21/0.51  fof(f1061,plain,(
% 0.21/0.51    k2_pre_topc(sK0,k1_xboole_0) = k2_tops_1(sK0,sK1) | ~spl2_104),
% 0.21/0.51    inference(avatar_component_clause,[],[f1059])).
% 0.21/0.51  fof(f1214,plain,(
% 0.21/0.51    spl2_109 | ~spl2_90 | ~spl2_108),
% 0.21/0.51    inference(avatar_split_clause,[],[f1209,f1187,f811,f1211])).
% 0.21/0.51  fof(f811,plain,(
% 0.21/0.51    spl2_90 <=> k2_pre_topc(sK0,k1_xboole_0) = k2_tops_1(sK0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_90])])).
% 0.21/0.51  fof(f1187,plain,(
% 0.21/0.51    spl2_108 <=> k1_xboole_0 = k2_tops_1(sK0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_108])])).
% 0.21/0.51  fof(f1209,plain,(
% 0.21/0.51    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) | (~spl2_90 | ~spl2_108)),
% 0.21/0.51    inference(backward_demodulation,[],[f813,f1189])).
% 0.21/0.51  fof(f1189,plain,(
% 0.21/0.51    k1_xboole_0 = k2_tops_1(sK0,k1_xboole_0) | ~spl2_108),
% 0.21/0.51    inference(avatar_component_clause,[],[f1187])).
% 0.21/0.51  fof(f813,plain,(
% 0.21/0.51    k2_pre_topc(sK0,k1_xboole_0) = k2_tops_1(sK0,k1_xboole_0) | ~spl2_90),
% 0.21/0.51    inference(avatar_component_clause,[],[f811])).
% 0.21/0.51  fof(f1190,plain,(
% 0.21/0.51    spl2_108 | ~spl2_5 | ~spl2_6 | ~spl2_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f1185,f147,f104,f99,f1187])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    spl2_6 <=> v2_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    spl2_10 <=> v4_pre_topc(k1_xboole_0,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.51  fof(f1185,plain,(
% 0.21/0.51    k1_xboole_0 = k2_tops_1(sK0,k1_xboole_0) | (~spl2_5 | ~spl2_6 | ~spl2_10)),
% 0.21/0.51    inference(forward_demodulation,[],[f1172,f129])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,X1)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f128,f115])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f73,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k7_subset_1(X0,k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,X1)) )),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f58,f76])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.51  fof(f1172,plain,(
% 0.21/0.51    k2_tops_1(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k1_xboole_0,k1_tops_1(sK0,k1_xboole_0)) | (~spl2_5 | ~spl2_6 | ~spl2_10)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f106,f101,f149,f58,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    v4_pre_topc(k1_xboole_0,sK0) | ~spl2_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f147])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    v2_pre_topc(sK0) | ~spl2_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f104])).
% 0.21/0.51  fof(f1062,plain,(
% 0.21/0.51    spl2_104 | ~spl2_88 | ~spl2_92 | ~spl2_96),
% 0.21/0.51    inference(avatar_split_clause,[],[f1057,f928,f831,f784,f1059])).
% 0.21/0.51  fof(f784,plain,(
% 0.21/0.51    spl2_88 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).
% 0.21/0.51  fof(f831,plain,(
% 0.21/0.51    spl2_92 <=> k2_pre_topc(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_92])])).
% 0.21/0.51  fof(f928,plain,(
% 0.21/0.51    spl2_96 <=> k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_96])])).
% 0.21/0.51  fof(f1057,plain,(
% 0.21/0.51    k2_pre_topc(sK0,k1_xboole_0) = k2_tops_1(sK0,sK1) | (~spl2_88 | ~spl2_92 | ~spl2_96)),
% 0.21/0.51    inference(forward_demodulation,[],[f1029,f833])).
% 0.21/0.51  fof(f833,plain,(
% 0.21/0.51    k2_pre_topc(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0) | ~spl2_92),
% 0.21/0.51    inference(avatar_component_clause,[],[f831])).
% 0.21/0.51  fof(f1029,plain,(
% 0.21/0.51    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0) | (~spl2_88 | ~spl2_96)),
% 0.21/0.51    inference(backward_demodulation,[],[f786,f930])).
% 0.21/0.51  fof(f930,plain,(
% 0.21/0.51    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_xboole_0) | ~spl2_96),
% 0.21/0.51    inference(avatar_component_clause,[],[f928])).
% 0.21/0.51  fof(f786,plain,(
% 0.21/0.51    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0) | ~spl2_88),
% 0.21/0.51    inference(avatar_component_clause,[],[f784])).
% 0.21/0.51  fof(f946,plain,(
% 0.21/0.51    spl2_96 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_22),
% 0.21/0.51    inference(avatar_split_clause,[],[f945,f241,f99,f94,f89,f928])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    spl2_3 <=> v3_pre_topc(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.51  fof(f241,plain,(
% 0.21/0.51    spl2_22 <=> k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.51  fof(f945,plain,(
% 0.21/0.51    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_xboole_0) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f944,f101])).
% 0.21/0.51  fof(f944,plain,(
% 0.21/0.51    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_xboole_0) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_4 | ~spl2_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f943,f96])).
% 0.21/0.51  fof(f943,plain,(
% 0.21/0.51    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f915,f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    v3_pre_topc(sK1,sK0) | ~spl2_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f89])).
% 0.21/0.51  fof(f915,plain,(
% 0.21/0.51    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_xboole_0) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_22),
% 0.21/0.51    inference(superposition,[],[f62,f243])).
% 0.21/0.51  fof(f243,plain,(
% 0.21/0.51    k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) | ~spl2_22),
% 0.21/0.51    inference(avatar_component_clause,[],[f241])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tops_1)).
% 0.21/0.51  fof(f834,plain,(
% 0.21/0.51    spl2_92 | ~spl2_87 | ~spl2_90),
% 0.21/0.51    inference(avatar_split_clause,[],[f825,f811,f778,f831])).
% 0.21/0.51  fof(f778,plain,(
% 0.21/0.51    spl2_87 <=> k2_tops_1(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).
% 0.21/0.51  fof(f825,plain,(
% 0.21/0.51    k2_pre_topc(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0) | (~spl2_87 | ~spl2_90)),
% 0.21/0.51    inference(backward_demodulation,[],[f780,f813])).
% 0.21/0.51  fof(f780,plain,(
% 0.21/0.51    k2_tops_1(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0) | ~spl2_87),
% 0.21/0.51    inference(avatar_component_clause,[],[f778])).
% 0.21/0.51  fof(f817,plain,(
% 0.21/0.51    spl2_90 | ~spl2_13 | ~spl2_87),
% 0.21/0.51    inference(avatar_split_clause,[],[f816,f778,f171,f811])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    spl2_13 <=> m1_subset_1(k2_pre_topc(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.51  fof(f816,plain,(
% 0.21/0.51    k2_pre_topc(sK0,k1_xboole_0) = k2_tops_1(sK0,k1_xboole_0) | (~spl2_13 | ~spl2_87)),
% 0.21/0.51    inference(forward_demodulation,[],[f815,f59])).
% 0.21/0.51  fof(f815,plain,(
% 0.21/0.51    k2_tops_1(sK0,k1_xboole_0) = k4_xboole_0(k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0) | (~spl2_13 | ~spl2_87)),
% 0.21/0.51    inference(subsumption_resolution,[],[f807,f173])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    m1_subset_1(k2_pre_topc(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f171])).
% 0.21/0.51  fof(f807,plain,(
% 0.21/0.51    k2_tops_1(sK0,k1_xboole_0) = k4_xboole_0(k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0) | ~m1_subset_1(k2_pre_topc(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_87),
% 0.21/0.51    inference(superposition,[],[f76,f780])).
% 0.21/0.51  fof(f796,plain,(
% 0.21/0.51    spl2_87 | ~spl2_5 | ~spl2_49),
% 0.21/0.51    inference(avatar_split_clause,[],[f795,f486,f99,f778])).
% 0.21/0.51  fof(f486,plain,(
% 0.21/0.51    spl2_49 <=> k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 0.21/0.51  fof(f795,plain,(
% 0.21/0.51    k2_tops_1(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0) | (~spl2_5 | ~spl2_49)),
% 0.21/0.51    inference(subsumption_resolution,[],[f794,f101])).
% 0.21/0.51  fof(f794,plain,(
% 0.21/0.51    k2_tops_1(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~spl2_49),
% 0.21/0.51    inference(subsumption_resolution,[],[f744,f58])).
% 0.21/0.51  fof(f744,plain,(
% 0.21/0.51    k2_tops_1(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_49),
% 0.21/0.51    inference(superposition,[],[f61,f488])).
% 0.21/0.51  fof(f488,plain,(
% 0.21/0.51    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) | ~spl2_49),
% 0.21/0.51    inference(avatar_component_clause,[],[f486])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 0.21/0.51  fof(f790,plain,(
% 0.21/0.51    spl2_88 | ~spl2_4 | ~spl2_5 | ~spl2_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f789,f221,f99,f94,f784])).
% 0.21/0.51  fof(f789,plain,(
% 0.21/0.51    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0) | (~spl2_4 | ~spl2_5 | ~spl2_20)),
% 0.21/0.51    inference(subsumption_resolution,[],[f788,f101])).
% 0.21/0.51  fof(f788,plain,(
% 0.21/0.51    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0) | ~l1_pre_topc(sK0) | (~spl2_4 | ~spl2_20)),
% 0.21/0.51    inference(subsumption_resolution,[],[f742,f96])).
% 0.21/0.51  fof(f742,plain,(
% 0.21/0.51    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_20),
% 0.21/0.51    inference(superposition,[],[f61,f223])).
% 0.21/0.51  fof(f507,plain,(
% 0.21/0.51    spl2_49 | ~spl2_5 | ~spl2_14 | ~spl2_22),
% 0.21/0.51    inference(avatar_split_clause,[],[f506,f241,f176,f99,f486])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    spl2_14 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.51  fof(f506,plain,(
% 0.21/0.51    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) | (~spl2_5 | ~spl2_14 | ~spl2_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f505,f101])).
% 0.21/0.51  fof(f505,plain,(
% 0.21/0.51    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) | ~l1_pre_topc(sK0) | (~spl2_14 | ~spl2_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f471,f178])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f176])).
% 0.21/0.51  fof(f471,plain,(
% 0.21/0.51    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_22),
% 0.21/0.51    inference(superposition,[],[f75,f243])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).
% 0.21/0.51  fof(f369,plain,(
% 0.21/0.51    spl2_23 | ~spl2_2 | ~spl2_4 | ~spl2_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f342,f99,f94,f84,f245])).
% 0.21/0.51  fof(f245,plain,(
% 0.21/0.51    spl2_23 <=> v2_tops_1(k2_pre_topc(sK0,sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    spl2_2 <=> v3_tops_1(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.51  fof(f342,plain,(
% 0.21/0.51    v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | (~spl2_2 | ~spl2_4 | ~spl2_5)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f101,f86,f96,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) | ~v2_tops_1(k2_pre_topc(X0,X1),X0)) & (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    v3_tops_1(sK1,sK0) | ~spl2_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f84])).
% 0.21/0.51  fof(f248,plain,(
% 0.21/0.51    spl2_22 | ~spl2_23 | ~spl2_5 | ~spl2_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f239,f176,f99,f245,f241])).
% 0.21/0.51  fof(f239,plain,(
% 0.21/0.51    ~v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) | (~spl2_5 | ~spl2_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f230,f101])).
% 0.21/0.51  fof(f230,plain,(
% 0.21/0.51    ~v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl2_14),
% 0.21/0.51    inference(resolution,[],[f178,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 0.21/0.51  fof(f227,plain,(
% 0.21/0.51    spl2_20 | ~spl2_4 | ~spl2_5 | ~spl2_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f226,f136,f99,f94,f221])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    spl2_9 <=> v2_tops_1(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.51  fof(f226,plain,(
% 0.21/0.51    k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl2_4 | ~spl2_5 | ~spl2_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f225,f101])).
% 0.21/0.51  fof(f225,plain,(
% 0.21/0.51    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl2_4 | ~spl2_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f215,f138])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    v2_tops_1(sK1,sK0) | ~spl2_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f136])).
% 0.21/0.51  fof(f215,plain,(
% 0.21/0.51    ~v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | ~spl2_4),
% 0.21/0.51    inference(resolution,[],[f64,f96])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    spl2_14 | ~spl2_4 | ~spl2_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f163,f99,f94,f176])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_4 | ~spl2_5)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f101,f96,f74])).
% 0.21/0.51  % (24079)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    spl2_13 | ~spl2_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f164,f99,f171])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    m1_subset_1(k2_pre_topc(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_5),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f101,f58,f74])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    spl2_10 | ~spl2_5 | ~spl2_6 | ~spl2_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f143,f109,f104,f99,f147])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl2_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    v4_pre_topc(k1_xboole_0,sK0) | (~spl2_5 | ~spl2_6 | ~spl2_7)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f106,f101,f111,f58,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0) | ~spl2_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f109])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    spl2_9 | ~spl2_2 | ~spl2_4 | ~spl2_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f141,f99,f94,f84,f136])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    v2_tops_1(sK1,sK0) | (~spl2_2 | ~spl2_4 | ~spl2_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f140,f101])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl2_2 | ~spl2_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f133,f86])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    ~v3_tops_1(sK1,sK0) | v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | ~spl2_4),
% 0.21/0.51    inference(resolution,[],[f63,f96])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tops_1(X1,X0) | v2_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    spl2_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f57,f109])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    spl2_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f51,f104])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    (k1_xboole_0 != sK1 & v3_tops_1(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f46,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (k1_xboole_0 != sK1 & v3_tops_1(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((k1_xboole_0 != X1 & (v3_tops_1(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 0.21/0.51    inference(negated_conjecture,[],[f19])).
% 0.21/0.51  fof(f19,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    spl2_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f52,f99])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    spl2_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f53,f94])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    spl2_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f54,f89])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    v3_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f55,f84])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    v3_tops_1(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ~spl2_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f56,f79])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    k1_xboole_0 != sK1),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (24090)------------------------------
% 0.21/0.51  % (24090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24090)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (24090)Memory used [KB]: 11385
% 0.21/0.51  % (24090)Time elapsed: 0.082 s
% 0.21/0.51  % (24090)------------------------------
% 0.21/0.51  % (24090)------------------------------
% 0.21/0.51  % (24073)Success in time 0.158 s
%------------------------------------------------------------------------------
