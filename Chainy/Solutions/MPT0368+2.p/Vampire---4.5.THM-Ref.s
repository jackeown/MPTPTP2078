%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0368+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:26 EST 2020

% Result     : Theorem 2.69s
% Output     : Refutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 275 expanded)
%              Number of leaves         :   32 (  97 expanded)
%              Depth                    :   10
%              Number of atoms          :  249 ( 678 expanded)
%              Number of equality atoms :   27 (  99 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1276,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1019,f1024,f1050,f1057,f1063,f1072,f1083,f1092,f1097,f1105,f1118,f1172,f1194,f1225,f1229,f1238,f1243,f1272,f1273,f1274,f1275])).

fof(f1275,plain,
    ( spl33_1
    | ~ spl33_14
    | ~ spl33_17 ),
    inference(avatar_split_clause,[],[f1270,f1235,f1191,f1016])).

fof(f1016,plain,
    ( spl33_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_1])])).

fof(f1191,plain,
    ( spl33_14
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_14])])).

fof(f1235,plain,
    ( spl33_17
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_17])])).

fof(f1270,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK0 = sK1
    | ~ spl33_17 ),
    inference(resolution,[],[f728,f1237])).

fof(f1237,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl33_17 ),
    inference(avatar_component_clause,[],[f1235])).

fof(f728,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1274,plain,
    ( spl33_1
    | ~ spl33_17
    | ~ spl33_14 ),
    inference(avatar_split_clause,[],[f1269,f1191,f1235,f1016])).

fof(f1269,plain,
    ( ~ r1_tarski(sK1,sK0)
    | sK0 = sK1
    | ~ spl33_14 ),
    inference(resolution,[],[f728,f1193])).

fof(f1193,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl33_14 ),
    inference(avatar_component_clause,[],[f1191])).

fof(f1273,plain,
    ( ~ spl33_17
    | ~ spl33_14
    | spl33_1 ),
    inference(avatar_split_clause,[],[f1263,f1016,f1191,f1235])).

fof(f1263,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_tarski(sK1,sK0)
    | spl33_1 ),
    inference(extensionality_resolution,[],[f728,f1018])).

fof(f1018,plain,
    ( sK0 != sK1
    | spl33_1 ),
    inference(avatar_component_clause,[],[f1016])).

fof(f1272,plain,
    ( ~ spl33_14
    | ~ spl33_17
    | spl33_1 ),
    inference(avatar_split_clause,[],[f1262,f1016,f1235,f1191])).

fof(f1262,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ r1_tarski(sK0,sK1)
    | spl33_1 ),
    inference(extensionality_resolution,[],[f728,f1018])).

fof(f1243,plain,
    ( ~ spl33_18
    | ~ spl33_16 ),
    inference(avatar_split_clause,[],[f1232,f1222,f1240])).

fof(f1240,plain,
    ( spl33_18
  <=> r2_hidden(k1_zfmisc_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_18])])).

fof(f1222,plain,
    ( spl33_16
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_16])])).

fof(f1232,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),sK1)
    | ~ spl33_16 ),
    inference(resolution,[],[f1224,f832])).

fof(f832,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f598])).

fof(f598,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f1224,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl33_16 ),
    inference(avatar_component_clause,[],[f1222])).

fof(f1238,plain,
    ( spl33_17
    | ~ spl33_16 ),
    inference(avatar_split_clause,[],[f1231,f1222,f1235])).

fof(f1231,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl33_16 ),
    inference(resolution,[],[f1224,f1006])).

fof(f1006,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f723])).

fof(f723,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f285])).

fof(f285,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f1229,plain,(
    ~ spl33_15 ),
    inference(avatar_contradiction_clause,[],[f1228])).

fof(f1228,plain,
    ( $false
    | ~ spl33_15 ),
    inference(resolution,[],[f1220,f877])).

fof(f877,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f471])).

fof(f471,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f1220,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl33_15 ),
    inference(avatar_component_clause,[],[f1218])).

fof(f1218,plain,
    ( spl33_15
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_15])])).

fof(f1225,plain,
    ( spl33_15
    | spl33_16
    | ~ spl33_2 ),
    inference(avatar_split_clause,[],[f1211,f1021,f1222,f1218])).

fof(f1021,plain,
    ( spl33_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_2])])).

fof(f1211,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl33_2 ),
    inference(resolution,[],[f843,f1023])).

fof(f1023,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl33_2 ),
    inference(avatar_component_clause,[],[f1021])).

fof(f843,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f603])).

fof(f603,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f455])).

fof(f455,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f1194,plain,(
    spl33_14 ),
    inference(avatar_split_clause,[],[f1189,f1191])).

fof(f1189,plain,(
    r1_tarski(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f1188])).

fof(f1188,plain,
    ( r1_tarski(sK0,sK1)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f1185,f817])).

fof(f817,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK21(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f586])).

fof(f586,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f1185,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK21(X1,sK1),sK0)
      | r1_tarski(X1,sK1) ) ),
    inference(resolution,[],[f818,f1075])).

fof(f1075,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f1045,f623])).

fof(f623,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f519])).

fof(f519,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f518])).

fof(f518,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f510])).

fof(f510,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => r2_hidden(X2,X1) )
         => X0 = X1 ) ) ),
    inference(negated_conjecture,[],[f509])).

fof(f509,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(f1045,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(global_subsumption,[],[f807,f842])).

fof(f842,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f603])).

fof(f807,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f585])).

fof(f585,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f818,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK21(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f586])).

fof(f1172,plain,(
    ~ spl33_13 ),
    inference(avatar_split_clause,[],[f1167,f1169])).

fof(f1169,plain,
    ( spl33_13
  <=> r2_hidden(k1_zfmisc_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_13])])).

fof(f1167,plain,(
    ~ r2_hidden(k1_zfmisc_1(sK1),sK0) ),
    inference(resolution,[],[f1158,f1076])).

fof(f1076,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,X0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f1075,f832])).

fof(f1158,plain,(
    ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f785,f986])).

fof(f986,plain,(
    ! [X0] : r1_tarski(k2_tarski(X0,X0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f874,f766])).

fof(f766,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f874,plain,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f434])).

fof(f434,axiom,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

fof(f785,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f396])).

fof(f396,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f1118,plain,
    ( ~ spl33_11
    | spl33_12 ),
    inference(avatar_split_clause,[],[f1110,f1116,f1112])).

fof(f1112,plain,
    ( spl33_11
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_11])])).

fof(f1116,plain,
    ( spl33_12
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_12])])).

fof(f1110,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(sK0)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f840,f623])).

fof(f840,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f603])).

fof(f1105,plain,(
    ~ spl33_10 ),
    inference(avatar_split_clause,[],[f1100,f1102])).

fof(f1102,plain,
    ( spl33_10
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_10])])).

fof(f1100,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f1099])).

fof(f1099,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f1076,f1075])).

fof(f1097,plain,
    ( spl33_9
    | ~ spl33_3 ),
    inference(avatar_split_clause,[],[f1087,f1047,f1094])).

fof(f1094,plain,
    ( spl33_9
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_9])])).

fof(f1047,plain,
    ( spl33_3
  <=> k1_zfmisc_1(k1_xboole_0) = k2_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_3])])).

fof(f1087,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl33_3 ),
    inference(superposition,[],[f1005,f1049])).

fof(f1049,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k2_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl33_3 ),
    inference(avatar_component_clause,[],[f1047])).

fof(f1005,plain,(
    ! [X2] : r2_hidden(X2,k2_tarski(X2,X2)) ),
    inference(equality_resolution,[],[f1004])).

fof(f1004,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k2_tarski(X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f935])).

fof(f935,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f718,f766])).

fof(f718,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f1092,plain,
    ( ~ spl33_8
    | ~ spl33_3 ),
    inference(avatar_split_clause,[],[f1084,f1047,f1089])).

fof(f1089,plain,
    ( spl33_8
  <=> r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_8])])).

fof(f1084,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl33_3 ),
    inference(superposition,[],[f1067,f1049])).

fof(f1067,plain,(
    ! [X0] : ~ r2_hidden(k2_tarski(X0,X0),X0) ),
    inference(resolution,[],[f832,f1005])).

fof(f1083,plain,(
    ~ spl33_7 ),
    inference(avatar_split_clause,[],[f1078,f1080])).

fof(f1080,plain,
    ( spl33_7
  <=> r2_hidden(k2_tarski(sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_7])])).

fof(f1078,plain,(
    ~ r2_hidden(k2_tarski(sK1,sK1),sK0) ),
    inference(resolution,[],[f1075,f1067])).

fof(f1072,plain,
    ( ~ spl33_6
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f1066,f1054,f1069])).

fof(f1069,plain,
    ( spl33_6
  <=> r2_hidden(sK1,sK31(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_6])])).

fof(f1054,plain,
    ( spl33_4
  <=> r2_hidden(sK31(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_4])])).

fof(f1066,plain,
    ( ~ r2_hidden(sK1,sK31(sK0))
    | ~ spl33_4 ),
    inference(resolution,[],[f832,f1056])).

fof(f1056,plain,
    ( r2_hidden(sK31(sK0),sK1)
    | ~ spl33_4 ),
    inference(avatar_component_clause,[],[f1054])).

fof(f1063,plain,
    ( ~ spl33_5
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f1058,f1054,f1060])).

fof(f1060,plain,
    ( spl33_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_5])])).

fof(f1058,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl33_4 ),
    inference(resolution,[],[f807,f1056])).

fof(f1057,plain,(
    spl33_4 ),
    inference(avatar_split_clause,[],[f1052,f1054])).

fof(f1052,plain,(
    r2_hidden(sK31(sK0),sK1) ),
    inference(resolution,[],[f864,f623])).

fof(f864,plain,(
    ! [X0] : m1_subset_1(sK31(X0),X0) ),
    inference(cnf_transformation,[],[f469])).

fof(f469,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f1050,plain,(
    spl33_3 ),
    inference(avatar_split_clause,[],[f987,f1047])).

fof(f987,plain,(
    k1_zfmisc_1(k1_xboole_0) = k2_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f878,f766])).

fof(f878,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f376])).

fof(f376,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f1024,plain,(
    spl33_2 ),
    inference(avatar_split_clause,[],[f624,f1021])).

fof(f624,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f519])).

fof(f1019,plain,(
    ~ spl33_1 ),
    inference(avatar_split_clause,[],[f625,f1016])).

fof(f625,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f519])).
%------------------------------------------------------------------------------
