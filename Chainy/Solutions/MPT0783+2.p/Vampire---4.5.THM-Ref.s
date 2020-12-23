%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0783+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:48 EST 2020

% Result     : Theorem 2.79s
% Output     : Refutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 178 expanded)
%              Number of leaves         :   23 (  77 expanded)
%              Depth                    :    7
%              Number of atoms          :  280 ( 628 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4617,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1348,f1353,f1358,f1377,f1383,f1389,f1395,f1401,f2046,f4566,f4576,f4586,f4596,f4606,f4616])).

fof(f4616,plain,
    ( ~ spl13_3
    | ~ spl13_10
    | spl13_56 ),
    inference(avatar_split_clause,[],[f4611,f2043,f1398,f1355])).

fof(f1355,plain,
    ( spl13_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f1398,plain,
    ( spl13_10
  <=> v1_wellord1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f2043,plain,
    ( spl13_56
  <=> v1_wellord1(k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_56])])).

fof(f4611,plain,
    ( ~ v1_wellord1(sK1)
    | ~ v1_relat_1(sK1)
    | spl13_56 ),
    inference(resolution,[],[f2045,f1275])).

fof(f1275,plain,(
    ! [X0,X1] :
      ( v1_wellord1(k2_wellord1(X1,X0))
      | ~ v1_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1193])).

fof(f1193,plain,(
    ! [X0,X1] :
      ( v1_wellord1(k2_wellord1(X1,X0))
      | ~ v1_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1192])).

fof(f1192,plain,(
    ! [X0,X1] :
      ( v1_wellord1(k2_wellord1(X1,X0))
      | ~ v1_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1166])).

fof(f1166,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v1_wellord1(X1)
       => v1_wellord1(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_wellord1)).

fof(f2045,plain,
    ( ~ v1_wellord1(k2_wellord1(sK1,sK0))
    | spl13_56 ),
    inference(avatar_component_clause,[],[f2043])).

fof(f4606,plain,
    ( ~ spl13_3
    | ~ spl13_9
    | spl13_55 ),
    inference(avatar_split_clause,[],[f4601,f2039,f1392,f1355])).

fof(f1392,plain,
    ( spl13_9
  <=> v6_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f2039,plain,
    ( spl13_55
  <=> v6_relat_2(k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_55])])).

fof(f4601,plain,
    ( ~ v6_relat_2(sK1)
    | ~ v1_relat_1(sK1)
    | spl13_55 ),
    inference(resolution,[],[f2041,f1271])).

fof(f1271,plain,(
    ! [X0,X1] :
      ( v6_relat_2(k2_wellord1(X1,X0))
      | ~ v6_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1185])).

fof(f1185,plain,(
    ! [X0,X1] :
      ( v6_relat_2(k2_wellord1(X1,X0))
      | ~ v6_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1184])).

fof(f1184,plain,(
    ! [X0,X1] :
      ( v6_relat_2(k2_wellord1(X1,X0))
      | ~ v6_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1157])).

fof(f1157,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
       => v6_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_wellord1)).

fof(f2041,plain,
    ( ~ v6_relat_2(k2_wellord1(sK1,sK0))
    | spl13_55 ),
    inference(avatar_component_clause,[],[f2039])).

fof(f4596,plain,
    ( ~ spl13_3
    | ~ spl13_8
    | spl13_54 ),
    inference(avatar_split_clause,[],[f4591,f2035,f1386,f1355])).

fof(f1386,plain,
    ( spl13_8
  <=> v4_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f2035,plain,
    ( spl13_54
  <=> v4_relat_2(k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_54])])).

fof(f4591,plain,
    ( ~ v4_relat_2(sK1)
    | ~ v1_relat_1(sK1)
    | spl13_54 ),
    inference(resolution,[],[f2037,f1274])).

fof(f1274,plain,(
    ! [X0,X1] :
      ( v4_relat_2(k2_wellord1(X1,X0))
      | ~ v4_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1191])).

fof(f1191,plain,(
    ! [X0,X1] :
      ( v4_relat_2(k2_wellord1(X1,X0))
      | ~ v4_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1190])).

fof(f1190,plain,(
    ! [X0,X1] :
      ( v4_relat_2(k2_wellord1(X1,X0))
      | ~ v4_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1159])).

fof(f1159,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
       => v4_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_wellord1)).

fof(f2037,plain,
    ( ~ v4_relat_2(k2_wellord1(sK1,sK0))
    | spl13_54 ),
    inference(avatar_component_clause,[],[f2035])).

fof(f4586,plain,
    ( ~ spl13_3
    | ~ spl13_7
    | spl13_53 ),
    inference(avatar_split_clause,[],[f4581,f2031,f1380,f1355])).

fof(f1380,plain,
    ( spl13_7
  <=> v8_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f2031,plain,
    ( spl13_53
  <=> v8_relat_2(k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_53])])).

fof(f4581,plain,
    ( ~ v8_relat_2(sK1)
    | ~ v1_relat_1(sK1)
    | spl13_53 ),
    inference(resolution,[],[f2033,f1272])).

fof(f1272,plain,(
    ! [X0,X1] :
      ( v8_relat_2(k2_wellord1(X1,X0))
      | ~ v8_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1187])).

fof(f1187,plain,(
    ! [X0,X1] :
      ( v8_relat_2(k2_wellord1(X1,X0))
      | ~ v8_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1186])).

fof(f1186,plain,(
    ! [X0,X1] :
      ( v8_relat_2(k2_wellord1(X1,X0))
      | ~ v8_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1158])).

fof(f1158,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
       => v8_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_wellord1)).

fof(f2033,plain,
    ( ~ v8_relat_2(k2_wellord1(sK1,sK0))
    | spl13_53 ),
    inference(avatar_component_clause,[],[f2031])).

fof(f4576,plain,
    ( ~ spl13_3
    | ~ spl13_6
    | spl13_52 ),
    inference(avatar_split_clause,[],[f4571,f2027,f1374,f1355])).

fof(f1374,plain,
    ( spl13_6
  <=> v1_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f2027,plain,
    ( spl13_52
  <=> v1_relat_2(k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_52])])).

fof(f4571,plain,
    ( ~ v1_relat_2(sK1)
    | ~ v1_relat_1(sK1)
    | spl13_52 ),
    inference(resolution,[],[f2029,f1273])).

fof(f1273,plain,(
    ! [X0,X1] :
      ( v1_relat_2(k2_wellord1(X1,X0))
      | ~ v1_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1189])).

fof(f1189,plain,(
    ! [X0,X1] :
      ( v1_relat_2(k2_wellord1(X1,X0))
      | ~ v1_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1188])).

fof(f1188,plain,(
    ! [X0,X1] :
      ( v1_relat_2(k2_wellord1(X1,X0))
      | ~ v1_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1156])).

fof(f1156,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
       => v1_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_wellord1)).

fof(f2029,plain,
    ( ~ v1_relat_2(k2_wellord1(sK1,sK0))
    | spl13_52 ),
    inference(avatar_component_clause,[],[f2027])).

fof(f4566,plain,
    ( ~ spl13_3
    | spl13_51 ),
    inference(avatar_split_clause,[],[f4561,f2023,f1355])).

fof(f2023,plain,
    ( spl13_51
  <=> v1_relat_1(k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_51])])).

fof(f4561,plain,
    ( ~ v1_relat_1(sK1)
    | spl13_51 ),
    inference(resolution,[],[f2025,f1281])).

fof(f1281,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1198])).

fof(f1198,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1139])).

fof(f1139,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f2025,plain,
    ( ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | spl13_51 ),
    inference(avatar_component_clause,[],[f2023])).

fof(f2046,plain,
    ( ~ spl13_51
    | ~ spl13_52
    | ~ spl13_53
    | ~ spl13_54
    | ~ spl13_55
    | ~ spl13_56
    | spl13_1 ),
    inference(avatar_split_clause,[],[f2021,f1345,f2043,f2039,f2035,f2031,f2027,f2023])).

fof(f1345,plain,
    ( spl13_1
  <=> v2_wellord1(k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f2021,plain,
    ( ~ v1_wellord1(k2_wellord1(sK1,sK0))
    | ~ v6_relat_2(k2_wellord1(sK1,sK0))
    | ~ v4_relat_2(k2_wellord1(sK1,sK0))
    | ~ v8_relat_2(k2_wellord1(sK1,sK0))
    | ~ v1_relat_2(k2_wellord1(sK1,sK0))
    | ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | spl13_1 ),
    inference(resolution,[],[f1293,f1347])).

fof(f1347,plain,
    ( ~ v2_wellord1(k2_wellord1(sK1,sK0))
    | spl13_1 ),
    inference(avatar_component_clause,[],[f1345])).

fof(f1293,plain,(
    ! [X0] :
      ( v2_wellord1(X0)
      | ~ v1_wellord1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1243])).

fof(f1243,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1242])).

fof(f1242,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1204])).

fof(f1204,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1133])).

fof(f1133,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(f1401,plain,
    ( spl13_10
    | ~ spl13_2
    | ~ spl13_3 ),
    inference(avatar_split_clause,[],[f1396,f1355,f1350,f1398])).

fof(f1350,plain,
    ( spl13_2
  <=> v2_wellord1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f1396,plain,
    ( v1_wellord1(sK1)
    | ~ spl13_2
    | ~ spl13_3 ),
    inference(unit_resulting_resolution,[],[f1357,f1352,f1292])).

fof(f1292,plain,(
    ! [X0] :
      ( v1_wellord1(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1243])).

fof(f1352,plain,
    ( v2_wellord1(sK1)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f1350])).

fof(f1357,plain,
    ( v1_relat_1(sK1)
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f1355])).

fof(f1395,plain,
    ( spl13_9
    | ~ spl13_2
    | ~ spl13_3 ),
    inference(avatar_split_clause,[],[f1390,f1355,f1350,f1392])).

fof(f1390,plain,
    ( v6_relat_2(sK1)
    | ~ spl13_2
    | ~ spl13_3 ),
    inference(unit_resulting_resolution,[],[f1357,f1352,f1291])).

fof(f1291,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1243])).

fof(f1389,plain,
    ( spl13_8
    | ~ spl13_2
    | ~ spl13_3 ),
    inference(avatar_split_clause,[],[f1384,f1355,f1350,f1386])).

fof(f1384,plain,
    ( v4_relat_2(sK1)
    | ~ spl13_2
    | ~ spl13_3 ),
    inference(unit_resulting_resolution,[],[f1357,f1352,f1290])).

fof(f1290,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1243])).

fof(f1383,plain,
    ( spl13_7
    | ~ spl13_2
    | ~ spl13_3 ),
    inference(avatar_split_clause,[],[f1378,f1355,f1350,f1380])).

fof(f1378,plain,
    ( v8_relat_2(sK1)
    | ~ spl13_2
    | ~ spl13_3 ),
    inference(unit_resulting_resolution,[],[f1357,f1352,f1289])).

fof(f1289,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1243])).

fof(f1377,plain,
    ( spl13_6
    | ~ spl13_2
    | ~ spl13_3 ),
    inference(avatar_split_clause,[],[f1372,f1355,f1350,f1374])).

fof(f1372,plain,
    ( v1_relat_2(sK1)
    | ~ spl13_2
    | ~ spl13_3 ),
    inference(unit_resulting_resolution,[],[f1357,f1352,f1288])).

fof(f1288,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1243])).

fof(f1358,plain,(
    spl13_3 ),
    inference(avatar_split_clause,[],[f1262,f1355])).

fof(f1262,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1238])).

fof(f1238,plain,
    ( ~ v2_wellord1(k2_wellord1(sK1,sK0))
    & v2_wellord1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1176,f1237])).

fof(f1237,plain,
    ( ? [X0,X1] :
        ( ~ v2_wellord1(k2_wellord1(X1,X0))
        & v2_wellord1(X1)
        & v1_relat_1(X1) )
   => ( ~ v2_wellord1(k2_wellord1(sK1,sK0))
      & v2_wellord1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1176,plain,(
    ? [X0,X1] :
      ( ~ v2_wellord1(k2_wellord1(X1,X0))
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1175])).

fof(f1175,plain,(
    ? [X0,X1] :
      ( ~ v2_wellord1(k2_wellord1(X1,X0))
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1168])).

fof(f1168,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v2_wellord1(X1)
         => v2_wellord1(k2_wellord1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f1167])).

fof(f1167,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => v2_wellord1(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord1)).

fof(f1353,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f1263,f1350])).

fof(f1263,plain,(
    v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f1238])).

fof(f1348,plain,(
    ~ spl13_1 ),
    inference(avatar_split_clause,[],[f1264,f1345])).

fof(f1264,plain,(
    ~ v2_wellord1(k2_wellord1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f1238])).
%------------------------------------------------------------------------------
