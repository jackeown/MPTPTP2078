%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattices__t45_lattices.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:02 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  278 (1169 expanded)
%              Number of leaves         :   69 ( 551 expanded)
%              Depth                    :    9
%              Number of atoms          : 1274 (4045 expanded)
%              Number of equality atoms :   34 (  92 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1376,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f146,f153,f160,f167,f174,f181,f188,f195,f204,f213,f220,f227,f234,f244,f251,f258,f266,f274,f282,f293,f321,f332,f339,f349,f356,f363,f373,f380,f396,f413,f420,f472,f537,f655,f662,f669,f872,f879,f886,f1150,f1157,f1198,f1205,f1215,f1222,f1229,f1353,f1355,f1357,f1359,f1361,f1363,f1365,f1367,f1369,f1371])).

fof(f1371,plain,
    ( spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(avatar_contradiction_clause,[],[f1370])).

fof(f1370,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f1335,f292])).

fof(f292,plain,
    ( m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl6_38
  <=> m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f1335,plain,
    ( ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_66 ),
    inference(unit_resulting_resolution,[],[f145,f265,f273,f281,f166,f233,f654,f194,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t45_lattices.p',redefinition_r3_lattices)).

fof(f194,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl6_14
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f654,plain,
    ( r1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl6_66 ),
    inference(avatar_component_clause,[],[f653])).

fof(f653,plain,
    ( spl6_66
  <=> r1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f233,plain,
    ( ~ r3_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl6_25
  <=> ~ r3_lattices(sK0,sK1,k6_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f166,plain,
    ( l3_lattices(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl6_6
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f281,plain,
    ( v9_lattices(sK0)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl6_36
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f273,plain,
    ( v8_lattices(sK0)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl6_34
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f265,plain,
    ( v6_lattices(sK0)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl6_32
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f145,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl6_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1369,plain,
    ( spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(avatar_contradiction_clause,[],[f1368])).

fof(f1368,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f1336,f654])).

fof(f1336,plain,
    ( ~ r1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f145,f265,f273,f281,f166,f194,f233,f292,f127])).

fof(f1367,plain,
    ( spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(avatar_contradiction_clause,[],[f1366])).

fof(f1366,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f1339,f233])).

fof(f1339,plain,
    ( r3_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(unit_resulting_resolution,[],[f145,f265,f273,f281,f166,f194,f654,f292,f127])).

fof(f1365,plain,
    ( spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(avatar_contradiction_clause,[],[f1364])).

fof(f1364,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f1340,f194])).

fof(f1340,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(unit_resulting_resolution,[],[f145,f265,f273,f281,f166,f233,f654,f292,f127])).

fof(f1363,plain,
    ( spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(avatar_contradiction_clause,[],[f1362])).

fof(f1362,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f1341,f166])).

fof(f1341,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(unit_resulting_resolution,[],[f145,f265,f273,f281,f194,f233,f654,f292,f127])).

fof(f1361,plain,
    ( spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(avatar_contradiction_clause,[],[f1360])).

fof(f1360,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f1342,f281])).

fof(f1342,plain,
    ( ~ v9_lattices(sK0)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(unit_resulting_resolution,[],[f145,f265,f273,f166,f194,f233,f654,f292,f127])).

fof(f1359,plain,
    ( spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(avatar_contradiction_clause,[],[f1358])).

fof(f1358,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f1343,f273])).

fof(f1343,plain,
    ( ~ v8_lattices(sK0)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_25
    | ~ spl6_32
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(unit_resulting_resolution,[],[f145,f265,f281,f166,f194,f233,f654,f292,f127])).

fof(f1357,plain,
    ( spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(avatar_contradiction_clause,[],[f1356])).

fof(f1356,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f1344,f265])).

fof(f1344,plain,
    ( ~ v6_lattices(sK0)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_25
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(unit_resulting_resolution,[],[f145,f273,f281,f166,f194,f233,f654,f292,f127])).

fof(f1355,plain,
    ( spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(avatar_contradiction_clause,[],[f1354])).

fof(f1354,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f1345,f145])).

fof(f1345,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(unit_resulting_resolution,[],[f265,f273,f281,f166,f194,f233,f654,f292,f127])).

fof(f1353,plain,
    ( spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(avatar_contradiction_clause,[],[f1346])).

fof(f1346,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_25
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(unit_resulting_resolution,[],[f145,f265,f273,f281,f166,f194,f233,f654,f292,f127])).

fof(f1229,plain,
    ( spl6_90
    | spl6_1
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f927,f264,f202,f193,f144,f1227])).

fof(f1227,plain,
    ( spl6_90
  <=> k4_lattices(sK0,sK1,sK1) = k2_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).

fof(f202,plain,
    ( spl6_16
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f927,plain,
    ( k4_lattices(sK0,sK1,sK1) = k2_lattices(sK0,sK1,sK1)
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f145,f265,f203,f194,f194,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t45_lattices.p',redefinition_k4_lattices)).

fof(f203,plain,
    ( l1_lattices(sK0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f202])).

fof(f1222,plain,
    ( spl6_88
    | spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_32
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f635,f272,f264,f193,f165,f144,f1220])).

fof(f1220,plain,
    ( spl6_88
  <=> r1_lattices(sK0,k4_lattices(sK0,sK1,sK2(u1_struct_0(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).

fof(f635,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK1,sK2(u1_struct_0(sK0))),sK1)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_32
    | ~ spl6_34 ),
    inference(unit_resulting_resolution,[],[f145,f265,f273,f166,f194,f119,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t45_lattices.p',t23_lattices)).

fof(f119,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t45_lattices.p',existence_m1_subset_1)).

fof(f1215,plain,
    ( spl6_86
    | spl6_1
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f456,f264,f202,f193,f144,f1213])).

fof(f1213,plain,
    ( spl6_86
  <=> m1_subset_1(k4_lattices(sK0,sK1,sK2(u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).

fof(f456,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK2(u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f145,f265,f203,f194,f119,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t45_lattices.p',dt_k4_lattices)).

fof(f1205,plain,
    ( spl6_84
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_16
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f748,f291,f272,f264,f202,f165,f158,f151,f144,f1203])).

fof(f1203,plain,
    ( spl6_84
  <=> r1_lattices(sK0,sK2(u1_struct_0(sK0)),sK2(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).

fof(f151,plain,
    ( spl6_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f158,plain,
    ( spl6_4
  <=> v14_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f748,plain,
    ( r1_lattices(sK0,sK2(u1_struct_0(sK0)),sK2(u1_struct_0(sK0)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_16
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_38 ),
    inference(backward_demodulation,[],[f747,f580])).

fof(f580,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK2(u1_struct_0(sK0)),k6_lattices(sK0)),sK2(u1_struct_0(sK0)))
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f145,f265,f273,f166,f119,f292,f116])).

fof(f747,plain,
    ( k4_lattices(sK0,sK2(u1_struct_0(sK0)),k6_lattices(sK0)) = sK2(u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_16
    | ~ spl6_32
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f726,f365])).

fof(f365,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),sK2(u1_struct_0(sK0))) = sK2(u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f145,f152,f159,f166,f119,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k4_lattices(X0,k6_lattices(X0),X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t45_lattices.p',t43_lattices)).

fof(f159,plain,
    ( v14_lattices(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f158])).

fof(f152,plain,
    ( v10_lattices(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f151])).

fof(f726,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),sK2(u1_struct_0(sK0))) = k4_lattices(sK0,sK2(u1_struct_0(sK0)),k6_lattices(sK0))
    | ~ spl6_1
    | ~ spl6_16
    | ~ spl6_32
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f145,f265,f203,f292,f119,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t45_lattices.p',commutativity_k4_lattices)).

fof(f1198,plain,
    ( spl6_82
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f644,f470,f291,f272,f264,f165,f158,f151,f144,f1196])).

fof(f1196,plain,
    ( spl6_82
  <=> r1_lattices(sK0,k4_lattices(sK0,sK1,sK1),k6_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).

fof(f470,plain,
    ( spl6_62
  <=> m1_subset_1(k4_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f644,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK1,sK1),k6_lattices(sK0))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_62 ),
    inference(forward_demodulation,[],[f581,f497])).

fof(f497,plain,
    ( k4_lattices(sK0,sK1,sK1) = k4_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK1,sK1))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_62 ),
    inference(unit_resulting_resolution,[],[f145,f152,f159,f166,f471,f115])).

fof(f471,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f470])).

fof(f581,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK1,sK1)),k6_lattices(sK0))
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_62 ),
    inference(unit_resulting_resolution,[],[f145,f265,f273,f166,f292,f471,f116])).

fof(f1157,plain,
    ( spl6_80
    | spl6_1
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_32
    | ~ spl6_38
    | ~ spl6_76 ),
    inference(avatar_split_clause,[],[f1092,f884,f291,f264,f202,f193,f144,f1155])).

fof(f1155,plain,
    ( spl6_80
  <=> k2_lattices(sK0,sK1,k6_lattices(sK0)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f884,plain,
    ( spl6_76
  <=> k4_lattices(sK0,sK1,k6_lattices(sK0)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f1092,plain,
    ( k2_lattices(sK0,sK1,k6_lattices(sK0)) = sK1
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_32
    | ~ spl6_38
    | ~ spl6_76 ),
    inference(forward_demodulation,[],[f892,f885])).

fof(f885,plain,
    ( k4_lattices(sK0,sK1,k6_lattices(sK0)) = sK1
    | ~ spl6_76 ),
    inference(avatar_component_clause,[],[f884])).

fof(f892,plain,
    ( k4_lattices(sK0,sK1,k6_lattices(sK0)) = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_32
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f145,f265,f203,f194,f292,f130])).

fof(f1150,plain,
    ( spl6_78
    | spl6_1
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_32
    | ~ spl6_38
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f999,f371,f291,f264,f202,f193,f144,f1148])).

fof(f1148,plain,
    ( spl6_78
  <=> k2_lattices(sK0,k6_lattices(sK0),sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f371,plain,
    ( spl6_52
  <=> k4_lattices(sK0,k6_lattices(sK0),sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f999,plain,
    ( k2_lattices(sK0,k6_lattices(sK0),sK1) = sK1
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_32
    | ~ spl6_38
    | ~ spl6_52 ),
    inference(forward_demodulation,[],[f922,f372])).

fof(f372,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),sK1) = sK1
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f371])).

fof(f922,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),sK1) = k2_lattices(sK0,k6_lattices(sK0),sK1)
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_32
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f145,f265,f203,f292,f194,f130])).

fof(f886,plain,
    ( spl6_76
    | spl6_1
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_32
    | ~ spl6_38
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f760,f371,f291,f264,f202,f193,f144,f884])).

fof(f760,plain,
    ( k4_lattices(sK0,sK1,k6_lattices(sK0)) = sK1
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_32
    | ~ spl6_38
    | ~ spl6_52 ),
    inference(forward_demodulation,[],[f718,f372])).

fof(f718,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),sK1) = k4_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_32
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f145,f265,f203,f292,f194,f129])).

fof(f879,plain,
    ( spl6_74
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f638,f291,f272,f264,f165,f158,f151,f144,f877])).

fof(f877,plain,
    ( spl6_74
  <=> r1_lattices(sK0,sK2(u1_struct_0(sK0)),k6_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f638,plain,
    ( r1_lattices(sK0,sK2(u1_struct_0(sK0)),k6_lattices(sK0))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f629,f365])).

fof(f629,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,k6_lattices(sK0),sK2(u1_struct_0(sK0))),k6_lattices(sK0))
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f145,f265,f273,f166,f292,f119,f116])).

fof(f872,plain,
    ( spl6_72
    | spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_52
    | ~ spl6_64 ),
    inference(avatar_split_clause,[],[f814,f535,f371,f291,f272,f264,f202,f193,f165,f144,f870])).

fof(f870,plain,
    ( spl6_72
  <=> r1_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f535,plain,
    ( spl6_64
  <=> m1_subset_1(k4_lattices(sK0,sK1,k6_lattices(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f814,plain,
    ( r1_lattices(sK0,sK1,sK1)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_52
    | ~ spl6_64 ),
    inference(forward_demodulation,[],[f791,f760])).

fof(f791,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK1,k6_lattices(sK0)),sK1)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_52
    | ~ spl6_64 ),
    inference(backward_demodulation,[],[f760,f575])).

fof(f575,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK1,k6_lattices(sK0)),k6_lattices(sK0)),k4_lattices(sK0,sK1,k6_lattices(sK0)))
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_64 ),
    inference(unit_resulting_resolution,[],[f145,f265,f273,f166,f536,f292,f116])).

fof(f536,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,k6_lattices(sK0)),u1_struct_0(sK0))
    | ~ spl6_64 ),
    inference(avatar_component_clause,[],[f535])).

fof(f669,plain,
    ( spl6_70
    | spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_32
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f627,f272,f264,f193,f165,f144,f667])).

fof(f667,plain,
    ( spl6_70
  <=> r1_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f627,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK1)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_32
    | ~ spl6_34 ),
    inference(unit_resulting_resolution,[],[f145,f265,f273,f166,f194,f194,f116])).

fof(f662,plain,
    ( spl6_68
    | spl6_1
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f645,f378,f291,f272,f264,f165,f144,f660])).

fof(f660,plain,
    ( spl6_68
  <=> r1_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f378,plain,
    ( spl6_54
  <=> k6_lattices(sK0) = k4_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f645,plain,
    ( r1_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_54 ),
    inference(forward_demodulation,[],[f573,f379])).

fof(f379,plain,
    ( k6_lattices(sK0) = k4_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f378])).

fof(f573,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)),k6_lattices(sK0))
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f145,f265,f273,f166,f292,f292,f116])).

fof(f655,plain,
    ( spl6_66
    | spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f639,f371,f291,f272,f264,f193,f165,f144,f653])).

fof(f639,plain,
    ( r1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_52 ),
    inference(forward_demodulation,[],[f621,f372])).

fof(f621,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,k6_lattices(sK0),sK1),k6_lattices(sK0))
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f145,f265,f273,f166,f292,f194,f116])).

fof(f537,plain,
    ( spl6_64
    | spl6_1
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_32
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f436,f291,f264,f202,f193,f144,f535])).

fof(f436,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,k6_lattices(sK0)),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_32
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f145,f265,f203,f194,f292,f128])).

fof(f472,plain,
    ( spl6_62
    | spl6_1
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f451,f264,f202,f193,f144,f470])).

fof(f451,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f145,f265,f203,f194,f194,f128])).

fof(f420,plain,
    ( spl6_60
    | spl6_1
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f387,f291,f202,f193,f144,f418])).

fof(f418,plain,
    ( spl6_60
  <=> m1_subset_1(k2_lattices(sK0,sK1,k6_lattices(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f387,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,k6_lattices(sK0)),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f145,f203,f194,f292,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t45_lattices.p',dt_k2_lattices)).

fof(f413,plain,
    ( spl6_58
    | spl6_1
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f383,f291,f202,f193,f144,f411])).

fof(f411,plain,
    ( spl6_58
  <=> m1_subset_1(k2_lattices(sK0,k6_lattices(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f383,plain,
    ( m1_subset_1(k2_lattices(sK0,k6_lattices(sK0),sK1),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f145,f203,f292,f194,f131])).

fof(f396,plain,
    ( spl6_56
    | spl6_1
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f381,f202,f193,f144,f394])).

fof(f394,plain,
    ( spl6_56
  <=> m1_subset_1(k2_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f381,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f145,f203,f194,f194,f131])).

fof(f380,plain,
    ( spl6_54
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f366,f291,f165,f158,f151,f144,f378])).

fof(f366,plain,
    ( k6_lattices(sK0) = k4_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f145,f152,f159,f166,f292,f115])).

fof(f373,plain,
    ( spl6_52
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f364,f193,f165,f158,f151,f144,f371])).

fof(f364,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),sK1) = sK1
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f145,f152,f159,f166,f194,f115])).

fof(f363,plain,
    ( spl6_50
    | spl6_1
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f341,f280,f272,f264,f165,f144,f361])).

fof(f361,plain,
    ( spl6_50
  <=> r3_lattices(sK0,sK2(u1_struct_0(sK0)),sK2(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f341,plain,
    ( r3_lattices(sK0,sK2(u1_struct_0(sK0)),sK2(u1_struct_0(sK0)))
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36 ),
    inference(unit_resulting_resolution,[],[f145,f265,f273,f281,f166,f119,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( r3_lattices(X1,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(condensation,[],[f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => r3_lattices(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t45_lattices.p',reflexivity_r3_lattices)).

fof(f356,plain,
    ( spl6_48
    | spl6_1
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f342,f291,f280,f272,f264,f165,f144,f354])).

fof(f354,plain,
    ( spl6_48
  <=> r3_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f342,plain,
    ( r3_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f145,f265,f273,f281,f166,f292,f139])).

fof(f349,plain,
    ( spl6_46
    | spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f340,f280,f272,f264,f193,f165,f144,f347])).

fof(f347,plain,
    ( spl6_46
  <=> r3_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f340,plain,
    ( r3_lattices(sK0,sK1,sK1)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_36 ),
    inference(unit_resulting_resolution,[],[f145,f265,f273,f281,f166,f194,f139])).

fof(f339,plain,
    ( spl6_44
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f307,f218,f337])).

fof(f337,plain,
    ( spl6_44
  <=> v1_funct_2(u1_lattices(sK4),k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f218,plain,
    ( spl6_20
  <=> l1_lattices(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f307,plain,
    ( v1_funct_2(u1_lattices(sK4),k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ spl6_20 ),
    inference(unit_resulting_resolution,[],[f219,f113])).

fof(f113,plain,(
    ! [X0] :
      ( v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( m1_subset_1(u1_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) )
      | ~ l1_lattices(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_lattices(X0)
     => ( m1_subset_1(u1_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t45_lattices.p',dt_u1_lattices)).

fof(f219,plain,
    ( l1_lattices(sK4)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f218])).

fof(f332,plain,
    ( spl6_42
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f306,f202,f330])).

fof(f330,plain,
    ( spl6_42
  <=> v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f306,plain,
    ( v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f203,f113])).

fof(f321,plain,
    ( spl6_40
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f305,f186,f319])).

fof(f319,plain,
    ( spl6_40
  <=> v1_funct_2(u1_lattices(sK5),k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f186,plain,
    ( spl6_12
  <=> l1_lattices(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f305,plain,
    ( v1_funct_2(u1_lattices(sK5),k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)),u1_struct_0(sK5))
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f187,f113])).

fof(f187,plain,
    ( l1_lattices(sK5)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f186])).

fof(f293,plain,
    ( spl6_38
    | spl6_1
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f286,f211,f144,f291])).

fof(f211,plain,
    ( spl6_18
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f286,plain,
    ( m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f145,f212,f117])).

fof(f117,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t45_lattices.p',dt_k6_lattices)).

fof(f212,plain,
    ( l2_lattices(sK0)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f211])).

fof(f282,plain,
    ( spl6_36
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f275,f165,f151,f144,f280])).

fof(f275,plain,
    ( v9_lattices(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f166,f145,f152,f111])).

fof(f111,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f41])).

fof(f41,plain,(
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
    inference(pure_predicate_removal,[],[f40])).

fof(f40,axiom,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t45_lattices.p',cc1_lattices)).

fof(f274,plain,
    ( spl6_34
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f267,f165,f151,f144,f272])).

fof(f267,plain,
    ( v8_lattices(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f166,f145,f152,f110])).

fof(f110,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f266,plain,
    ( spl6_32
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f259,f165,f151,f144,f264])).

fof(f259,plain,
    ( v6_lattices(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f166,f145,f152,f109])).

fof(f109,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f258,plain,
    ( spl6_30
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f237,f218,f256])).

fof(f256,plain,
    ( spl6_30
  <=> v1_funct_1(u1_lattices(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f237,plain,
    ( v1_funct_1(u1_lattices(sK4))
    | ~ spl6_20 ),
    inference(unit_resulting_resolution,[],[f219,f112])).

fof(f112,plain,(
    ! [X0] :
      ( v1_funct_1(u1_lattices(X0))
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f251,plain,
    ( spl6_28
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f236,f202,f249])).

fof(f249,plain,
    ( spl6_28
  <=> v1_funct_1(u1_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f236,plain,
    ( v1_funct_1(u1_lattices(sK0))
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f203,f112])).

fof(f244,plain,
    ( spl6_26
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f235,f186,f242])).

fof(f242,plain,
    ( spl6_26
  <=> v1_funct_1(u1_lattices(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f235,plain,
    ( v1_funct_1(u1_lattices(sK5))
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f187,f112])).

fof(f234,plain,(
    ~ spl6_25 ),
    inference(avatar_split_clause,[],[f104,f232])).

fof(f104,plain,(
    ~ r3_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,
    ( ~ r3_lattices(sK0,sK1,k6_lattices(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v14_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f88,f87])).

fof(f87,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r3_lattices(X0,X1,k6_lattices(X0))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r3_lattices(sK0,X1,k6_lattices(sK0))
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v14_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f88,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r3_lattices(X0,X1,k6_lattices(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK1,k6_lattices(X0))
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_lattices(X0,X1,k6_lattices(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_lattices(X0,X1,k6_lattices(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v14_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r3_lattices(X0,X1,k6_lattices(X0)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r3_lattices(X0,X1,k6_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t45_lattices.p',t45_lattices)).

fof(f227,plain,
    ( spl6_22
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f206,f179,f225])).

fof(f225,plain,
    ( spl6_22
  <=> l2_lattices(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f179,plain,
    ( spl6_10
  <=> l3_lattices(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f206,plain,
    ( l2_lattices(sK4)
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f180,f107])).

fof(f107,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t45_lattices.p',dt_l3_lattices)).

fof(f180,plain,
    ( l3_lattices(sK4)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f179])).

fof(f220,plain,
    ( spl6_20
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f197,f179,f218])).

fof(f197,plain,
    ( l1_lattices(sK4)
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f180,f106])).

fof(f106,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f213,plain,
    ( spl6_18
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f205,f165,f211])).

fof(f205,plain,
    ( l2_lattices(sK0)
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f166,f107])).

fof(f204,plain,
    ( spl6_16
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f196,f165,f202])).

fof(f196,plain,
    ( l1_lattices(sK0)
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f166,f106])).

fof(f195,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f103,f193])).

fof(f103,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f89])).

fof(f188,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f138,f186])).

fof(f138,plain,(
    l1_lattices(sK5) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    l1_lattices(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f97])).

fof(f97,plain,
    ( ? [X0] : l1_lattices(X0)
   => l1_lattices(sK5) ),
    introduced(choice_axiom,[])).

fof(f21,axiom,(
    ? [X0] : l1_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t45_lattices.p',existence_l1_lattices)).

fof(f181,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f137,f179])).

fof(f137,plain,(
    l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    l3_lattices(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f95])).

fof(f95,plain,
    ( ? [X0] : l3_lattices(X0)
   => l3_lattices(sK4) ),
    introduced(choice_axiom,[])).

fof(f24,axiom,(
    ? [X0] : l3_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t45_lattices.p',existence_l3_lattices)).

fof(f174,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f136,f172])).

fof(f172,plain,
    ( spl6_8
  <=> l2_lattices(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f136,plain,(
    l2_lattices(sK3) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    l2_lattices(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f93])).

fof(f93,plain,
    ( ? [X0] : l2_lattices(X0)
   => l2_lattices(sK3) ),
    introduced(choice_axiom,[])).

fof(f23,axiom,(
    ? [X0] : l2_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t45_lattices.p',existence_l2_lattices)).

fof(f167,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f102,f165])).

fof(f102,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f89])).

fof(f160,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f101,f158])).

fof(f101,plain,(
    v14_lattices(sK0) ),
    inference(cnf_transformation,[],[f89])).

fof(f153,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f100,f151])).

fof(f100,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f89])).

fof(f146,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f99,f144])).

fof(f99,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f89])).
%------------------------------------------------------------------------------
