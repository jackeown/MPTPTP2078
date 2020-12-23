%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattices__t41_lattices.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:02 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  267 ( 925 expanded)
%              Number of leaves         :   74 ( 464 expanded)
%              Depth                    :    8
%              Number of atoms          : 1063 (3049 expanded)
%              Number of equality atoms :   44 (  86 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1196,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f146,f153,f160,f167,f174,f181,f188,f195,f204,f213,f220,f227,f234,f244,f251,f258,f266,f274,f282,f290,f298,f309,f337,f348,f355,f365,f372,f379,f389,f396,f412,f429,f436,f488,f553,f824,f832,f839,f846,f935,f942,f1065,f1074,f1081,f1091,f1098,f1105,f1120,f1130,f1137,f1175])).

fof(f1175,plain,
    ( spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_40
    | ~ spl6_42
    | ~ spl6_70
    | spl6_95 ),
    inference(avatar_contradiction_clause,[],[f1174])).

fof(f1174,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_40
    | ~ spl6_42
    | ~ spl6_70
    | ~ spl6_95 ),
    inference(subsumption_resolution,[],[f1173,f1119])).

fof(f1119,plain,
    ( ~ r1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl6_95 ),
    inference(avatar_component_clause,[],[f1118])).

fof(f1118,plain,
    ( spl6_95
  <=> ~ r1_lattices(sK0,k5_lattices(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).

fof(f1173,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_40
    | ~ spl6_42
    | ~ spl6_70 ),
    inference(forward_demodulation,[],[f1153,f823])).

fof(f823,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),sK1) = sK1
    | ~ spl6_70 ),
    inference(avatar_component_clause,[],[f822])).

fof(f822,plain,
    ( spl6_70
  <=> k1_lattices(sK0,k5_lattices(sK0),sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f1153,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),k1_lattices(sK0,k5_lattices(sK0),sK1))
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_34
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_40
    | ~ spl6_42 ),
    inference(unit_resulting_resolution,[],[f145,f273,f281,f289,f297,f166,f308,f194,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',t22_lattices)).

fof(f194,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl6_14
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f308,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl6_42
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f166,plain,
    ( l3_lattices(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl6_6
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f297,plain,
    ( v9_lattices(sK0)
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl6_40
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f289,plain,
    ( v8_lattices(sK0)
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl6_38
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f281,plain,
    ( v6_lattices(sK0)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl6_36
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f273,plain,
    ( v5_lattices(sK0)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl6_34
  <=> v5_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f145,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl6_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1137,plain,
    ( spl6_98
    | spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_42
    | ~ spl6_80 ),
    inference(avatar_split_clause,[],[f1053,f940,f307,f211,f193,f144,f1135])).

fof(f1135,plain,
    ( spl6_98
  <=> k4_binop_1(u1_struct_0(sK0),u2_lattices(sK0),sK1,k5_lattices(sK0)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).

fof(f211,plain,
    ( spl6_18
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f940,plain,
    ( spl6_80
  <=> k1_lattices(sK0,sK1,k5_lattices(sK0)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f1053,plain,
    ( k4_binop_1(u1_struct_0(sK0),u2_lattices(sK0),sK1,k5_lattices(sK0)) = sK1
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_42
    | ~ spl6_80 ),
    inference(forward_demodulation,[],[f1010,f941])).

fof(f941,plain,
    ( k1_lattices(sK0,sK1,k5_lattices(sK0)) = sK1
    | ~ spl6_80 ),
    inference(avatar_component_clause,[],[f940])).

fof(f1010,plain,
    ( k1_lattices(sK0,sK1,k5_lattices(sK0)) = k4_binop_1(u1_struct_0(sK0),u2_lattices(sK0),sK1,k5_lattices(sK0))
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_42 ),
    inference(unit_resulting_resolution,[],[f145,f212,f194,f308,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = k4_binop_1(u1_struct_0(X0),u2_lattices(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_lattices(X0,X1,X2) = k4_binop_1(u1_struct_0(X0),u2_lattices(X0),X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_lattices(X0,X1,X2) = k4_binop_1(u1_struct_0(X0),u2_lattices(X0),X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k1_lattices(X0,X1,X2) = k4_binop_1(u1_struct_0(X0),u2_lattices(X0),X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',d1_lattices)).

fof(f212,plain,
    ( l2_lattices(sK0)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f211])).

fof(f1130,plain,
    ( spl6_96
    | spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_42
    | ~ spl6_70 ),
    inference(avatar_split_clause,[],[f1041,f822,f307,f211,f193,f144,f1128])).

fof(f1128,plain,
    ( spl6_96
  <=> k4_binop_1(u1_struct_0(sK0),u2_lattices(sK0),k5_lattices(sK0),sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).

fof(f1041,plain,
    ( k4_binop_1(u1_struct_0(sK0),u2_lattices(sK0),k5_lattices(sK0),sK1) = sK1
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_42
    | ~ spl6_70 ),
    inference(forward_demodulation,[],[f1022,f823])).

fof(f1022,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),sK1) = k4_binop_1(u1_struct_0(sK0),u2_lattices(sK0),k5_lattices(sK0),sK1)
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_42 ),
    inference(unit_resulting_resolution,[],[f145,f212,f308,f194,f118])).

fof(f1120,plain,
    ( ~ spl6_95
    | spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | spl6_25
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_40
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f1107,f307,f296,f288,f280,f232,f193,f165,f144,f1118])).

fof(f232,plain,
    ( spl6_25
  <=> ~ r3_lattices(sK0,k5_lattices(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f1107,plain,
    ( ~ r1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_25
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_40
    | ~ spl6_42 ),
    inference(unit_resulting_resolution,[],[f145,f281,f289,f297,f166,f233,f308,f194,f127])).

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
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
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
    inference(nnf_transformation,[],[f69])).

fof(f69,plain,(
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
    inference(flattening,[],[f68])).

fof(f68,plain,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',redefinition_r3_lattices)).

fof(f233,plain,
    ( ~ r3_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f232])).

fof(f1105,plain,
    ( spl6_92
    | spl6_1
    | ~ spl6_6
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_40
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f1084,f377,f296,f288,f280,f165,f144,f1103])).

fof(f1103,plain,
    ( spl6_92
  <=> r1_lattices(sK0,sK2(u1_struct_0(sK0)),sK2(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f377,plain,
    ( spl6_54
  <=> r3_lattices(sK0,sK2(u1_struct_0(sK0)),sK2(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f1084,plain,
    ( r1_lattices(sK0,sK2(u1_struct_0(sK0)),sK2(u1_struct_0(sK0)))
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_40
    | ~ spl6_54 ),
    inference(unit_resulting_resolution,[],[f145,f281,f289,f297,f166,f119,f378,f119,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f378,plain,
    ( r3_lattices(sK0,sK2(u1_struct_0(sK0)),sK2(u1_struct_0(sK0)))
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f377])).

fof(f119,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',existence_m1_subset_1)).

fof(f1098,plain,
    ( spl6_90
    | spl6_1
    | ~ spl6_6
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_40
    | ~ spl6_42
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f1082,f370,f307,f296,f288,f280,f165,f144,f1096])).

fof(f1096,plain,
    ( spl6_90
  <=> r1_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).

fof(f370,plain,
    ( spl6_52
  <=> r3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f1082,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_40
    | ~ spl6_42
    | ~ spl6_52 ),
    inference(unit_resulting_resolution,[],[f145,f281,f289,f297,f166,f308,f371,f308,f126])).

fof(f371,plain,
    ( r3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f370])).

fof(f1091,plain,
    ( spl6_88
    | spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_40
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f1083,f363,f296,f288,f280,f193,f165,f144,f1089])).

fof(f1089,plain,
    ( spl6_88
  <=> r1_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).

fof(f363,plain,
    ( spl6_50
  <=> r3_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f1083,plain,
    ( r1_lattices(sK0,sK1,sK1)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_40
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f145,f281,f289,f297,f166,f194,f364,f194,f126])).

fof(f364,plain,
    ( r3_lattices(sK0,sK1,sK1)
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f363])).

fof(f1081,plain,
    ( spl6_86
    | spl6_1
    | ~ spl6_6
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_40
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f514,f486,f296,f288,f280,f165,f144,f1079])).

fof(f1079,plain,
    ( spl6_86
  <=> r3_lattices(sK0,k3_lattices(sK0,sK1,sK1),k3_lattices(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).

fof(f486,plain,
    ( spl6_66
  <=> m1_subset_1(k3_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f514,plain,
    ( r3_lattices(sK0,k3_lattices(sK0,sK1,sK1),k3_lattices(sK0,sK1,sK1))
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_40
    | ~ spl6_66 ),
    inference(unit_resulting_resolution,[],[f145,f281,f289,f297,f166,f487,f139])).

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
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',reflexivity_r3_lattices)).

fof(f487,plain,
    ( m1_subset_1(k3_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl6_66 ),
    inference(avatar_component_clause,[],[f486])).

fof(f1074,plain,
    ( spl6_84
    | spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_32
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f499,f486,f264,f211,f193,f144,f1072])).

fof(f1072,plain,
    ( spl6_84
  <=> m1_subset_1(k3_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).

fof(f264,plain,
    ( spl6_32
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f499,plain,
    ( m1_subset_1(k3_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK1)),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_32
    | ~ spl6_66 ),
    inference(unit_resulting_resolution,[],[f145,f265,f212,f194,f487,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',dt_k3_lattices)).

fof(f265,plain,
    ( v4_lattices(sK0)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f264])).

fof(f1065,plain,
    ( spl6_82
    | spl6_1
    | ~ spl6_18
    | ~ spl6_32
    | ~ spl6_42
    | ~ spl6_58 ),
    inference(avatar_split_clause,[],[f814,f394,f307,f264,f211,f144,f1063])).

fof(f1063,plain,
    ( spl6_82
  <=> k5_lattices(sK0) = k1_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).

fof(f394,plain,
    ( spl6_58
  <=> k5_lattices(sK0) = k3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f814,plain,
    ( k5_lattices(sK0) = k1_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))
    | ~ spl6_1
    | ~ spl6_18
    | ~ spl6_32
    | ~ spl6_42
    | ~ spl6_58 ),
    inference(forward_demodulation,[],[f589,f395])).

fof(f395,plain,
    ( k5_lattices(sK0) = k3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f394])).

fof(f589,plain,
    ( k3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) = k1_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))
    | ~ spl6_1
    | ~ spl6_18
    | ~ spl6_32
    | ~ spl6_42 ),
    inference(unit_resulting_resolution,[],[f145,f265,f212,f308,f308,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',redefinition_k3_lattices)).

fof(f942,plain,
    ( spl6_80
    | spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_32
    | ~ spl6_42
    | ~ spl6_56 ),
    inference(avatar_split_clause,[],[f896,f387,f307,f264,f211,f193,f144,f940])).

fof(f387,plain,
    ( spl6_56
  <=> k3_lattices(sK0,k5_lattices(sK0),sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f896,plain,
    ( k1_lattices(sK0,sK1,k5_lattices(sK0)) = sK1
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_32
    | ~ spl6_42
    | ~ spl6_56 ),
    inference(backward_demodulation,[],[f886,f595])).

fof(f595,plain,
    ( k3_lattices(sK0,sK1,k5_lattices(sK0)) = k1_lattices(sK0,sK1,k5_lattices(sK0))
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_32
    | ~ spl6_42 ),
    inference(unit_resulting_resolution,[],[f145,f265,f212,f194,f308,f129])).

fof(f886,plain,
    ( k3_lattices(sK0,sK1,k5_lattices(sK0)) = sK1
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_32
    | ~ spl6_42
    | ~ spl6_56 ),
    inference(forward_demodulation,[],[f862,f388])).

fof(f388,plain,
    ( k3_lattices(sK0,k5_lattices(sK0),sK1) = sK1
    | ~ spl6_56 ),
    inference(avatar_component_clause,[],[f387])).

fof(f862,plain,
    ( k3_lattices(sK0,k5_lattices(sK0),sK1) = k3_lattices(sK0,sK1,k5_lattices(sK0))
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_32
    | ~ spl6_42 ),
    inference(unit_resulting_resolution,[],[f145,f265,f212,f308,f194,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',commutativity_k3_lattices)).

fof(f935,plain,
    ( spl6_78
    | spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_32
    | ~ spl6_42
    | ~ spl6_56 ),
    inference(avatar_split_clause,[],[f886,f387,f307,f264,f211,f193,f144,f933])).

fof(f933,plain,
    ( spl6_78
  <=> k3_lattices(sK0,sK1,k5_lattices(sK0)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f846,plain,
    ( spl6_76
    | spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f643,f264,f211,f193,f144,f844])).

fof(f844,plain,
    ( spl6_76
  <=> k3_lattices(sK0,sK1,sK1) = k1_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f643,plain,
    ( k3_lattices(sK0,sK1,sK1) = k1_lattices(sK0,sK1,sK1)
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f145,f265,f212,f194,f194,f129])).

fof(f839,plain,
    ( spl6_74
    | spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f472,f264,f211,f193,f144,f837])).

fof(f837,plain,
    ( spl6_74
  <=> m1_subset_1(k3_lattices(sK0,sK1,sK2(u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f472,plain,
    ( m1_subset_1(k3_lattices(sK0,sK1,sK2(u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f145,f265,f212,f194,f119,f128])).

fof(f832,plain,
    ( spl6_72
    | spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f468,f264,f211,f193,f144,f830])).

fof(f830,plain,
    ( spl6_72
  <=> m1_subset_1(k3_lattices(sK0,sK2(u1_struct_0(sK0)),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f468,plain,
    ( m1_subset_1(k3_lattices(sK0,sK2(u1_struct_0(sK0)),sK1),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f145,f265,f212,f119,f194,f128])).

fof(f824,plain,
    ( spl6_70
    | spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_32
    | ~ spl6_42
    | ~ spl6_56 ),
    inference(avatar_split_clause,[],[f701,f387,f307,f264,f211,f193,f144,f822])).

fof(f701,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),sK1) = sK1
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_32
    | ~ spl6_42
    | ~ spl6_56 ),
    inference(forward_demodulation,[],[f637,f388])).

fof(f637,plain,
    ( k3_lattices(sK0,k5_lattices(sK0),sK1) = k1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_32
    | ~ spl6_42 ),
    inference(unit_resulting_resolution,[],[f145,f265,f212,f308,f194,f129])).

fof(f553,plain,
    ( spl6_68
    | spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_32
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f452,f307,f264,f211,f193,f144,f551])).

fof(f551,plain,
    ( spl6_68
  <=> m1_subset_1(k3_lattices(sK0,sK1,k5_lattices(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f452,plain,
    ( m1_subset_1(k3_lattices(sK0,sK1,k5_lattices(sK0)),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_32
    | ~ spl6_42 ),
    inference(unit_resulting_resolution,[],[f145,f265,f212,f194,f308,f128])).

fof(f488,plain,
    ( spl6_66
    | spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f467,f264,f211,f193,f144,f486])).

fof(f467,plain,
    ( m1_subset_1(k3_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f145,f265,f212,f194,f194,f128])).

fof(f436,plain,
    ( spl6_64
    | spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f403,f307,f211,f193,f144,f434])).

fof(f434,plain,
    ( spl6_64
  <=> m1_subset_1(k1_lattices(sK0,sK1,k5_lattices(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f403,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,k5_lattices(sK0)),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_42 ),
    inference(unit_resulting_resolution,[],[f145,f212,f194,f308,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',dt_k1_lattices)).

fof(f429,plain,
    ( spl6_62
    | spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f399,f307,f211,f193,f144,f427])).

fof(f427,plain,
    ( spl6_62
  <=> m1_subset_1(k1_lattices(sK0,k5_lattices(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f399,plain,
    ( m1_subset_1(k1_lattices(sK0,k5_lattices(sK0),sK1),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_42 ),
    inference(unit_resulting_resolution,[],[f145,f212,f308,f194,f131])).

fof(f412,plain,
    ( spl6_60
    | spl6_1
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f397,f211,f193,f144,f410])).

fof(f410,plain,
    ( spl6_60
  <=> m1_subset_1(k1_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f397,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f145,f212,f194,f194,f131])).

fof(f396,plain,
    ( spl6_58
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f382,f307,f165,f158,f151,f144,f394])).

fof(f151,plain,
    ( spl6_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f158,plain,
    ( spl6_4
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f382,plain,
    ( k5_lattices(sK0) = k3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_42 ),
    inference(unit_resulting_resolution,[],[f145,f152,f159,f166,f308,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( k3_lattices(X0,k5_lattices(X0),X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',t39_lattices)).

fof(f159,plain,
    ( v13_lattices(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f158])).

fof(f152,plain,
    ( v10_lattices(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f151])).

fof(f389,plain,
    ( spl6_56
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f380,f193,f165,f158,f151,f144,f387])).

fof(f380,plain,
    ( k3_lattices(sK0,k5_lattices(sK0),sK1) = sK1
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f145,f152,f159,f166,f194,f116])).

fof(f379,plain,
    ( spl6_54
    | spl6_1
    | ~ spl6_6
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f357,f296,f288,f280,f165,f144,f377])).

fof(f357,plain,
    ( r3_lattices(sK0,sK2(u1_struct_0(sK0)),sK2(u1_struct_0(sK0)))
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f145,f281,f289,f297,f166,f119,f139])).

fof(f372,plain,
    ( spl6_52
    | spl6_1
    | ~ spl6_6
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_40
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f358,f307,f296,f288,f280,f165,f144,f370])).

fof(f358,plain,
    ( r3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_40
    | ~ spl6_42 ),
    inference(unit_resulting_resolution,[],[f145,f281,f289,f297,f166,f308,f139])).

fof(f365,plain,
    ( spl6_50
    | spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f356,f296,f288,f280,f193,f165,f144,f363])).

fof(f356,plain,
    ( r3_lattices(sK0,sK1,sK1)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_36
    | ~ spl6_38
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f145,f281,f289,f297,f166,f194,f139])).

fof(f355,plain,
    ( spl6_48
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f323,f225,f353])).

fof(f353,plain,
    ( spl6_48
  <=> v1_funct_2(u2_lattices(sK4),k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f225,plain,
    ( spl6_22
  <=> l2_lattices(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f323,plain,
    ( v1_funct_2(u2_lattices(sK4),k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f226,f113])).

fof(f113,plain,(
    ! [X0] :
      ( v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) )
      | ~ l2_lattices(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l2_lattices(X0)
     => ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',dt_u2_lattices)).

fof(f226,plain,
    ( l2_lattices(sK4)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f225])).

fof(f348,plain,
    ( spl6_46
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f322,f211,f346])).

fof(f346,plain,
    ( spl6_46
  <=> v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f322,plain,
    ( v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f212,f113])).

fof(f337,plain,
    ( spl6_44
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f321,f186,f335])).

fof(f335,plain,
    ( spl6_44
  <=> v1_funct_2(u2_lattices(sK5),k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f186,plain,
    ( spl6_12
  <=> l2_lattices(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f321,plain,
    ( v1_funct_2(u2_lattices(sK5),k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)),u1_struct_0(sK5))
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f187,f113])).

fof(f187,plain,
    ( l2_lattices(sK5)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f186])).

fof(f309,plain,
    ( spl6_42
    | spl6_1
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f302,f202,f144,f307])).

fof(f202,plain,
    ( spl6_16
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f302,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f145,f203,f117])).

fof(f117,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',dt_k5_lattices)).

fof(f203,plain,
    ( l1_lattices(sK0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f202])).

fof(f298,plain,
    ( spl6_40
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f291,f165,f151,f144,f296])).

fof(f291,plain,
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
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f41])).

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
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',cc1_lattices)).

fof(f290,plain,
    ( spl6_38
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f283,f165,f151,f144,f288])).

fof(f283,plain,
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
    inference(cnf_transformation,[],[f50])).

fof(f282,plain,
    ( spl6_36
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f275,f165,f151,f144,f280])).

fof(f275,plain,
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
    inference(cnf_transformation,[],[f50])).

fof(f274,plain,
    ( spl6_34
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f267,f165,f151,f144,f272])).

fof(f267,plain,
    ( v5_lattices(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f166,f145,f152,f108])).

fof(f108,plain,(
    ! [X0] :
      ( v5_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f266,plain,
    ( spl6_32
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f259,f165,f151,f144,f264])).

fof(f259,plain,
    ( v4_lattices(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f166,f145,f152,f107])).

fof(f107,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f258,plain,
    ( spl6_30
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f237,f225,f256])).

fof(f256,plain,
    ( spl6_30
  <=> v1_funct_1(u2_lattices(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f237,plain,
    ( v1_funct_1(u2_lattices(sK4))
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f226,f112])).

fof(f112,plain,(
    ! [X0] :
      ( v1_funct_1(u2_lattices(X0))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f251,plain,
    ( spl6_28
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f236,f211,f249])).

fof(f249,plain,
    ( spl6_28
  <=> v1_funct_1(u2_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f236,plain,
    ( v1_funct_1(u2_lattices(sK0))
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f212,f112])).

fof(f244,plain,
    ( spl6_26
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f235,f186,f242])).

fof(f242,plain,
    ( spl6_26
  <=> v1_funct_1(u2_lattices(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f235,plain,
    ( v1_funct_1(u2_lattices(sK5))
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f187,f112])).

fof(f234,plain,(
    ~ spl6_25 ),
    inference(avatar_split_clause,[],[f102,f232])).

fof(f102,plain,(
    ~ r3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,
    ( ~ r3_lattices(sK0,k5_lattices(sK0),sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v13_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f46,f86,f85])).

fof(f85,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r3_lattices(X0,k5_lattices(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r3_lattices(sK0,k5_lattices(sK0),X1)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v13_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r3_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,k5_lattices(X0),sK1)
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r3_lattices(X0,k5_lattices(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r3_lattices(X0,k5_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',t41_lattices)).

fof(f227,plain,
    ( spl6_22
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f206,f179,f225])).

fof(f179,plain,
    ( spl6_10
  <=> l3_lattices(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f206,plain,
    ( l2_lattices(sK4)
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f180,f105])).

fof(f105,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',dt_l3_lattices)).

fof(f180,plain,
    ( l3_lattices(sK4)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f179])).

fof(f220,plain,
    ( spl6_20
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f197,f179,f218])).

fof(f218,plain,
    ( spl6_20
  <=> l1_lattices(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f197,plain,
    ( l1_lattices(sK4)
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f180,f104])).

fof(f104,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f213,plain,
    ( spl6_18
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f205,f165,f211])).

fof(f205,plain,
    ( l2_lattices(sK0)
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f166,f105])).

fof(f204,plain,
    ( spl6_16
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f196,f165,f202])).

fof(f196,plain,
    ( l1_lattices(sK0)
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f166,f104])).

fof(f195,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f101,f193])).

fof(f101,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f87])).

fof(f188,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f138,f186])).

fof(f138,plain,(
    l2_lattices(sK5) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    l2_lattices(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f95])).

fof(f95,plain,
    ( ? [X0] : l2_lattices(X0)
   => l2_lattices(sK5) ),
    introduced(choice_axiom,[])).

fof(f23,axiom,(
    ? [X0] : l2_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',existence_l2_lattices)).

fof(f181,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f137,f179])).

fof(f137,plain,(
    l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    l3_lattices(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f93])).

fof(f93,plain,
    ( ? [X0] : l3_lattices(X0)
   => l3_lattices(sK4) ),
    introduced(choice_axiom,[])).

fof(f24,axiom,(
    ? [X0] : l3_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',existence_l3_lattices)).

fof(f174,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f136,f172])).

fof(f172,plain,
    ( spl6_8
  <=> l1_lattices(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f136,plain,(
    l1_lattices(sK3) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    l1_lattices(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f91])).

fof(f91,plain,
    ( ? [X0] : l1_lattices(X0)
   => l1_lattices(sK3) ),
    introduced(choice_axiom,[])).

fof(f21,axiom,(
    ? [X0] : l1_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t41_lattices.p',existence_l1_lattices)).

fof(f167,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f100,f165])).

fof(f100,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f87])).

fof(f160,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f99,f158])).

fof(f99,plain,(
    v13_lattices(sK0) ),
    inference(cnf_transformation,[],[f87])).

fof(f153,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f98,f151])).

fof(f98,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f87])).

fof(f146,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f97,f144])).

fof(f97,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f87])).
%------------------------------------------------------------------------------
