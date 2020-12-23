%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattices__t32_lattices.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:01 EDT 2019

% Result     : Theorem 11.10s
% Output     : Refutation 11.10s
% Verified   : 
% Statistics : Number of formulae       :  931 (404597 expanded)
%              Number of leaves         :  117 (154261 expanded)
%              Depth                    :   53
%              Number of atoms          : 8528 (1677324 expanded)
%              Number of equality atoms :  580 (196229 expanded)
%              Maximal formula depth    :   28 (  10 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25621,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f172,f179,f186,f193,f200,f207,f214,f221,f228,f235,f242,f251,f260,f267,f274,f284,f294,f301,f308,f315,f322,f330,f338,f346,f356,f363,f399,f406,f413,f423,f430,f441,f448,f457,f469,f478,f486,f493,f502,f526,f533,f540,f547,f554,f577,f584,f591,f598,f832,f922,f929,f936,f943,f950,f1041,f1048,f1055,f1776,f1783,f1790,f3469,f3476,f3483,f3490,f3497,f3957,f3964,f3971,f3978,f4124,f7145,f7152,f7159,f7166,f7571,f7578,f7585,f7592,f7599,f14067,f14083,f14091,f14112,f14647,f14666,f14675,f14700,f14851,f14867,f14875,f14896,f15184,f15227,f16096,f16361,f18881,f18897,f18905,f18927,f18955])).

fof(f18955,plain,
    ( spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(avatar_contradiction_clause,[],[f18954])).

fof(f18954,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f18953,f220])).

fof(f220,plain,
    ( sK2 != sK3
    | ~ spl13_15 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl13_15
  <=> sK2 != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).

fof(f18953,plain,
    ( sK2 = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f18952,f12315])).

fof(f12315,plain,
    ( k1_lattices(sK0,sK3,sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f12162,f11919])).

fof(f11919,plain,
    ( k3_lattices(sK0,sK3,sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f11918,f1373])).

fof(f1373,plain,
    ( k3_lattices(sK0,sK2,sK3) = k3_lattices(sK0,sK3,sK2)
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f234,f241,f153])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',commutativity_k3_lattices)).

fof(f241,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl13_20 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl13_20
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).

fof(f234,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl13_18 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl13_18
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f259,plain,
    ( l2_lattices(sK0)
    | ~ spl13_24 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl13_24
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_24])])).

fof(f329,plain,
    ( v4_lattices(sK0)
    | ~ spl13_42 ),
    inference(avatar_component_clause,[],[f328])).

fof(f328,plain,
    ( spl13_42
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_42])])).

fof(f171,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl13_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f11918,plain,
    ( k3_lattices(sK0,sK2,sK3) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f11799,f11311])).

fof(f11311,plain,
    ( k3_lattices(sK0,sK2,sK3) = k1_lattices(sK0,sK3,sK3)
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f11309,f3997])).

fof(f3997,plain,
    ( k3_lattices(sK0,sK3,sK3) = k1_lattices(sK0,sK3,sK3)
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f241,f241,f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',redefinition_k3_lattices)).

fof(f11309,plain,
    ( k3_lattices(sK0,sK2,sK3) = k3_lattices(sK0,sK3,sK3)
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f11308,f11304])).

fof(f11304,plain,
    ( k3_lattices(sK0,sK3,sK3) = k1_lattices(sK0,k4_lattices(sK0,sK1,k3_lattices(sK0,sK2,sK3)),sK3)
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11303,f11147])).

fof(f11147,plain,
    ( k4_lattices(sK0,sK1,k3_lattices(sK0,sK2,sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK1)
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_48
    | ~ spl13_134
    | ~ spl13_136 ),
    inference(backward_demodulation,[],[f11143,f6610])).

fof(f6610,plain,
    ( k4_lattices(sK0,sK1,k3_lattices(sK0,sK3,sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK1)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_136 ),
    inference(forward_demodulation,[],[f6417,f6456])).

fof(f6456,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK1) = k4_lattices(sK0,sK1,k3_lattices(sK0,sK3,sK3))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_136 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f227,f3977,f155])).

fof(f155,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',commutativity_k4_lattices)).

fof(f3977,plain,
    ( m1_subset_1(k3_lattices(sK0,sK3,sK3),u1_struct_0(sK0))
    | ~ spl13_136 ),
    inference(avatar_component_clause,[],[f3976])).

fof(f3976,plain,
    ( spl13_136
  <=> m1_subset_1(k3_lattices(sK0,sK3,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_136])])).

fof(f227,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl13_16 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl13_16
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).

fof(f250,plain,
    ( l1_lattices(sK0)
    | ~ spl13_22 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl13_22
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_22])])).

fof(f337,plain,
    ( v6_lattices(sK0)
    | ~ spl13_44 ),
    inference(avatar_component_clause,[],[f336])).

fof(f336,plain,
    ( spl13_44
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_44])])).

fof(f6417,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK1) = k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK1)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_136 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f227,f3977,f154])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',redefinition_k4_lattices)).

fof(f11143,plain,
    ( k4_lattices(sK0,sK1,k3_lattices(sK0,sK2,sK3)) = k4_lattices(sK0,sK1,k3_lattices(sK0,sK3,sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_48
    | ~ spl13_134
    | ~ spl13_136 ),
    inference(backward_demodulation,[],[f11142,f11021])).

fof(f11021,plain,
    ( k4_lattices(sK0,sK1,k3_lattices(sK0,sK3,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_48
    | ~ spl13_136 ),
    inference(forward_demodulation,[],[f11020,f2241])).

fof(f2241,plain,
    ( k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK3)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_48 ),
    inference(forward_demodulation,[],[f1943,f355])).

fof(f355,plain,
    ( k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3)
    | ~ spl13_48 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl13_48
  <=> k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_48])])).

fof(f1943,plain,
    ( k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,sK3)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f227,f241,f154])).

fof(f11020,plain,
    ( k4_lattices(sK0,sK1,k3_lattices(sK0,sK3,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK1,sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_136 ),
    inference(forward_demodulation,[],[f11019,f6430])).

fof(f6430,plain,
    ( k4_lattices(sK0,sK1,k3_lattices(sK0,sK3,sK3)) = k2_lattices(sK0,sK1,k3_lattices(sK0,sK3,sK3))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_136 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f227,f3977,f154])).

fof(f11019,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK1,sK3)) = k2_lattices(sK0,sK1,k3_lattices(sK0,sK3,sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(forward_demodulation,[],[f10130,f3997])).

fof(f10130,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK1,sK3)) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK3,sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f227,f241,f241,f140])).

fof(f140,plain,(
    ! [X6,X4,X0,X5] :
      ( ~ v11_lattices(X0)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ( k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),k2_lattices(X0,sK6(X0),sK8(X0))) != k2_lattices(X0,sK6(X0),k1_lattices(X0,sK7(X0),sK8(X0)))
            & m1_subset_1(sK8(X0),u1_struct_0(X0))
            & m1_subset_1(sK7(X0),u1_struct_0(X0))
            & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6))
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f100,f103,f102,f101])).

fof(f101,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k1_lattices(X0,k2_lattices(X0,sK6(X0),X2),k2_lattices(X0,sK6(X0),X3)) != k2_lattices(X0,sK6(X0),k1_lattices(X0,X2,X3))
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f102,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k1_lattices(X0,k2_lattices(X0,X1,sK7(X0)),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,sK7(X0),X3))
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f103,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,sK8(X0))) != k2_lattices(X0,X1,k1_lattices(X0,X2,sK8(X0)))
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f100,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6))
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f99])).

fof(f99,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ! [X3] :
                      ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
                   => k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',d11_lattices)).

fof(f185,plain,
    ( v11_lattices(sK0)
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl13_4
  <=> v11_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f192,plain,
    ( l3_lattices(sK0)
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl13_6
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f11142,plain,
    ( k4_lattices(sK0,sK1,k3_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_48
    | ~ spl13_134 ),
    inference(forward_demodulation,[],[f11141,f1930])).

fof(f1930,plain,
    ( k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f227,f234,f154])).

fof(f11141,plain,
    ( k4_lattices(sK0,sK1,k3_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_48
    | ~ spl13_134 ),
    inference(forward_demodulation,[],[f11140,f2241])).

fof(f11140,plain,
    ( k4_lattices(sK0,sK1,k3_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),k2_lattices(sK0,sK1,sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_134 ),
    inference(forward_demodulation,[],[f11139,f6049])).

fof(f6049,plain,
    ( k4_lattices(sK0,sK1,k3_lattices(sK0,sK2,sK3)) = k2_lattices(sK0,sK1,k3_lattices(sK0,sK2,sK3))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_134 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f227,f3970,f154])).

fof(f3970,plain,
    ( m1_subset_1(k3_lattices(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl13_134 ),
    inference(avatar_component_clause,[],[f3969])).

fof(f3969,plain,
    ( spl13_134
  <=> m1_subset_1(k3_lattices(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_134])])).

fof(f11139,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),k2_lattices(sK0,sK1,sK3)) = k2_lattices(sK0,sK1,k3_lattices(sK0,sK2,sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(forward_demodulation,[],[f10116,f3996])).

fof(f3996,plain,
    ( k3_lattices(sK0,sK2,sK3) = k1_lattices(sK0,sK2,sK3)
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f234,f241,f156])).

fof(f10116,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),k2_lattices(sK0,sK1,sK3)) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f227,f234,f241,f140])).

fof(f11303,plain,
    ( k3_lattices(sK0,sK3,sK3) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK1),sK3)
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11302,f6606])).

fof(f6606,plain,
    ( k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK3) = sK3
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_136 ),
    inference(forward_demodulation,[],[f6419,f6592])).

fof(f6592,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK3) = sK3
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_136 ),
    inference(backward_demodulation,[],[f6591,f6458])).

fof(f6458,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK3) = k4_lattices(sK0,sK3,k3_lattices(sK0,sK3,sK3))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_136 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f241,f3977,f155])).

fof(f6591,plain,
    ( k4_lattices(sK0,sK3,k3_lattices(sK0,sK3,sK3)) = sK3
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_136 ),
    inference(forward_demodulation,[],[f6432,f4020])).

fof(f4020,plain,
    ( k2_lattices(sK0,sK3,k3_lattices(sK0,sK3,sK3)) = sK3
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_46 ),
    inference(backward_demodulation,[],[f3997,f1021])).

fof(f1021,plain,
    ( k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,sK3)) = sK3
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_46 ),
    inference(unit_resulting_resolution,[],[f171,f192,f345,f241,f241,f136])).

fof(f136,plain,(
    ! [X4,X0,X3] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),sK5(X0))) != sK4(X0)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f95,f97,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),X2)) != sK4(X0)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,k1_lattices(X0,X1,sK5(X0))) != X1
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f95,plain,(
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
    inference(rectify,[],[f94])).

fof(f94,plain,(
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
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',d9_lattices)).

fof(f345,plain,
    ( v9_lattices(sK0)
    | ~ spl13_46 ),
    inference(avatar_component_clause,[],[f344])).

fof(f344,plain,
    ( spl13_46
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_46])])).

fof(f6432,plain,
    ( k4_lattices(sK0,sK3,k3_lattices(sK0,sK3,sK3)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK3,sK3))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_136 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f241,f3977,f154])).

fof(f6419,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK3) = k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK3)
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_136 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f241,f3977,f154])).

fof(f11302,plain,
    ( k3_lattices(sK0,sK3,sK3) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK1),k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11301,f11054])).

fof(f11054,plain,
    ( k3_lattices(sK0,sK3,sK3) = k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f11049,f7020])).

fof(f7020,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK3,sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f6838,f6866])).

fof(f6866,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK3,sK3)) = k4_lattices(sK0,k3_lattices(sK0,sK3,sK3),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f3977,f4123,f155])).

fof(f4123,plain,
    ( m1_subset_1(k3_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl13_138 ),
    inference(avatar_component_clause,[],[f4122])).

fof(f4122,plain,
    ( spl13_138
  <=> m1_subset_1(k3_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_138])])).

fof(f6838,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK3,sK3),k3_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f3977,f4123,f154])).

fof(f11049,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK3,sK3)) = k3_lattices(sK0,sK3,sK3)
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11048,f3997])).

fof(f11048,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK3,sK3)) = k1_lattices(sK0,sK3,sK3)
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11047,f7035])).

fof(f7035,plain,
    ( k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3) = sK3
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f6827,f7015])).

fof(f7015,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3) = sK3
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f7014,f6869])).

fof(f6869,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3) = k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f241,f4123,f155])).

fof(f7014,plain,
    ( k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = sK3
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f6841,f4046])).

fof(f4046,plain,
    ( k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = sK3
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_46
    | ~ spl13_50 ),
    inference(backward_demodulation,[],[f4045,f1003])).

fof(f1003,plain,
    ( k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,sK1)) = sK3
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_46 ),
    inference(unit_resulting_resolution,[],[f171,f192,f345,f241,f227,f136])).

fof(f4045,plain,
    ( k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK3,sK1)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_50 ),
    inference(forward_demodulation,[],[f3987,f1399])).

fof(f1399,plain,
    ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK3,sK1)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_50 ),
    inference(forward_demodulation,[],[f1372,f362])).

fof(f362,plain,
    ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3)
    | ~ spl13_50 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl13_50
  <=> k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_50])])).

fof(f1372,plain,
    ( k3_lattices(sK0,sK1,sK3) = k3_lattices(sK0,sK3,sK1)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f227,f241,f153])).

fof(f3987,plain,
    ( k3_lattices(sK0,sK3,sK1) = k1_lattices(sK0,sK3,sK1)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f241,f227,f156])).

fof(f6841,plain,
    ( k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f241,f4123,f154])).

fof(f6827,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3)
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f241,f4123,f154])).

fof(f11047,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK3,sK3)) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3),k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11046,f6824])).

fof(f6824,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK3,sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK3,sK3))
    | ~ spl13_1
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f3977,f4123,f154])).

fof(f11046,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3),k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK3,sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f10126,f3997])).

fof(f10126,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3),k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k1_lattices(sK0,sK3,sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f4123,f241,f241,f140])).

fof(f11301,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK1),k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_50
    | ~ spl13_136 ),
    inference(forward_demodulation,[],[f10101,f4023])).

fof(f4023,plain,
    ( k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK3)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_50 ),
    inference(forward_demodulation,[],[f3995,f362])).

fof(f3995,plain,
    ( k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK1,sK3)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f227,f241,f156])).

fof(f10101,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK1),k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),k1_lattices(sK0,sK1,sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_136 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f3977,f227,f241,f140])).

fof(f11308,plain,
    ( k3_lattices(sK0,sK2,sK3) = k1_lattices(sK0,k4_lattices(sK0,sK1,k3_lattices(sK0,sK2,sK3)),sK3)
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_134
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11307,f6218])).

fof(f6218,plain,
    ( k4_lattices(sK0,sK1,k3_lattices(sK0,sK2,sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK1)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_134 ),
    inference(forward_demodulation,[],[f6037,f6073])).

fof(f6073,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK1) = k4_lattices(sK0,sK1,k3_lattices(sK0,sK2,sK3))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_134 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f227,f3970,f155])).

fof(f6037,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK1) = k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK1)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_134 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f227,f3970,f154])).

fof(f11307,plain,
    ( k3_lattices(sK0,sK2,sK3) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK1),sK3)
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_134
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11306,f6214])).

fof(f6214,plain,
    ( k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK3) = sK3
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_134 ),
    inference(forward_demodulation,[],[f6039,f6200])).

fof(f6200,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK3) = sK3
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_134 ),
    inference(backward_demodulation,[],[f6199,f6075])).

fof(f6075,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK3) = k4_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_134 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f241,f3970,f155])).

fof(f6199,plain,
    ( k4_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3)) = sK3
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_134 ),
    inference(forward_demodulation,[],[f6051,f4033])).

fof(f4033,plain,
    ( k2_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3)) = sK3
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_46 ),
    inference(backward_demodulation,[],[f4032,f1012])).

fof(f1012,plain,
    ( k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,sK2)) = sK3
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_46 ),
    inference(unit_resulting_resolution,[],[f171,f192,f345,f241,f234,f136])).

fof(f4032,plain,
    ( k3_lattices(sK0,sK2,sK3) = k1_lattices(sK0,sK3,sK2)
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(forward_demodulation,[],[f3992,f1373])).

fof(f3992,plain,
    ( k3_lattices(sK0,sK3,sK2) = k1_lattices(sK0,sK3,sK2)
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f241,f234,f156])).

fof(f6051,plain,
    ( k4_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_134 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f241,f3970,f154])).

fof(f6039,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK3) = k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK3)
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_134 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f241,f3970,f154])).

fof(f11306,plain,
    ( k3_lattices(sK0,sK2,sK3) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK1),k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_134
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11305,f11178])).

fof(f11178,plain,
    ( k3_lattices(sK0,sK2,sK3) = k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_134
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f11173,f7022])).

fof(f7022,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_134
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f6837,f6865])).

fof(f6865,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK3),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_134
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f3970,f4123,f155])).

fof(f6837,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK2,sK3),k3_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_134
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f3970,f4123,f154])).

fof(f11173,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)) = k3_lattices(sK0,sK2,sK3)
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_134
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11172,f3996])).

fof(f11172,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,sK2,sK3)
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_134
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11171,f7037])).

fof(f7037,plain,
    ( k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK2) = sK2
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f6826,f7017])).

fof(f7017,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK2) = sK2
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f7016,f6868])).

fof(f6868,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK2) = k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f234,f4123,f155])).

fof(f7016,plain,
    ( k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = sK2
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f6840,f4049])).

fof(f4049,plain,
    ( k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = sK2
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_46 ),
    inference(backward_demodulation,[],[f4048,f1002])).

fof(f1002,plain,
    ( k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK1)) = sK2
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_46 ),
    inference(unit_resulting_resolution,[],[f171,f192,f345,f234,f227,f136])).

fof(f4048,plain,
    ( k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK2,sK1)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(forward_demodulation,[],[f3986,f1361])).

fof(f1361,plain,
    ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f227,f234,f153])).

fof(f3986,plain,
    ( k3_lattices(sK0,sK2,sK1) = k1_lattices(sK0,sK2,sK1)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f234,f227,f156])).

fof(f6840,plain,
    ( k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f234,f4123,f154])).

fof(f6826,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK2) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK2)
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f234,f4123,f154])).

fof(f11171,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK2),sK3)
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_134
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11170,f7035])).

fof(f11170,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK2),k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_134
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11169,f6823])).

fof(f6823,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3))
    | ~ spl13_1
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_134
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f3970,f4123,f154])).

fof(f11169,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK2),k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f10112,f3996])).

fof(f10112,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK2),k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k1_lattices(sK0,sK2,sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f4123,f234,f241,f140])).

fof(f11305,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK1),k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_50
    | ~ spl13_134 ),
    inference(forward_demodulation,[],[f10100,f4023])).

fof(f10100,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK1),k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),k1_lattices(sK0,sK1,sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_134 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f3970,f227,f241,f140])).

fof(f11799,plain,
    ( k1_lattices(sK0,sK3,sK3) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f11628,f11001])).

fof(f11001,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK3,sK3),k4_lattices(sK0,sK3,sK3)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46 ),
    inference(forward_demodulation,[],[f11000,f1945])).

fof(f1945,plain,
    ( k4_lattices(sK0,sK3,sK3) = k2_lattices(sK0,sK3,sK3)
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f241,f241,f154])).

fof(f11000,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK3),k2_lattices(sK0,sK3,sK3)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_46 ),
    inference(forward_demodulation,[],[f10999,f4020])).

fof(f10999,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK3),k2_lattices(sK0,sK3,sK3)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK3,sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(forward_demodulation,[],[f10132,f3997])).

fof(f10132,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK3),k2_lattices(sK0,sK3,sK3)) = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_20 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f241,f241,f241,f140])).

fof(f11628,plain,
    ( k4_lattices(sK0,sK3,sK3) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f11625,f1945])).

fof(f11625,plain,
    ( k2_lattices(sK0,sK3,sK3) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f11622,f4840])).

fof(f4840,plain,
    ( k2_lattices(sK0,sK3,k3_lattices(sK0,sK3,k4_lattices(sK0,sK3,sK3))) = sK3
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_94
    | ~ spl13_126 ),
    inference(backward_demodulation,[],[f4787,f1999])).

fof(f1999,plain,
    ( k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,k4_lattices(sK0,sK3,sK3))) = sK3
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_94 ),
    inference(backward_demodulation,[],[f1945,f1626])).

fof(f1626,plain,
    ( k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,k2_lattices(sK0,sK3,sK3))) = sK3
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_46
    | ~ spl13_94 ),
    inference(unit_resulting_resolution,[],[f171,f192,f345,f241,f597,f136])).

fof(f597,plain,
    ( m1_subset_1(k2_lattices(sK0,sK3,sK3),u1_struct_0(sK0))
    | ~ spl13_94 ),
    inference(avatar_component_clause,[],[f596])).

fof(f596,plain,
    ( spl13_94
  <=> m1_subset_1(k2_lattices(sK0,sK3,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_94])])).

fof(f4787,plain,
    ( k3_lattices(sK0,sK3,k4_lattices(sK0,sK3,sK3)) = k1_lattices(sK0,sK3,k4_lattices(sK0,sK3,sK3))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_126 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f241,f3489,f156])).

fof(f3489,plain,
    ( m1_subset_1(k4_lattices(sK0,sK3,sK3),u1_struct_0(sK0))
    | ~ spl13_126 ),
    inference(avatar_component_clause,[],[f3488])).

fof(f3488,plain,
    ( spl13_126
  <=> m1_subset_1(k4_lattices(sK0,sK3,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_126])])).

fof(f11622,plain,
    ( k3_lattices(sK0,sK3,k4_lattices(sK0,sK3,sK3)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f11621,f4787])).

fof(f11621,plain,
    ( k1_lattices(sK0,sK3,k4_lattices(sK0,sK3,sK3)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11620,f4033])).

fof(f11620,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3)),k4_lattices(sK0,sK3,sK3)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11619,f1945])).

fof(f11619,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3)),k2_lattices(sK0,sK3,sK3)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11618,f6281])).

fof(f6281,plain,
    ( k2_lattices(sK0,sK3,k3_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3))) = sK3
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_46
    | ~ spl13_134 ),
    inference(forward_demodulation,[],[f5955,f6099])).

fof(f6099,plain,
    ( k3_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_134 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f241,f3970,f156])).

fof(f5955,plain,
    ( k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3))) = sK3
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_46
    | ~ spl13_134 ),
    inference(unit_resulting_resolution,[],[f171,f192,f345,f241,f3970,f136])).

fof(f11618,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3)),k2_lattices(sK0,sK3,sK3)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11617,f6237])).

fof(f6237,plain,
    ( k3_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK3)
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_134 ),
    inference(backward_demodulation,[],[f6027,f6087])).

fof(f6087,plain,
    ( k3_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK3) = k1_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK3)
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_134 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f241,f3970,f156])).

fof(f6027,plain,
    ( k3_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK3) = k3_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_134 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f241,f3970,f153])).

fof(f11617,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK3)),k2_lattices(sK0,sK3,sK3)) = k2_lattices(sK0,sK3,k1_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f10090,f11309])).

fof(f10090,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,k3_lattices(sK0,sK3,sK3)),k2_lattices(sK0,sK3,sK3)) = k2_lattices(sK0,sK3,k1_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_136 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f241,f3977,f241,f140])).

fof(f12162,plain,
    ( k3_lattices(sK0,sK3,sK2) = k1_lattices(sK0,sK3,sK2)
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f12130,f4557])).

fof(f4557,plain,
    ( k3_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK3))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_124 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f241,f3482,f156])).

fof(f3482,plain,
    ( m1_subset_1(k4_lattices(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl13_124 ),
    inference(avatar_component_clause,[],[f3481])).

fof(f3481,plain,
    ( spl13_124
  <=> m1_subset_1(k4_lattices(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_124])])).

fof(f12130,plain,
    ( k4_lattices(sK0,sK2,sK3) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f11922,f1944])).

fof(f1944,plain,
    ( k4_lattices(sK0,sK2,sK3) = k2_lattices(sK0,sK2,sK3)
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f234,f241,f154])).

fof(f11922,plain,
    ( k2_lattices(sK0,sK2,sK3) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f11918,f4022])).

fof(f4022,plain,
    ( k2_lattices(sK0,sK2,k3_lattices(sK0,sK2,sK3)) = sK2
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_46 ),
    inference(backward_demodulation,[],[f3996,f1020])).

fof(f1020,plain,
    ( k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK3)) = sK2
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_46 ),
    inference(unit_resulting_resolution,[],[f171,f192,f345,f234,f241,f136])).

fof(f18952,plain,
    ( k1_lattices(sK0,sK3,sK2) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f18951,f11625])).

fof(f18951,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK3),sK2) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f18950,f15181])).

fof(f15181,plain,
    ( k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f15098,f1361])).

fof(f15098,plain,
    ( k2_lattices(sK0,sK3,k3_lattices(sK0,sK2,sK1)) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f14986,f14959])).

fof(f14959,plain,
    ( k2_lattices(sK0,sK3,k3_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK1))) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14939,f12617])).

fof(f12617,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f12616,f7016])).

fof(f12616,plain,
    ( k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f12526,f12153])).

fof(f12153,plain,
    ( k4_lattices(sK0,sK3,sK2) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f12130,f3507])).

fof(f3507,plain,
    ( k4_lattices(sK0,sK2,sK3) = k4_lattices(sK0,sK3,sK2)
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f234,f241,f155])).

fof(f12526,plain,
    ( k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK3,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f12376,f11596])).

fof(f11596,plain,
    ( k4_lattices(sK0,k4_lattices(sK0,sK2,sK2),k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,k4_lattices(sK0,sK2,sK2)),k4_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK2)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_120
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11595,f4430])).

fof(f4430,plain,
    ( k4_lattices(sK0,sK1,k4_lattices(sK0,sK2,sK2)) = k2_lattices(sK0,k4_lattices(sK0,sK2,sK2),sK1)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_86
    | ~ spl13_120 ),
    inference(backward_demodulation,[],[f4345,f3167])).

fof(f3167,plain,
    ( k4_lattices(sK0,k4_lattices(sK0,sK2,sK2),sK1) = k2_lattices(sK0,k4_lattices(sK0,sK2,sK2),sK1)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_86 ),
    inference(forward_demodulation,[],[f1912,f1931])).

fof(f1931,plain,
    ( k4_lattices(sK0,sK2,sK2) = k2_lattices(sK0,sK2,sK2)
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f234,f234,f154])).

fof(f1912,plain,
    ( k4_lattices(sK0,k2_lattices(sK0,sK2,sK2),sK1) = k2_lattices(sK0,k2_lattices(sK0,sK2,sK2),sK1)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_86 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f553,f227,f154])).

fof(f553,plain,
    ( m1_subset_1(k2_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl13_86 ),
    inference(avatar_component_clause,[],[f552])).

fof(f552,plain,
    ( spl13_86
  <=> m1_subset_1(k2_lattices(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_86])])).

fof(f4345,plain,
    ( k4_lattices(sK0,k4_lattices(sK0,sK2,sK2),sK1) = k4_lattices(sK0,sK1,k4_lattices(sK0,sK2,sK2))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_120 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f227,f3468,f155])).

fof(f3468,plain,
    ( m1_subset_1(k4_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl13_120 ),
    inference(avatar_component_clause,[],[f3467])).

fof(f3467,plain,
    ( spl13_120
  <=> m1_subset_1(k4_lattices(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_120])])).

fof(f11595,plain,
    ( k4_lattices(sK0,k4_lattices(sK0,sK2,sK2),k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK2,sK2),sK1),k4_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK2)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_120
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11594,f4426])).

fof(f4426,plain,
    ( k4_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK2)) = k2_lattices(sK0,k4_lattices(sK0,sK2,sK2),sK3)
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_86
    | ~ spl13_120 ),
    inference(backward_demodulation,[],[f4347,f2601])).

fof(f2601,plain,
    ( k4_lattices(sK0,k4_lattices(sK0,sK2,sK2),sK3) = k2_lattices(sK0,k4_lattices(sK0,sK2,sK2),sK3)
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_86 ),
    inference(backward_demodulation,[],[f1931,f1938])).

fof(f1938,plain,
    ( k4_lattices(sK0,k2_lattices(sK0,sK2,sK2),sK3) = k2_lattices(sK0,k2_lattices(sK0,sK2,sK2),sK3)
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_86 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f553,f241,f154])).

fof(f4347,plain,
    ( k4_lattices(sK0,k4_lattices(sK0,sK2,sK2),sK3) = k4_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK2))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_120 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f241,f3468,f155])).

fof(f11594,plain,
    ( k4_lattices(sK0,k4_lattices(sK0,sK2,sK2),k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK2,sK2),sK1),k2_lattices(sK0,k4_lattices(sK0,sK2,sK2),sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_50
    | ~ spl13_120
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11593,f6831])).

fof(f6831,plain,
    ( k4_lattices(sK0,k4_lattices(sK0,sK2,sK2),k3_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,k4_lattices(sK0,sK2,sK2),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_120
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f3468,f4123,f154])).

fof(f11593,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK2,sK2),sK1),k2_lattices(sK0,k4_lattices(sK0,sK2,sK2),sK3)) = k2_lattices(sK0,k4_lattices(sK0,sK2,sK2),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_50
    | ~ spl13_120 ),
    inference(forward_demodulation,[],[f10094,f4023])).

fof(f10094,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK2,sK2),sK1),k2_lattices(sK0,k4_lattices(sK0,sK2,sK2),sK3)) = k2_lattices(sK0,k4_lattices(sK0,sK2,sK2),k1_lattices(sK0,sK1,sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_120 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f3468,f227,f241,f140])).

fof(f12376,plain,
    ( k4_lattices(sK0,sK2,sK2) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f12372,f1931])).

fof(f12372,plain,
    ( k2_lattices(sK0,sK2,sK2) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f12370,f4401])).

fof(f4401,plain,
    ( k2_lattices(sK0,sK2,k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK2))) = sK2
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_86
    | ~ spl13_120 ),
    inference(backward_demodulation,[],[f4358,f2586])).

fof(f2586,plain,
    ( k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK2))) = sK2
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_86 ),
    inference(backward_demodulation,[],[f1931,f993])).

fof(f993,plain,
    ( k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,k2_lattices(sK0,sK2,sK2))) = sK2
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_46
    | ~ spl13_86 ),
    inference(unit_resulting_resolution,[],[f171,f192,f345,f234,f553,f136])).

fof(f4358,plain,
    ( k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK2)) = k1_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK2))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_120 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f234,f3468,f156])).

fof(f12370,plain,
    ( k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK2)) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f12282,f4415])).

fof(f4415,plain,
    ( k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK2),sK2)
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_86
    | ~ spl13_120 ),
    inference(forward_demodulation,[],[f4352,f2598])).

fof(f2598,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK2,sK2),sK2) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK2))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_86 ),
    inference(backward_demodulation,[],[f1931,f1358])).

fof(f1358,plain,
    ( k3_lattices(sK0,k2_lattices(sK0,sK2,sK2),sK2) = k3_lattices(sK0,sK2,k2_lattices(sK0,sK2,sK2))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_86 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f553,f234,f153])).

fof(f4352,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK2,sK2),sK2) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK2),sK2)
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_120 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f234,f3468,f156])).

fof(f12282,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK2,sK2),sK2) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f12130,f11116])).

fof(f11116,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK2,sK2),k4_lattices(sK0,sK2,sK3)) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46 ),
    inference(forward_demodulation,[],[f11115,f1931])).

fof(f11115,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK2,sK2),k4_lattices(sK0,sK2,sK3)) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46 ),
    inference(forward_demodulation,[],[f11114,f1944])).

fof(f11114,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK2,sK2),k2_lattices(sK0,sK2,sK3)) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_46 ),
    inference(forward_demodulation,[],[f11113,f4022])).

fof(f11113,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK2,sK2),k2_lattices(sK0,sK2,sK3)) = k2_lattices(sK0,sK2,k3_lattices(sK0,sK2,sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(forward_demodulation,[],[f10117,f3996])).

fof(f10117,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK2,sK2),k2_lattices(sK0,sK2,sK3)) = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f234,f234,f241,f140])).

fof(f14939,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK1)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_126
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f14923,f14375])).

fof(f14375,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK1)),sK2) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK1)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_126
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14374,f4070])).

fof(f4070,plain,
    ( k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK1)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK1))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_96 ),
    inference(backward_demodulation,[],[f3985,f3895])).

fof(f3895,plain,
    ( k4_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK1)) = k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK1))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_96 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f241,f831,f154])).

fof(f831,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl13_96 ),
    inference(avatar_component_clause,[],[f830])).

fof(f830,plain,
    ( spl13_96
  <=> m1_subset_1(k1_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_96])])).

fof(f3985,plain,
    ( k3_lattices(sK0,sK1,sK1) = k1_lattices(sK0,sK1,sK1)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f227,f227,f156])).

fof(f14374,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK1)),sK2) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK1)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_126
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14373,f12154])).

fof(f12154,plain,
    ( k2_lattices(sK0,sK3,sK2) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f12130,f3521])).

fof(f3521,plain,
    ( k4_lattices(sK0,sK2,sK3) = k2_lattices(sK0,sK3,sK2)
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(backward_demodulation,[],[f3507,f1932])).

fof(f1932,plain,
    ( k4_lattices(sK0,sK3,sK2) = k2_lattices(sK0,sK3,sK2)
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f241,f234,f154])).

fof(f14373,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK1)),k2_lattices(sK0,sK3,sK2)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK1)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_96
    | ~ spl13_130 ),
    inference(forward_demodulation,[],[f9838,f4095])).

fof(f4095,plain,
    ( k3_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK1)) = k1_lattices(sK0,k3_lattices(sK0,sK1,sK1),sK2)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_96 ),
    inference(backward_demodulation,[],[f3985,f4039])).

fof(f4039,plain,
    ( k3_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK1)) = k1_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK2)
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_96 ),
    inference(forward_demodulation,[],[f3989,f3884])).

fof(f3884,plain,
    ( k3_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK2) = k3_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK1))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_96 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f234,f831,f153])).

fof(f3989,plain,
    ( k3_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK2) = k1_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK2)
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_96 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f831,f234,f156])).

fof(f9838,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK1)),k2_lattices(sK0,sK3,sK2)) = k2_lattices(sK0,sK3,k1_lattices(sK0,k3_lattices(sK0,sK1,sK1),sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_130 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f241,f3956,f234,f140])).

fof(f3956,plain,
    ( m1_subset_1(k3_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl13_130 ),
    inference(avatar_component_clause,[],[f3955])).

fof(f3955,plain,
    ( spl13_130
  <=> m1_subset_1(k3_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_130])])).

fof(f14923,plain,
    ( k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK1))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14922,f13040])).

fof(f13040,plain,
    ( k4_lattices(sK0,sK1,sK2) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f12086,f355])).

fof(f12086,plain,
    ( k4_lattices(sK0,sK1,sK3) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f11918,f11142])).

fof(f14922,plain,
    ( k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK1)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_48
    | ~ spl13_96 ),
    inference(forward_demodulation,[],[f14921,f3640])).

fof(f3640,plain,
    ( k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK3,sK1)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_48 ),
    inference(backward_demodulation,[],[f3638,f1919])).

fof(f1919,plain,
    ( k4_lattices(sK0,sK3,sK1) = k2_lattices(sK0,sK3,sK1)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f241,f227,f154])).

fof(f3638,plain,
    ( k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK3,sK1)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_48 ),
    inference(forward_demodulation,[],[f3506,f355])).

fof(f3506,plain,
    ( k4_lattices(sK0,sK1,sK3) = k4_lattices(sK0,sK3,sK1)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f227,f241,f155])).

fof(f14921,plain,
    ( k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK1))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_96 ),
    inference(forward_demodulation,[],[f14920,f4070])).

fof(f14920,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK1)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK1))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(forward_demodulation,[],[f9712,f3985])).

fof(f9712,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK1)) = k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK1))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f241,f227,f227,f140])).

fof(f14986,plain,
    ( k3_lattices(sK0,sK1,sK1) = sK1
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_128
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f14985,f3985])).

fof(f14985,plain,
    ( k1_lattices(sK0,sK1,sK1) = sK1
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_128
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14984,f13328])).

fof(f13328,plain,
    ( k2_lattices(sK0,sK1,sK1) = sK1
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_128
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f13324,f5198])).

fof(f5198,plain,
    ( k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK2))) = sK1
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_90
    | ~ spl13_128 ),
    inference(backward_demodulation,[],[f5115,f2260])).

fof(f2260,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK2))) = sK1
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_90 ),
    inference(backward_demodulation,[],[f2241,f1174])).

fof(f1174,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,k2_lattices(sK0,sK1,sK3))) = sK1
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_46
    | ~ spl13_90 ),
    inference(unit_resulting_resolution,[],[f171,f192,f345,f227,f583,f136])).

fof(f583,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl13_90 ),
    inference(avatar_component_clause,[],[f582])).

fof(f582,plain,
    ( spl13_90
  <=> m1_subset_1(k2_lattices(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_90])])).

fof(f5115,plain,
    ( k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_128 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f227,f3496,f156])).

fof(f3496,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl13_128 ),
    inference(avatar_component_clause,[],[f3495])).

fof(f3495,plain,
    ( spl13_128
  <=> m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_128])])).

fof(f13324,plain,
    ( k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK2)) = sK1
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_128
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f13322,f4025])).

fof(f4025,plain,
    ( k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2)) = sK1
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_46
    | ~ spl13_50 ),
    inference(backward_demodulation,[],[f4023,f1019])).

fof(f1019,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK3)) = sK1
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_46 ),
    inference(unit_resulting_resolution,[],[f171,f192,f345,f227,f241,f136])).

fof(f13322,plain,
    ( k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_128
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f13314,f13294])).

fof(f13294,plain,
    ( k3_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,sK1,k3_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_128
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f13293,f5115])).

fof(f13293,plain,
    ( k1_lattices(sK0,sK1,k4_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,sK1,k3_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f13292,f4025])).

fof(f13292,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2)),k4_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,sK1,k3_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_48
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f13291,f2241])).

fof(f13291,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2)),k2_lattices(sK0,sK1,sK3)) = k2_lattices(sK0,sK1,k3_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f10046,f7059])).

fof(f7059,plain,
    ( k3_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3)
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f6813,f6883])).

fof(f6883,plain,
    ( k3_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3) = k1_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3)
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f241,f4123,f156])).

fof(f6813,plain,
    ( k3_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3) = k3_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f241,f4123,f153])).

fof(f10046,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2)),k2_lattices(sK0,sK1,sK3)) = k2_lattices(sK0,sK1,k1_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f227,f4123,f241,f140])).

fof(f13314,plain,
    ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f13313,f7059])).

fof(f13313,plain,
    ( k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3)
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f13312,f11580])).

fof(f11580,plain,
    ( k3_lattices(sK0,sK1,sK2) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f11577,f6835])).

fof(f6835,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f4123,f4123,f154])).

fof(f11577,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,sK2)
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11576,f4023])).

fof(f11576,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,sK1,sK3)
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11575,f7039])).

fof(f7039,plain,
    ( k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1) = sK1
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f6825,f7019])).

fof(f7019,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1) = sK1
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f7018,f6867])).

fof(f6867,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1) = k4_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f227,f4123,f155])).

fof(f7018,plain,
    ( k4_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2)) = sK1
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f6839,f4025])).

fof(f6839,plain,
    ( k4_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f227,f4123,f154])).

fof(f6825,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f227,f4123,f154])).

fof(f11575,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1),sK3)
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11574,f7035])).

fof(f11574,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1),k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_50
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11573,f6835])).

fof(f11573,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1),k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_50
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f10098,f4023])).

fof(f10098,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1),k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k1_lattices(sK0,sK1,sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f4123,f227,f241,f140])).

fof(f13312,plain,
    ( k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK2)),sK3)
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f13311,f7035])).

fof(f13311,plain,
    ( k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK2)),k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_46
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f13310,f7126])).

fof(f7126,plain,
    ( k3_lattices(sK0,sK1,sK2) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)))
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_46
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f6715,f7059])).

fof(f6715,plain,
    ( k3_lattices(sK0,sK1,sK2) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k1_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3))
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_46
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f192,f345,f241,f4123,f136])).

fof(f13310,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK2)),k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f10042,f7059])).

fof(f10042,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK2)),k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k1_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f4123,f4123,f241,f140])).

fof(f14984,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK1,sK1),k2_lattices(sK0,sK1,sK1)) = sK1
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_46 ),
    inference(forward_demodulation,[],[f14983,f4052])).

fof(f4052,plain,
    ( k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK1)) = sK1
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_46 ),
    inference(backward_demodulation,[],[f3985,f1001])).

fof(f1001,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) = sK1
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_46 ),
    inference(unit_resulting_resolution,[],[f171,f192,f345,f227,f227,f136])).

fof(f14983,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK1,sK1),k2_lattices(sK0,sK1,sK1)) = k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK1))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(forward_demodulation,[],[f9710,f3985])).

fof(f9710,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK1,sK1),k2_lattices(sK0,sK1,sK1)) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f227,f227,f227,f140])).

fof(f18950,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK3),k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f8956,f13316])).

fof(f13316,plain,
    ( k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f13314,f6897])).

fof(f6897,plain,
    ( k3_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f241,f4123,f156])).

fof(f8956,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK3),k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))) = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f241,f241,f4123,f140])).

fof(f18927,plain,
    ( spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(avatar_contradiction_clause,[],[f18926])).

fof(f18926,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f18925,f220])).

fof(f18925,plain,
    ( sK2 = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f18924,f12577])).

fof(f12577,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0))),sK2) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f12503,f12369])).

fof(f12369,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0))),sK2) = k1_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0))))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f12276,f12258])).

fof(f12258,plain,
    ( k1_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0)))) = k2_lattices(sK0,sK2,k3_lattices(sK0,sK3,sK9(u1_struct_0(sK0))))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f12130,f10384])).

fof(f10384,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0)))) = k2_lattices(sK0,sK2,k3_lattices(sK0,sK3,sK9(u1_struct_0(sK0))))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44 ),
    inference(forward_demodulation,[],[f10383,f1944])).

fof(f10383,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0)))) = k2_lattices(sK0,sK2,k3_lattices(sK0,sK3,sK9(u1_struct_0(sK0))))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44 ),
    inference(forward_demodulation,[],[f10382,f1957])).

fof(f1957,plain,
    ( k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0))) = k2_lattices(sK0,sK2,sK9(u1_struct_0(sK0)))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f234,f145,f154])).

fof(f145,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(cnf_transformation,[],[f106])).

fof(f106,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f29,f105])).

fof(f105,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK9(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',existence_m1_subset_1)).

fof(f10382,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK2,sK3),k2_lattices(sK0,sK2,sK9(u1_struct_0(sK0)))) = k2_lattices(sK0,sK2,k3_lattices(sK0,sK3,sK9(u1_struct_0(sK0))))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(forward_demodulation,[],[f10327,f4002])).

fof(f4002,plain,
    ( k3_lattices(sK0,sK3,sK9(u1_struct_0(sK0))) = k1_lattices(sK0,sK3,sK9(u1_struct_0(sK0)))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f241,f145,f156])).

fof(f10327,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK2,sK3),k2_lattices(sK0,sK2,sK9(u1_struct_0(sK0)))) = k2_lattices(sK0,sK2,k1_lattices(sK0,sK3,sK9(u1_struct_0(sK0))))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f234,f241,f145,f140])).

fof(f12276,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0))),sK2) = k2_lattices(sK0,sK2,k3_lattices(sK0,sK3,sK9(u1_struct_0(sK0))))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f12130,f10957])).

fof(f10957,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0))),k4_lattices(sK0,sK2,sK3)) = k2_lattices(sK0,sK2,k3_lattices(sK0,sK3,sK9(u1_struct_0(sK0))))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44 ),
    inference(forward_demodulation,[],[f10956,f1957])).

fof(f10956,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK2,sK9(u1_struct_0(sK0))),k4_lattices(sK0,sK2,sK3)) = k2_lattices(sK0,sK2,k3_lattices(sK0,sK3,sK9(u1_struct_0(sK0))))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44 ),
    inference(forward_demodulation,[],[f10955,f1944])).

fof(f10955,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK2,sK9(u1_struct_0(sK0))),k2_lattices(sK0,sK2,sK3)) = k2_lattices(sK0,sK2,k3_lattices(sK0,sK3,sK9(u1_struct_0(sK0))))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(forward_demodulation,[],[f10145,f4016])).

fof(f4016,plain,
    ( k3_lattices(sK0,sK3,sK9(u1_struct_0(sK0))) = k1_lattices(sK0,sK9(u1_struct_0(sK0)),sK3)
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(forward_demodulation,[],[f3998,f1385])).

fof(f1385,plain,
    ( k3_lattices(sK0,sK3,sK9(u1_struct_0(sK0))) = k3_lattices(sK0,sK9(u1_struct_0(sK0)),sK3)
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f241,f145,f153])).

fof(f3998,plain,
    ( k3_lattices(sK0,sK9(u1_struct_0(sK0)),sK3) = k1_lattices(sK0,sK9(u1_struct_0(sK0)),sK3)
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f145,f241,f156])).

fof(f10145,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK2,sK9(u1_struct_0(sK0))),k2_lattices(sK0,sK2,sK3)) = k2_lattices(sK0,sK2,k1_lattices(sK0,sK9(u1_struct_0(sK0)),sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f234,f145,f241,f140])).

fof(f12503,plain,
    ( k1_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0)))) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f12376,f10428])).

fof(f10428,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK2,sK2),k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0)))) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46 ),
    inference(forward_demodulation,[],[f10427,f1931])).

fof(f10427,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK2,sK2),k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0)))) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46 ),
    inference(forward_demodulation,[],[f10426,f1957])).

fof(f10426,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK2,sK2),k2_lattices(sK0,sK2,sK9(u1_struct_0(sK0)))) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_46 ),
    inference(forward_demodulation,[],[f10425,f4009])).

fof(f4009,plain,
    ( k2_lattices(sK0,sK2,k3_lattices(sK0,sK2,sK9(u1_struct_0(sK0)))) = sK2
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_46 ),
    inference(backward_demodulation,[],[f4001,f1029])).

fof(f1029,plain,
    ( k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK9(u1_struct_0(sK0)))) = sK2
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_46 ),
    inference(unit_resulting_resolution,[],[f171,f192,f345,f234,f145,f136])).

fof(f4001,plain,
    ( k3_lattices(sK0,sK2,sK9(u1_struct_0(sK0))) = k1_lattices(sK0,sK2,sK9(u1_struct_0(sK0)))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f234,f145,f156])).

fof(f10425,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK2,sK2),k2_lattices(sK0,sK2,sK9(u1_struct_0(sK0)))) = k2_lattices(sK0,sK2,k3_lattices(sK0,sK2,sK9(u1_struct_0(sK0))))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(forward_demodulation,[],[f10313,f4001])).

fof(f10313,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK2,sK2),k2_lattices(sK0,sK2,sK9(u1_struct_0(sK0)))) = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK9(u1_struct_0(sK0))))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f234,f234,f145,f140])).

fof(f18924,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0))),sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f18923,f16575])).

fof(f16575,plain,
    ( k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0))) = k2_lattices(sK0,sK3,sK9(u1_struct_0(sK0)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f16574,f1958])).

fof(f1958,plain,
    ( k4_lattices(sK0,sK3,sK9(u1_struct_0(sK0))) = k2_lattices(sK0,sK3,sK9(u1_struct_0(sK0)))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f241,f145,f154])).

fof(f16574,plain,
    ( k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0))) = k4_lattices(sK0,sK3,sK9(u1_struct_0(sK0)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f16573,f13039])).

fof(f13039,plain,
    ( k4_lattices(sK0,sK3,sK9(u1_struct_0(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0))),k4_lattices(sK0,sK3,sK9(u1_struct_0(sK0))))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f12085,f3512])).

fof(f3512,plain,
    ( k4_lattices(sK0,sK3,sK9(u1_struct_0(sK0))) = k4_lattices(sK0,sK9(u1_struct_0(sK0)),sK3)
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f241,f145,f155])).

fof(f12085,plain,
    ( k4_lattices(sK0,sK9(u1_struct_0(sK0)),sK3) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0))),k4_lattices(sK0,sK3,sK9(u1_struct_0(sK0))))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f11918,f11085])).

fof(f11085,plain,
    ( k4_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0))),k4_lattices(sK0,sK3,sK9(u1_struct_0(sK0))))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_134 ),
    inference(forward_demodulation,[],[f11084,f3517])).

fof(f3517,plain,
    ( k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0))) = k2_lattices(sK0,sK9(u1_struct_0(sK0)),sK2)
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(backward_demodulation,[],[f3511,f1933])).

fof(f1933,plain,
    ( k4_lattices(sK0,sK9(u1_struct_0(sK0)),sK2) = k2_lattices(sK0,sK9(u1_struct_0(sK0)),sK2)
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f145,f234,f154])).

fof(f3511,plain,
    ( k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0))) = k4_lattices(sK0,sK9(u1_struct_0(sK0)),sK2)
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f234,f145,f155])).

fof(f11084,plain,
    ( k4_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK9(u1_struct_0(sK0)),sK2),k4_lattices(sK0,sK3,sK9(u1_struct_0(sK0))))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_134 ),
    inference(forward_demodulation,[],[f11083,f3515])).

fof(f3515,plain,
    ( k4_lattices(sK0,sK3,sK9(u1_struct_0(sK0))) = k2_lattices(sK0,sK9(u1_struct_0(sK0)),sK3)
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(backward_demodulation,[],[f3512,f1946])).

fof(f1946,plain,
    ( k4_lattices(sK0,sK9(u1_struct_0(sK0)),sK3) = k2_lattices(sK0,sK9(u1_struct_0(sK0)),sK3)
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f145,f241,f154])).

fof(f11083,plain,
    ( k4_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK9(u1_struct_0(sK0)),sK2),k2_lattices(sK0,sK9(u1_struct_0(sK0)),sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_134 ),
    inference(forward_demodulation,[],[f11082,f6052])).

fof(f6052,plain,
    ( k4_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK2,sK3)) = k2_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK2,sK3))
    | ~ spl13_1
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_134 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f145,f3970,f154])).

fof(f11082,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK9(u1_struct_0(sK0)),sK2),k2_lattices(sK0,sK9(u1_struct_0(sK0)),sK3)) = k2_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK2,sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(forward_demodulation,[],[f10119,f3996])).

fof(f10119,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK9(u1_struct_0(sK0)),sK2),k2_lattices(sK0,sK9(u1_struct_0(sK0)),sK3)) = k2_lattices(sK0,sK9(u1_struct_0(sK0)),k1_lattices(sK0,sK2,sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f145,f234,f241,f140])).

fof(f16573,plain,
    ( k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0))),k4_lattices(sK0,sK3,sK9(u1_struct_0(sK0))))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f16572,f3515])).

fof(f16572,plain,
    ( k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0))),k2_lattices(sK0,sK9(u1_struct_0(sK0)),sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f16571,f3517])).

fof(f16571,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK9(u1_struct_0(sK0)),sK2),k2_lattices(sK0,sK9(u1_struct_0(sK0)),sK3)) = k2_lattices(sK0,sK9(u1_struct_0(sK0)),sK2)
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f16570,f16358])).

fof(f16358,plain,
    ( k1_lattices(sK0,sK2,sK3) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f16357,f11625])).

fof(f16357,plain,
    ( k1_lattices(sK0,sK2,k2_lattices(sK0,sK3,sK3)) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f16356,f15181])).

fof(f16356,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)),k2_lattices(sK0,sK3,sK3)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f16355,f13313])).

fof(f16355,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)),k2_lattices(sK0,sK3,sK3)) = k2_lattices(sK0,sK3,k1_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f9460,f12907])).

fof(f12907,plain,
    ( k3_lattices(sK0,sK3,sK3) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f11952,f11799])).

fof(f11952,plain,
    ( k3_lattices(sK0,sK3,sK3) = k1_lattices(sK0,sK3,sK3)
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f11918,f6096])).

fof(f6096,plain,
    ( k3_lattices(sK0,k3_lattices(sK0,sK2,sK3),k3_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k3_lattices(sK0,sK2,sK3),k3_lattices(sK0,sK2,sK3))
    | ~ spl13_1
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_134 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f3970,f3970,f156])).

fof(f9460,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)),k2_lattices(sK0,sK3,k3_lattices(sK0,sK3,sK3))) = k2_lattices(sK0,sK3,k1_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK3,sK3)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f241,f4123,f3977,f140])).

fof(f16570,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK9(u1_struct_0(sK0)),sK2),k2_lattices(sK0,sK9(u1_struct_0(sK0)),sK3)) = k2_lattices(sK0,sK9(u1_struct_0(sK0)),k1_lattices(sK0,sK2,sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f16569,f12130])).

fof(f16569,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK9(u1_struct_0(sK0)),k4_lattices(sK0,sK2,sK3)),k2_lattices(sK0,sK9(u1_struct_0(sK0)),sK3)) = k2_lattices(sK0,sK9(u1_struct_0(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f9419,f12907])).

fof(f9419,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK9(u1_struct_0(sK0)),k4_lattices(sK0,sK2,sK3)),k2_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK3,sK3))) = k2_lattices(sK0,sK9(u1_struct_0(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k3_lattices(sK0,sK3,sK3)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_124
    | ~ spl13_136 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f145,f3482,f3977,f140])).

fof(f18923,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK9(u1_struct_0(sK0))),sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f18922,f15181])).

fof(f18922,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK9(u1_struct_0(sK0))),k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f18921,f11877])).

fof(f11877,plain,
    ( k2_lattices(sK0,sK3,k3_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK1,sK2))) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f11777,f10645])).

fof(f10645,plain,
    ( k1_lattices(sK0,sK3,k4_lattices(sK0,sK3,sK9(u1_struct_0(sK0)))) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK1,sK2)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_50
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f10644,f4046])).

fof(f10644,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)),k4_lattices(sK0,sK3,sK9(u1_struct_0(sK0)))) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK1,sK2)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f10643,f1958])).

fof(f10643,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)),k2_lattices(sK0,sK3,sK9(u1_struct_0(sK0)))) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK1,sK2)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f10244,f7057])).

fof(f7057,plain,
    ( k3_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK9(u1_struct_0(sK0)))
    | ~ spl13_1
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f6814,f6884])).

fof(f6884,plain,
    ( k3_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK9(u1_struct_0(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK9(u1_struct_0(sK0)))
    | ~ spl13_1
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f145,f4123,f156])).

fof(f6814,plain,
    ( k3_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK9(u1_struct_0(sK0))) = k3_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f145,f4123,f153])).

fof(f10244,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)),k2_lattices(sK0,sK3,sK9(u1_struct_0(sK0)))) = k2_lattices(sK0,sK3,k1_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK9(u1_struct_0(sK0))))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f241,f4123,f145,f140])).

fof(f11777,plain,
    ( k1_lattices(sK0,sK3,k4_lattices(sK0,sK3,sK9(u1_struct_0(sK0)))) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f11628,f10381])).

fof(f10381,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK3,sK3),k4_lattices(sK0,sK3,sK9(u1_struct_0(sK0)))) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46 ),
    inference(forward_demodulation,[],[f10380,f1945])).

fof(f10380,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK3),k4_lattices(sK0,sK3,sK9(u1_struct_0(sK0)))) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46 ),
    inference(forward_demodulation,[],[f10379,f1958])).

fof(f10379,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK3),k2_lattices(sK0,sK3,sK9(u1_struct_0(sK0)))) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_46 ),
    inference(forward_demodulation,[],[f10378,f4007])).

fof(f4007,plain,
    ( k2_lattices(sK0,sK3,k3_lattices(sK0,sK3,sK9(u1_struct_0(sK0)))) = sK3
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_46 ),
    inference(backward_demodulation,[],[f4002,f1030])).

fof(f1030,plain,
    ( k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,sK9(u1_struct_0(sK0)))) = sK3
    | ~ spl13_1
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_46 ),
    inference(unit_resulting_resolution,[],[f171,f192,f345,f241,f145,f136])).

fof(f10378,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK3),k2_lattices(sK0,sK3,sK9(u1_struct_0(sK0)))) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK3,sK9(u1_struct_0(sK0))))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(forward_demodulation,[],[f10328,f4002])).

fof(f10328,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK3),k2_lattices(sK0,sK3,sK9(u1_struct_0(sK0)))) = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,sK9(u1_struct_0(sK0))))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_20 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f241,f241,f145,f140])).

fof(f18921,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK9(u1_struct_0(sK0))),k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK1,sK2)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f18920,f11628])).

fof(f18920,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),sK9(u1_struct_0(sK0))),k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),k3_lattices(sK0,sK1,sK2))) = k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),k3_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK1,sK2)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_126
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f8962,f6898])).

fof(f6898,plain,
    ( k3_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f145,f4123,f156])).

fof(f8962,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),sK9(u1_struct_0(sK0))),k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),k3_lattices(sK0,sK1,sK2))) = k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),k1_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK1,sK2)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_126
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f3489,f145,f4123,f140])).

fof(f18905,plain,
    ( spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(avatar_contradiction_clause,[],[f18904])).

fof(f18904,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f18903,f220])).

fof(f18903,plain,
    ( sK2 = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f18902,f12577])).

fof(f18902,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0))),sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f18901,f16575])).

fof(f18901,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK9(u1_struct_0(sK0))),sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f18900,f15181])).

fof(f18900,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK9(u1_struct_0(sK0))),k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f18899,f11877])).

fof(f18899,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK9(u1_struct_0(sK0))),k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK1,sK2)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f18898,f11918])).

fof(f18898,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK9(u1_struct_0(sK0))),k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),k3_lattices(sK0,sK1,sK2))) = k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),k3_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK1,sK2)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_134
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f8966,f6898])).

fof(f8966,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK9(u1_struct_0(sK0))),k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),k3_lattices(sK0,sK1,sK2))) = k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),k1_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK1,sK2)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_134
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f3970,f145,f4123,f140])).

fof(f18897,plain,
    ( spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(avatar_contradiction_clause,[],[f18896])).

fof(f18896,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f18895,f220])).

fof(f18895,plain,
    ( sK2 = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f18894,f12577])).

fof(f18894,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0))),sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f18893,f16575])).

fof(f18893,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK9(u1_struct_0(sK0))),sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f18892,f15181])).

fof(f18892,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK9(u1_struct_0(sK0))),k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f18891,f11877])).

fof(f18891,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK9(u1_struct_0(sK0))),k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK1,sK2)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f18890,f12907])).

fof(f18890,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK9(u1_struct_0(sK0))),k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),k3_lattices(sK0,sK1,sK2))) = k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),k3_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK1,sK2)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f8967,f6898])).

fof(f8967,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK9(u1_struct_0(sK0))),k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),k3_lattices(sK0,sK1,sK2))) = k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),k1_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK1,sK2)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f3977,f145,f4123,f140])).

fof(f18881,plain,
    ( spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(avatar_contradiction_clause,[],[f18880])).

fof(f18880,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f18879,f220])).

fof(f18879,plain,
    ( sK2 = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f18878,f12577])).

fof(f18878,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0))),sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_124
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f18877,f16575])).

fof(f18877,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK9(u1_struct_0(sK0))),sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f18876,f15181])).

fof(f18876,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK9(u1_struct_0(sK0))),k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f18875,f11877])).

fof(f18875,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK9(u1_struct_0(sK0))),k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK1,sK2)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f8970,f6898])).

fof(f8970,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK9(u1_struct_0(sK0))),k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))) = k2_lattices(sK0,sK3,k1_lattices(sK0,sK9(u1_struct_0(sK0)),k3_lattices(sK0,sK1,sK2)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_20
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f241,f145,f4123,f140])).

fof(f16361,plain,
    ( spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(avatar_contradiction_clause,[],[f16360])).

fof(f16360,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f16359,f220])).

fof(f16359,plain,
    ( sK2 = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f16358,f11921])).

fof(f11921,plain,
    ( k1_lattices(sK0,sK2,sK3) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f11918,f3996])).

fof(f16096,plain,
    ( spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(avatar_contradiction_clause,[],[f16095])).

fof(f16095,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f16094,f220])).

fof(f16094,plain,
    ( sK2 = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f16093,f13064])).

fof(f13064,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f12107,f355])).

fof(f12107,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK3) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f11918,f11308])).

fof(f16093,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f16092,f3640])).

fof(f16092,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),sK3) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f16091,f11625])).

fof(f16091,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK3)) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f16090,f15181])).

fof(f16090,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK3)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f16089,f4023])).

fof(f16089,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK3)) = k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK3))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f9516,f12907])).

fof(f9516,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,k3_lattices(sK0,sK3,sK3))) = k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,k3_lattices(sK0,sK3,sK3)))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_136 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f241,f227,f3977,f140])).

fof(f15227,plain,
    ( spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(avatar_contradiction_clause,[],[f15226])).

fof(f15226,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f15225,f220])).

fof(f15225,plain,
    ( sK2 = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f15224,f13068])).

fof(f13068,plain,
    ( k1_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f13065,f5117])).

fof(f5117,plain,
    ( k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_128 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f241,f3496,f156])).

fof(f13065,plain,
    ( k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f13064,f5215])).

fof(f5215,plain,
    ( k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_48
    | ~ spl13_90
    | ~ spl13_128 ),
    inference(forward_demodulation,[],[f5108,f2345])).

fof(f2345,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_48
    | ~ spl13_90 ),
    inference(backward_demodulation,[],[f2241,f1371])).

fof(f1371,plain,
    ( k3_lattices(sK0,k2_lattices(sK0,sK1,sK3),sK3) = k3_lattices(sK0,sK3,k2_lattices(sK0,sK1,sK3))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_90 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f583,f241,f153])).

fof(f5108,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3)
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_128 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f241,f3496,f156])).

fof(f15224,plain,
    ( k1_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2)) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f15223,f11625])).

fof(f15223,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK3),k4_lattices(sK0,sK1,sK2)) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f15222,f3640])).

fof(f15222,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK3),k2_lattices(sK0,sK3,sK1)) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f15221,f15181])).

fof(f15221,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK3),k2_lattices(sK0,sK3,sK1)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f15220,f4045])).

fof(f15220,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK3),k2_lattices(sK0,sK3,sK1)) = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,sK1))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f9698,f12907])).

fof(f9698,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,k3_lattices(sK0,sK3,sK3)),k2_lattices(sK0,sK3,sK1)) = k2_lattices(sK0,sK3,k1_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK1))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_136 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f241,f3977,f227,f140])).

fof(f15184,plain,
    ( spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(avatar_contradiction_clause,[],[f15183])).

fof(f15183,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f15182,f220])).

fof(f15182,plain,
    ( sK2 = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_96
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_130
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f15181,f4046])).

fof(f14896,plain,
    ( spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(avatar_contradiction_clause,[],[f14895])).

fof(f14895,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f14894,f220])).

fof(f14894,plain,
    ( sK2 = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14893,f12621])).

fof(f12621,plain,
    ( k1_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f12618,f5116])).

fof(f5116,plain,
    ( k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_128 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f234,f3496,f156])).

fof(f12618,plain,
    ( k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = sK2
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f12617,f5218])).

fof(f5218,plain,
    ( k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_48
    | ~ spl13_90
    | ~ spl13_128 ),
    inference(forward_demodulation,[],[f5107,f2344])).

fof(f2344,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_48
    | ~ spl13_90 ),
    inference(backward_demodulation,[],[f2241,f1360])).

fof(f1360,plain,
    ( k3_lattices(sK0,k2_lattices(sK0,sK1,sK3),sK2) = k3_lattices(sK0,sK2,k2_lattices(sK0,sK1,sK3))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_90 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f583,f234,f153])).

fof(f5107,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_128 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f234,f3496,f156])).

fof(f14893,plain,
    ( k1_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14892,f12154])).

fof(f14892,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k4_lattices(sK0,sK1,sK2)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14891,f3640])).

fof(f14891,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k2_lattices(sK0,sK3,sK1)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14890,f4046])).

fof(f14890,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k2_lattices(sK0,sK3,sK1)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14889,f11628])).

fof(f14889,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),sK2),k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),sK1)) = k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_126 ),
    inference(forward_demodulation,[],[f9718,f4048])).

fof(f9718,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),sK2),k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),sK1)) = k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),k1_lattices(sK0,sK2,sK1))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_126 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f3489,f234,f227,f140])).

fof(f14875,plain,
    ( spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(avatar_contradiction_clause,[],[f14874])).

fof(f14874,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f14873,f220])).

fof(f14873,plain,
    ( sK2 = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14872,f12621])).

fof(f14872,plain,
    ( k1_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14871,f12154])).

fof(f14871,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k4_lattices(sK0,sK1,sK2)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14870,f3640])).

fof(f14870,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k2_lattices(sK0,sK3,sK1)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14869,f4046])).

fof(f14869,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k2_lattices(sK0,sK3,sK1)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14868,f11918])).

fof(f14868,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK2),k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK1)) = k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_134 ),
    inference(forward_demodulation,[],[f9722,f4048])).

fof(f9722,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK2),k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK1)) = k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),k1_lattices(sK0,sK2,sK1))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_134 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f3970,f234,f227,f140])).

fof(f14867,plain,
    ( spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(avatar_contradiction_clause,[],[f14866])).

fof(f14866,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f14865,f220])).

fof(f14865,plain,
    ( sK2 = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14864,f12621])).

fof(f14864,plain,
    ( k1_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14863,f12154])).

fof(f14863,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k4_lattices(sK0,sK1,sK2)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14862,f3640])).

fof(f14862,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k2_lattices(sK0,sK3,sK1)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14861,f4046])).

fof(f14861,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k2_lattices(sK0,sK3,sK1)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14860,f12907])).

fof(f14860,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK2),k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK1)) = k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_136 ),
    inference(forward_demodulation,[],[f9723,f4048])).

fof(f9723,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK2),k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK1)) = k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),k1_lattices(sK0,sK2,sK1))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_136 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f3977,f234,f227,f140])).

fof(f14851,plain,
    ( spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(avatar_contradiction_clause,[],[f14850])).

fof(f14850,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f14849,f220])).

fof(f14849,plain,
    ( sK2 = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14848,f12621])).

fof(f14848,plain,
    ( k1_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14847,f12154])).

fof(f14847,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k4_lattices(sK0,sK1,sK2)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50 ),
    inference(forward_demodulation,[],[f14846,f3640])).

fof(f14846,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k2_lattices(sK0,sK3,sK1)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_46
    | ~ spl13_50 ),
    inference(forward_demodulation,[],[f14845,f4046])).

fof(f14845,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k2_lattices(sK0,sK3,sK1)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(forward_demodulation,[],[f9726,f4048])).

fof(f9726,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k2_lattices(sK0,sK3,sK1)) = k2_lattices(sK0,sK3,k1_lattices(sK0,sK2,sK1))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f241,f234,f227,f140])).

fof(f14700,plain,
    ( spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(avatar_contradiction_clause,[],[f14699])).

fof(f14699,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f14698,f220])).

fof(f14698,plain,
    ( sK2 = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14697,f12617])).

fof(f14697,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14696,f3640])).

fof(f14696,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14695,f12154])).

fof(f14695,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK2)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14694,f4046])).

fof(f14694,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK2)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14693,f11628])).

fof(f14693,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),sK1),k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),sK2)) = k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_114
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14692,f3990])).

fof(f3990,plain,
    ( k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f227,f234,f156])).

fof(f14692,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),sK1),k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),sK2)) = k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),k1_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_114
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f9760,f13331])).

fof(f13331,plain,
    ( k4_lattices(sK0,sK1,sK1) = sK1
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_128
    | ~ spl13_138 ),
    inference(backward_demodulation,[],[f13328,f1917])).

fof(f1917,plain,
    ( k4_lattices(sK0,sK1,sK1) = k2_lattices(sK0,sK1,sK1)
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f227,f227,f154])).

fof(f9760,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),k4_lattices(sK0,sK1,sK1)),k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),sK2)) = k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),k1_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_114
    | ~ spl13_126 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f3489,f1775,f234,f140])).

fof(f1775,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl13_114 ),
    inference(avatar_component_clause,[],[f1774])).

fof(f1774,plain,
    ( spl13_114
  <=> m1_subset_1(k4_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_114])])).

fof(f14675,plain,
    ( spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(avatar_contradiction_clause,[],[f14674])).

fof(f14674,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f14673,f220])).

fof(f14673,plain,
    ( sK2 = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14672,f12617])).

fof(f14672,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14671,f3640])).

fof(f14671,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14670,f12154])).

fof(f14670,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK2)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14669,f4046])).

fof(f14669,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK2)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14668,f11918])).

fof(f14668,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK1),k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK2)) = k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_114
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14667,f3990])).

fof(f14667,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK1),k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK2)) = k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),k1_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_114
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f9764,f13331])).

fof(f9764,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK1)),k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK2)) = k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),k1_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_114
    | ~ spl13_134 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f3970,f1775,f234,f140])).

fof(f14666,plain,
    ( spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(avatar_contradiction_clause,[],[f14665])).

fof(f14665,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f14664,f220])).

fof(f14664,plain,
    ( sK2 = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14663,f12617])).

fof(f14663,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14662,f3640])).

fof(f14662,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14661,f12154])).

fof(f14661,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK2)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14660,f4046])).

fof(f14660,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK2)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14659,f12907])).

fof(f14659,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK1),k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK2)) = k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_114
    | ~ spl13_128
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14658,f3990])).

fof(f14658,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK1),k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK2)) = k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),k1_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_114
    | ~ spl13_128
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f9765,f13331])).

fof(f9765,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),k4_lattices(sK0,sK1,sK1)),k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK2)) = k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),k1_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_114
    | ~ spl13_136 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f3977,f1775,f234,f140])).

fof(f14647,plain,
    ( spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(avatar_contradiction_clause,[],[f14646])).

fof(f14646,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f14645,f220])).

fof(f14645,plain,
    ( sK2 = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14644,f12617])).

fof(f14644,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14643,f3640])).

fof(f14643,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_94
    | ~ spl13_114
    | ~ spl13_126
    | ~ spl13_128
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14642,f12154])).

fof(f14642,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK2)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_114
    | ~ spl13_128
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14641,f4046])).

fof(f14641,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK2)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_114
    | ~ spl13_128
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14640,f3990])).

fof(f14640,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK2)) = k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_90
    | ~ spl13_114
    | ~ spl13_128
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f9768,f13331])).

fof(f9768,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK1)),k2_lattices(sK0,sK3,sK2)) = k2_lattices(sK0,sK3,k1_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_114 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f241,f1775,f234,f140])).

fof(f14112,plain,
    ( spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(avatar_contradiction_clause,[],[f14111])).

fof(f14111,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f14110,f220])).

fof(f14110,plain,
    ( sK2 = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14109,f12617])).

fof(f14109,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14108,f3640])).

fof(f14108,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14107,f12154])).

fof(f14107,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK2)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14106,f4046])).

fof(f14106,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK2)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14105,f11628])).

fof(f14105,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),sK1),k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),sK2)) = k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_126 ),
    inference(forward_demodulation,[],[f9900,f3990])).

fof(f9900,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),sK1),k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),sK2)) = k2_lattices(sK0,k4_lattices(sK0,sK3,sK3),k1_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_126 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f3489,f227,f234,f140])).

fof(f14091,plain,
    ( spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(avatar_contradiction_clause,[],[f14090])).

fof(f14090,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f14089,f220])).

fof(f14089,plain,
    ( sK2 = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14088,f12617])).

fof(f14088,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14087,f3640])).

fof(f14087,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14086,f12154])).

fof(f14086,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK2)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14085,f4046])).

fof(f14085,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK2)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14084,f11918])).

fof(f14084,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK1),k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK2)) = k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_134 ),
    inference(forward_demodulation,[],[f9904,f3990])).

fof(f9904,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK1),k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),sK2)) = k2_lattices(sK0,k3_lattices(sK0,sK2,sK3),k1_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_134 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f3970,f227,f234,f140])).

fof(f14083,plain,
    ( spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(avatar_contradiction_clause,[],[f14082])).

fof(f14082,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f14081,f220])).

fof(f14081,plain,
    ( sK2 = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14080,f12617])).

fof(f14080,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14079,f3640])).

fof(f14079,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14078,f12154])).

fof(f14078,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK2)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14077,f4046])).

fof(f14077,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK2)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14076,f12907])).

fof(f14076,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK1),k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK2)) = k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_136 ),
    inference(forward_demodulation,[],[f9905,f3990])).

fof(f9905,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK1),k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),sK2)) = k2_lattices(sK0,k3_lattices(sK0,sK3,sK3),k1_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_136 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f3977,f227,f234,f140])).

fof(f14067,plain,
    ( spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(avatar_contradiction_clause,[],[f14066])).

fof(f14066,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_15
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f14065,f220])).

fof(f14065,plain,
    ( sK2 = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_86
    | ~ spl13_94
    | ~ spl13_120
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14064,f12617])).

fof(f14064,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14063,f3640])).

fof(f14063,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),sK2) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_44
    | ~ spl13_46
    | ~ spl13_48
    | ~ spl13_50
    | ~ spl13_94
    | ~ spl13_126
    | ~ spl13_134
    | ~ spl13_136
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f14062,f12154])).

fof(f14062,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK2)) = sK3
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_46
    | ~ spl13_50 ),
    inference(forward_demodulation,[],[f14061,f4046])).

fof(f14061,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK2)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(forward_demodulation,[],[f9908,f3990])).

fof(f9908,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK2)) = k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK2))
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_20 ),
    inference(unit_resulting_resolution,[],[f171,f192,f185,f241,f227,f234,f140])).

fof(f7599,plain,
    ( spl13_156
    | ~ spl13_18
    | ~ spl13_34
    | ~ spl13_54
    | ~ spl13_72 ),
    inference(avatar_split_clause,[],[f7398,f484,f404,f299,f233,f7597])).

fof(f7597,plain,
    ( spl13_156
  <=> m1_subset_1(k1_binop_1(u1_lattices(sK0),sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_156])])).

fof(f299,plain,
    ( spl13_34
  <=> v1_funct_1(u1_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_34])])).

fof(f404,plain,
    ( spl13_54
  <=> v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_54])])).

fof(f484,plain,
    ( spl13_72
  <=> m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_72])])).

fof(f7398,plain,
    ( m1_subset_1(k1_binop_1(u1_lattices(sK0),sK2,sK2),u1_struct_0(sK0))
    | ~ spl13_18
    | ~ spl13_34
    | ~ spl13_54
    | ~ spl13_72 ),
    inference(backward_demodulation,[],[f7333,f4971])).

fof(f4971,plain,
    ( m1_subset_1(k4_binop_1(u1_struct_0(sK0),u1_lattices(sK0),sK2,sK2),u1_struct_0(sK0))
    | ~ spl13_18
    | ~ spl13_34
    | ~ spl13_54
    | ~ spl13_72 ),
    inference(unit_resulting_resolution,[],[f300,f234,f234,f405,f485,f161])).

fof(f161,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k4_binop_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k4_binop_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k4_binop_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X1) )
     => m1_subset_1(k4_binop_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',dt_k4_binop_1)).

fof(f485,plain,
    ( m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ spl13_72 ),
    inference(avatar_component_clause,[],[f484])).

fof(f405,plain,
    ( v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl13_54 ),
    inference(avatar_component_clause,[],[f404])).

fof(f300,plain,
    ( v1_funct_1(u1_lattices(sK0))
    | ~ spl13_34 ),
    inference(avatar_component_clause,[],[f299])).

fof(f7333,plain,
    ( k4_binop_1(u1_struct_0(sK0),u1_lattices(sK0),sK2,sK2) = k1_binop_1(u1_lattices(sK0),sK2,sK2)
    | ~ spl13_18
    | ~ spl13_34
    | ~ spl13_54
    | ~ spl13_72 ),
    inference(unit_resulting_resolution,[],[f300,f234,f234,f405,f485,f162])).

fof(f162,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_binop_1(X0,X1,X2,X3) = k1_binop_1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1,X2,X3] :
      ( k4_binop_1(X0,X1,X2,X3) = k1_binop_1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2,X3] :
      ( k4_binop_1(X0,X1,X2,X3) = k1_binop_1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X1) )
     => k4_binop_1(X0,X1,X2,X3) = k1_binop_1(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',redefinition_k4_binop_1)).

fof(f7592,plain,
    ( spl13_154
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_34
    | ~ spl13_54
    | ~ spl13_72 ),
    inference(avatar_split_clause,[],[f7397,f484,f404,f299,f240,f233,f7590])).

fof(f7590,plain,
    ( spl13_154
  <=> m1_subset_1(k1_binop_1(u1_lattices(sK0),sK3,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_154])])).

fof(f7397,plain,
    ( m1_subset_1(k1_binop_1(u1_lattices(sK0),sK3,sK2),u1_struct_0(sK0))
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_34
    | ~ spl13_54
    | ~ spl13_72 ),
    inference(backward_demodulation,[],[f7334,f4979])).

fof(f4979,plain,
    ( m1_subset_1(k4_binop_1(u1_struct_0(sK0),u1_lattices(sK0),sK3,sK2),u1_struct_0(sK0))
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_34
    | ~ spl13_54
    | ~ spl13_72 ),
    inference(unit_resulting_resolution,[],[f300,f234,f241,f405,f485,f161])).

fof(f7334,plain,
    ( k4_binop_1(u1_struct_0(sK0),u1_lattices(sK0),sK3,sK2) = k1_binop_1(u1_lattices(sK0),sK3,sK2)
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_34
    | ~ spl13_54
    | ~ spl13_72 ),
    inference(unit_resulting_resolution,[],[f300,f241,f234,f405,f485,f162])).

fof(f7585,plain,
    ( spl13_152
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_34
    | ~ spl13_54
    | ~ spl13_72 ),
    inference(avatar_split_clause,[],[f7385,f484,f404,f299,f240,f226,f7583])).

fof(f7583,plain,
    ( spl13_152
  <=> m1_subset_1(k1_binop_1(u1_lattices(sK0),sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_152])])).

fof(f7385,plain,
    ( m1_subset_1(k1_binop_1(u1_lattices(sK0),sK1,sK3),u1_struct_0(sK0))
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_34
    | ~ spl13_54
    | ~ spl13_72 ),
    inference(backward_demodulation,[],[f7346,f4964])).

fof(f4964,plain,
    ( m1_subset_1(k4_binop_1(u1_struct_0(sK0),u1_lattices(sK0),sK1,sK3),u1_struct_0(sK0))
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_34
    | ~ spl13_54
    | ~ spl13_72 ),
    inference(unit_resulting_resolution,[],[f300,f241,f227,f405,f485,f161])).

fof(f7346,plain,
    ( k4_binop_1(u1_struct_0(sK0),u1_lattices(sK0),sK1,sK3) = k1_binop_1(u1_lattices(sK0),sK1,sK3)
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_34
    | ~ spl13_54
    | ~ spl13_72 ),
    inference(unit_resulting_resolution,[],[f300,f227,f241,f405,f485,f162])).

fof(f7578,plain,
    ( spl13_150
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_34
    | ~ spl13_54
    | ~ spl13_72 ),
    inference(avatar_split_clause,[],[f7384,f484,f404,f299,f240,f233,f7576])).

fof(f7576,plain,
    ( spl13_150
  <=> m1_subset_1(k1_binop_1(u1_lattices(sK0),sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_150])])).

fof(f7384,plain,
    ( m1_subset_1(k1_binop_1(u1_lattices(sK0),sK2,sK3),u1_struct_0(sK0))
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_34
    | ~ spl13_54
    | ~ spl13_72 ),
    inference(backward_demodulation,[],[f7347,f4972])).

fof(f4972,plain,
    ( m1_subset_1(k4_binop_1(u1_struct_0(sK0),u1_lattices(sK0),sK2,sK3),u1_struct_0(sK0))
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_34
    | ~ spl13_54
    | ~ spl13_72 ),
    inference(unit_resulting_resolution,[],[f300,f241,f234,f405,f485,f161])).

fof(f7347,plain,
    ( k4_binop_1(u1_struct_0(sK0),u1_lattices(sK0),sK2,sK3) = k1_binop_1(u1_lattices(sK0),sK2,sK3)
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_34
    | ~ spl13_54
    | ~ spl13_72 ),
    inference(unit_resulting_resolution,[],[f300,f234,f241,f405,f485,f162])).

fof(f7571,plain,
    ( spl13_148
    | ~ spl13_20
    | ~ spl13_34
    | ~ spl13_54
    | ~ spl13_72 ),
    inference(avatar_split_clause,[],[f7383,f484,f404,f299,f240,f7569])).

fof(f7569,plain,
    ( spl13_148
  <=> m1_subset_1(k1_binop_1(u1_lattices(sK0),sK3,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_148])])).

fof(f7383,plain,
    ( m1_subset_1(k1_binop_1(u1_lattices(sK0),sK3,sK3),u1_struct_0(sK0))
    | ~ spl13_20
    | ~ spl13_34
    | ~ spl13_54
    | ~ spl13_72 ),
    inference(backward_demodulation,[],[f7348,f4980])).

fof(f4980,plain,
    ( m1_subset_1(k4_binop_1(u1_struct_0(sK0),u1_lattices(sK0),sK3,sK3),u1_struct_0(sK0))
    | ~ spl13_20
    | ~ spl13_34
    | ~ spl13_54
    | ~ spl13_72 ),
    inference(unit_resulting_resolution,[],[f300,f241,f241,f405,f485,f161])).

fof(f7348,plain,
    ( k4_binop_1(u1_struct_0(sK0),u1_lattices(sK0),sK3,sK3) = k1_binop_1(u1_lattices(sK0),sK3,sK3)
    | ~ spl13_20
    | ~ spl13_34
    | ~ spl13_54
    | ~ spl13_72 ),
    inference(unit_resulting_resolution,[],[f300,f241,f241,f405,f485,f162])).

fof(f7166,plain,
    ( spl13_146
    | spl13_1
    | ~ spl13_16
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(avatar_split_clause,[],[f910,f328,f258,f226,f170,f7164])).

fof(f7164,plain,
    ( spl13_146
  <=> m1_subset_1(k3_lattices(sK0,sK1,sK9(u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_146])])).

fof(f910,plain,
    ( m1_subset_1(k3_lattices(sK0,sK1,sK9(u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f227,f145,f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',dt_k3_lattices)).

fof(f7159,plain,
    ( spl13_144
    | spl13_1
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(avatar_split_clause,[],[f642,f336,f249,f240,f170,f7157])).

fof(f7157,plain,
    ( spl13_144
  <=> m1_subset_1(k4_lattices(sK0,sK3,sK9(u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_144])])).

fof(f642,plain,
    ( m1_subset_1(k4_lattices(sK0,sK3,sK9(u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f241,f145,f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',dt_k4_lattices)).

fof(f7152,plain,
    ( spl13_142
    | spl13_1
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(avatar_split_clause,[],[f641,f336,f249,f233,f170,f7150])).

fof(f7150,plain,
    ( spl13_142
  <=> m1_subset_1(k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_142])])).

fof(f641,plain,
    ( m1_subset_1(k4_lattices(sK0,sK2,sK9(u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f234,f145,f151])).

fof(f7145,plain,
    ( spl13_140
    | spl13_1
    | ~ spl13_16
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(avatar_split_clause,[],[f640,f336,f249,f226,f170,f7143])).

fof(f7143,plain,
    ( spl13_140
  <=> m1_subset_1(k4_lattices(sK0,sK1,sK9(u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_140])])).

fof(f640,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK9(u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f227,f145,f151])).

fof(f4124,plain,
    ( spl13_138
    | spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_50 ),
    inference(avatar_split_clause,[],[f915,f361,f328,f258,f240,f226,f170,f4122])).

fof(f915,plain,
    ( m1_subset_1(k3_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42
    | ~ spl13_50 ),
    inference(forward_demodulation,[],[f901,f362])).

fof(f901,plain,
    ( m1_subset_1(k3_lattices(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f227,f241,f152])).

fof(f3978,plain,
    ( spl13_136
    | spl13_1
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(avatar_split_clause,[],[f903,f328,f258,f240,f170,f3976])).

fof(f903,plain,
    ( m1_subset_1(k3_lattices(sK0,sK3,sK3),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f241,f241,f152])).

fof(f3971,plain,
    ( spl13_134
    | spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(avatar_split_clause,[],[f902,f328,f258,f240,f233,f170,f3969])).

fof(f902,plain,
    ( m1_subset_1(k3_lattices(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f234,f241,f152])).

fof(f3964,plain,
    ( spl13_132
    | spl13_1
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(avatar_split_clause,[],[f893,f328,f258,f233,f170,f3962])).

fof(f3962,plain,
    ( spl13_132
  <=> m1_subset_1(k3_lattices(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_132])])).

fof(f893,plain,
    ( m1_subset_1(k3_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f234,f234,f152])).

fof(f3957,plain,
    ( spl13_130
    | spl13_1
    | ~ spl13_16
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(avatar_split_clause,[],[f883,f328,f258,f226,f170,f3955])).

fof(f883,plain,
    ( m1_subset_1(k3_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_24
    | ~ spl13_42 ),
    inference(unit_resulting_resolution,[],[f171,f329,f259,f227,f227,f152])).

fof(f3497,plain,
    ( spl13_128
    | spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_48 ),
    inference(avatar_split_clause,[],[f645,f354,f336,f249,f240,f226,f170,f3495])).

fof(f645,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44
    | ~ spl13_48 ),
    inference(forward_demodulation,[],[f635,f355])).

fof(f635,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f227,f241,f151])).

fof(f3490,plain,
    ( spl13_126
    | spl13_1
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(avatar_split_clause,[],[f637,f336,f249,f240,f170,f3488])).

fof(f637,plain,
    ( m1_subset_1(k4_lattices(sK0,sK3,sK3),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f241,f241,f151])).

fof(f3483,plain,
    ( spl13_124
    | spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(avatar_split_clause,[],[f636,f336,f249,f240,f233,f170,f3481])).

fof(f636,plain,
    ( m1_subset_1(k4_lattices(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f234,f241,f151])).

fof(f3476,plain,
    ( spl13_122
    | spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(avatar_split_clause,[],[f632,f336,f249,f240,f233,f170,f3474])).

fof(f3474,plain,
    ( spl13_122
  <=> m1_subset_1(k4_lattices(sK0,sK3,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_122])])).

fof(f632,plain,
    ( m1_subset_1(k4_lattices(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f241,f234,f151])).

fof(f3469,plain,
    ( spl13_120
    | spl13_1
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(avatar_split_clause,[],[f631,f336,f249,f233,f170,f3467])).

fof(f631,plain,
    ( m1_subset_1(k4_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f234,f234,f151])).

fof(f1790,plain,
    ( spl13_118
    | spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(avatar_split_clause,[],[f627,f336,f249,f240,f226,f170,f1788])).

fof(f1788,plain,
    ( spl13_118
  <=> m1_subset_1(k4_lattices(sK0,sK3,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_118])])).

fof(f627,plain,
    ( m1_subset_1(k4_lattices(sK0,sK3,sK1),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f241,f227,f151])).

fof(f1783,plain,
    ( spl13_116
    | spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(avatar_split_clause,[],[f626,f336,f249,f233,f226,f170,f1781])).

fof(f1781,plain,
    ( spl13_116
  <=> m1_subset_1(k4_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_116])])).

fof(f626,plain,
    ( m1_subset_1(k4_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f234,f227,f151])).

fof(f1776,plain,
    ( spl13_114
    | spl13_1
    | ~ spl13_16
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(avatar_split_clause,[],[f625,f336,f249,f226,f170,f1774])).

fof(f625,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_22
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f171,f337,f250,f227,f227,f151])).

fof(f1055,plain,
    ( spl13_112
    | spl13_1
    | ~ spl13_20
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f565,f258,f240,f170,f1053])).

fof(f1053,plain,
    ( spl13_112
  <=> m1_subset_1(k1_lattices(sK0,sK3,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_112])])).

fof(f565,plain,
    ( m1_subset_1(k1_lattices(sK0,sK3,sK3),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f171,f259,f241,f241,f158])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',dt_k1_lattices)).

fof(f1048,plain,
    ( spl13_110
    | spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f564,f258,f240,f233,f170,f1046])).

fof(f1046,plain,
    ( spl13_110
  <=> m1_subset_1(k1_lattices(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_110])])).

fof(f564,plain,
    ( m1_subset_1(k1_lattices(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f171,f259,f234,f241,f158])).

fof(f1041,plain,
    ( spl13_108
    | spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f563,f258,f240,f226,f170,f1039])).

fof(f1039,plain,
    ( spl13_108
  <=> m1_subset_1(k1_lattices(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_108])])).

fof(f563,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f171,f259,f227,f241,f158])).

fof(f950,plain,
    ( spl13_106
    | spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f561,f258,f240,f233,f170,f948])).

fof(f948,plain,
    ( spl13_106
  <=> m1_subset_1(k1_lattices(sK0,sK3,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_106])])).

fof(f561,plain,
    ( m1_subset_1(k1_lattices(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f171,f259,f241,f234,f158])).

fof(f943,plain,
    ( spl13_104
    | spl13_1
    | ~ spl13_18
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f560,f258,f233,f170,f941])).

fof(f941,plain,
    ( spl13_104
  <=> m1_subset_1(k1_lattices(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_104])])).

fof(f560,plain,
    ( m1_subset_1(k1_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f171,f259,f234,f234,f158])).

fof(f936,plain,
    ( spl13_102
    | spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f559,f258,f233,f226,f170,f934])).

fof(f934,plain,
    ( spl13_102
  <=> m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_102])])).

fof(f559,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f171,f259,f227,f234,f158])).

fof(f929,plain,
    ( spl13_100
    | spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f557,f258,f240,f226,f170,f927])).

fof(f927,plain,
    ( spl13_100
  <=> m1_subset_1(k1_lattices(sK0,sK3,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_100])])).

fof(f557,plain,
    ( m1_subset_1(k1_lattices(sK0,sK3,sK1),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f171,f259,f241,f227,f158])).

fof(f922,plain,
    ( spl13_98
    | spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f556,f258,f233,f226,f170,f920])).

fof(f920,plain,
    ( spl13_98
  <=> m1_subset_1(k1_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_98])])).

fof(f556,plain,
    ( m1_subset_1(k1_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f171,f259,f234,f227,f158])).

fof(f832,plain,
    ( spl13_96
    | spl13_1
    | ~ spl13_16
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f555,f258,f226,f170,f830])).

fof(f555,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f171,f259,f227,f227,f158])).

fof(f598,plain,
    ( spl13_94
    | spl13_1
    | ~ spl13_20
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f514,f249,f240,f170,f596])).

fof(f514,plain,
    ( m1_subset_1(k2_lattices(sK0,sK3,sK3),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_20
    | ~ spl13_22 ),
    inference(unit_resulting_resolution,[],[f171,f250,f241,f241,f157])).

fof(f157,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',dt_k2_lattices)).

fof(f591,plain,
    ( spl13_92
    | spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f513,f249,f240,f233,f170,f589])).

fof(f589,plain,
    ( spl13_92
  <=> m1_subset_1(k2_lattices(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_92])])).

fof(f513,plain,
    ( m1_subset_1(k2_lattices(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22 ),
    inference(unit_resulting_resolution,[],[f171,f250,f234,f241,f157])).

fof(f584,plain,
    ( spl13_90
    | spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f512,f249,f240,f226,f170,f582])).

fof(f512,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22 ),
    inference(unit_resulting_resolution,[],[f171,f250,f227,f241,f157])).

fof(f577,plain,
    ( spl13_88
    | spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f510,f249,f240,f233,f170,f575])).

fof(f575,plain,
    ( spl13_88
  <=> m1_subset_1(k2_lattices(sK0,sK3,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_88])])).

fof(f510,plain,
    ( m1_subset_1(k2_lattices(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_22 ),
    inference(unit_resulting_resolution,[],[f171,f250,f241,f234,f157])).

fof(f554,plain,
    ( spl13_86
    | spl13_1
    | ~ spl13_18
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f509,f249,f233,f170,f552])).

fof(f509,plain,
    ( m1_subset_1(k2_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_18
    | ~ spl13_22 ),
    inference(unit_resulting_resolution,[],[f171,f250,f234,f234,f157])).

fof(f547,plain,
    ( spl13_84
    | spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f508,f249,f233,f226,f170,f545])).

fof(f545,plain,
    ( spl13_84
  <=> m1_subset_1(k2_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_84])])).

fof(f508,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_22 ),
    inference(unit_resulting_resolution,[],[f171,f250,f227,f234,f157])).

fof(f540,plain,
    ( spl13_82
    | spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f506,f249,f240,f226,f170,f538])).

fof(f538,plain,
    ( spl13_82
  <=> m1_subset_1(k2_lattices(sK0,sK3,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_82])])).

fof(f506,plain,
    ( m1_subset_1(k2_lattices(sK0,sK3,sK1),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_20
    | ~ spl13_22 ),
    inference(unit_resulting_resolution,[],[f171,f250,f241,f227,f157])).

fof(f533,plain,
    ( spl13_80
    | spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f505,f249,f233,f226,f170,f531])).

fof(f531,plain,
    ( spl13_80
  <=> m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_80])])).

fof(f505,plain,
    ( m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_18
    | ~ spl13_22 ),
    inference(unit_resulting_resolution,[],[f171,f250,f234,f227,f157])).

fof(f526,plain,
    ( spl13_78
    | spl13_1
    | ~ spl13_16
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f504,f249,f226,f170,f524])).

fof(f524,plain,
    ( spl13_78
  <=> m1_subset_1(k2_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_78])])).

fof(f504,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_16
    | ~ spl13_22 ),
    inference(unit_resulting_resolution,[],[f171,f250,f227,f227,f157])).

fof(f502,plain,
    ( ~ spl13_77
    | ~ spl13_72 ),
    inference(avatar_split_clause,[],[f494,f484,f500])).

fof(f500,plain,
    ( spl13_77
  <=> ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)),u1_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_77])])).

fof(f494,plain,
    ( ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)),u1_lattices(sK0))
    | ~ spl13_72 ),
    inference(unit_resulting_resolution,[],[f485,f371])).

fof(f371,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f370,f160])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',t5_subset)).

fof(f370,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f369,f159])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',t4_subset)).

fof(f369,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f368])).

fof(f368,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X0)
      | ~ m1_subset_1(X0,X0) ) ),
    inference(factoring,[],[f349])).

fof(f349,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f348,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',t2_subset)).

fof(f348,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f148,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',antisymmetry_r2_hidden)).

fof(f493,plain,
    ( spl13_74
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f459,f258,f491])).

fof(f491,plain,
    ( spl13_74
  <=> m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_74])])).

fof(f459,plain,
    ( m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f259,f135])).

fof(f135,plain,(
    ! [X0] :
      ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) )
      | ~ l2_lattices(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l2_lattices(X0)
     => ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',dt_u2_lattices)).

fof(f486,plain,
    ( spl13_72
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f432,f249,f484])).

fof(f432,plain,
    ( m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ spl13_22 ),
    inference(unit_resulting_resolution,[],[f250,f132])).

fof(f132,plain,(
    ! [X0] :
      ( m1_subset_1(u1_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( m1_subset_1(u1_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) )
      | ~ l1_lattices(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_lattices(X0)
     => ( m1_subset_1(u1_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',dt_u1_lattices)).

fof(f478,plain,
    ( ~ spl13_71
    | ~ spl13_68 ),
    inference(avatar_split_clause,[],[f470,f467,f476])).

fof(f476,plain,
    ( spl13_71
  <=> ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)),u1_struct_0(sK12)),u2_lattices(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_71])])).

fof(f467,plain,
    ( spl13_68
  <=> m1_subset_1(u2_lattices(sK12),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)),u1_struct_0(sK12)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_68])])).

fof(f470,plain,
    ( ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)),u1_struct_0(sK12)),u2_lattices(sK12))
    | ~ spl13_68 ),
    inference(unit_resulting_resolution,[],[f468,f371])).

fof(f468,plain,
    ( m1_subset_1(u2_lattices(sK12),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)),u1_struct_0(sK12))))
    | ~ spl13_68 ),
    inference(avatar_component_clause,[],[f467])).

fof(f469,plain,
    ( spl13_68
    | ~ spl13_12 ),
    inference(avatar_split_clause,[],[f458,f212,f467])).

fof(f212,plain,
    ( spl13_12
  <=> l2_lattices(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f458,plain,
    ( m1_subset_1(u2_lattices(sK12),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)),u1_struct_0(sK12))))
    | ~ spl13_12 ),
    inference(unit_resulting_resolution,[],[f213,f135])).

fof(f213,plain,
    ( l2_lattices(sK12)
    | ~ spl13_12 ),
    inference(avatar_component_clause,[],[f212])).

fof(f457,plain,
    ( ~ spl13_67
    | ~ spl13_64 ),
    inference(avatar_split_clause,[],[f449,f446,f455])).

fof(f455,plain,
    ( spl13_67
  <=> ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK11)),u1_struct_0(sK11)),u1_lattices(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_67])])).

fof(f446,plain,
    ( spl13_64
  <=> m1_subset_1(u1_lattices(sK11),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK11)),u1_struct_0(sK11)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_64])])).

fof(f449,plain,
    ( ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK11)),u1_struct_0(sK11)),u1_lattices(sK11))
    | ~ spl13_64 ),
    inference(unit_resulting_resolution,[],[f447,f371])).

fof(f447,plain,
    ( m1_subset_1(u1_lattices(sK11),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK11)),u1_struct_0(sK11))))
    | ~ spl13_64 ),
    inference(avatar_component_clause,[],[f446])).

fof(f448,plain,
    ( spl13_64
    | ~ spl13_10 ),
    inference(avatar_split_clause,[],[f431,f205,f446])).

fof(f205,plain,
    ( spl13_10
  <=> l1_lattices(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f431,plain,
    ( m1_subset_1(u1_lattices(sK11),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK11)),u1_struct_0(sK11))))
    | ~ spl13_10 ),
    inference(unit_resulting_resolution,[],[f206,f132])).

fof(f206,plain,
    ( l1_lattices(sK11)
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f205])).

fof(f441,plain,
    ( spl13_62
    | ~ spl13_28 ),
    inference(avatar_split_clause,[],[f416,f272,f439])).

fof(f439,plain,
    ( spl13_62
  <=> v1_funct_2(u2_lattices(sK10),k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK10)),u1_struct_0(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_62])])).

fof(f272,plain,
    ( spl13_28
  <=> l2_lattices(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_28])])).

fof(f416,plain,
    ( v1_funct_2(u2_lattices(sK10),k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK10)),u1_struct_0(sK10))
    | ~ spl13_28 ),
    inference(unit_resulting_resolution,[],[f273,f134])).

fof(f134,plain,(
    ! [X0] :
      ( v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f273,plain,
    ( l2_lattices(sK10)
    | ~ spl13_28 ),
    inference(avatar_component_clause,[],[f272])).

fof(f430,plain,
    ( spl13_60
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f415,f258,f428])).

fof(f428,plain,
    ( spl13_60
  <=> v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_60])])).

fof(f415,plain,
    ( v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f259,f134])).

fof(f423,plain,
    ( spl13_58
    | ~ spl13_12 ),
    inference(avatar_split_clause,[],[f414,f212,f421])).

fof(f421,plain,
    ( spl13_58
  <=> v1_funct_2(u2_lattices(sK12),k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)),u1_struct_0(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_58])])).

fof(f414,plain,
    ( v1_funct_2(u2_lattices(sK12),k2_zfmisc_1(u1_struct_0(sK12),u1_struct_0(sK12)),u1_struct_0(sK12))
    | ~ spl13_12 ),
    inference(unit_resulting_resolution,[],[f213,f134])).

fof(f413,plain,
    ( spl13_56
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f392,f265,f411])).

fof(f411,plain,
    ( spl13_56
  <=> v1_funct_2(u1_lattices(sK10),k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK10)),u1_struct_0(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_56])])).

fof(f265,plain,
    ( spl13_26
  <=> l1_lattices(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).

fof(f392,plain,
    ( v1_funct_2(u1_lattices(sK10),k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK10)),u1_struct_0(sK10))
    | ~ spl13_26 ),
    inference(unit_resulting_resolution,[],[f266,f131])).

fof(f131,plain,(
    ! [X0] :
      ( v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f266,plain,
    ( l1_lattices(sK10)
    | ~ spl13_26 ),
    inference(avatar_component_clause,[],[f265])).

fof(f406,plain,
    ( spl13_54
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f391,f249,f404])).

fof(f391,plain,
    ( v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl13_22 ),
    inference(unit_resulting_resolution,[],[f250,f131])).

fof(f399,plain,
    ( spl13_52
    | ~ spl13_10 ),
    inference(avatar_split_clause,[],[f390,f205,f397])).

fof(f397,plain,
    ( spl13_52
  <=> v1_funct_2(u1_lattices(sK11),k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK11)),u1_struct_0(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_52])])).

fof(f390,plain,
    ( v1_funct_2(u1_lattices(sK11),k2_zfmisc_1(u1_struct_0(sK11),u1_struct_0(sK11)),u1_struct_0(sK11))
    | ~ spl13_10 ),
    inference(unit_resulting_resolution,[],[f206,f131])).

fof(f363,plain,(
    spl13_50 ),
    inference(avatar_split_clause,[],[f121,f361])).

fof(f121,plain,(
    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,
    ( sK2 != sK3
    & k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3)
    & k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3)
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v11_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f49,f92,f91,f90,f89])).

fof(f89,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( X2 != X3
                    & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                    & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
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
                  ( X2 != X3
                  & k3_lattices(sK0,X1,X2) = k3_lattices(sK0,X1,X3)
                  & k4_lattices(sK0,X1,X2) = k4_lattices(sK0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v11_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f90,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                  & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( X2 != X3
                & k3_lattices(X0,sK1,X2) = k3_lattices(X0,sK1,X3)
                & k4_lattices(X0,sK1,X2) = k4_lattices(X0,sK1,X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
              & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( sK2 != X3
            & k3_lattices(X0,X1,sK2) = k3_lattices(X0,X1,X3)
            & k4_lattices(X0,X1,sK2) = k4_lattices(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( X2 != X3
          & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
          & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sK3 != X2
        & k3_lattices(X0,X1,sK3) = k3_lattices(X0,X1,X2)
        & k4_lattices(X0,X1,sK3) = k4_lattices(X0,X1,X2)
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                  & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v11_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                  & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v11_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
                   => ( ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                        & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) )
                     => X2 = X3 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
                 => ( ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                      & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) )
                   => X2 = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',t32_lattices)).

fof(f356,plain,(
    spl13_48 ),
    inference(avatar_split_clause,[],[f120,f354])).

fof(f120,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f93])).

fof(f346,plain,
    ( spl13_46
    | spl13_1
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f339,f191,f177,f170,f344])).

fof(f177,plain,
    ( spl13_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f339,plain,
    ( v9_lattices(sK0)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(unit_resulting_resolution,[],[f192,f171,f178,f129])).

fof(f129,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f41])).

fof(f41,axiom,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',cc1_lattices)).

fof(f178,plain,
    ( v10_lattices(sK0)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f177])).

fof(f338,plain,
    ( spl13_44
    | spl13_1
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f331,f191,f177,f170,f336])).

fof(f331,plain,
    ( v6_lattices(sK0)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(unit_resulting_resolution,[],[f192,f171,f178,f128])).

fof(f128,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f330,plain,
    ( spl13_42
    | spl13_1
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f323,f191,f177,f170,f328])).

fof(f323,plain,
    ( v4_lattices(sK0)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(unit_resulting_resolution,[],[f192,f171,f178,f127])).

fof(f127,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f322,plain,
    ( spl13_40
    | ~ spl13_28 ),
    inference(avatar_split_clause,[],[f287,f272,f320])).

fof(f320,plain,
    ( spl13_40
  <=> v1_funct_1(u2_lattices(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_40])])).

fof(f287,plain,
    ( v1_funct_1(u2_lattices(sK10))
    | ~ spl13_28 ),
    inference(unit_resulting_resolution,[],[f273,f133])).

fof(f133,plain,(
    ! [X0] :
      ( v1_funct_1(u2_lattices(X0))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f315,plain,
    ( spl13_38
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f277,f265,f313])).

fof(f313,plain,
    ( spl13_38
  <=> v1_funct_1(u1_lattices(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_38])])).

fof(f277,plain,
    ( v1_funct_1(u1_lattices(sK10))
    | ~ spl13_26 ),
    inference(unit_resulting_resolution,[],[f266,f130])).

fof(f130,plain,(
    ! [X0] :
      ( v1_funct_1(u1_lattices(X0))
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f308,plain,
    ( spl13_36
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f286,f258,f306])).

fof(f306,plain,
    ( spl13_36
  <=> v1_funct_1(u2_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_36])])).

fof(f286,plain,
    ( v1_funct_1(u2_lattices(sK0))
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f259,f133])).

fof(f301,plain,
    ( spl13_34
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f276,f249,f299])).

fof(f276,plain,
    ( v1_funct_1(u1_lattices(sK0))
    | ~ spl13_22 ),
    inference(unit_resulting_resolution,[],[f250,f130])).

fof(f294,plain,
    ( spl13_32
    | ~ spl13_12 ),
    inference(avatar_split_clause,[],[f285,f212,f292])).

fof(f292,plain,
    ( spl13_32
  <=> v1_funct_1(u2_lattices(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_32])])).

fof(f285,plain,
    ( v1_funct_1(u2_lattices(sK12))
    | ~ spl13_12 ),
    inference(unit_resulting_resolution,[],[f213,f133])).

fof(f284,plain,
    ( spl13_30
    | ~ spl13_10 ),
    inference(avatar_split_clause,[],[f275,f205,f282])).

fof(f282,plain,
    ( spl13_30
  <=> v1_funct_1(u1_lattices(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_30])])).

fof(f275,plain,
    ( v1_funct_1(u1_lattices(sK11))
    | ~ spl13_10 ),
    inference(unit_resulting_resolution,[],[f206,f130])).

fof(f274,plain,
    ( spl13_28
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f253,f198,f272])).

fof(f198,plain,
    ( spl13_8
  <=> l3_lattices(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f253,plain,
    ( l2_lattices(sK10)
    | ~ spl13_8 ),
    inference(unit_resulting_resolution,[],[f199,f125])).

fof(f125,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',dt_l3_lattices)).

fof(f199,plain,
    ( l3_lattices(sK10)
    | ~ spl13_8 ),
    inference(avatar_component_clause,[],[f198])).

fof(f267,plain,
    ( spl13_26
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f244,f198,f265])).

fof(f244,plain,
    ( l1_lattices(sK10)
    | ~ spl13_8 ),
    inference(unit_resulting_resolution,[],[f199,f124])).

fof(f124,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f260,plain,
    ( spl13_24
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f252,f191,f258])).

fof(f252,plain,
    ( l2_lattices(sK0)
    | ~ spl13_6 ),
    inference(unit_resulting_resolution,[],[f192,f125])).

fof(f251,plain,
    ( spl13_22
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f243,f191,f249])).

fof(f243,plain,
    ( l1_lattices(sK0)
    | ~ spl13_6 ),
    inference(unit_resulting_resolution,[],[f192,f124])).

fof(f242,plain,(
    spl13_20 ),
    inference(avatar_split_clause,[],[f119,f240])).

fof(f119,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f93])).

fof(f235,plain,(
    spl13_18 ),
    inference(avatar_split_clause,[],[f118,f233])).

fof(f118,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f93])).

fof(f228,plain,(
    spl13_16 ),
    inference(avatar_split_clause,[],[f117,f226])).

fof(f117,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f93])).

fof(f221,plain,(
    ~ spl13_15 ),
    inference(avatar_split_clause,[],[f122,f219])).

fof(f122,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f93])).

fof(f214,plain,(
    spl13_12 ),
    inference(avatar_split_clause,[],[f165,f212])).

fof(f165,plain,(
    l2_lattices(sK12) ),
    inference(cnf_transformation,[],[f112])).

fof(f112,plain,(
    l2_lattices(sK12) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f27,f111])).

fof(f111,plain,
    ( ? [X0] : l2_lattices(X0)
   => l2_lattices(sK12) ),
    introduced(choice_axiom,[])).

fof(f27,axiom,(
    ? [X0] : l2_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',existence_l2_lattices)).

fof(f207,plain,(
    spl13_10 ),
    inference(avatar_split_clause,[],[f164,f205])).

fof(f164,plain,(
    l1_lattices(sK11) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,plain,(
    l1_lattices(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f25,f109])).

fof(f109,plain,
    ( ? [X0] : l1_lattices(X0)
   => l1_lattices(sK11) ),
    introduced(choice_axiom,[])).

fof(f25,axiom,(
    ? [X0] : l1_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',existence_l1_lattices)).

fof(f200,plain,(
    spl13_8 ),
    inference(avatar_split_clause,[],[f163,f198])).

fof(f163,plain,(
    l3_lattices(sK10) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,plain,(
    l3_lattices(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f28,f107])).

fof(f107,plain,
    ( ? [X0] : l3_lattices(X0)
   => l3_lattices(sK10) ),
    introduced(choice_axiom,[])).

fof(f28,axiom,(
    ? [X0] : l3_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t32_lattices.p',existence_l3_lattices)).

fof(f193,plain,(
    spl13_6 ),
    inference(avatar_split_clause,[],[f116,f191])).

fof(f116,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f93])).

fof(f186,plain,(
    spl13_4 ),
    inference(avatar_split_clause,[],[f115,f184])).

fof(f115,plain,(
    v11_lattices(sK0) ),
    inference(cnf_transformation,[],[f93])).

fof(f179,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f114,f177])).

fof(f114,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f93])).

fof(f172,plain,(
    ~ spl13_1 ),
    inference(avatar_split_clause,[],[f113,f170])).

fof(f113,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f93])).
%------------------------------------------------------------------------------
