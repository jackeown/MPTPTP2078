%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  204 ( 356 expanded)
%              Number of leaves         :   53 ( 172 expanded)
%              Depth                    :    7
%              Number of atoms          :  537 ( 939 expanded)
%              Number of equality atoms :   95 ( 168 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4872,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f71,f75,f80,f85,f89,f93,f97,f101,f105,f118,f125,f132,f141,f220,f235,f345,f499,f503,f512,f551,f582,f588,f599,f689,f863,f1051,f1738,f2149,f2316,f2438,f3242,f3330,f3592,f4625,f4662,f4696,f4841])).

fof(f4841,plain,
    ( ~ spl2_4
    | spl2_26
    | ~ spl2_162 ),
    inference(avatar_contradiction_clause,[],[f4830])).

fof(f4830,plain,
    ( $false
    | ~ spl2_4
    | spl2_26
    | ~ spl2_162 ),
    inference(subsumption_resolution,[],[f234,f4778])).

fof(f4778,plain,
    ( ! [X1] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X1)),X1)
    | ~ spl2_4
    | ~ spl2_162 ),
    inference(superposition,[],[f4695,f70])).

fof(f70,plain,
    ( ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl2_4
  <=> ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f4695,plain,
    ( ! [X6] : k1_xboole_0 = k6_subset_1(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X6)),X6),k1_xboole_0)
    | ~ spl2_162 ),
    inference(avatar_component_clause,[],[f4694])).

fof(f4694,plain,
    ( spl2_162
  <=> ! [X6] : k1_xboole_0 = k6_subset_1(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X6)),X6),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_162])])).

fof(f234,plain,
    ( k1_xboole_0 != k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | spl2_26 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl2_26
  <=> k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f4696,plain,
    ( spl2_162
    | ~ spl2_11
    | ~ spl2_159 ),
    inference(avatar_split_clause,[],[f4671,f4660,f99,f4694])).

fof(f99,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k6_subset_1(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f4660,plain,
    ( spl2_159
  <=> ! [X11] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_159])])).

fof(f4671,plain,
    ( ! [X6] : k1_xboole_0 = k6_subset_1(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X6)),X6),k1_xboole_0)
    | ~ spl2_11
    | ~ spl2_159 ),
    inference(resolution,[],[f4661,f100])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k6_subset_1(X0,X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f99])).

fof(f4661,plain,
    ( ! [X11] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_xboole_0)
    | ~ spl2_159 ),
    inference(avatar_component_clause,[],[f4660])).

fof(f4662,plain,
    ( spl2_159
    | ~ spl2_46
    | ~ spl2_67
    | ~ spl2_146
    | ~ spl2_158 ),
    inference(avatar_split_clause,[],[f4658,f4623,f3589,f861,f586,f4660])).

fof(f586,plain,
    ( spl2_46
  <=> ! [X5,X6] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X5),X6),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f861,plain,
    ( spl2_67
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).

fof(f3589,plain,
    ( spl2_146
  <=> k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_146])])).

fof(f4623,plain,
    ( spl2_158
  <=> ! [X0] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_158])])).

fof(f4658,plain,
    ( ! [X11] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_xboole_0)
    | ~ spl2_46
    | ~ spl2_67
    | ~ spl2_146
    | ~ spl2_158 ),
    inference(forward_demodulation,[],[f4657,f3591])).

fof(f3591,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl2_146 ),
    inference(avatar_component_clause,[],[f3589])).

fof(f4657,plain,
    ( ! [X11] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k10_relat_1(sK1,k1_xboole_0))
    | ~ spl2_46
    | ~ spl2_67
    | ~ spl2_158 ),
    inference(subsumption_resolution,[],[f4643,f587])).

fof(f587,plain,
    ( ! [X6,X5] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X5),X6),k1_relat_1(sK1))
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f586])).

fof(f4643,plain,
    ( ! [X11] :
        ( r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k10_relat_1(sK1,k1_xboole_0))
        | ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_relat_1(sK1)) )
    | ~ spl2_67
    | ~ spl2_158 ),
    inference(superposition,[],[f862,f4624])).

fof(f4624,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0))
    | ~ spl2_158 ),
    inference(avatar_component_clause,[],[f4623])).

fof(f862,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))
        | ~ r1_tarski(X0,k1_relat_1(sK1)) )
    | ~ spl2_67 ),
    inference(avatar_component_clause,[],[f861])).

fof(f4625,plain,
    ( spl2_158
    | ~ spl2_47
    | ~ spl2_144 ),
    inference(avatar_split_clause,[],[f4023,f3328,f597,f4623])).

fof(f597,plain,
    ( spl2_47
  <=> ! [X0] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f3328,plain,
    ( spl2_144
  <=> ! [X1,X0] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_144])])).

fof(f4023,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0))
    | ~ spl2_47
    | ~ spl2_144 ),
    inference(superposition,[],[f3329,f598])).

fof(f598,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f597])).

fof(f3329,plain,
    ( ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
    | ~ spl2_144 ),
    inference(avatar_component_clause,[],[f3328])).

fof(f3592,plain,
    ( spl2_146
    | ~ spl2_25
    | ~ spl2_114
    | ~ spl2_139 ),
    inference(avatar_split_clause,[],[f3390,f3240,f2314,f218,f3589])).

fof(f218,plain,
    ( spl2_25
  <=> ! [X9,X8] : k1_xboole_0 = k6_subset_1(X8,k2_xboole_0(X8,X9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f2314,plain,
    ( spl2_114
  <=> ! [X13,X12] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X12),k10_relat_1(sK1,k2_xboole_0(X12,X13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_114])])).

fof(f3240,plain,
    ( spl2_139
  <=> ! [X1,X0] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_139])])).

fof(f3390,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl2_25
    | ~ spl2_114
    | ~ spl2_139 ),
    inference(forward_demodulation,[],[f3332,f219])).

fof(f219,plain,
    ( ! [X8,X9] : k1_xboole_0 = k6_subset_1(X8,k2_xboole_0(X8,X9))
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f218])).

fof(f3332,plain,
    ( ! [X2,X1] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X1,k2_xboole_0(X1,X2)))
    | ~ spl2_114
    | ~ spl2_139 ),
    inference(superposition,[],[f3241,f2315])).

fof(f2315,plain,
    ( ! [X12,X13] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X12),k10_relat_1(sK1,k2_xboole_0(X12,X13)))
    | ~ spl2_114 ),
    inference(avatar_component_clause,[],[f2314])).

fof(f3241,plain,
    ( ! [X0,X1] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
    | ~ spl2_139 ),
    inference(avatar_component_clause,[],[f3240])).

fof(f3330,plain,
    ( spl2_144
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_118 ),
    inference(avatar_split_clause,[],[f2778,f2436,f64,f59,f54,f3328])).

fof(f54,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f59,plain,
    ( spl2_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f64,plain,
    ( spl2_3
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f2436,plain,
    ( spl2_118
  <=> ! [X1,X0,X2] :
        ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        | ~ v2_funct_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_118])])).

fof(f2778,plain,
    ( ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_118 ),
    inference(subsumption_resolution,[],[f2777,f56])).

fof(f56,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f2777,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_118 ),
    inference(subsumption_resolution,[],[f2776,f61])).

fof(f61,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f2776,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_3
    | ~ spl2_118 ),
    inference(resolution,[],[f2437,f66])).

fof(f66,plain,
    ( v2_funct_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f2437,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_funct_1(X2)
        | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl2_118 ),
    inference(avatar_component_clause,[],[f2436])).

fof(f3242,plain,
    ( spl2_139
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_100 ),
    inference(avatar_split_clause,[],[f2174,f1736,f59,f54,f3240])).

fof(f1736,plain,
    ( spl2_100
  <=> ! [X1,X0,X2] :
        ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_100])])).

fof(f2174,plain,
    ( ! [X0,X1] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_100 ),
    inference(subsumption_resolution,[],[f2173,f56])).

fof(f2173,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_2
    | ~ spl2_100 ),
    inference(resolution,[],[f1737,f61])).

fof(f1737,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        | ~ v1_relat_1(X2) )
    | ~ spl2_100 ),
    inference(avatar_component_clause,[],[f1736])).

fof(f2438,plain,(
    spl2_118 ),
    inference(avatar_split_clause,[],[f48,f2436])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(f2316,plain,
    ( spl2_114
    | ~ spl2_25
    | ~ spl2_106 ),
    inference(avatar_split_clause,[],[f2156,f2147,f218,f2314])).

fof(f2147,plain,
    ( spl2_106
  <=> ! [X1,X0] : k10_relat_1(sK1,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_106])])).

fof(f2156,plain,
    ( ! [X12,X13] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X12),k10_relat_1(sK1,k2_xboole_0(X12,X13)))
    | ~ spl2_25
    | ~ spl2_106 ),
    inference(superposition,[],[f219,f2148])).

fof(f2148,plain,
    ( ! [X0,X1] : k10_relat_1(sK1,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
    | ~ spl2_106 ),
    inference(avatar_component_clause,[],[f2147])).

fof(f2149,plain,
    ( spl2_106
    | ~ spl2_1
    | ~ spl2_78 ),
    inference(avatar_split_clause,[],[f1439,f1049,f54,f2147])).

fof(f1049,plain,
    ( spl2_78
  <=> ! [X1,X0,X2] :
        ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).

fof(f1439,plain,
    ( ! [X0,X1] : k10_relat_1(sK1,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
    | ~ spl2_1
    | ~ spl2_78 ),
    inference(resolution,[],[f1050,f56])).

fof(f1050,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
    | ~ spl2_78 ),
    inference(avatar_component_clause,[],[f1049])).

fof(f1738,plain,(
    spl2_100 ),
    inference(avatar_split_clause,[],[f47,f1736])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f1051,plain,(
    spl2_78 ),
    inference(avatar_split_clause,[],[f45,f1049])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(f863,plain,
    ( spl2_67
    | ~ spl2_1
    | ~ spl2_56 ),
    inference(avatar_split_clause,[],[f859,f687,f54,f861])).

fof(f687,plain,
    ( spl2_56
  <=> ! [X1,X0] :
        ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        | ~ r1_tarski(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f859,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) )
    | ~ spl2_1
    | ~ spl2_56 ),
    inference(resolution,[],[f688,f56])).

fof(f688,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(X0,k1_relat_1(X1))
        | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) )
    | ~ spl2_56 ),
    inference(avatar_component_clause,[],[f687])).

fof(f689,plain,(
    spl2_56 ),
    inference(avatar_split_clause,[],[f40,f687])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f599,plain,
    ( spl2_47
    | ~ spl2_11
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f583,f580,f99,f597])).

fof(f580,plain,
    ( spl2_45
  <=> ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f583,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
    | ~ spl2_11
    | ~ spl2_45 ),
    inference(resolution,[],[f581,f100])).

fof(f581,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f580])).

fof(f588,plain,
    ( spl2_46
    | ~ spl2_17
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f555,f549,f139,f586])).

fof(f139,plain,
    ( spl2_17
  <=> ! [X3,X2,X4] : r1_tarski(k6_subset_1(X2,X3),k2_xboole_0(X2,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f549,plain,
    ( spl2_42
  <=> ! [X16] : k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X16),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f555,plain,
    ( ! [X6,X5] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X5),X6),k1_relat_1(sK1))
    | ~ spl2_17
    | ~ spl2_42 ),
    inference(superposition,[],[f140,f550])).

fof(f550,plain,
    ( ! [X16] : k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X16),k1_relat_1(sK1))
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f549])).

fof(f140,plain,
    ( ! [X4,X2,X3] : r1_tarski(k6_subset_1(X2,X3),k2_xboole_0(X2,X4))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f139])).

fof(f582,plain,
    ( spl2_45
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f578,f343,f59,f54,f580])).

fof(f343,plain,
    ( spl2_34
  <=> ! [X1,X0] :
        ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f578,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f577,f56])).

fof(f577,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_2
    | ~ spl2_34 ),
    inference(resolution,[],[f344,f61])).

fof(f344,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f343])).

fof(f551,plain,
    ( spl2_42
    | ~ spl2_39
    | ~ spl2_41 ),
    inference(avatar_split_clause,[],[f540,f510,f501,f549])).

fof(f501,plain,
    ( spl2_39
  <=> ! [X3,X2] :
        ( k1_xboole_0 != k6_subset_1(X2,X3)
        | k2_xboole_0(X2,X3) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f510,plain,
    ( spl2_41
  <=> ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f540,plain,
    ( ! [X16] : k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X16),k1_relat_1(sK1))
    | ~ spl2_39
    | ~ spl2_41 ),
    inference(trivial_inequality_removal,[],[f539])).

fof(f539,plain,
    ( ! [X16] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X16),k1_relat_1(sK1)) )
    | ~ spl2_39
    | ~ spl2_41 ),
    inference(superposition,[],[f502,f511])).

fof(f511,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f510])).

fof(f502,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 != k6_subset_1(X2,X3)
        | k2_xboole_0(X2,X3) = X3 )
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f501])).

fof(f512,plain,
    ( spl2_41
    | ~ spl2_1
    | ~ spl2_38 ),
    inference(avatar_split_clause,[],[f508,f497,f54,f510])).

fof(f497,plain,
    ( spl2_38
  <=> ! [X7,X6] :
        ( k1_xboole_0 = k6_subset_1(k10_relat_1(X6,X7),k1_relat_1(X6))
        | ~ v1_relat_1(X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f508,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_38 ),
    inference(resolution,[],[f498,f56])).

fof(f498,plain,
    ( ! [X6,X7] :
        ( ~ v1_relat_1(X6)
        | k1_xboole_0 = k6_subset_1(k10_relat_1(X6,X7),k1_relat_1(X6)) )
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f497])).

fof(f503,plain,
    ( spl2_39
    | ~ spl2_9
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f195,f103,f91,f501])).

fof(f91,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f103,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f195,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 != k6_subset_1(X2,X3)
        | k2_xboole_0(X2,X3) = X3 )
    | ~ spl2_9
    | ~ spl2_12 ),
    inference(resolution,[],[f104,f92])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k6_subset_1(X0,X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f103])).

fof(f499,plain,
    ( spl2_38
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f156,f99,f87,f497])).

fof(f87,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f156,plain,
    ( ! [X6,X7] :
        ( k1_xboole_0 = k6_subset_1(k10_relat_1(X6,X7),k1_relat_1(X6))
        | ~ v1_relat_1(X6) )
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(resolution,[],[f100,f88])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f345,plain,(
    spl2_34 ),
    inference(avatar_split_clause,[],[f42,f343])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f235,plain,
    ( ~ spl2_26
    | spl2_7
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f193,f103,f82,f232])).

fof(f82,plain,
    ( spl2_7
  <=> r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f193,plain,
    ( k1_xboole_0 != k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | spl2_7
    | ~ spl2_12 ),
    inference(resolution,[],[f104,f84])).

fof(f84,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f220,plain,
    ( spl2_25
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f157,f116,f99,f218])).

fof(f116,plain,
    ( spl2_14
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f157,plain,
    ( ! [X8,X9] : k1_xboole_0 = k6_subset_1(X8,k2_xboole_0(X8,X9))
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(resolution,[],[f100,f117])).

fof(f117,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f116])).

fof(f141,plain,
    ( spl2_17
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f136,f130,f123,f139])).

fof(f123,plain,
    ( spl2_15
  <=> ! [X1,X0] : k2_xboole_0(k6_subset_1(X0,X1),X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f130,plain,
    ( spl2_16
  <=> ! [X3,X2,X4] : r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f136,plain,
    ( ! [X4,X2,X3] : r1_tarski(k6_subset_1(X2,X3),k2_xboole_0(X2,X4))
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(superposition,[],[f131,f124])).

fof(f124,plain,
    ( ! [X0,X1] : k2_xboole_0(k6_subset_1(X0,X1),X0) = X0
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f123])).

fof(f131,plain,
    ( ! [X4,X2,X3] : r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f130])).

fof(f132,plain,
    ( spl2_16
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f120,f116,f95,f130])).

fof(f95,plain,
    ( spl2_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f120,plain,
    ( ! [X4,X2,X3] : r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4))
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(resolution,[],[f117,f96])).

fof(f96,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
        | r1_tarski(X0,X2) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f95])).

fof(f125,plain,
    ( spl2_15
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f106,f91,f73,f123])).

fof(f73,plain,
    ( spl2_5
  <=> ! [X1,X0] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f106,plain,
    ( ! [X0,X1] : k2_xboole_0(k6_subset_1(X0,X1),X0) = X0
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(resolution,[],[f92,f74])).

fof(f74,plain,
    ( ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f118,plain,
    ( spl2_14
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f113,f95,f78,f116])).

fof(f78,plain,
    ( spl2_6
  <=> ! [X0] : r1_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f113,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(resolution,[],[f96,f79])).

fof(f79,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f105,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f52,f103])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f101,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f51,f99])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f38])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f97,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f46,f95])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f93,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f41,f91])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f89,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f39,f87])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f85,plain,(
    ~ spl2_7 ),
    inference(avatar_split_clause,[],[f35,f82])).

fof(f35,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(f80,plain,
    ( spl2_6
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f76,f73,f69,f78])).

fof(f76,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(superposition,[],[f74,f70])).

fof(f75,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f50,f73])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f71,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f49,f69])).

fof(f49,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f36,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f67,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f34,f64])).

fof(f34,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f33,f59])).

fof(f33,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f32,f54])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:45:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (15886)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (15884)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.46  % (15876)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (15873)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (15874)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (15880)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (15878)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (15889)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.47  % (15875)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (15879)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (15885)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % (15881)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (15887)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (15883)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % (15890)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (15888)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (15882)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.52  % (15877)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.65  % (15880)Refutation found. Thanks to Tanya!
% 0.20/0.65  % SZS status Theorem for theBenchmark
% 0.20/0.65  % SZS output start Proof for theBenchmark
% 0.20/0.65  fof(f4872,plain,(
% 0.20/0.65    $false),
% 0.20/0.65    inference(avatar_sat_refutation,[],[f57,f62,f67,f71,f75,f80,f85,f89,f93,f97,f101,f105,f118,f125,f132,f141,f220,f235,f345,f499,f503,f512,f551,f582,f588,f599,f689,f863,f1051,f1738,f2149,f2316,f2438,f3242,f3330,f3592,f4625,f4662,f4696,f4841])).
% 0.20/0.65  fof(f4841,plain,(
% 0.20/0.65    ~spl2_4 | spl2_26 | ~spl2_162),
% 0.20/0.65    inference(avatar_contradiction_clause,[],[f4830])).
% 0.20/0.65  fof(f4830,plain,(
% 0.20/0.65    $false | (~spl2_4 | spl2_26 | ~spl2_162)),
% 0.20/0.65    inference(subsumption_resolution,[],[f234,f4778])).
% 0.20/0.65  fof(f4778,plain,(
% 0.20/0.65    ( ! [X1] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X1)),X1)) ) | (~spl2_4 | ~spl2_162)),
% 0.20/0.65    inference(superposition,[],[f4695,f70])).
% 0.20/0.65  fof(f70,plain,(
% 0.20/0.65    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) ) | ~spl2_4),
% 0.20/0.65    inference(avatar_component_clause,[],[f69])).
% 0.20/0.65  fof(f69,plain,(
% 0.20/0.65    spl2_4 <=> ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.65  fof(f4695,plain,(
% 0.20/0.65    ( ! [X6] : (k1_xboole_0 = k6_subset_1(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X6)),X6),k1_xboole_0)) ) | ~spl2_162),
% 0.20/0.65    inference(avatar_component_clause,[],[f4694])).
% 0.20/0.65  fof(f4694,plain,(
% 0.20/0.65    spl2_162 <=> ! [X6] : k1_xboole_0 = k6_subset_1(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X6)),X6),k1_xboole_0)),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_162])])).
% 0.20/0.65  fof(f234,plain,(
% 0.20/0.65    k1_xboole_0 != k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) | spl2_26),
% 0.20/0.65    inference(avatar_component_clause,[],[f232])).
% 0.20/0.65  fof(f232,plain,(
% 0.20/0.65    spl2_26 <=> k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.20/0.65  fof(f4696,plain,(
% 0.20/0.65    spl2_162 | ~spl2_11 | ~spl2_159),
% 0.20/0.65    inference(avatar_split_clause,[],[f4671,f4660,f99,f4694])).
% 0.20/0.65  fof(f99,plain,(
% 0.20/0.65    spl2_11 <=> ! [X1,X0] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1))),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.65  fof(f4660,plain,(
% 0.20/0.65    spl2_159 <=> ! [X11] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_xboole_0)),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_159])])).
% 0.20/0.65  fof(f4671,plain,(
% 0.20/0.65    ( ! [X6] : (k1_xboole_0 = k6_subset_1(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X6)),X6),k1_xboole_0)) ) | (~spl2_11 | ~spl2_159)),
% 0.20/0.65    inference(resolution,[],[f4661,f100])).
% 0.20/0.65  fof(f100,plain,(
% 0.20/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) ) | ~spl2_11),
% 0.20/0.65    inference(avatar_component_clause,[],[f99])).
% 0.20/0.65  fof(f4661,plain,(
% 0.20/0.65    ( ! [X11] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_xboole_0)) ) | ~spl2_159),
% 0.20/0.65    inference(avatar_component_clause,[],[f4660])).
% 0.20/0.65  fof(f4662,plain,(
% 0.20/0.65    spl2_159 | ~spl2_46 | ~spl2_67 | ~spl2_146 | ~spl2_158),
% 0.20/0.65    inference(avatar_split_clause,[],[f4658,f4623,f3589,f861,f586,f4660])).
% 0.20/0.65  fof(f586,plain,(
% 0.20/0.65    spl2_46 <=> ! [X5,X6] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X5),X6),k1_relat_1(sK1))),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 0.20/0.65  fof(f861,plain,(
% 0.20/0.65    spl2_67 <=> ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))))),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).
% 0.20/0.65  fof(f3589,plain,(
% 0.20/0.65    spl2_146 <=> k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_146])])).
% 0.20/0.65  fof(f4623,plain,(
% 0.20/0.65    spl2_158 <=> ! [X0] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0))),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_158])])).
% 0.20/0.65  fof(f4658,plain,(
% 0.20/0.65    ( ! [X11] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_xboole_0)) ) | (~spl2_46 | ~spl2_67 | ~spl2_146 | ~spl2_158)),
% 0.20/0.65    inference(forward_demodulation,[],[f4657,f3591])).
% 0.20/0.65  fof(f3591,plain,(
% 0.20/0.65    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) | ~spl2_146),
% 0.20/0.65    inference(avatar_component_clause,[],[f3589])).
% 0.20/0.65  fof(f4657,plain,(
% 0.20/0.65    ( ! [X11] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k10_relat_1(sK1,k1_xboole_0))) ) | (~spl2_46 | ~spl2_67 | ~spl2_158)),
% 0.20/0.65    inference(subsumption_resolution,[],[f4643,f587])).
% 0.20/0.65  fof(f587,plain,(
% 0.20/0.65    ( ! [X6,X5] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,X5),X6),k1_relat_1(sK1))) ) | ~spl2_46),
% 0.20/0.65    inference(avatar_component_clause,[],[f586])).
% 0.20/0.65  fof(f4643,plain,(
% 0.20/0.65    ( ! [X11] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k10_relat_1(sK1,k1_xboole_0)) | ~r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X11)),X11),k1_relat_1(sK1))) ) | (~spl2_67 | ~spl2_158)),
% 0.20/0.65    inference(superposition,[],[f862,f4624])).
% 0.20/0.65  fof(f4624,plain,(
% 0.20/0.65    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0))) ) | ~spl2_158),
% 0.20/0.65    inference(avatar_component_clause,[],[f4623])).
% 0.20/0.65  fof(f862,plain,(
% 0.20/0.65    ( ! [X0] : (r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) | ~r1_tarski(X0,k1_relat_1(sK1))) ) | ~spl2_67),
% 0.20/0.65    inference(avatar_component_clause,[],[f861])).
% 0.20/0.65  fof(f4625,plain,(
% 0.20/0.65    spl2_158 | ~spl2_47 | ~spl2_144),
% 0.20/0.65    inference(avatar_split_clause,[],[f4023,f3328,f597,f4623])).
% 0.20/0.65  fof(f597,plain,(
% 0.20/0.65    spl2_47 <=> ! [X0] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 0.20/0.65  fof(f3328,plain,(
% 0.20/0.65    spl2_144 <=> ! [X1,X0] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_144])])).
% 0.20/0.65  fof(f4023,plain,(
% 0.20/0.65    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0))) ) | (~spl2_47 | ~spl2_144)),
% 0.20/0.65    inference(superposition,[],[f3329,f598])).
% 0.20/0.65  fof(f598,plain,(
% 0.20/0.65    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) ) | ~spl2_47),
% 0.20/0.65    inference(avatar_component_clause,[],[f597])).
% 0.20/0.65  fof(f3329,plain,(
% 0.20/0.65    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) ) | ~spl2_144),
% 0.20/0.65    inference(avatar_component_clause,[],[f3328])).
% 0.20/0.65  fof(f3592,plain,(
% 0.20/0.65    spl2_146 | ~spl2_25 | ~spl2_114 | ~spl2_139),
% 0.20/0.65    inference(avatar_split_clause,[],[f3390,f3240,f2314,f218,f3589])).
% 0.20/0.65  fof(f218,plain,(
% 0.20/0.65    spl2_25 <=> ! [X9,X8] : k1_xboole_0 = k6_subset_1(X8,k2_xboole_0(X8,X9))),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.20/0.65  fof(f2314,plain,(
% 0.20/0.65    spl2_114 <=> ! [X13,X12] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X12),k10_relat_1(sK1,k2_xboole_0(X12,X13)))),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_114])])).
% 0.20/0.65  fof(f3240,plain,(
% 0.20/0.65    spl2_139 <=> ! [X1,X0] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_139])])).
% 0.20/0.65  fof(f3390,plain,(
% 0.20/0.65    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) | (~spl2_25 | ~spl2_114 | ~spl2_139)),
% 0.20/0.65    inference(forward_demodulation,[],[f3332,f219])).
% 0.20/0.65  fof(f219,plain,(
% 0.20/0.65    ( ! [X8,X9] : (k1_xboole_0 = k6_subset_1(X8,k2_xboole_0(X8,X9))) ) | ~spl2_25),
% 0.20/0.65    inference(avatar_component_clause,[],[f218])).
% 0.20/0.65  fof(f3332,plain,(
% 0.20/0.65    ( ! [X2,X1] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X1,k2_xboole_0(X1,X2)))) ) | (~spl2_114 | ~spl2_139)),
% 0.20/0.65    inference(superposition,[],[f3241,f2315])).
% 0.20/0.65  fof(f2315,plain,(
% 0.20/0.65    ( ! [X12,X13] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X12),k10_relat_1(sK1,k2_xboole_0(X12,X13)))) ) | ~spl2_114),
% 0.20/0.65    inference(avatar_component_clause,[],[f2314])).
% 0.20/0.65  fof(f3241,plain,(
% 0.20/0.65    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) ) | ~spl2_139),
% 0.20/0.65    inference(avatar_component_clause,[],[f3240])).
% 0.20/0.65  fof(f3330,plain,(
% 0.20/0.65    spl2_144 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_118),
% 0.20/0.65    inference(avatar_split_clause,[],[f2778,f2436,f64,f59,f54,f3328])).
% 0.20/0.65  fof(f54,plain,(
% 0.20/0.65    spl2_1 <=> v1_relat_1(sK1)),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.65  fof(f59,plain,(
% 0.20/0.65    spl2_2 <=> v1_funct_1(sK1)),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.65  fof(f64,plain,(
% 0.20/0.65    spl2_3 <=> v2_funct_1(sK1)),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.65  fof(f2436,plain,(
% 0.20/0.65    spl2_118 <=> ! [X1,X0,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_118])])).
% 0.20/0.65  fof(f2778,plain,(
% 0.20/0.65    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_118)),
% 0.20/0.65    inference(subsumption_resolution,[],[f2777,f56])).
% 0.20/0.65  fof(f56,plain,(
% 0.20/0.65    v1_relat_1(sK1) | ~spl2_1),
% 0.20/0.65    inference(avatar_component_clause,[],[f54])).
% 0.20/0.65  fof(f2777,plain,(
% 0.20/0.65    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) ) | (~spl2_2 | ~spl2_3 | ~spl2_118)),
% 0.20/0.65    inference(subsumption_resolution,[],[f2776,f61])).
% 0.20/0.65  fof(f61,plain,(
% 0.20/0.65    v1_funct_1(sK1) | ~spl2_2),
% 0.20/0.65    inference(avatar_component_clause,[],[f59])).
% 0.20/0.65  fof(f2776,plain,(
% 0.20/0.65    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | (~spl2_3 | ~spl2_118)),
% 0.20/0.65    inference(resolution,[],[f2437,f66])).
% 0.20/0.65  fof(f66,plain,(
% 0.20/0.65    v2_funct_1(sK1) | ~spl2_3),
% 0.20/0.65    inference(avatar_component_clause,[],[f64])).
% 0.20/0.65  fof(f2437,plain,(
% 0.20/0.65    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | ~spl2_118),
% 0.20/0.65    inference(avatar_component_clause,[],[f2436])).
% 0.20/0.65  fof(f3242,plain,(
% 0.20/0.65    spl2_139 | ~spl2_1 | ~spl2_2 | ~spl2_100),
% 0.20/0.65    inference(avatar_split_clause,[],[f2174,f1736,f59,f54,f3240])).
% 0.20/0.65  fof(f1736,plain,(
% 0.20/0.65    spl2_100 <=> ! [X1,X0,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_100])])).
% 0.20/0.65  fof(f2174,plain,(
% 0.20/0.65    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) ) | (~spl2_1 | ~spl2_2 | ~spl2_100)),
% 0.20/0.65    inference(subsumption_resolution,[],[f2173,f56])).
% 0.20/0.65  fof(f2173,plain,(
% 0.20/0.65    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) ) | (~spl2_2 | ~spl2_100)),
% 0.20/0.65    inference(resolution,[],[f1737,f61])).
% 0.20/0.65  fof(f1737,plain,(
% 0.20/0.65    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) ) | ~spl2_100),
% 0.20/0.65    inference(avatar_component_clause,[],[f1736])).
% 0.20/0.65  fof(f2438,plain,(
% 0.20/0.65    spl2_118),
% 0.20/0.65    inference(avatar_split_clause,[],[f48,f2436])).
% 0.20/0.65  fof(f48,plain,(
% 0.20/0.65    ( ! [X2,X0,X1] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.65    inference(cnf_transformation,[],[f28])).
% 0.20/0.65  fof(f28,plain,(
% 0.20/0.65    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.65    inference(flattening,[],[f27])).
% 0.20/0.65  fof(f27,plain,(
% 0.20/0.65    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.65    inference(ennf_transformation,[],[f9])).
% 0.20/0.65  fof(f9,axiom,(
% 0.20/0.65    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).
% 0.20/0.65  fof(f2316,plain,(
% 0.20/0.65    spl2_114 | ~spl2_25 | ~spl2_106),
% 0.20/0.65    inference(avatar_split_clause,[],[f2156,f2147,f218,f2314])).
% 0.20/0.65  fof(f2147,plain,(
% 0.20/0.65    spl2_106 <=> ! [X1,X0] : k10_relat_1(sK1,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_106])])).
% 0.20/0.65  fof(f2156,plain,(
% 0.20/0.65    ( ! [X12,X13] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X12),k10_relat_1(sK1,k2_xboole_0(X12,X13)))) ) | (~spl2_25 | ~spl2_106)),
% 0.20/0.65    inference(superposition,[],[f219,f2148])).
% 0.20/0.65  fof(f2148,plain,(
% 0.20/0.65    ( ! [X0,X1] : (k10_relat_1(sK1,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) ) | ~spl2_106),
% 0.20/0.65    inference(avatar_component_clause,[],[f2147])).
% 0.20/0.65  fof(f2149,plain,(
% 0.20/0.65    spl2_106 | ~spl2_1 | ~spl2_78),
% 0.20/0.65    inference(avatar_split_clause,[],[f1439,f1049,f54,f2147])).
% 0.20/0.65  fof(f1049,plain,(
% 0.20/0.65    spl2_78 <=> ! [X1,X0,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).
% 0.20/0.65  fof(f1439,plain,(
% 0.20/0.65    ( ! [X0,X1] : (k10_relat_1(sK1,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) ) | (~spl2_1 | ~spl2_78)),
% 0.20/0.65    inference(resolution,[],[f1050,f56])).
% 0.20/0.65  fof(f1050,plain,(
% 0.20/0.65    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) | ~spl2_78),
% 0.20/0.65    inference(avatar_component_clause,[],[f1049])).
% 0.20/0.65  fof(f1738,plain,(
% 0.20/0.65    spl2_100),
% 0.20/0.65    inference(avatar_split_clause,[],[f47,f1736])).
% 0.20/0.65  fof(f47,plain,(
% 0.20/0.65    ( ! [X2,X0,X1] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.65    inference(cnf_transformation,[],[f26])).
% 0.20/0.65  fof(f26,plain,(
% 0.20/0.65    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.65    inference(flattening,[],[f25])).
% 0.20/0.65  fof(f25,plain,(
% 0.20/0.65    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.65    inference(ennf_transformation,[],[f10])).
% 0.20/0.65  fof(f10,axiom,(
% 0.20/0.65    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 0.20/0.65  fof(f1051,plain,(
% 0.20/0.65    spl2_78),
% 0.20/0.65    inference(avatar_split_clause,[],[f45,f1049])).
% 0.20/0.65  fof(f45,plain,(
% 0.20/0.65    ( ! [X2,X0,X1] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.20/0.65    inference(cnf_transformation,[],[f23])).
% 0.20/0.65  fof(f23,plain,(
% 0.20/0.65    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.20/0.65    inference(ennf_transformation,[],[f8])).
% 0.20/0.65  fof(f8,axiom,(
% 0.20/0.65    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
% 0.20/0.65  fof(f863,plain,(
% 0.20/0.65    spl2_67 | ~spl2_1 | ~spl2_56),
% 0.20/0.65    inference(avatar_split_clause,[],[f859,f687,f54,f861])).
% 0.20/0.65  fof(f687,plain,(
% 0.20/0.65    spl2_56 <=> ! [X1,X0] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 0.20/0.65  fof(f859,plain,(
% 0.20/0.65    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))) ) | (~spl2_1 | ~spl2_56)),
% 0.20/0.65    inference(resolution,[],[f688,f56])).
% 0.20/0.65  fof(f688,plain,(
% 0.20/0.65    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) ) | ~spl2_56),
% 0.20/0.65    inference(avatar_component_clause,[],[f687])).
% 0.20/0.65  fof(f689,plain,(
% 0.20/0.65    spl2_56),
% 0.20/0.65    inference(avatar_split_clause,[],[f40,f687])).
% 0.20/0.65  fof(f40,plain,(
% 0.20/0.65    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.65    inference(cnf_transformation,[],[f19])).
% 0.20/0.65  fof(f19,plain,(
% 0.20/0.65    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.65    inference(flattening,[],[f18])).
% 0.20/0.65  fof(f18,plain,(
% 0.20/0.65    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.65    inference(ennf_transformation,[],[f12])).
% 0.20/0.65  fof(f12,axiom,(
% 0.20/0.65    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 0.20/0.65  fof(f599,plain,(
% 0.20/0.65    spl2_47 | ~spl2_11 | ~spl2_45),
% 0.20/0.65    inference(avatar_split_clause,[],[f583,f580,f99,f597])).
% 0.20/0.65  fof(f580,plain,(
% 0.20/0.65    spl2_45 <=> ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 0.20/0.65  fof(f583,plain,(
% 0.20/0.65    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) ) | (~spl2_11 | ~spl2_45)),
% 0.20/0.65    inference(resolution,[],[f581,f100])).
% 0.20/0.65  fof(f581,plain,(
% 0.20/0.65    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) ) | ~spl2_45),
% 0.20/0.65    inference(avatar_component_clause,[],[f580])).
% 0.20/0.65  fof(f588,plain,(
% 0.20/0.65    spl2_46 | ~spl2_17 | ~spl2_42),
% 0.20/0.65    inference(avatar_split_clause,[],[f555,f549,f139,f586])).
% 0.20/0.65  fof(f139,plain,(
% 0.20/0.65    spl2_17 <=> ! [X3,X2,X4] : r1_tarski(k6_subset_1(X2,X3),k2_xboole_0(X2,X4))),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.20/0.65  fof(f549,plain,(
% 0.20/0.65    spl2_42 <=> ! [X16] : k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X16),k1_relat_1(sK1))),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 0.20/0.65  fof(f555,plain,(
% 0.20/0.65    ( ! [X6,X5] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,X5),X6),k1_relat_1(sK1))) ) | (~spl2_17 | ~spl2_42)),
% 0.20/0.65    inference(superposition,[],[f140,f550])).
% 0.20/0.65  fof(f550,plain,(
% 0.20/0.65    ( ! [X16] : (k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X16),k1_relat_1(sK1))) ) | ~spl2_42),
% 0.20/0.65    inference(avatar_component_clause,[],[f549])).
% 0.20/0.65  fof(f140,plain,(
% 0.20/0.65    ( ! [X4,X2,X3] : (r1_tarski(k6_subset_1(X2,X3),k2_xboole_0(X2,X4))) ) | ~spl2_17),
% 0.20/0.65    inference(avatar_component_clause,[],[f139])).
% 0.20/0.65  fof(f582,plain,(
% 0.20/0.65    spl2_45 | ~spl2_1 | ~spl2_2 | ~spl2_34),
% 0.20/0.65    inference(avatar_split_clause,[],[f578,f343,f59,f54,f580])).
% 0.20/0.65  fof(f343,plain,(
% 0.20/0.65    spl2_34 <=> ! [X1,X0] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.20/0.65  fof(f578,plain,(
% 0.20/0.65    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) ) | (~spl2_1 | ~spl2_2 | ~spl2_34)),
% 0.20/0.65    inference(subsumption_resolution,[],[f577,f56])).
% 0.20/0.65  fof(f577,plain,(
% 0.20/0.65    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) | ~v1_relat_1(sK1)) ) | (~spl2_2 | ~spl2_34)),
% 0.20/0.65    inference(resolution,[],[f344,f61])).
% 0.20/0.65  fof(f344,plain,(
% 0.20/0.65    ( ! [X0,X1] : (~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) ) | ~spl2_34),
% 0.20/0.65    inference(avatar_component_clause,[],[f343])).
% 0.20/0.65  fof(f551,plain,(
% 0.20/0.65    spl2_42 | ~spl2_39 | ~spl2_41),
% 0.20/0.65    inference(avatar_split_clause,[],[f540,f510,f501,f549])).
% 0.20/0.65  fof(f501,plain,(
% 0.20/0.65    spl2_39 <=> ! [X3,X2] : (k1_xboole_0 != k6_subset_1(X2,X3) | k2_xboole_0(X2,X3) = X3)),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 0.20/0.65  fof(f510,plain,(
% 0.20/0.65    spl2_41 <=> ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 0.20/0.65  fof(f540,plain,(
% 0.20/0.65    ( ! [X16] : (k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X16),k1_relat_1(sK1))) ) | (~spl2_39 | ~spl2_41)),
% 0.20/0.65    inference(trivial_inequality_removal,[],[f539])).
% 0.20/0.65  fof(f539,plain,(
% 0.20/0.65    ( ! [X16] : (k1_xboole_0 != k1_xboole_0 | k1_relat_1(sK1) = k2_xboole_0(k10_relat_1(sK1,X16),k1_relat_1(sK1))) ) | (~spl2_39 | ~spl2_41)),
% 0.20/0.65    inference(superposition,[],[f502,f511])).
% 0.20/0.65  fof(f511,plain,(
% 0.20/0.65    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))) ) | ~spl2_41),
% 0.20/0.65    inference(avatar_component_clause,[],[f510])).
% 0.20/0.65  fof(f502,plain,(
% 0.20/0.65    ( ! [X2,X3] : (k1_xboole_0 != k6_subset_1(X2,X3) | k2_xboole_0(X2,X3) = X3) ) | ~spl2_39),
% 0.20/0.65    inference(avatar_component_clause,[],[f501])).
% 0.20/0.65  fof(f512,plain,(
% 0.20/0.65    spl2_41 | ~spl2_1 | ~spl2_38),
% 0.20/0.65    inference(avatar_split_clause,[],[f508,f497,f54,f510])).
% 0.20/0.65  fof(f497,plain,(
% 0.20/0.65    spl2_38 <=> ! [X7,X6] : (k1_xboole_0 = k6_subset_1(k10_relat_1(X6,X7),k1_relat_1(X6)) | ~v1_relat_1(X6))),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 0.20/0.65  fof(f508,plain,(
% 0.20/0.65    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))) ) | (~spl2_1 | ~spl2_38)),
% 0.20/0.65    inference(resolution,[],[f498,f56])).
% 0.20/0.65  fof(f498,plain,(
% 0.20/0.65    ( ! [X6,X7] : (~v1_relat_1(X6) | k1_xboole_0 = k6_subset_1(k10_relat_1(X6,X7),k1_relat_1(X6))) ) | ~spl2_38),
% 0.20/0.65    inference(avatar_component_clause,[],[f497])).
% 0.20/0.65  fof(f503,plain,(
% 0.20/0.65    spl2_39 | ~spl2_9 | ~spl2_12),
% 0.20/0.65    inference(avatar_split_clause,[],[f195,f103,f91,f501])).
% 0.20/0.65  fof(f91,plain,(
% 0.20/0.65    spl2_9 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.65  fof(f103,plain,(
% 0.20/0.65    spl2_12 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1))),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.65  fof(f195,plain,(
% 0.20/0.65    ( ! [X2,X3] : (k1_xboole_0 != k6_subset_1(X2,X3) | k2_xboole_0(X2,X3) = X3) ) | (~spl2_9 | ~spl2_12)),
% 0.20/0.65    inference(resolution,[],[f104,f92])).
% 0.20/0.65  fof(f92,plain,(
% 0.20/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl2_9),
% 0.20/0.65    inference(avatar_component_clause,[],[f91])).
% 0.20/0.65  fof(f104,plain,(
% 0.20/0.65    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) ) | ~spl2_12),
% 0.20/0.65    inference(avatar_component_clause,[],[f103])).
% 0.20/0.65  fof(f499,plain,(
% 0.20/0.65    spl2_38 | ~spl2_8 | ~spl2_11),
% 0.20/0.65    inference(avatar_split_clause,[],[f156,f99,f87,f497])).
% 0.20/0.65  fof(f87,plain,(
% 0.20/0.65    spl2_8 <=> ! [X1,X0] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.65  fof(f156,plain,(
% 0.20/0.65    ( ! [X6,X7] : (k1_xboole_0 = k6_subset_1(k10_relat_1(X6,X7),k1_relat_1(X6)) | ~v1_relat_1(X6)) ) | (~spl2_8 | ~spl2_11)),
% 0.20/0.65    inference(resolution,[],[f100,f88])).
% 0.20/0.65  fof(f88,plain,(
% 0.20/0.65    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl2_8),
% 0.20/0.65    inference(avatar_component_clause,[],[f87])).
% 0.20/0.65  fof(f345,plain,(
% 0.20/0.65    spl2_34),
% 0.20/0.65    inference(avatar_split_clause,[],[f42,f343])).
% 0.20/0.65  fof(f42,plain,(
% 0.20/0.65    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.65    inference(cnf_transformation,[],[f22])).
% 0.20/0.65  fof(f22,plain,(
% 0.20/0.65    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.65    inference(flattening,[],[f21])).
% 0.20/0.65  fof(f21,plain,(
% 0.20/0.65    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.65    inference(ennf_transformation,[],[f11])).
% 0.20/0.65  fof(f11,axiom,(
% 0.20/0.65    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 0.20/0.65  fof(f235,plain,(
% 0.20/0.65    ~spl2_26 | spl2_7 | ~spl2_12),
% 0.20/0.65    inference(avatar_split_clause,[],[f193,f103,f82,f232])).
% 0.20/0.65  fof(f82,plain,(
% 0.20/0.65    spl2_7 <=> r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.65  fof(f193,plain,(
% 0.20/0.65    k1_xboole_0 != k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) | (spl2_7 | ~spl2_12)),
% 0.20/0.65    inference(resolution,[],[f104,f84])).
% 0.20/0.65  fof(f84,plain,(
% 0.20/0.65    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) | spl2_7),
% 0.20/0.65    inference(avatar_component_clause,[],[f82])).
% 0.20/0.65  fof(f220,plain,(
% 0.20/0.65    spl2_25 | ~spl2_11 | ~spl2_14),
% 0.20/0.65    inference(avatar_split_clause,[],[f157,f116,f99,f218])).
% 0.20/0.65  fof(f116,plain,(
% 0.20/0.65    spl2_14 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.65  fof(f157,plain,(
% 0.20/0.65    ( ! [X8,X9] : (k1_xboole_0 = k6_subset_1(X8,k2_xboole_0(X8,X9))) ) | (~spl2_11 | ~spl2_14)),
% 0.20/0.65    inference(resolution,[],[f100,f117])).
% 0.20/0.65  fof(f117,plain,(
% 0.20/0.65    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl2_14),
% 0.20/0.65    inference(avatar_component_clause,[],[f116])).
% 0.20/0.65  fof(f141,plain,(
% 0.20/0.65    spl2_17 | ~spl2_15 | ~spl2_16),
% 0.20/0.65    inference(avatar_split_clause,[],[f136,f130,f123,f139])).
% 0.20/0.65  fof(f123,plain,(
% 0.20/0.65    spl2_15 <=> ! [X1,X0] : k2_xboole_0(k6_subset_1(X0,X1),X0) = X0),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.65  fof(f130,plain,(
% 0.20/0.65    spl2_16 <=> ! [X3,X2,X4] : r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4))),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.65  fof(f136,plain,(
% 0.20/0.65    ( ! [X4,X2,X3] : (r1_tarski(k6_subset_1(X2,X3),k2_xboole_0(X2,X4))) ) | (~spl2_15 | ~spl2_16)),
% 0.20/0.65    inference(superposition,[],[f131,f124])).
% 0.20/0.65  fof(f124,plain,(
% 0.20/0.65    ( ! [X0,X1] : (k2_xboole_0(k6_subset_1(X0,X1),X0) = X0) ) | ~spl2_15),
% 0.20/0.65    inference(avatar_component_clause,[],[f123])).
% 0.20/0.65  fof(f131,plain,(
% 0.20/0.65    ( ! [X4,X2,X3] : (r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4))) ) | ~spl2_16),
% 0.20/0.65    inference(avatar_component_clause,[],[f130])).
% 0.20/0.65  fof(f132,plain,(
% 0.20/0.65    spl2_16 | ~spl2_10 | ~spl2_14),
% 0.20/0.65    inference(avatar_split_clause,[],[f120,f116,f95,f130])).
% 0.20/0.65  fof(f95,plain,(
% 0.20/0.65    spl2_10 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.65  fof(f120,plain,(
% 0.20/0.65    ( ! [X4,X2,X3] : (r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4))) ) | (~spl2_10 | ~spl2_14)),
% 0.20/0.65    inference(resolution,[],[f117,f96])).
% 0.20/0.65  fof(f96,plain,(
% 0.20/0.65    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) ) | ~spl2_10),
% 0.20/0.65    inference(avatar_component_clause,[],[f95])).
% 0.20/0.65  fof(f125,plain,(
% 0.20/0.65    spl2_15 | ~spl2_5 | ~spl2_9),
% 0.20/0.65    inference(avatar_split_clause,[],[f106,f91,f73,f123])).
% 0.20/0.65  fof(f73,plain,(
% 0.20/0.65    spl2_5 <=> ! [X1,X0] : r1_tarski(k6_subset_1(X0,X1),X0)),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.65  fof(f106,plain,(
% 0.20/0.65    ( ! [X0,X1] : (k2_xboole_0(k6_subset_1(X0,X1),X0) = X0) ) | (~spl2_5 | ~spl2_9)),
% 0.20/0.65    inference(resolution,[],[f92,f74])).
% 0.20/0.65  fof(f74,plain,(
% 0.20/0.65    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) ) | ~spl2_5),
% 0.20/0.65    inference(avatar_component_clause,[],[f73])).
% 0.20/0.65  fof(f118,plain,(
% 0.20/0.65    spl2_14 | ~spl2_6 | ~spl2_10),
% 0.20/0.65    inference(avatar_split_clause,[],[f113,f95,f78,f116])).
% 0.20/0.65  fof(f78,plain,(
% 0.20/0.65    spl2_6 <=> ! [X0] : r1_tarski(X0,X0)),
% 0.20/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.65  fof(f113,plain,(
% 0.20/0.65    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | (~spl2_6 | ~spl2_10)),
% 0.20/0.65    inference(resolution,[],[f96,f79])).
% 0.20/0.65  fof(f79,plain,(
% 0.20/0.65    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl2_6),
% 0.20/0.65    inference(avatar_component_clause,[],[f78])).
% 0.20/0.65  fof(f105,plain,(
% 0.20/0.65    spl2_12),
% 0.20/0.65    inference(avatar_split_clause,[],[f52,f103])).
% 0.20/0.65  fof(f52,plain,(
% 0.20/0.65    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 0.20/0.65    inference(definition_unfolding,[],[f43,f38])).
% 0.20/0.65  fof(f38,plain,(
% 0.20/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.20/0.65    inference(cnf_transformation,[],[f6])).
% 0.20/0.65  fof(f6,axiom,(
% 0.20/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.20/0.65  fof(f43,plain,(
% 0.20/0.65    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.65    inference(cnf_transformation,[],[f31])).
% 0.20/0.65  fof(f31,plain,(
% 0.20/0.65    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.65    inference(nnf_transformation,[],[f1])).
% 0.20/0.65  fof(f1,axiom,(
% 0.20/0.65    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.65  fof(f101,plain,(
% 0.20/0.65    spl2_11),
% 0.20/0.65    inference(avatar_split_clause,[],[f51,f99])).
% 0.20/0.65  fof(f51,plain,(
% 0.20/0.65    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.65    inference(definition_unfolding,[],[f44,f38])).
% 0.20/0.65  fof(f44,plain,(
% 0.20/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.65    inference(cnf_transformation,[],[f31])).
% 0.20/0.65  fof(f97,plain,(
% 0.20/0.65    spl2_10),
% 0.20/0.65    inference(avatar_split_clause,[],[f46,f95])).
% 0.20/0.65  fof(f46,plain,(
% 0.20/0.65    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.20/0.65    inference(cnf_transformation,[],[f24])).
% 0.20/0.65  fof(f24,plain,(
% 0.20/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.65    inference(ennf_transformation,[],[f2])).
% 0.20/0.65  fof(f2,axiom,(
% 0.20/0.65    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.20/0.65  fof(f93,plain,(
% 0.20/0.65    spl2_9),
% 0.20/0.65    inference(avatar_split_clause,[],[f41,f91])).
% 0.20/0.65  fof(f41,plain,(
% 0.20/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.65    inference(cnf_transformation,[],[f20])).
% 0.20/0.65  fof(f20,plain,(
% 0.20/0.65    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.65    inference(ennf_transformation,[],[f3])).
% 0.20/0.65  fof(f3,axiom,(
% 0.20/0.65    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.65  fof(f89,plain,(
% 0.20/0.65    spl2_8),
% 0.20/0.65    inference(avatar_split_clause,[],[f39,f87])).
% 0.20/0.65  fof(f39,plain,(
% 0.20/0.65    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.65    inference(cnf_transformation,[],[f17])).
% 0.20/0.65  fof(f17,plain,(
% 0.20/0.65    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.65    inference(ennf_transformation,[],[f7])).
% 0.20/0.65  fof(f7,axiom,(
% 0.20/0.65    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 0.20/0.65  fof(f85,plain,(
% 0.20/0.65    ~spl2_7),
% 0.20/0.65    inference(avatar_split_clause,[],[f35,f82])).
% 0.20/0.65  fof(f35,plain,(
% 0.20/0.65    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 0.20/0.65    inference(cnf_transformation,[],[f30])).
% 0.20/0.65  fof(f30,plain,(
% 0.20/0.65    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.20/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f29])).
% 0.20/0.65  fof(f29,plain,(
% 0.20/0.65    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.65    introduced(choice_axiom,[])).
% 0.20/0.65  fof(f16,plain,(
% 0.20/0.65    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.65    inference(flattening,[],[f15])).
% 0.20/0.65  fof(f15,plain,(
% 0.20/0.65    ? [X0,X1] : ((~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.65    inference(ennf_transformation,[],[f14])).
% 0.20/0.65  fof(f14,negated_conjecture,(
% 0.20/0.65    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 0.20/0.65    inference(negated_conjecture,[],[f13])).
% 0.20/0.65  fof(f13,conjecture,(
% 0.20/0.65    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 0.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).
% 0.20/0.65  fof(f80,plain,(
% 0.20/0.65    spl2_6 | ~spl2_4 | ~spl2_5),
% 0.20/0.65    inference(avatar_split_clause,[],[f76,f73,f69,f78])).
% 0.20/0.65  fof(f76,plain,(
% 0.20/0.65    ( ! [X0] : (r1_tarski(X0,X0)) ) | (~spl2_4 | ~spl2_5)),
% 0.20/0.65    inference(superposition,[],[f74,f70])).
% 0.20/0.65  fof(f75,plain,(
% 0.20/0.65    spl2_5),
% 0.20/0.65    inference(avatar_split_clause,[],[f50,f73])).
% 0.20/0.65  fof(f50,plain,(
% 0.20/0.65    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 0.20/0.65    inference(definition_unfolding,[],[f37,f38])).
% 0.20/0.65  fof(f37,plain,(
% 0.20/0.65    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.65    inference(cnf_transformation,[],[f4])).
% 0.20/0.65  fof(f4,axiom,(
% 0.20/0.65    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.65  fof(f71,plain,(
% 0.20/0.65    spl2_4),
% 0.20/0.65    inference(avatar_split_clause,[],[f49,f69])).
% 0.20/0.65  fof(f49,plain,(
% 0.20/0.65    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 0.20/0.65    inference(definition_unfolding,[],[f36,f38])).
% 0.20/0.65  fof(f36,plain,(
% 0.20/0.65    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.65    inference(cnf_transformation,[],[f5])).
% 0.20/0.65  fof(f5,axiom,(
% 0.20/0.65    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.65  fof(f67,plain,(
% 0.20/0.65    spl2_3),
% 0.20/0.65    inference(avatar_split_clause,[],[f34,f64])).
% 0.20/0.65  fof(f34,plain,(
% 0.20/0.65    v2_funct_1(sK1)),
% 0.20/0.65    inference(cnf_transformation,[],[f30])).
% 0.20/0.65  fof(f62,plain,(
% 0.20/0.65    spl2_2),
% 0.20/0.65    inference(avatar_split_clause,[],[f33,f59])).
% 0.20/0.65  fof(f33,plain,(
% 0.20/0.65    v1_funct_1(sK1)),
% 0.20/0.65    inference(cnf_transformation,[],[f30])).
% 0.20/0.65  fof(f57,plain,(
% 0.20/0.65    spl2_1),
% 0.20/0.65    inference(avatar_split_clause,[],[f32,f54])).
% 0.20/0.65  fof(f32,plain,(
% 0.20/0.65    v1_relat_1(sK1)),
% 0.20/0.65    inference(cnf_transformation,[],[f30])).
% 0.20/0.65  % SZS output end Proof for theBenchmark
% 0.20/0.65  % (15880)------------------------------
% 0.20/0.65  % (15880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.65  % (15880)Termination reason: Refutation
% 0.20/0.65  
% 0.20/0.65  % (15880)Memory used [KB]: 9722
% 0.20/0.65  % (15880)Time elapsed: 0.188 s
% 0.20/0.65  % (15880)------------------------------
% 0.20/0.65  % (15880)------------------------------
% 0.20/0.65  % (15869)Success in time 0.293 s
%------------------------------------------------------------------------------
