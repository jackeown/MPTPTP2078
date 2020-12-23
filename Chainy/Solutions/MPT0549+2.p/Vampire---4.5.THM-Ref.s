%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0549+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:36 EST 2020

% Result     : Theorem 4.47s
% Output     : Refutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :  272 ( 449 expanded)
%              Number of leaves         :   76 ( 192 expanded)
%              Depth                    :   10
%              Number of atoms          :  614 ( 988 expanded)
%              Number of equality atoms :  130 ( 206 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4116,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1604,f1609,f1614,f1619,f1628,f1629,f1634,f1639,f1644,f1649,f1656,f1672,f1689,f1696,f1794,f1843,f1855,f1864,f1875,f2014,f2016,f2078,f2122,f2160,f2243,f2276,f2361,f2443,f2514,f2609,f2719,f2864,f2944,f3088,f3195,f3267,f3470,f3588,f3638,f3734,f3745,f3833,f3849,f3901,f3974,f3994,f4104])).

fof(f4104,plain,
    ( ~ spl51_1
    | spl51_5
    | ~ spl51_9
    | ~ spl51_40 ),
    inference(avatar_contradiction_clause,[],[f4103])).

fof(f4103,plain,
    ( $false
    | ~ spl51_1
    | spl51_5
    | ~ spl51_9
    | ~ spl51_40 ),
    inference(subsumption_resolution,[],[f4102,f1622])).

fof(f1622,plain,
    ( k1_xboole_0 != k9_relat_1(sK1,sK0)
    | spl51_5 ),
    inference(avatar_component_clause,[],[f1621])).

fof(f1621,plain,
    ( spl51_5
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_5])])).

fof(f4102,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl51_1
    | ~ spl51_9
    | ~ spl51_40 ),
    inference(forward_demodulation,[],[f4086,f1643])).

fof(f1643,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl51_9 ),
    inference(avatar_component_clause,[],[f1641])).

fof(f1641,plain,
    ( spl51_9
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_9])])).

fof(f4086,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,sK0)
    | ~ spl51_1
    | ~ spl51_40 ),
    inference(superposition,[],[f3001,f3587])).

fof(f3587,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl51_40 ),
    inference(avatar_component_clause,[],[f3585])).

fof(f3585,plain,
    ( spl51_40
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_40])])).

fof(f3001,plain,
    ( ! [X47] : k9_relat_1(sK1,X47) = k2_relat_1(k7_relat_1(sK1,X47))
    | ~ spl51_1 ),
    inference(resolution,[],[f1333,f1603])).

fof(f1603,plain,
    ( v1_relat_1(sK1)
    | ~ spl51_1 ),
    inference(avatar_component_clause,[],[f1601])).

fof(f1601,plain,
    ( spl51_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_1])])).

fof(f1333,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f961])).

fof(f961,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f728])).

fof(f728,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f3994,plain,
    ( spl51_40
    | ~ spl51_1
    | ~ spl51_6 ),
    inference(avatar_split_clause,[],[f3847,f1625,f1601,f3585])).

fof(f1625,plain,
    ( spl51_6
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_6])])).

fof(f3847,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl51_1
    | ~ spl51_6 ),
    inference(subsumption_resolution,[],[f3834,f1603])).

fof(f3834,plain,
    ( ~ v1_relat_1(sK1)
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl51_6 ),
    inference(resolution,[],[f1627,f1162])).

fof(f1162,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f868])).

fof(f868,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f797])).

fof(f797,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f1627,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl51_6 ),
    inference(avatar_component_clause,[],[f1625])).

fof(f3974,plain,
    ( ~ spl51_42
    | spl51_5 ),
    inference(avatar_split_clause,[],[f3591,f1621,f3971])).

fof(f3971,plain,
    ( spl51_42
  <=> r1_tarski(k9_relat_1(sK1,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_42])])).

fof(f3591,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,sK0),k1_xboole_0)
    | spl51_5 ),
    inference(subsumption_resolution,[],[f3589,f1425])).

fof(f1425,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f3589,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,sK0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k9_relat_1(sK1,sK0))
    | spl51_5 ),
    inference(extensionality_resolution,[],[f1292,f1622])).

fof(f1292,plain,(
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

fof(f3901,plain,
    ( ~ spl51_41
    | ~ spl51_6
    | spl51_34 ),
    inference(avatar_split_clause,[],[f3851,f2941,f1625,f3898])).

fof(f3898,plain,
    ( spl51_41
  <=> r1_tarski(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_41])])).

fof(f2941,plain,
    ( spl51_34
  <=> v1_xboole_0(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_34])])).

fof(f3851,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | ~ spl51_6
    | spl51_34 ),
    inference(subsumption_resolution,[],[f3845,f2943])).

fof(f2943,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK1))
    | spl51_34 ),
    inference(avatar_component_clause,[],[f2941])).

fof(f3845,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | v1_xboole_0(k1_relat_1(sK1))
    | ~ spl51_6 ),
    inference(resolution,[],[f1627,f1164])).

fof(f1164,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f870])).

fof(f870,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f869])).

fof(f869,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f135])).

fof(f135,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f3849,plain,
    ( ~ spl51_1
    | ~ spl51_6
    | spl51_40 ),
    inference(avatar_contradiction_clause,[],[f3848])).

fof(f3848,plain,
    ( $false
    | ~ spl51_1
    | ~ spl51_6
    | spl51_40 ),
    inference(subsumption_resolution,[],[f3847,f3586])).

fof(f3586,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | spl51_40 ),
    inference(avatar_component_clause,[],[f3585])).

fof(f3833,plain,
    ( spl51_6
    | ~ spl51_12 ),
    inference(avatar_split_clause,[],[f1679,f1669,f1625])).

fof(f1669,plain,
    ( spl51_12
  <=> r1_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_12])])).

fof(f1679,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl51_12 ),
    inference(resolution,[],[f1671,f1158])).

fof(f1158,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f864])).

fof(f864,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1671,plain,
    ( r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl51_12 ),
    inference(avatar_component_clause,[],[f1669])).

fof(f3745,plain,
    ( ~ spl51_24
    | spl51_30 ),
    inference(avatar_contradiction_clause,[],[f3744])).

fof(f3744,plain,
    ( $false
    | ~ spl51_24
    | spl51_30 ),
    inference(subsumption_resolution,[],[f3743,f1425])).

fof(f3743,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl51_24
    | spl51_30 ),
    inference(backward_demodulation,[],[f2608,f2241])).

fof(f2241,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl51_24 ),
    inference(avatar_component_clause,[],[f2240])).

fof(f2240,plain,
    ( spl51_24
  <=> k1_xboole_0 = k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_24])])).

fof(f2608,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_xboole_0)
    | spl51_30 ),
    inference(avatar_component_clause,[],[f2606])).

fof(f2606,plain,
    ( spl51_30
  <=> r1_tarski(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_30])])).

fof(f3734,plain,
    ( ~ spl51_1
    | spl51_6
    | ~ spl51_40 ),
    inference(avatar_contradiction_clause,[],[f3733])).

fof(f3733,plain,
    ( $false
    | ~ spl51_1
    | spl51_6
    | ~ spl51_40 ),
    inference(subsumption_resolution,[],[f3732,f1603])).

fof(f3732,plain,
    ( ~ v1_relat_1(sK1)
    | spl51_6
    | ~ spl51_40 ),
    inference(subsumption_resolution,[],[f3730,f1626])).

fof(f1626,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl51_6 ),
    inference(avatar_component_clause,[],[f1625])).

fof(f3730,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl51_40 ),
    inference(trivial_inequality_removal,[],[f3719])).

fof(f3719,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl51_40 ),
    inference(superposition,[],[f1163,f3587])).

fof(f1163,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f868])).

fof(f3638,plain,
    ( ~ spl51_12
    | spl51_24 ),
    inference(avatar_contradiction_clause,[],[f3637])).

fof(f3637,plain,
    ( $false
    | ~ spl51_12
    | spl51_24 ),
    inference(subsumption_resolution,[],[f3631,f2242])).

fof(f2242,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,k1_relat_1(sK1))
    | spl51_24 ),
    inference(avatar_component_clause,[],[f2240])).

fof(f3631,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl51_12 ),
    inference(resolution,[],[f1671,f1139])).

fof(f1139,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f3588,plain,
    ( spl51_40
    | ~ spl51_39 ),
    inference(avatar_split_clause,[],[f3525,f3467,f3585])).

fof(f3467,plain,
    ( spl51_39
  <=> v1_xboole_0(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_39])])).

fof(f3525,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl51_39 ),
    inference(resolution,[],[f3469,f1409])).

fof(f1409,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f997])).

fof(f997,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f136])).

fof(f136,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f3469,plain,
    ( v1_xboole_0(k7_relat_1(sK1,sK0))
    | ~ spl51_39 ),
    inference(avatar_component_clause,[],[f3467])).

fof(f3470,plain,
    ( spl51_39
    | ~ spl51_1
    | ~ spl51_2
    | ~ spl51_5 ),
    inference(avatar_split_clause,[],[f3443,f1621,f1606,f1601,f3467])).

fof(f1606,plain,
    ( spl51_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_2])])).

fof(f3443,plain,
    ( v1_xboole_0(k7_relat_1(sK1,sK0))
    | ~ spl51_1
    | ~ spl51_2
    | ~ spl51_5 ),
    inference(subsumption_resolution,[],[f3439,f1608])).

fof(f1608,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl51_2 ),
    inference(avatar_component_clause,[],[f1606])).

fof(f3439,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k7_relat_1(sK1,sK0))
    | ~ spl51_1
    | ~ spl51_5 ),
    inference(superposition,[],[f3140,f1623])).

fof(f1623,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl51_5 ),
    inference(avatar_component_clause,[],[f1621])).

fof(f3140,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(k9_relat_1(sK1,X2))
        | v1_xboole_0(k7_relat_1(sK1,X2)) )
    | ~ spl51_1 ),
    inference(subsumption_resolution,[],[f3136,f1603])).

fof(f3136,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(k9_relat_1(sK1,X2))
        | v1_xboole_0(k7_relat_1(sK1,X2))
        | ~ v1_relat_1(sK1) )
    | ~ spl51_1 ),
    inference(resolution,[],[f3037,f1488])).

fof(f1488,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1068])).

fof(f1068,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f658])).

fof(f658,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f3037,plain,
    ( ! [X10] :
        ( ~ v1_relat_1(k7_relat_1(sK1,X10))
        | ~ v1_xboole_0(k9_relat_1(sK1,X10))
        | v1_xboole_0(k7_relat_1(sK1,X10)) )
    | ~ spl51_1 ),
    inference(superposition,[],[f1495,f3001])).

fof(f1495,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1072])).

fof(f1072,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1071])).

fof(f1071,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f680])).

fof(f680,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f3267,plain,
    ( ~ spl51_38
    | spl51_37 ),
    inference(avatar_split_clause,[],[f3234,f3192,f3264])).

fof(f3264,plain,
    ( spl51_38
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_38])])).

fof(f3192,plain,
    ( spl51_37
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_37])])).

fof(f3234,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl51_37 ),
    inference(subsumption_resolution,[],[f3232,f1425])).

fof(f3232,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK1)
    | spl51_37 ),
    inference(extensionality_resolution,[],[f1292,f3194])).

fof(f3194,plain,
    ( k1_xboole_0 != sK1
    | spl51_37 ),
    inference(avatar_component_clause,[],[f3192])).

fof(f3195,plain,
    ( spl51_36
    | ~ spl51_37
    | ~ spl51_1
    | ~ spl51_23 ),
    inference(avatar_split_clause,[],[f3186,f2157,f1601,f3192,f3188])).

fof(f3188,plain,
    ( spl51_36
  <=> r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_36])])).

fof(f2157,plain,
    ( spl51_23
  <=> sK1 = k7_relat_1(sK1,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_23])])).

fof(f3186,plain,
    ( k1_xboole_0 != sK1
    | r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ spl51_1
    | ~ spl51_23 ),
    inference(subsumption_resolution,[],[f3180,f1603])).

fof(f3180,plain,
    ( k1_xboole_0 != sK1
    | r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl51_23 ),
    inference(superposition,[],[f1163,f2159])).

fof(f2159,plain,
    ( sK1 = k7_relat_1(sK1,k1_relat_1(sK1))
    | ~ spl51_23 ),
    inference(avatar_component_clause,[],[f2157])).

fof(f3088,plain,
    ( ~ spl51_28
    | spl51_35
    | ~ spl51_22 ),
    inference(avatar_split_clause,[],[f2191,f2119,f3086,f2440])).

fof(f2440,plain,
    ( spl51_28
  <=> v1_relat_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_28])])).

fof(f3086,plain,
    ( spl51_35
  <=> ! [X0] : r1_tarski(k9_relat_1(k4_relat_1(sK1),X0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_35])])).

fof(f2119,plain,
    ( spl51_22
  <=> k1_relat_1(sK1) = k2_relat_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_22])])).

fof(f2191,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(k4_relat_1(sK1),X0),k1_relat_1(sK1))
        | ~ v1_relat_1(k4_relat_1(sK1)) )
    | ~ spl51_22 ),
    inference(superposition,[],[f1334,f2121])).

fof(f2121,plain,
    ( k1_relat_1(sK1) = k2_relat_1(k4_relat_1(sK1))
    | ~ spl51_22 ),
    inference(avatar_component_clause,[],[f2119])).

fof(f1334,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f962])).

fof(f962,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f724])).

fof(f724,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f2944,plain,
    ( spl51_25
    | ~ spl51_28
    | ~ spl51_34
    | ~ spl51_22 ),
    inference(avatar_split_clause,[],[f2192,f2119,f2941,f2440,f2269])).

fof(f2269,plain,
    ( spl51_25
  <=> v1_xboole_0(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_25])])).

fof(f2192,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK1))
    | ~ v1_relat_1(k4_relat_1(sK1))
    | v1_xboole_0(k4_relat_1(sK1))
    | ~ spl51_22 ),
    inference(superposition,[],[f1495,f2121])).

fof(f2864,plain,
    ( spl51_33
    | ~ spl51_1 ),
    inference(avatar_split_clause,[],[f2531,f1601,f2861])).

fof(f2861,plain,
    ( spl51_33
  <=> k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_33])])).

fof(f2531,plain,
    ( k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))
    | ~ spl51_1 ),
    inference(resolution,[],[f1229,f1603])).

fof(f1229,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f922])).

fof(f922,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f726])).

fof(f726,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f2719,plain,
    ( ~ spl51_31
    | spl51_32
    | ~ spl51_1
    | ~ spl51_29 ),
    inference(avatar_split_clause,[],[f2675,f2511,f1601,f2716,f2712])).

fof(f2712,plain,
    ( spl51_31
  <=> v1_xboole_0(k6_relat_1(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_31])])).

fof(f2716,plain,
    ( spl51_32
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_32])])).

fof(f2511,plain,
    ( spl51_29
  <=> sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_29])])).

fof(f2675,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(k6_relat_1(k1_relat_1(sK1)))
    | ~ spl51_1
    | ~ spl51_29 ),
    inference(subsumption_resolution,[],[f2674,f1603])).

fof(f2674,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_xboole_0(k6_relat_1(k1_relat_1(sK1)))
    | ~ spl51_29 ),
    inference(superposition,[],[f1449,f2513])).

fof(f2513,plain,
    ( sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)
    | ~ spl51_29 ),
    inference(avatar_component_clause,[],[f2511])).

fof(f1449,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1029])).

fof(f1029,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k5_relat_1(X0,X1))
        & v1_xboole_0(k5_relat_1(X0,X1)) )
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1028])).

fof(f1028,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k5_relat_1(X0,X1))
        & v1_xboole_0(k5_relat_1(X0,X1)) )
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f667])).

fof(f667,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_xboole_0(X0) )
     => ( v1_relat_1(k5_relat_1(X0,X1))
        & v1_xboole_0(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_relat_1)).

fof(f2609,plain,
    ( ~ spl51_30
    | spl51_20 ),
    inference(avatar_split_clause,[],[f2585,f2011,f2606])).

fof(f2011,plain,
    ( spl51_20
  <=> k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_20])])).

fof(f2585,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_xboole_0)
    | spl51_20 ),
    inference(forward_demodulation,[],[f2584,f1324])).

fof(f1324,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2584,plain,
    ( ~ r1_tarski(k3_xboole_0(k1_relat_1(sK1),sK0),k1_xboole_0)
    | spl51_20 ),
    inference(subsumption_resolution,[],[f2543,f1425])).

fof(f2543,plain,
    ( ~ r1_tarski(k3_xboole_0(k1_relat_1(sK1),sK0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k3_xboole_0(k1_relat_1(sK1),sK0))
    | spl51_20 ),
    inference(extensionality_resolution,[],[f1292,f2012])).

fof(f2012,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_relat_1(sK1),sK0)
    | spl51_20 ),
    inference(avatar_component_clause,[],[f2011])).

fof(f2514,plain,
    ( spl51_29
    | ~ spl51_1 ),
    inference(avatar_split_clause,[],[f2506,f1601,f2511])).

fof(f2506,plain,
    ( sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)
    | ~ spl51_1 ),
    inference(resolution,[],[f1228,f1603])).

fof(f1228,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f921])).

fof(f921,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f783])).

fof(f783,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f2443,plain,
    ( spl51_25
    | ~ spl51_28
    | ~ spl51_26
    | ~ spl51_21 ),
    inference(avatar_split_clause,[],[f2172,f2075,f2273,f2440,f2269])).

fof(f2273,plain,
    ( spl51_26
  <=> v1_xboole_0(k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_26])])).

fof(f2075,plain,
    ( spl51_21
  <=> k2_relat_1(sK1) = k1_relat_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_21])])).

fof(f2172,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK1))
    | ~ v1_relat_1(k4_relat_1(sK1))
    | v1_xboole_0(k4_relat_1(sK1))
    | ~ spl51_21 ),
    inference(superposition,[],[f1210,f2077])).

fof(f2077,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k4_relat_1(sK1))
    | ~ spl51_21 ),
    inference(avatar_component_clause,[],[f2075])).

fof(f1210,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f903])).

fof(f903,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f902])).

fof(f902,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f679])).

fof(f679,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f2361,plain,
    ( spl51_27
    | ~ spl51_1 ),
    inference(avatar_split_clause,[],[f2335,f1601,f2358])).

fof(f2358,plain,
    ( spl51_27
  <=> sK1 = k8_relat_1(k2_relat_1(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_27])])).

fof(f2335,plain,
    ( sK1 = k8_relat_1(k2_relat_1(sK1),sK1)
    | ~ spl51_1 ),
    inference(resolution,[],[f1526,f1603])).

fof(f1526,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    inference(cnf_transformation,[],[f1091])).

fof(f1091,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f707])).

fof(f707,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).

fof(f2276,plain,
    ( ~ spl51_25
    | spl51_26
    | ~ spl51_21 ),
    inference(avatar_split_clause,[],[f2173,f2075,f2273,f2269])).

fof(f2173,plain,
    ( v1_xboole_0(k2_relat_1(sK1))
    | ~ v1_xboole_0(k4_relat_1(sK1))
    | ~ spl51_21 ),
    inference(superposition,[],[f1211,f2077])).

fof(f1211,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f904])).

fof(f904,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f665])).

fof(f665,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f2243,plain,
    ( ~ spl51_24
    | spl51_20 ),
    inference(avatar_split_clause,[],[f2049,f2011,f2240])).

fof(f2049,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,k1_relat_1(sK1))
    | spl51_20 ),
    inference(superposition,[],[f2012,f1324])).

fof(f2160,plain,
    ( spl51_23
    | ~ spl51_1 ),
    inference(avatar_split_clause,[],[f2070,f1601,f2157])).

fof(f2070,plain,
    ( sK1 = k7_relat_1(sK1,k1_relat_1(sK1))
    | ~ spl51_1 ),
    inference(resolution,[],[f1230,f1603])).

fof(f1230,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f923])).

fof(f923,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f800])).

fof(f800,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f2122,plain,
    ( spl51_22
    | ~ spl51_1 ),
    inference(avatar_split_clause,[],[f2059,f1601,f2119])).

fof(f2059,plain,
    ( k1_relat_1(sK1) = k2_relat_1(k4_relat_1(sK1))
    | ~ spl51_1 ),
    inference(resolution,[],[f1225,f1603])).

fof(f1225,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f918])).

fof(f918,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f751])).

fof(f751,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f2078,plain,
    ( spl51_21
    | ~ spl51_1 ),
    inference(avatar_split_clause,[],[f2046,f1601,f2075])).

fof(f2046,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k4_relat_1(sK1))
    | ~ spl51_1 ),
    inference(resolution,[],[f1224,f1603])).

fof(f1224,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f918])).

fof(f2016,plain,
    ( spl51_6
    | ~ spl51_12 ),
    inference(avatar_contradiction_clause,[],[f2015])).

fof(f2015,plain,
    ( $false
    | spl51_6
    | ~ spl51_12 ),
    inference(subsumption_resolution,[],[f1626,f1679])).

fof(f2014,plain,
    ( spl51_20
    | ~ spl51_6 ),
    inference(avatar_split_clause,[],[f1963,f1625,f2011])).

fof(f1963,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl51_6 ),
    inference(resolution,[],[f1139,f1627])).

fof(f1875,plain,
    ( spl51_19
    | ~ spl51_1 ),
    inference(avatar_split_clause,[],[f1833,f1601,f1872])).

fof(f1872,plain,
    ( spl51_19
  <=> k1_xboole_0 = k8_relat_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_19])])).

fof(f1833,plain,
    ( k1_xboole_0 = k8_relat_1(k1_xboole_0,sK1)
    | ~ spl51_1 ),
    inference(resolution,[],[f1415,f1603])).

fof(f1415,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    inference(cnf_transformation,[],[f1003])).

fof(f1003,plain,(
    ! [X0] :
      ( k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f718])).

fof(f718,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).

fof(f1864,plain,
    ( spl51_18
    | ~ spl51_1 ),
    inference(avatar_split_clause,[],[f1823,f1601,f1861])).

fof(f1861,plain,
    ( spl51_18
  <=> k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_18])])).

fof(f1823,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0)
    | ~ spl51_1 ),
    inference(resolution,[],[f1414,f1603])).

fof(f1414,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f1002])).

fof(f1002,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f693])).

fof(f693,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

fof(f1855,plain,
    ( spl51_17
    | ~ spl51_1 ),
    inference(avatar_split_clause,[],[f1813,f1601,f1852])).

fof(f1852,plain,
    ( spl51_17
  <=> k1_xboole_0 = k5_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_17])])).

fof(f1813,plain,
    ( k1_xboole_0 = k5_relat_1(sK1,k1_xboole_0)
    | ~ spl51_1 ),
    inference(resolution,[],[f1413,f1603])).

fof(f1413,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f1001])).

fof(f1001,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f770])).

fof(f770,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f1843,plain,
    ( spl51_16
    | ~ spl51_1 ),
    inference(avatar_split_clause,[],[f1803,f1601,f1840])).

fof(f1840,plain,
    ( spl51_16
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_16])])).

fof(f1803,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK1)
    | ~ spl51_1 ),
    inference(resolution,[],[f1412,f1603])).

fof(f1412,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ),
    inference(cnf_transformation,[],[f1001])).

fof(f1794,plain,
    ( spl51_15
    | ~ spl51_1 ),
    inference(avatar_split_clause,[],[f1773,f1601,f1791])).

fof(f1791,plain,
    ( spl51_15
  <=> k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_15])])).

fof(f1773,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0)
    | ~ spl51_1 ),
    inference(resolution,[],[f1341,f1603])).

fof(f1341,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f964])).

fof(f964,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f729])).

fof(f729,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

fof(f1696,plain,
    ( spl51_14
    | ~ spl51_11 ),
    inference(avatar_split_clause,[],[f1663,f1653,f1693])).

fof(f1693,plain,
    ( spl51_14
  <=> m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_14])])).

fof(f1653,plain,
    ( spl51_11
  <=> k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_11])])).

fof(f1663,plain,
    ( m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ spl51_11 ),
    inference(superposition,[],[f1424,f1655])).

fof(f1655,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)
    | ~ spl51_11 ),
    inference(avatar_component_clause,[],[f1653])).

fof(f1424,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f1689,plain,(
    spl51_13 ),
    inference(avatar_split_clause,[],[f1661,f1686])).

fof(f1686,plain,
    ( spl51_13
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_13])])).

fof(f1661,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f1491,f1575])).

fof(f1575,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f1390])).

fof(f1390,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f329])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1491,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f677])).

fof(f677,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f1672,plain,
    ( spl51_12
    | ~ spl51_6 ),
    inference(avatar_split_clause,[],[f1667,f1625,f1669])).

fof(f1667,plain,
    ( r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl51_6 ),
    inference(resolution,[],[f1158,f1627])).

fof(f1656,plain,(
    spl51_11 ),
    inference(avatar_split_clause,[],[f1332,f1653])).

fof(f1332,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f376])).

fof(f376,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f1649,plain,(
    spl51_10 ),
    inference(avatar_split_clause,[],[f1426,f1646])).

fof(f1646,plain,
    ( spl51_10
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_10])])).

fof(f1426,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f387])).

fof(f387,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f1644,plain,(
    spl51_9 ),
    inference(avatar_split_clause,[],[f1234,f1641])).

fof(f1234,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f769])).

fof(f769,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f1639,plain,(
    spl51_8 ),
    inference(avatar_split_clause,[],[f1233,f1636])).

fof(f1636,plain,
    ( spl51_8
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_8])])).

fof(f1233,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f769])).

fof(f1634,plain,(
    spl51_7 ),
    inference(avatar_split_clause,[],[f1528,f1631])).

fof(f1631,plain,
    ( spl51_7
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_7])])).

fof(f1528,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f1179])).

fof(f1179,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f875])).

fof(f875,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f132])).

fof(f132,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f1629,plain,
    ( ~ spl51_5
    | ~ spl51_6 ),
    inference(avatar_split_clause,[],[f1093,f1625,f1621])).

fof(f1093,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f806])).

fof(f806,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f733])).

fof(f733,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k9_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f732])).

fof(f732,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f1628,plain,
    ( spl51_5
    | spl51_6 ),
    inference(avatar_split_clause,[],[f1092,f1625,f1621])).

fof(f1092,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f806])).

fof(f1619,plain,(
    spl51_4 ),
    inference(avatar_split_clause,[],[f1429,f1616])).

fof(f1616,plain,
    ( spl51_4
  <=> v1_relat_1(sK35) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_4])])).

fof(f1429,plain,(
    v1_relat_1(sK35) ),
    inference(cnf_transformation,[],[f682])).

fof(f682,axiom,(
    ? [X0] :
      ( v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relat_1)).

fof(f1614,plain,(
    ~ spl51_3 ),
    inference(avatar_split_clause,[],[f1428,f1611])).

fof(f1611,plain,
    ( spl51_3
  <=> v1_xboole_0(sK35) ),
    introduced(avatar_definition,[new_symbols(naming,[spl51_3])])).

fof(f1428,plain,(
    ~ v1_xboole_0(sK35) ),
    inference(cnf_transformation,[],[f682])).

fof(f1609,plain,(
    spl51_2 ),
    inference(avatar_split_clause,[],[f1427,f1606])).

fof(f1427,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1604,plain,(
    spl51_1 ),
    inference(avatar_split_clause,[],[f1094,f1601])).

fof(f1094,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f806])).
%------------------------------------------------------------------------------
