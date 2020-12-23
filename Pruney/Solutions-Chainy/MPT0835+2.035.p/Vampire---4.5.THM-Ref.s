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
% DateTime   : Thu Dec  3 12:57:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 336 expanded)
%              Number of leaves         :   49 ( 148 expanded)
%              Depth                    :   10
%              Number of atoms          :  472 ( 808 expanded)
%              Number of equality atoms :  110 ( 191 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f363,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f82,f92,f99,f106,f119,f128,f144,f149,f160,f164,f173,f178,f183,f198,f214,f221,f231,f237,f271,f276,f280,f300,f308,f318,f339,f341,f352,f361,f362])).

fof(f362,plain,
    ( k10_relat_1(sK2,sK0) != k10_relat_1(sK2,k2_relat_1(sK2))
    | k1_relat_1(sK2) != k10_relat_1(sK2,sK0)
    | k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f361,plain,
    ( ~ spl4_40
    | ~ spl4_16
    | spl4_39 ),
    inference(avatar_split_clause,[],[f356,f349,f171,f358])).

fof(f358,plain,
    ( spl4_40
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f171,plain,
    ( spl4_16
  <=> ! [X0] : k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f349,plain,
    ( spl4_39
  <=> k1_relat_1(sK2) = k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f356,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl4_16
    | spl4_39 ),
    inference(superposition,[],[f351,f172])).

fof(f172,plain,
    ( ! [X0] : k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f171])).

fof(f351,plain,
    ( k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2))
    | spl4_39 ),
    inference(avatar_component_clause,[],[f349])).

fof(f352,plain,
    ( ~ spl4_39
    | spl4_10
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f345,f268,f162,f146,f141,f349])).

fof(f141,plain,
    ( spl4_10
  <=> k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) = k1_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f146,plain,
    ( spl4_11
  <=> k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f162,plain,
    ( spl4_14
  <=> ! [X0] : k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f268,plain,
    ( spl4_29
  <=> k2_relat_1(sK2) = k9_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f345,plain,
    ( k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2))
    | spl4_10
    | ~ spl4_11
    | ~ spl4_14
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f344,f270])).

fof(f270,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK1)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f268])).

fof(f344,plain,
    ( k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1))
    | spl4_10
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f343,f163])).

fof(f163,plain,
    ( ! [X0] : k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f162])).

fof(f343,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)
    | spl4_10
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f143,f148])).

fof(f148,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f146])).

fof(f143,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f141])).

fof(f341,plain,
    ( ~ spl4_2
    | spl4_23
    | ~ spl4_30
    | ~ spl4_37 ),
    inference(avatar_contradiction_clause,[],[f340])).

fof(f340,plain,
    ( $false
    | ~ spl4_2
    | spl4_23
    | ~ spl4_30
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f333,f275])).

fof(f275,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl4_30
  <=> k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f333,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl4_2
    | spl4_23
    | ~ spl4_37 ),
    inference(backward_demodulation,[],[f230,f329])).

fof(f329,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK0)
    | ~ spl4_2
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f325,f81])).

fof(f81,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f325,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl4_37 ),
    inference(resolution,[],[f317,f84])).

fof(f84,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k10_relat_1(X1,X2))
      | k1_relat_1(X1) = k10_relat_1(X1,X2)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f56,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f317,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f315])).

fof(f315,plain,
    ( spl4_37
  <=> r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f230,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl4_23
  <=> k2_relat_1(sK2) = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f339,plain,
    ( spl4_38
    | ~ spl4_2
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f329,f315,f79,f336])).

fof(f336,plain,
    ( spl4_38
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f318,plain,
    ( spl4_37
    | ~ spl4_30
    | ~ spl4_35
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f312,f306,f297,f273,f315])).

fof(f297,plain,
    ( spl4_35
  <=> k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f306,plain,
    ( spl4_36
  <=> ! [X3] :
        ( ~ r1_tarski(X3,k1_relat_1(sK2))
        | r1_tarski(X3,k10_relat_1(sK2,k9_relat_1(sK2,X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f312,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0))
    | ~ spl4_30
    | ~ spl4_35
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f311,f299])).

fof(f299,plain,
    ( k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f297])).

fof(f311,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2)))
    | ~ spl4_30
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f309,f275])).

fof(f309,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2))))
    | ~ spl4_36 ),
    inference(resolution,[],[f307,f64])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f307,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,k1_relat_1(sK2))
        | r1_tarski(X3,k10_relat_1(sK2,k9_relat_1(sK2,X3))) )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f306])).

fof(f308,plain,
    ( spl4_36
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f114,f79,f306])).

fof(f114,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,k1_relat_1(sK2))
        | r1_tarski(X3,k10_relat_1(sK2,k9_relat_1(sK2,X3))) )
    | ~ spl4_2 ),
    inference(resolution,[],[f49,f81])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f300,plain,
    ( spl4_35
    | ~ spl4_17
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f293,f278,f175,f297])).

fof(f175,plain,
    ( spl4_17
  <=> k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f278,plain,
    ( spl4_31
  <=> ! [X3] : k10_relat_1(sK2,X3) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f293,plain,
    ( k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl4_17
    | ~ spl4_31 ),
    inference(superposition,[],[f279,f177])).

fof(f177,plain,
    ( k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK0)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f175])).

fof(f279,plain,
    ( ! [X3] : k10_relat_1(sK2,X3) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X3))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f278])).

fof(f280,plain,
    ( spl4_31
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f112,f79,f278])).

fof(f112,plain,
    ( ! [X3] : k10_relat_1(sK2,X3) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X3))
    | ~ spl4_2 ),
    inference(resolution,[],[f48,f81])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f276,plain,
    ( spl4_30
    | ~ spl4_22
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f266,f235,f218,f273])).

fof(f218,plain,
    ( spl4_22
  <=> sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f235,plain,
    ( spl4_24
  <=> ! [X3] : k2_relat_1(k7_relat_1(sK2,X3)) = k9_relat_1(sK2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f266,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl4_22
    | ~ spl4_24 ),
    inference(superposition,[],[f236,f220])).

fof(f220,plain,
    ( sK2 = k7_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f218])).

fof(f236,plain,
    ( ! [X3] : k2_relat_1(k7_relat_1(sK2,X3)) = k9_relat_1(sK2,X3)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f235])).

fof(f271,plain,
    ( spl4_29
    | ~ spl4_7
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f265,f235,f125,f268])).

fof(f125,plain,
    ( spl4_7
  <=> sK2 = k7_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f265,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK1)
    | ~ spl4_7
    | ~ spl4_24 ),
    inference(superposition,[],[f236,f127])).

fof(f127,plain,
    ( sK2 = k7_relat_1(sK2,sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f125])).

fof(f237,plain,
    ( spl4_24
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f101,f79,f235])).

fof(f101,plain,
    ( ! [X3] : k2_relat_1(k7_relat_1(sK2,X3)) = k9_relat_1(sK2,X3)
    | ~ spl4_2 ),
    inference(resolution,[],[f47,f81])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f231,plain,
    ( ~ spl4_23
    | ~ spl4_14
    | spl4_18 ),
    inference(avatar_split_clause,[],[f191,f180,f162,f228])).

fof(f180,plain,
    ( spl4_18
  <=> k2_relat_1(sK2) = k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f191,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | ~ spl4_14
    | spl4_18 ),
    inference(superposition,[],[f182,f163])).

fof(f182,plain,
    ( k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f180])).

fof(f221,plain,
    ( spl4_22
    | ~ spl4_2
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f216,f211,f79,f218])).

fof(f211,plain,
    ( spl4_21
  <=> v4_relat_1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f216,plain,
    ( sK2 = k7_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl4_2
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f215,f81])).

fof(f215,plain,
    ( sK2 = k7_relat_1(sK2,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_21 ),
    inference(resolution,[],[f213,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

% (32279)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f213,plain,
    ( v4_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f211])).

fof(f214,plain,
    ( spl4_21
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f202,f195,f211])).

fof(f195,plain,
    ( spl4_20
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

% (32278)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f202,plain,
    ( v4_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl4_20 ),
    inference(resolution,[],[f197,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f197,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f195])).

fof(f198,plain,
    ( spl4_20
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f193,f103,f195])).

fof(f103,plain,
    ( spl4_5
  <=> sP3(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f193,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))
    | ~ spl4_5 ),
    inference(resolution,[],[f129,f105])).

fof(f105,plain,
    ( sP3(sK2,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) ) ),
    inference(resolution,[],[f67,f64])).

fof(f67,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(k1_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ sP3(X3,X2) ) ),
    inference(general_splitting,[],[f63,f66_D])).

fof(f66,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | sP3(X3,X2) ) ),
    inference(cnf_transformation,[],[f66_D])).

fof(f66_D,plain,(
    ! [X2,X3] :
      ( ! [X0] : ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
    <=> ~ sP3(X3,X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

fof(f183,plain,
    ( ~ spl4_18
    | ~ spl4_1
    | spl4_13 ),
    inference(avatar_split_clause,[],[f169,f157,f69,f180])).

fof(f69,plain,
    ( spl4_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f157,plain,
    ( spl4_13
  <=> k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f169,plain,
    ( k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0))
    | ~ spl4_1
    | spl4_13 ),
    inference(backward_demodulation,[],[f159,f135])).

fof(f135,plain,
    ( ! [X0] : k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl4_1 ),
    inference(resolution,[],[f62,f71])).

fof(f71,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f159,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f157])).

fof(f178,plain,
    ( spl4_17
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f122,f116,f175])).

fof(f116,plain,
    ( spl4_6
  <=> r1_tarski(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f122,plain,
    ( k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f118,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f118,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f173,plain,
    ( spl4_16
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f135,f69,f171])).

fof(f164,plain,
    ( spl4_14
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f130,f69,f162])).

fof(f130,plain,
    ( ! [X0] : k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0)
    | ~ spl4_1 ),
    inference(resolution,[],[f61,f71])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f160,plain,
    ( ~ spl4_13
    | ~ spl4_1
    | spl4_9 ),
    inference(avatar_split_clause,[],[f150,f137,f69,f157])).

fof(f137,plain,
    ( spl4_9
  <=> k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) = k2_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f150,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
    | ~ spl4_1
    | spl4_9 ),
    inference(backward_demodulation,[],[f139,f123])).

fof(f123,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f58,f71])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f139,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f137])).

fof(f149,plain,
    ( spl4_11
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f120,f69,f146])).

fof(f120,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f57,f71])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f144,plain,
    ( ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f43,f141,f137])).

fof(f43,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
          | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
        | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
        | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
          & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

fof(f128,plain,
    ( spl4_7
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f108,f89,f79,f125])).

fof(f89,plain,
    ( spl4_3
  <=> v4_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f108,plain,
    ( sK2 = k7_relat_1(sK2,sK1)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f107,f81])).

fof(f107,plain,
    ( sK2 = k7_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(resolution,[],[f53,f91])).

fof(f91,plain,
    ( v4_relat_1(sK2,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f119,plain,
    ( spl4_6
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f110,f96,f79,f116])).

fof(f96,plain,
    ( spl4_4
  <=> v5_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f110,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f109,f81])).

fof(f109,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f98,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f98,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f106,plain,
    ( spl4_5
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f94,f69,f103])).

fof(f94,plain,
    ( sP3(sK2,sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f66,f71])).

fof(f99,plain,
    ( spl4_4
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f93,f69,f96])).

fof(f93,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f60,f71])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f92,plain,
    ( spl4_3
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f87,f69,f89])).

fof(f87,plain,
    ( v4_relat_1(sK2,sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f59,f71])).

fof(f82,plain,
    ( spl4_2
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f76,f69,f79])).

fof(f76,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f73,f71])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f44,f45])).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f72,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f42,f69])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:26:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (32263)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (32260)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (32268)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (32267)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.53  % (32262)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (32263)Refutation not found, incomplete strategy% (32263)------------------------------
% 0.21/0.53  % (32263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32263)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32263)Memory used [KB]: 6140
% 0.21/0.53  % (32263)Time elapsed: 0.108 s
% 0.21/0.53  % (32263)------------------------------
% 0.21/0.53  % (32263)------------------------------
% 0.21/0.53  % (32260)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f363,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f72,f82,f92,f99,f106,f119,f128,f144,f149,f160,f164,f173,f178,f183,f198,f214,f221,f231,f237,f271,f276,f280,f300,f308,f318,f339,f341,f352,f361,f362])).
% 0.21/0.54  fof(f362,plain,(
% 0.21/0.54    k10_relat_1(sK2,sK0) != k10_relat_1(sK2,k2_relat_1(sK2)) | k1_relat_1(sK2) != k10_relat_1(sK2,sK0) | k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.21/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.54  fof(f361,plain,(
% 0.21/0.54    ~spl4_40 | ~spl4_16 | spl4_39),
% 0.21/0.54    inference(avatar_split_clause,[],[f356,f349,f171,f358])).
% 0.21/0.54  fof(f358,plain,(
% 0.21/0.54    spl4_40 <=> k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.21/0.54  fof(f171,plain,(
% 0.21/0.54    spl4_16 <=> ! [X0] : k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.54  fof(f349,plain,(
% 0.21/0.54    spl4_39 <=> k1_relat_1(sK2) = k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.21/0.54  fof(f356,plain,(
% 0.21/0.54    k1_relat_1(sK2) != k10_relat_1(sK2,k2_relat_1(sK2)) | (~spl4_16 | spl4_39)),
% 0.21/0.54    inference(superposition,[],[f351,f172])).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    ( ! [X0] : (k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0)) ) | ~spl4_16),
% 0.21/0.54    inference(avatar_component_clause,[],[f171])).
% 0.21/0.54  fof(f351,plain,(
% 0.21/0.54    k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) | spl4_39),
% 0.21/0.54    inference(avatar_component_clause,[],[f349])).
% 0.21/0.54  fof(f352,plain,(
% 0.21/0.54    ~spl4_39 | spl4_10 | ~spl4_11 | ~spl4_14 | ~spl4_29),
% 0.21/0.54    inference(avatar_split_clause,[],[f345,f268,f162,f146,f141,f349])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    spl4_10 <=> k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) = k1_relset_1(sK1,sK0,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    spl4_11 <=> k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    spl4_14 <=> ! [X0] : k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.54  fof(f268,plain,(
% 0.21/0.54    spl4_29 <=> k2_relat_1(sK2) = k9_relat_1(sK2,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.21/0.54  fof(f345,plain,(
% 0.21/0.54    k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) | (spl4_10 | ~spl4_11 | ~spl4_14 | ~spl4_29)),
% 0.21/0.54    inference(forward_demodulation,[],[f344,f270])).
% 0.21/0.54  fof(f270,plain,(
% 0.21/0.54    k2_relat_1(sK2) = k9_relat_1(sK2,sK1) | ~spl4_29),
% 0.21/0.54    inference(avatar_component_clause,[],[f268])).
% 0.21/0.54  fof(f344,plain,(
% 0.21/0.54    k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1)) | (spl4_10 | ~spl4_11 | ~spl4_14)),
% 0.21/0.54    inference(forward_demodulation,[],[f343,f163])).
% 0.21/0.54  fof(f163,plain,(
% 0.21/0.54    ( ! [X0] : (k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0)) ) | ~spl4_14),
% 0.21/0.54    inference(avatar_component_clause,[],[f162])).
% 0.21/0.54  fof(f343,plain,(
% 0.21/0.54    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) | (spl4_10 | ~spl4_11)),
% 0.21/0.54    inference(forward_demodulation,[],[f143,f148])).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) | ~spl4_11),
% 0.21/0.54    inference(avatar_component_clause,[],[f146])).
% 0.21/0.54  fof(f143,plain,(
% 0.21/0.54    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | spl4_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f141])).
% 0.21/0.54  fof(f341,plain,(
% 0.21/0.54    ~spl4_2 | spl4_23 | ~spl4_30 | ~spl4_37),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f340])).
% 0.21/0.54  fof(f340,plain,(
% 0.21/0.54    $false | (~spl4_2 | spl4_23 | ~spl4_30 | ~spl4_37)),
% 0.21/0.54    inference(subsumption_resolution,[],[f333,f275])).
% 0.21/0.54  fof(f275,plain,(
% 0.21/0.54    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) | ~spl4_30),
% 0.21/0.54    inference(avatar_component_clause,[],[f273])).
% 0.21/0.54  fof(f273,plain,(
% 0.21/0.54    spl4_30 <=> k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.54  fof(f333,plain,(
% 0.21/0.54    k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2)) | (~spl4_2 | spl4_23 | ~spl4_37)),
% 0.21/0.54    inference(backward_demodulation,[],[f230,f329])).
% 0.21/0.54  fof(f329,plain,(
% 0.21/0.54    k1_relat_1(sK2) = k10_relat_1(sK2,sK0) | (~spl4_2 | ~spl4_37)),
% 0.21/0.54    inference(subsumption_resolution,[],[f325,f81])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    v1_relat_1(sK2) | ~spl4_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f79])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    spl4_2 <=> v1_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.54  fof(f325,plain,(
% 0.21/0.54    k1_relat_1(sK2) = k10_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | ~spl4_37),
% 0.21/0.54    inference(resolution,[],[f317,f84])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X2,X1] : (~r1_tarski(k1_relat_1(X1),k10_relat_1(X1,X2)) | k1_relat_1(X1) = k10_relat_1(X1,X2) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(resolution,[],[f56,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(flattening,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f317,plain,(
% 0.21/0.54    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0)) | ~spl4_37),
% 0.21/0.54    inference(avatar_component_clause,[],[f315])).
% 0.21/0.54  fof(f315,plain,(
% 0.21/0.54    spl4_37 <=> r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.21/0.54  fof(f230,plain,(
% 0.21/0.54    k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | spl4_23),
% 0.21/0.54    inference(avatar_component_clause,[],[f228])).
% 0.21/0.54  fof(f228,plain,(
% 0.21/0.54    spl4_23 <=> k2_relat_1(sK2) = k9_relat_1(sK2,k10_relat_1(sK2,sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.54  fof(f339,plain,(
% 0.21/0.54    spl4_38 | ~spl4_2 | ~spl4_37),
% 0.21/0.54    inference(avatar_split_clause,[],[f329,f315,f79,f336])).
% 0.21/0.54  fof(f336,plain,(
% 0.21/0.54    spl4_38 <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.21/0.54  fof(f318,plain,(
% 0.21/0.54    spl4_37 | ~spl4_30 | ~spl4_35 | ~spl4_36),
% 0.21/0.54    inference(avatar_split_clause,[],[f312,f306,f297,f273,f315])).
% 0.21/0.54  fof(f297,plain,(
% 0.21/0.54    spl4_35 <=> k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.21/0.54  fof(f306,plain,(
% 0.21/0.54    spl4_36 <=> ! [X3] : (~r1_tarski(X3,k1_relat_1(sK2)) | r1_tarski(X3,k10_relat_1(sK2,k9_relat_1(sK2,X3))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.21/0.54  fof(f312,plain,(
% 0.21/0.54    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0)) | (~spl4_30 | ~spl4_35 | ~spl4_36)),
% 0.21/0.54    inference(forward_demodulation,[],[f311,f299])).
% 0.21/0.54  fof(f299,plain,(
% 0.21/0.54    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~spl4_35),
% 0.21/0.54    inference(avatar_component_clause,[],[f297])).
% 0.21/0.54  fof(f311,plain,(
% 0.21/0.54    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k2_relat_1(sK2))) | (~spl4_30 | ~spl4_36)),
% 0.21/0.54    inference(forward_demodulation,[],[f309,f275])).
% 0.21/0.54  fof(f309,plain,(
% 0.21/0.54    r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2)))) | ~spl4_36),
% 0.21/0.54    inference(resolution,[],[f307,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f307,plain,(
% 0.21/0.54    ( ! [X3] : (~r1_tarski(X3,k1_relat_1(sK2)) | r1_tarski(X3,k10_relat_1(sK2,k9_relat_1(sK2,X3)))) ) | ~spl4_36),
% 0.21/0.54    inference(avatar_component_clause,[],[f306])).
% 0.21/0.54  fof(f308,plain,(
% 0.21/0.54    spl4_36 | ~spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f114,f79,f306])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    ( ! [X3] : (~r1_tarski(X3,k1_relat_1(sK2)) | r1_tarski(X3,k10_relat_1(sK2,k9_relat_1(sK2,X3)))) ) | ~spl4_2),
% 0.21/0.54    inference(resolution,[],[f49,f81])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.21/0.54  fof(f300,plain,(
% 0.21/0.54    spl4_35 | ~spl4_17 | ~spl4_31),
% 0.21/0.54    inference(avatar_split_clause,[],[f293,f278,f175,f297])).
% 0.21/0.54  fof(f175,plain,(
% 0.21/0.54    spl4_17 <=> k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.54  fof(f278,plain,(
% 0.21/0.54    spl4_31 <=> ! [X3] : k10_relat_1(sK2,X3) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X3))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.54  fof(f293,plain,(
% 0.21/0.54    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k2_relat_1(sK2)) | (~spl4_17 | ~spl4_31)),
% 0.21/0.54    inference(superposition,[],[f279,f177])).
% 0.21/0.54  fof(f177,plain,(
% 0.21/0.54    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK0) | ~spl4_17),
% 0.21/0.54    inference(avatar_component_clause,[],[f175])).
% 0.21/0.54  fof(f279,plain,(
% 0.21/0.54    ( ! [X3] : (k10_relat_1(sK2,X3) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X3))) ) | ~spl4_31),
% 0.21/0.54    inference(avatar_component_clause,[],[f278])).
% 0.21/0.54  fof(f280,plain,(
% 0.21/0.54    spl4_31 | ~spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f112,f79,f278])).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    ( ! [X3] : (k10_relat_1(sK2,X3) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X3))) ) | ~spl4_2),
% 0.21/0.54    inference(resolution,[],[f48,f81])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 0.21/0.54  fof(f276,plain,(
% 0.21/0.54    spl4_30 | ~spl4_22 | ~spl4_24),
% 0.21/0.54    inference(avatar_split_clause,[],[f266,f235,f218,f273])).
% 0.21/0.54  fof(f218,plain,(
% 0.21/0.54    spl4_22 <=> sK2 = k7_relat_1(sK2,k1_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.54  fof(f235,plain,(
% 0.21/0.54    spl4_24 <=> ! [X3] : k2_relat_1(k7_relat_1(sK2,X3)) = k9_relat_1(sK2,X3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.54  fof(f266,plain,(
% 0.21/0.54    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) | (~spl4_22 | ~spl4_24)),
% 0.21/0.54    inference(superposition,[],[f236,f220])).
% 0.21/0.54  fof(f220,plain,(
% 0.21/0.54    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) | ~spl4_22),
% 0.21/0.54    inference(avatar_component_clause,[],[f218])).
% 0.21/0.54  fof(f236,plain,(
% 0.21/0.54    ( ! [X3] : (k2_relat_1(k7_relat_1(sK2,X3)) = k9_relat_1(sK2,X3)) ) | ~spl4_24),
% 0.21/0.54    inference(avatar_component_clause,[],[f235])).
% 0.21/0.54  fof(f271,plain,(
% 0.21/0.54    spl4_29 | ~spl4_7 | ~spl4_24),
% 0.21/0.54    inference(avatar_split_clause,[],[f265,f235,f125,f268])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    spl4_7 <=> sK2 = k7_relat_1(sK2,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.54  fof(f265,plain,(
% 0.21/0.54    k2_relat_1(sK2) = k9_relat_1(sK2,sK1) | (~spl4_7 | ~spl4_24)),
% 0.21/0.54    inference(superposition,[],[f236,f127])).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    sK2 = k7_relat_1(sK2,sK1) | ~spl4_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f125])).
% 0.21/0.54  fof(f237,plain,(
% 0.21/0.54    spl4_24 | ~spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f101,f79,f235])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    ( ! [X3] : (k2_relat_1(k7_relat_1(sK2,X3)) = k9_relat_1(sK2,X3)) ) | ~spl4_2),
% 0.21/0.54    inference(resolution,[],[f47,f81])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.54  fof(f231,plain,(
% 0.21/0.54    ~spl4_23 | ~spl4_14 | spl4_18),
% 0.21/0.54    inference(avatar_split_clause,[],[f191,f180,f162,f228])).
% 0.21/0.54  fof(f180,plain,(
% 0.21/0.54    spl4_18 <=> k2_relat_1(sK2) = k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.54  fof(f191,plain,(
% 0.21/0.54    k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | (~spl4_14 | spl4_18)),
% 0.21/0.54    inference(superposition,[],[f182,f163])).
% 0.21/0.54  fof(f182,plain,(
% 0.21/0.54    k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) | spl4_18),
% 0.21/0.54    inference(avatar_component_clause,[],[f180])).
% 0.21/0.54  fof(f221,plain,(
% 0.21/0.54    spl4_22 | ~spl4_2 | ~spl4_21),
% 0.21/0.54    inference(avatar_split_clause,[],[f216,f211,f79,f218])).
% 0.21/0.54  fof(f211,plain,(
% 0.21/0.54    spl4_21 <=> v4_relat_1(sK2,k1_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.54  fof(f216,plain,(
% 0.21/0.54    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) | (~spl4_2 | ~spl4_21)),
% 0.21/0.54    inference(subsumption_resolution,[],[f215,f81])).
% 0.21/0.54  fof(f215,plain,(
% 0.21/0.54    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl4_21),
% 0.21/0.54    inference(resolution,[],[f213,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  % (32279)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.54  fof(f213,plain,(
% 0.21/0.54    v4_relat_1(sK2,k1_relat_1(sK2)) | ~spl4_21),
% 0.21/0.54    inference(avatar_component_clause,[],[f211])).
% 0.21/0.54  fof(f214,plain,(
% 0.21/0.54    spl4_21 | ~spl4_20),
% 0.21/0.54    inference(avatar_split_clause,[],[f202,f195,f211])).
% 0.21/0.54  fof(f195,plain,(
% 0.21/0.54    spl4_20 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.54  % (32278)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.54  fof(f202,plain,(
% 0.21/0.54    v4_relat_1(sK2,k1_relat_1(sK2)) | ~spl4_20),
% 0.21/0.54    inference(resolution,[],[f197,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.54  fof(f197,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) | ~spl4_20),
% 0.21/0.54    inference(avatar_component_clause,[],[f195])).
% 0.21/0.54  fof(f198,plain,(
% 0.21/0.54    spl4_20 | ~spl4_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f193,f103,f195])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    spl4_5 <=> sP3(sK2,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.54  fof(f193,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) | ~spl4_5),
% 0.21/0.54    inference(resolution,[],[f129,f105])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    sP3(sK2,sK0) | ~spl4_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f103])).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~sP3(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))) )),
% 0.21/0.54    inference(resolution,[],[f67,f64])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X2,X3,X1] : (~r1_tarski(k1_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~sP3(X3,X2)) )),
% 0.21/0.54    inference(general_splitting,[],[f63,f66_D])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X2,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | sP3(X3,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f66_D])).
% 0.21/0.54  fof(f66_D,plain,(
% 0.21/0.54    ( ! [X2,X3] : (( ! [X0] : ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) <=> ~sP3(X3,X2)) )),
% 0.21/0.54    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.54    inference(flattening,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).
% 0.21/0.54  fof(f183,plain,(
% 0.21/0.54    ~spl4_18 | ~spl4_1 | spl4_13),
% 0.21/0.54    inference(avatar_split_clause,[],[f169,f157,f69,f180])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    spl4_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    spl4_13 <=> k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) = k2_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) | (~spl4_1 | spl4_13)),
% 0.21/0.54    inference(backward_demodulation,[],[f159,f135])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    ( ! [X0] : (k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0)) ) | ~spl4_1),
% 0.21/0.54    inference(resolution,[],[f62,f71])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f69])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) | spl4_13),
% 0.21/0.54    inference(avatar_component_clause,[],[f157])).
% 0.21/0.54  fof(f178,plain,(
% 0.21/0.54    spl4_17 | ~spl4_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f122,f116,f175])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    spl4_6 <=> r1_tarski(k2_relat_1(sK2),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK0) | ~spl4_6),
% 0.21/0.54    inference(resolution,[],[f118,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    r1_tarski(k2_relat_1(sK2),sK0) | ~spl4_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f116])).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    spl4_16 | ~spl4_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f135,f69,f171])).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    spl4_14 | ~spl4_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f130,f69,f162])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    ( ! [X0] : (k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0)) ) | ~spl4_1),
% 0.21/0.54    inference(resolution,[],[f61,f71])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    ~spl4_13 | ~spl4_1 | spl4_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f150,f137,f69,f157])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    spl4_9 <=> k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) = k2_relset_1(sK1,sK0,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) | (~spl4_1 | spl4_9)),
% 0.21/0.54    inference(backward_demodulation,[],[f139,f123])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) | ~spl4_1),
% 0.21/0.54    inference(resolution,[],[f58,f71])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) | spl4_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f137])).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    spl4_11 | ~spl4_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f120,f69,f146])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) | ~spl4_1),
% 0.21/0.54    inference(resolution,[],[f57,f71])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    ~spl4_9 | ~spl4_10),
% 0.21/0.54    inference(avatar_split_clause,[],[f43,f141,f137])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    (k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.54    inference(ennf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 0.21/0.54    inference(negated_conjecture,[],[f17])).
% 0.21/0.54  fof(f17,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    spl4_7 | ~spl4_2 | ~spl4_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f108,f89,f79,f125])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    spl4_3 <=> v4_relat_1(sK2,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    sK2 = k7_relat_1(sK2,sK1) | (~spl4_2 | ~spl4_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f107,f81])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    sK2 = k7_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | ~spl4_3),
% 0.21/0.54    inference(resolution,[],[f53,f91])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    v4_relat_1(sK2,sK1) | ~spl4_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f89])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    spl4_6 | ~spl4_2 | ~spl4_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f110,f96,f79,f116])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    spl4_4 <=> v5_relat_1(sK2,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    r1_tarski(k2_relat_1(sK2),sK0) | (~spl4_2 | ~spl4_4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f109,f81])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    r1_tarski(k2_relat_1(sK2),sK0) | ~v1_relat_1(sK2) | ~spl4_4),
% 0.21/0.54    inference(resolution,[],[f98,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    v5_relat_1(sK2,sK0) | ~spl4_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f96])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    spl4_5 | ~spl4_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f94,f69,f103])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    sP3(sK2,sK0) | ~spl4_1),
% 0.21/0.54    inference(resolution,[],[f66,f71])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    spl4_4 | ~spl4_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f93,f69,f96])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    v5_relat_1(sK2,sK0) | ~spl4_1),
% 0.21/0.54    inference(resolution,[],[f60,f71])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    spl4_3 | ~spl4_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f87,f69,f89])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    v4_relat_1(sK2,sK1) | ~spl4_1),
% 0.21/0.54    inference(resolution,[],[f59,f71])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    spl4_2 | ~spl4_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f76,f69,f79])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    v1_relat_1(sK2) | ~spl4_1),
% 0.21/0.54    inference(resolution,[],[f73,f71])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 0.21/0.54    inference(resolution,[],[f44,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    spl4_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f42,f69])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (32260)------------------------------
% 0.21/0.55  % (32260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32260)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (32260)Memory used [KB]: 6396
% 0.21/0.55  % (32260)Time elapsed: 0.108 s
% 0.21/0.55  % (32260)------------------------------
% 0.21/0.55  % (32260)------------------------------
% 0.21/0.55  % (32257)Success in time 0.187 s
%------------------------------------------------------------------------------
