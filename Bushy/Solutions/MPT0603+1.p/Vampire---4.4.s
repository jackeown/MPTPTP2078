%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t207_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:58 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 200 expanded)
%              Number of leaves         :   28 (  74 expanded)
%              Depth                    :   10
%              Number of atoms          :  252 ( 464 expanded)
%              Number of equality atoms :   29 (  71 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f284,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f76,f83,f93,f102,f113,f122,f130,f170,f185,f212,f232,f242,f272,f276])).

fof(f276,plain,
    ( ~ spl4_0
    | ~ spl4_4
    | ~ spl4_6
    | spl4_15
    | ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f274,f92])).

fof(f92,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f274,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_0
    | ~ spl4_4
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f273,f194])).

fof(f194,plain,
    ( k7_relat_1(sK2,k1_xboole_0) = k1_xboole_0
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f184,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t207_relat_1.p',t6_boole)).

fof(f184,plain,
    ( v1_xboole_0(k7_relat_1(sK2,k1_xboole_0))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl4_18
  <=> v1_xboole_0(k7_relat_1(sK2,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f273,plain,
    ( ~ v1_xboole_0(k7_relat_1(sK2,k1_xboole_0))
    | ~ spl4_0
    | ~ spl4_4
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f262,f171])).

fof(f171,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f82,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k3_xboole_0(X0,X1) )
      & ( k1_xboole_0 = k3_xboole_0(X0,X1)
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k1_xboole_0 = k3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t207_relat_1.p',d7_xboole_0)).

fof(f82,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_4
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f262,plain,
    ( ~ v1_xboole_0(k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_15 ),
    inference(backward_demodulation,[],[f243,f129])).

fof(f129,plain,
    ( ~ v1_xboole_0(k7_relat_1(k7_relat_1(sK2,sK0),sK1))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl4_15
  <=> ~ v1_xboole_0(k7_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f243,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f68,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t207_relat_1.p',t100_relat_1)).

fof(f68,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl4_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f272,plain,
    ( ~ spl4_0
    | ~ spl4_4
    | ~ spl4_6
    | spl4_15
    | ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f270,f103])).

fof(f103,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f92,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t207_relat_1.p',t7_boole)).

fof(f270,plain,
    ( r2_hidden(sK3(k1_xboole_0),k1_xboole_0)
    | ~ spl4_0
    | ~ spl4_4
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f269,f194])).

fof(f269,plain,
    ( r2_hidden(sK3(k7_relat_1(sK2,k1_xboole_0)),k7_relat_1(sK2,k1_xboole_0))
    | ~ spl4_0
    | ~ spl4_4
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f261,f171])).

fof(f261,plain,
    ( r2_hidden(sK3(k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),k7_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_15 ),
    inference(backward_demodulation,[],[f243,f143])).

fof(f143,plain,
    ( r2_hidden(sK3(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k7_relat_1(k7_relat_1(sK2,sK0),sK1))
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f129,f48,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t207_relat_1.p',t2_subset)).

fof(f48,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t207_relat_1.p',existence_m1_subset_1)).

fof(f242,plain,
    ( ~ spl4_25
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f215,f210,f240])).

fof(f240,plain,
    ( spl4_25
  <=> ~ r2_hidden(sK1,sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f210,plain,
    ( spl4_20
  <=> r2_hidden(sK3(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f215,plain,
    ( ~ r2_hidden(sK1,sK3(sK1))
    | ~ spl4_20 ),
    inference(unit_resulting_resolution,[],[f211,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t207_relat_1.p',antisymmetry_r2_hidden)).

fof(f211,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f210])).

fof(f232,plain,(
    spl4_22 ),
    inference(avatar_split_clause,[],[f221,f230])).

fof(f230,plain,
    ( spl4_22
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f221,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f49,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f49,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/relat_1__t207_relat_1.p',idempotence_k3_xboole_0)).

fof(f212,plain,
    ( spl4_20
    | spl4_17 ),
    inference(avatar_split_clause,[],[f177,f168,f210])).

fof(f168,plain,
    ( spl4_17
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f177,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | ~ spl4_17 ),
    inference(unit_resulting_resolution,[],[f48,f169,f54])).

fof(f169,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f168])).

fof(f185,plain,
    ( spl4_18
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f158,f91,f67,f183])).

fof(f158,plain,
    ( v1_xboole_0(k7_relat_1(sK2,k1_xboole_0))
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f68,f92,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_xboole_0(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X0) )
     => ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t207_relat_1.p',fc16_relat_1)).

fof(f170,plain,
    ( ~ spl4_17
    | ~ spl4_0
    | spl4_15 ),
    inference(avatar_split_clause,[],[f161,f128,f67,f168])).

fof(f161,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl4_0
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f104,f129,f56])).

fof(f104,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK2,X0))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f68,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t207_relat_1.p',dt_k7_relat_1)).

fof(f130,plain,
    ( ~ spl4_15
    | spl4_13 ),
    inference(avatar_split_clause,[],[f123,f120,f128])).

fof(f120,plain,
    ( spl4_13
  <=> k7_relat_1(k7_relat_1(sK2,sK0),sK1) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f123,plain,
    ( ~ v1_xboole_0(k7_relat_1(k7_relat_1(sK2,sK0),sK1))
    | ~ spl4_13 ),
    inference(unit_resulting_resolution,[],[f121,f47])).

fof(f121,plain,
    ( k7_relat_1(k7_relat_1(sK2,sK0),sK1) != k1_xboole_0
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f120])).

fof(f122,plain,(
    ~ spl4_13 ),
    inference(avatar_split_clause,[],[f44,f120])).

fof(f44,plain,(
    k7_relat_1(k7_relat_1(sK2,sK0),sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( k7_relat_1(k7_relat_1(sK2,sK0),sK1) != k1_xboole_0
    & r1_xboole_0(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) != k1_xboole_0
        & r1_xboole_0(X0,X1)
        & v1_relat_1(X2) )
   => ( k7_relat_1(k7_relat_1(sK2,sK0),sK1) != k1_xboole_0
      & r1_xboole_0(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) != k1_xboole_0
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) != k1_xboole_0
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_xboole_0(X0,X1)
         => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t207_relat_1.p',t207_relat_1)).

fof(f113,plain,
    ( spl4_10
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f106,f81,f111])).

fof(f111,plain,
    ( spl4_10
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f106,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f82,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t207_relat_1.p',symmetry_r1_xboole_0)).

fof(f102,plain,
    ( spl4_8
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f84,f74,f100])).

fof(f100,plain,
    ( spl4_8
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f74,plain,
    ( spl4_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f84,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f75,f47])).

fof(f75,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f93,plain,
    ( spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f86,f74,f91])).

fof(f86,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f84,f75])).

fof(f83,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f43,f81])).

fof(f43,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f45,f74])).

fof(f45,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t207_relat_1.p',dt_o_0_0_xboole_0)).

fof(f69,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f42,f67])).

fof(f42,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
