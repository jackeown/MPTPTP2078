%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t73_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:32 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 206 expanded)
%              Number of leaves         :   28 (  83 expanded)
%              Depth                    :    9
%              Number of atoms          :  196 ( 387 expanded)
%              Number of equality atoms :   42 ( 106 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f615,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f66,f73,f80,f90,f99,f109,f153,f165,f174,f312,f321,f460,f501,f595,f611])).

fof(f611,plain,
    ( spl3_5
    | ~ spl3_28 ),
    inference(avatar_contradiction_clause,[],[f610])).

fof(f610,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f601,f72])).

fof(f72,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_5
  <=> ~ r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f601,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_28 ),
    inference(superposition,[],[f122,f594])).

fof(f594,plain,
    ( k3_xboole_0(sK0,sK1) = sK0
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f593])).

fof(f593,plain,
    ( spl3_28
  <=> k3_xboole_0(sK0,sK1) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f122,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(X3,X2),X2) ),
    inference(superposition,[],[f44,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t73_xboole_1.p',commutativity_k3_xboole_0)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t73_xboole_1.p',t17_xboole_1)).

fof(f595,plain,
    ( spl3_28
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f563,f163,f151,f593])).

fof(f151,plain,
    ( spl3_14
  <=> k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f163,plain,
    ( spl3_16
  <=> k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f563,plain,
    ( k3_xboole_0(sK0,sK1) = sK0
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(superposition,[],[f276,f152])).

fof(f152,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f151])).

fof(f276,plain,
    ( ! [X18] : k3_xboole_0(sK0,X18) = k3_xboole_0(sK0,k2_xboole_0(X18,sK2))
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f258,f39])).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t73_xboole_1.p',t1_boole)).

fof(f258,plain,
    ( ! [X18] : k2_xboole_0(k3_xboole_0(sK0,X18),k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(X18,sK2))
    | ~ spl3_16 ),
    inference(superposition,[],[f52,f164])).

fof(f164,plain,
    ( k3_xboole_0(sK0,sK2) = k1_xboole_0
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f163])).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t73_xboole_1.p',t23_xboole_1)).

fof(f501,plain,
    ( spl3_26
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f490,f458,f163,f499])).

fof(f499,plain,
    ( spl3_26
  <=> r1_tarski(sK0,k2_xboole_0(sK2,k2_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f458,plain,
    ( spl3_24
  <=> k3_xboole_0(sK0,k2_xboole_0(sK0,sK2)) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f490,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK2,k2_xboole_0(sK0,sK2)))
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f478,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t73_xboole_1.p',commutativity_k2_xboole_0)).

fof(f478,plain,
    ( r1_tarski(sK0,k2_xboole_0(k2_xboole_0(sK0,sK2),sK2))
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(superposition,[],[f302,f459])).

fof(f459,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK0,sK2)) = sK0
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f458])).

fof(f302,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),k2_xboole_0(X0,sK2))
    | ~ spl3_16 ),
    inference(superposition,[],[f285,f45])).

fof(f285,plain,
    ( ! [X7] : r1_tarski(k3_xboole_0(sK0,X7),k2_xboole_0(sK2,X7))
    | ~ spl3_16 ),
    inference(superposition,[],[f122,f270])).

fof(f270,plain,
    ( ! [X18] : k3_xboole_0(sK0,X18) = k3_xboole_0(sK0,k2_xboole_0(sK2,X18))
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f248,f111])).

fof(f111,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f45,f39])).

fof(f248,plain,
    ( ! [X18] : k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X18)) = k3_xboole_0(sK0,k2_xboole_0(sK2,X18))
    | ~ spl3_16 ),
    inference(superposition,[],[f52,f164])).

fof(f460,plain,
    ( spl3_24
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f313,f310,f458])).

fof(f310,plain,
    ( spl3_20
  <=> r1_tarski(sK0,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f313,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK0,sK2)) = sK0
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f311,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t73_xboole_1.p',t28_xboole_1)).

fof(f311,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK0,sK2))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f310])).

fof(f321,plain,
    ( spl3_22
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f294,f163,f151,f319])).

fof(f319,plain,
    ( spl3_22
  <=> r1_tarski(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f294,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)))
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(superposition,[],[f285,f152])).

fof(f312,plain,
    ( spl3_20
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f304,f163,f310])).

fof(f304,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK0,sK2))
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f297,f45])).

fof(f297,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK2,sK0))
    | ~ spl3_16 ),
    inference(superposition,[],[f285,f42])).

fof(f42,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t73_xboole_1.p',idempotence_k3_xboole_0)).

fof(f174,plain,
    ( spl3_18
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f155,f107,f172])).

fof(f172,plain,
    ( spl3_18
  <=> k3_xboole_0(sK2,sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f107,plain,
    ( spl3_12
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f155,plain,
    ( k3_xboole_0(sK2,sK0) = k1_xboole_0
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f108,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t73_xboole_1.p',d7_xboole_0)).

fof(f108,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f107])).

fof(f165,plain,
    ( spl3_16
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f154,f64,f163])).

fof(f64,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f154,plain,
    ( k3_xboole_0(sK0,sK2) = k1_xboole_0
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f65,f49])).

fof(f65,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f153,plain,
    ( spl3_14
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f141,f78,f151])).

fof(f78,plain,
    ( spl3_6
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f141,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f79,f48])).

fof(f79,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f109,plain,
    ( spl3_12
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f102,f64,f107])).

fof(f102,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f65,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t73_xboole_1.p',symmetry_r1_xboole_0)).

fof(f99,plain,
    ( spl3_10
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f81,f57,f97])).

fof(f97,plain,
    ( spl3_10
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f57,plain,
    ( spl3_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f81,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl3_0 ),
    inference(unit_resulting_resolution,[],[f58,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t73_xboole_1.p',t6_boole)).

fof(f58,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f57])).

fof(f90,plain,
    ( spl3_8
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f83,f57,f88])).

fof(f88,plain,
    ( spl3_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f83,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_0 ),
    inference(backward_demodulation,[],[f81,f58])).

fof(f80,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f35,f78])).

fof(f35,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t73_xboole_1.p',t73_xboole_1)).

fof(f73,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f37,f71])).

fof(f37,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f36,f64])).

fof(f36,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f38,f57])).

fof(f38,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t73_xboole_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
