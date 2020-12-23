%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 273 expanded)
%              Number of leaves         :   40 ( 135 expanded)
%              Depth                    :    7
%              Number of atoms          :  353 ( 627 expanded)
%              Number of equality atoms :   97 ( 196 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f828,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f48,f52,f56,f60,f66,f72,f76,f82,f91,f95,f99,f105,f117,f139,f161,f173,f179,f183,f187,f366,f449,f552,f622,f653,f694,f758,f789,f825])).

fof(f825,plain,
    ( spl3_10
    | ~ spl3_11
    | ~ spl3_52 ),
    inference(avatar_contradiction_clause,[],[f824])).

fof(f824,plain,
    ( $false
    | spl3_10
    | ~ spl3_11
    | ~ spl3_52 ),
    inference(subsumption_resolution,[],[f813,f81])).

fof(f81,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_10
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f813,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_11
    | ~ spl3_52 ),
    inference(superposition,[],[f90,f788])).

fof(f788,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK2))
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f787])).

fof(f787,plain,
    ( spl3_52
  <=> ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f90,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl3_11
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f789,plain,
    ( spl3_52
    | ~ spl3_6
    | ~ spl3_50 ),
    inference(avatar_split_clause,[],[f759,f756,f58,f787])).

fof(f58,plain,
    ( spl3_6
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f756,plain,
    ( spl3_50
  <=> ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f759,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK2))
    | ~ spl3_6
    | ~ spl3_50 ),
    inference(superposition,[],[f757,f59])).

fof(f59,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f757,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f756])).

fof(f758,plain,
    ( spl3_50
    | ~ spl3_24
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f698,f691,f181,f756])).

fof(f181,plain,
    ( spl3_24
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f691,plain,
    ( spl3_46
  <=> sK0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f698,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)
    | ~ spl3_24
    | ~ spl3_46 ),
    inference(superposition,[],[f182,f693])).

fof(f693,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f691])).

fof(f182,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f181])).

fof(f694,plain,
    ( spl3_46
    | ~ spl3_6
    | ~ spl3_18
    | ~ spl3_24
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f665,f650,f181,f137,f58,f691])).

fof(f137,plain,
    ( spl3_18
  <=> ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f650,plain,
    ( spl3_45
  <=> sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f665,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_6
    | ~ spl3_18
    | ~ spl3_24
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f664,f138])).

fof(f138,plain,
    ( ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f137])).

fof(f664,plain,
    ( sK0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK2))
    | ~ spl3_6
    | ~ spl3_24
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f654,f59])).

fof(f654,plain,
    ( sK0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k1_xboole_0))
    | ~ spl3_24
    | ~ spl3_45 ),
    inference(superposition,[],[f652,f182])).

fof(f652,plain,
    ( sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0)
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f650])).

fof(f653,plain,
    ( spl3_45
    | ~ spl3_14
    | ~ spl3_24
    | ~ spl3_37
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f638,f619,f447,f181,f103,f650])).

fof(f103,plain,
    ( spl3_14
  <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f447,plain,
    ( spl3_37
  <=> ! [X20,X21] : k4_xboole_0(k2_xboole_0(X20,X21),k4_xboole_0(X21,X20)) = X20 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f619,plain,
    ( spl3_42
  <=> k4_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f638,plain,
    ( sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0)
    | ~ spl3_14
    | ~ spl3_24
    | ~ spl3_37
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f637,f104])).

fof(f104,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f103])).

fof(f637,plain,
    ( sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,sK0)))
    | ~ spl3_24
    | ~ spl3_37
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f633,f182])).

fof(f633,plain,
    ( sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK0))
    | ~ spl3_37
    | ~ spl3_42 ),
    inference(superposition,[],[f448,f621])).

fof(f621,plain,
    ( k4_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f619])).

fof(f448,plain,
    ( ! [X21,X20] : k4_xboole_0(k2_xboole_0(X20,X21),k4_xboole_0(X21,X20)) = X20
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f447])).

fof(f622,plain,
    ( spl3_42
    | ~ spl3_4
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f595,f549,f50,f619])).

fof(f50,plain,
    ( spl3_4
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f549,plain,
    ( spl3_40
  <=> k4_xboole_0(sK0,sK2) = k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f595,plain,
    ( k4_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_4
    | ~ spl3_40 ),
    inference(superposition,[],[f551,f51])).

fof(f51,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f551,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k1_xboole_0)
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f549])).

fof(f552,plain,
    ( spl3_40
    | ~ spl3_23
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f390,f364,f176,f549])).

fof(f176,plain,
    ( spl3_23
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f364,plain,
    ( spl3_34
  <=> ! [X18,X19] : k4_xboole_0(k2_xboole_0(X18,X19),k4_xboole_0(X18,X19)) = X19 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f390,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k1_xboole_0)
    | ~ spl3_23
    | ~ spl3_34 ),
    inference(superposition,[],[f365,f178])).

fof(f178,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f176])).

fof(f365,plain,
    ( ! [X19,X18] : k4_xboole_0(k2_xboole_0(X18,X19),k4_xboole_0(X18,X19)) = X19
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f364])).

fof(f449,plain,
    ( spl3_37
    | ~ spl3_4
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f345,f185,f159,f97,f50,f447])).

fof(f97,plain,
    ( spl3_13
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f159,plain,
    ( spl3_21
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f185,plain,
    ( spl3_25
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f345,plain,
    ( ! [X21,X20] : k4_xboole_0(k2_xboole_0(X20,X21),k4_xboole_0(X21,X20)) = X20
    | ~ spl3_4
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f344,f51])).

fof(f344,plain,
    ( ! [X21,X20] : k4_xboole_0(k2_xboole_0(X20,X21),k4_xboole_0(X21,X20)) = k4_xboole_0(X20,k1_xboole_0)
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f321,f98])).

fof(f98,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f97])).

fof(f321,plain,
    ( ! [X21,X20] : k4_xboole_0(X20,k4_xboole_0(X20,k2_xboole_0(X20,X21))) = k4_xboole_0(k2_xboole_0(X20,X21),k4_xboole_0(X21,X20))
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(superposition,[],[f186,f160])).

fof(f160,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f159])).

fof(f186,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f185])).

fof(f366,plain,
    ( spl3_34
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f343,f185,f103,f93,f50,f364])).

fof(f93,plain,
    ( spl3_12
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f343,plain,
    ( ! [X19,X18] : k4_xboole_0(k2_xboole_0(X18,X19),k4_xboole_0(X18,X19)) = X19
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f342,f51])).

fof(f342,plain,
    ( ! [X19,X18] : k4_xboole_0(k2_xboole_0(X18,X19),k4_xboole_0(X18,X19)) = k4_xboole_0(X19,k1_xboole_0)
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f320,f104])).

fof(f320,plain,
    ( ! [X19,X18] : k4_xboole_0(X19,k4_xboole_0(X19,k2_xboole_0(X18,X19))) = k4_xboole_0(k2_xboole_0(X18,X19),k4_xboole_0(X18,X19))
    | ~ spl3_12
    | ~ spl3_25 ),
    inference(superposition,[],[f186,f94])).

fof(f94,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f93])).

fof(f187,plain,(
    spl3_25 ),
    inference(avatar_split_clause,[],[f32,f185])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f24,f26,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f183,plain,(
    spl3_24 ),
    inference(avatar_split_clause,[],[f31,f181])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f179,plain,
    ( spl3_23
    | ~ spl3_1
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f174,f171,f35,f176])).

fof(f35,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f171,plain,
    ( spl3_22
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f174,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_1
    | ~ spl3_22 ),
    inference(resolution,[],[f172,f37])).

fof(f37,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f172,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f171])).

fof(f173,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f33,f171])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f26])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f161,plain,
    ( spl3_21
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f108,f93,f58,f159])).

fof(f108,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(superposition,[],[f94,f59])).

fof(f139,plain,
    ( spl3_18
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f118,f115,f58,f137])).

fof(f115,plain,
    ( spl3_15
  <=> ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f118,plain,
    ( ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(superposition,[],[f116,f59])).

fof(f116,plain,
    ( ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f115])).

fof(f117,plain,
    ( spl3_15
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f112,f93,f50,f115])).

fof(f112,plain,
    ( ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f110,f51])).

fof(f110,plain,
    ( ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(superposition,[],[f94,f51])).

fof(f105,plain,
    ( spl3_14
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f85,f74,f64,f103])).

fof(f64,plain,
    ( spl3_7
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f74,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f85,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(resolution,[],[f75,f65])).

fof(f65,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f74])).

fof(f99,plain,
    ( spl3_13
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f84,f74,f54,f97])).

fof(f54,plain,
    ( spl3_5
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f84,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(resolution,[],[f75,f55])).

fof(f55,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f95,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f27,f93])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f91,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f83,f74,f45,f88])).

fof(f45,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f83,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f75,f47])).

fof(f47,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f82,plain,
    ( ~ spl3_10
    | spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f77,f70,f40,f79])).

fof(f40,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f70,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f77,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_2
    | ~ spl3_8 ),
    inference(resolution,[],[f71,f42])).

fof(f42,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f70])).

fof(f76,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f30,f74])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f72,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f29,f70])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f66,plain,
    ( spl3_7
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f61,f58,f54,f64])).

fof(f61,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0))
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(superposition,[],[f55,f59])).

fof(f60,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f25,f58])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f56,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f23,f54])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f52,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f22,f50])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f48,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f19,f45])).

fof(f19,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f43,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f21,f40])).

fof(f21,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f20,f35])).

fof(f20,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n006.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 19:41:37 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.20/0.45  % (19892)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (19901)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.45  % (19890)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.45  % (19891)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.45  % (19896)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.45  % (19893)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.46  % (19902)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (19894)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (19900)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (19899)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (19887)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (19897)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (19898)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (19888)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (19904)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.48  % (19895)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (19889)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (19894)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f828,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f38,f43,f48,f52,f56,f60,f66,f72,f76,f82,f91,f95,f99,f105,f117,f139,f161,f173,f179,f183,f187,f366,f449,f552,f622,f653,f694,f758,f789,f825])).
% 0.20/0.49  fof(f825,plain,(
% 0.20/0.49    spl3_10 | ~spl3_11 | ~spl3_52),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f824])).
% 0.20/0.49  fof(f824,plain,(
% 0.20/0.49    $false | (spl3_10 | ~spl3_11 | ~spl3_52)),
% 0.20/0.49    inference(subsumption_resolution,[],[f813,f81])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    k1_xboole_0 != k4_xboole_0(sK0,sK1) | spl3_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f79])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    spl3_10 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.49  fof(f813,plain,(
% 0.20/0.49    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl3_11 | ~spl3_52)),
% 0.20/0.49    inference(superposition,[],[f90,f788])).
% 0.20/0.49  fof(f788,plain,(
% 0.20/0.49    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK2))) ) | ~spl3_52),
% 0.20/0.49    inference(avatar_component_clause,[],[f787])).
% 0.20/0.49  fof(f787,plain,(
% 0.20/0.49    spl3_52 <=> ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f88])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    spl3_11 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.49  fof(f789,plain,(
% 0.20/0.49    spl3_52 | ~spl3_6 | ~spl3_50),
% 0.20/0.49    inference(avatar_split_clause,[],[f759,f756,f58,f787])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    spl3_6 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.49  fof(f756,plain,(
% 0.20/0.49    spl3_50 <=> ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.20/0.49  fof(f759,plain,(
% 0.20/0.49    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK2))) ) | (~spl3_6 | ~spl3_50)),
% 0.20/0.49    inference(superposition,[],[f757,f59])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f58])).
% 0.20/0.49  fof(f757,plain,(
% 0.20/0.49    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)) ) | ~spl3_50),
% 0.20/0.49    inference(avatar_component_clause,[],[f756])).
% 0.20/0.49  fof(f758,plain,(
% 0.20/0.49    spl3_50 | ~spl3_24 | ~spl3_46),
% 0.20/0.49    inference(avatar_split_clause,[],[f698,f691,f181,f756])).
% 0.20/0.49  fof(f181,plain,(
% 0.20/0.49    spl3_24 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.49  fof(f691,plain,(
% 0.20/0.49    spl3_46 <=> sK0 = k4_xboole_0(sK0,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.20/0.49  fof(f698,plain,(
% 0.20/0.49    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)) ) | (~spl3_24 | ~spl3_46)),
% 0.20/0.49    inference(superposition,[],[f182,f693])).
% 0.20/0.49  fof(f693,plain,(
% 0.20/0.49    sK0 = k4_xboole_0(sK0,sK2) | ~spl3_46),
% 0.20/0.49    inference(avatar_component_clause,[],[f691])).
% 0.20/0.49  fof(f182,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl3_24),
% 0.20/0.49    inference(avatar_component_clause,[],[f181])).
% 0.20/0.49  fof(f694,plain,(
% 0.20/0.49    spl3_46 | ~spl3_6 | ~spl3_18 | ~spl3_24 | ~spl3_45),
% 0.20/0.49    inference(avatar_split_clause,[],[f665,f650,f181,f137,f58,f691])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    spl3_18 <=> ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.49  fof(f650,plain,(
% 0.20/0.49    spl3_45 <=> sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.20/0.49  fof(f665,plain,(
% 0.20/0.49    sK0 = k4_xboole_0(sK0,sK2) | (~spl3_6 | ~spl3_18 | ~spl3_24 | ~spl3_45)),
% 0.20/0.49    inference(forward_demodulation,[],[f664,f138])).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) ) | ~spl3_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f137])).
% 0.20/0.49  fof(f664,plain,(
% 0.20/0.49    sK0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK2)) | (~spl3_6 | ~spl3_24 | ~spl3_45)),
% 0.20/0.49    inference(forward_demodulation,[],[f654,f59])).
% 0.20/0.49  fof(f654,plain,(
% 0.20/0.49    sK0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k1_xboole_0)) | (~spl3_24 | ~spl3_45)),
% 0.20/0.49    inference(superposition,[],[f652,f182])).
% 0.20/0.49  fof(f652,plain,(
% 0.20/0.49    sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) | ~spl3_45),
% 0.20/0.49    inference(avatar_component_clause,[],[f650])).
% 0.20/0.49  fof(f653,plain,(
% 0.20/0.49    spl3_45 | ~spl3_14 | ~spl3_24 | ~spl3_37 | ~spl3_42),
% 0.20/0.49    inference(avatar_split_clause,[],[f638,f619,f447,f181,f103,f650])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    spl3_14 <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.49  fof(f447,plain,(
% 0.20/0.49    spl3_37 <=> ! [X20,X21] : k4_xboole_0(k2_xboole_0(X20,X21),k4_xboole_0(X21,X20)) = X20),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.20/0.49  fof(f619,plain,(
% 0.20/0.49    spl3_42 <=> k4_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.20/0.49  fof(f638,plain,(
% 0.20/0.49    sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) | (~spl3_14 | ~spl3_24 | ~spl3_37 | ~spl3_42)),
% 0.20/0.49    inference(forward_demodulation,[],[f637,f104])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))) ) | ~spl3_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f103])).
% 0.20/0.49  fof(f637,plain,(
% 0.20/0.49    sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK2,sK0))) | (~spl3_24 | ~spl3_37 | ~spl3_42)),
% 0.20/0.49    inference(forward_demodulation,[],[f633,f182])).
% 0.20/0.49  fof(f633,plain,(
% 0.20/0.49    sK0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK0)) | (~spl3_37 | ~spl3_42)),
% 0.20/0.49    inference(superposition,[],[f448,f621])).
% 0.20/0.49  fof(f621,plain,(
% 0.20/0.49    k4_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl3_42),
% 0.20/0.49    inference(avatar_component_clause,[],[f619])).
% 0.20/0.49  fof(f448,plain,(
% 0.20/0.49    ( ! [X21,X20] : (k4_xboole_0(k2_xboole_0(X20,X21),k4_xboole_0(X21,X20)) = X20) ) | ~spl3_37),
% 0.20/0.49    inference(avatar_component_clause,[],[f447])).
% 0.20/0.49  fof(f622,plain,(
% 0.20/0.49    spl3_42 | ~spl3_4 | ~spl3_40),
% 0.20/0.49    inference(avatar_split_clause,[],[f595,f549,f50,f619])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    spl3_4 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.49  fof(f549,plain,(
% 0.20/0.49    spl3_40 <=> k4_xboole_0(sK0,sK2) = k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.20/0.49  fof(f595,plain,(
% 0.20/0.49    k4_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | (~spl3_4 | ~spl3_40)),
% 0.20/0.49    inference(superposition,[],[f551,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f50])).
% 0.20/0.49  fof(f551,plain,(
% 0.20/0.49    k4_xboole_0(sK0,sK2) = k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k1_xboole_0) | ~spl3_40),
% 0.20/0.49    inference(avatar_component_clause,[],[f549])).
% 0.20/0.49  fof(f552,plain,(
% 0.20/0.49    spl3_40 | ~spl3_23 | ~spl3_34),
% 0.20/0.49    inference(avatar_split_clause,[],[f390,f364,f176,f549])).
% 0.20/0.49  fof(f176,plain,(
% 0.20/0.49    spl3_23 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.49  fof(f364,plain,(
% 0.20/0.49    spl3_34 <=> ! [X18,X19] : k4_xboole_0(k2_xboole_0(X18,X19),k4_xboole_0(X18,X19)) = X19),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.20/0.49  fof(f390,plain,(
% 0.20/0.49    k4_xboole_0(sK0,sK2) = k4_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k1_xboole_0) | (~spl3_23 | ~spl3_34)),
% 0.20/0.49    inference(superposition,[],[f365,f178])).
% 0.20/0.49  fof(f178,plain,(
% 0.20/0.49    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl3_23),
% 0.20/0.49    inference(avatar_component_clause,[],[f176])).
% 0.20/0.49  fof(f365,plain,(
% 0.20/0.49    ( ! [X19,X18] : (k4_xboole_0(k2_xboole_0(X18,X19),k4_xboole_0(X18,X19)) = X19) ) | ~spl3_34),
% 0.20/0.49    inference(avatar_component_clause,[],[f364])).
% 0.20/0.49  fof(f449,plain,(
% 0.20/0.49    spl3_37 | ~spl3_4 | ~spl3_13 | ~spl3_21 | ~spl3_25),
% 0.20/0.49    inference(avatar_split_clause,[],[f345,f185,f159,f97,f50,f447])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    spl3_13 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.49  fof(f159,plain,(
% 0.20/0.49    spl3_21 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.49  fof(f185,plain,(
% 0.20/0.49    spl3_25 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.49  fof(f345,plain,(
% 0.20/0.49    ( ! [X21,X20] : (k4_xboole_0(k2_xboole_0(X20,X21),k4_xboole_0(X21,X20)) = X20) ) | (~spl3_4 | ~spl3_13 | ~spl3_21 | ~spl3_25)),
% 0.20/0.49    inference(forward_demodulation,[],[f344,f51])).
% 0.20/0.49  fof(f344,plain,(
% 0.20/0.49    ( ! [X21,X20] : (k4_xboole_0(k2_xboole_0(X20,X21),k4_xboole_0(X21,X20)) = k4_xboole_0(X20,k1_xboole_0)) ) | (~spl3_13 | ~spl3_21 | ~spl3_25)),
% 0.20/0.49    inference(forward_demodulation,[],[f321,f98])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) ) | ~spl3_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f97])).
% 0.20/0.49  fof(f321,plain,(
% 0.20/0.49    ( ! [X21,X20] : (k4_xboole_0(X20,k4_xboole_0(X20,k2_xboole_0(X20,X21))) = k4_xboole_0(k2_xboole_0(X20,X21),k4_xboole_0(X21,X20))) ) | (~spl3_21 | ~spl3_25)),
% 0.20/0.49    inference(superposition,[],[f186,f160])).
% 0.20/0.49  fof(f160,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) ) | ~spl3_21),
% 0.20/0.49    inference(avatar_component_clause,[],[f159])).
% 0.20/0.49  fof(f186,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl3_25),
% 0.20/0.49    inference(avatar_component_clause,[],[f185])).
% 0.20/0.49  fof(f366,plain,(
% 0.20/0.49    spl3_34 | ~spl3_4 | ~spl3_12 | ~spl3_14 | ~spl3_25),
% 0.20/0.49    inference(avatar_split_clause,[],[f343,f185,f103,f93,f50,f364])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    spl3_12 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.49  fof(f343,plain,(
% 0.20/0.49    ( ! [X19,X18] : (k4_xboole_0(k2_xboole_0(X18,X19),k4_xboole_0(X18,X19)) = X19) ) | (~spl3_4 | ~spl3_12 | ~spl3_14 | ~spl3_25)),
% 0.20/0.49    inference(forward_demodulation,[],[f342,f51])).
% 0.20/0.49  fof(f342,plain,(
% 0.20/0.49    ( ! [X19,X18] : (k4_xboole_0(k2_xboole_0(X18,X19),k4_xboole_0(X18,X19)) = k4_xboole_0(X19,k1_xboole_0)) ) | (~spl3_12 | ~spl3_14 | ~spl3_25)),
% 0.20/0.49    inference(forward_demodulation,[],[f320,f104])).
% 0.20/0.49  fof(f320,plain,(
% 0.20/0.49    ( ! [X19,X18] : (k4_xboole_0(X19,k4_xboole_0(X19,k2_xboole_0(X18,X19))) = k4_xboole_0(k2_xboole_0(X18,X19),k4_xboole_0(X18,X19))) ) | (~spl3_12 | ~spl3_25)),
% 0.20/0.49    inference(superposition,[],[f186,f94])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) ) | ~spl3_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f93])).
% 0.20/0.49  fof(f187,plain,(
% 0.20/0.49    spl3_25),
% 0.20/0.49    inference(avatar_split_clause,[],[f32,f185])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f24,f26,f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.49  fof(f183,plain,(
% 0.20/0.49    spl3_24),
% 0.20/0.49    inference(avatar_split_clause,[],[f31,f181])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.49  fof(f179,plain,(
% 0.20/0.49    spl3_23 | ~spl3_1 | ~spl3_22),
% 0.20/0.49    inference(avatar_split_clause,[],[f174,f171,f35,f176])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    spl3_1 <=> r1_xboole_0(sK0,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f171,plain,(
% 0.20/0.49    spl3_22 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | (~spl3_1 | ~spl3_22)),
% 0.20/0.49    inference(resolution,[],[f172,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    r1_xboole_0(sK0,sK2) | ~spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f35])).
% 0.20/0.49  fof(f172,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_22),
% 0.20/0.49    inference(avatar_component_clause,[],[f171])).
% 0.20/0.49  fof(f173,plain,(
% 0.20/0.49    spl3_22),
% 0.20/0.49    inference(avatar_split_clause,[],[f33,f171])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f28,f26])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.49    inference(unused_predicate_definition_removal,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.49  fof(f161,plain,(
% 0.20/0.49    spl3_21 | ~spl3_6 | ~spl3_12),
% 0.20/0.49    inference(avatar_split_clause,[],[f108,f93,f58,f159])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) ) | (~spl3_6 | ~spl3_12)),
% 0.20/0.49    inference(superposition,[],[f94,f59])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    spl3_18 | ~spl3_6 | ~spl3_15),
% 0.20/0.49    inference(avatar_split_clause,[],[f118,f115,f58,f137])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    spl3_15 <=> ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) ) | (~spl3_6 | ~spl3_15)),
% 0.20/0.49    inference(superposition,[],[f116,f59])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) ) | ~spl3_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f115])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    spl3_15 | ~spl3_4 | ~spl3_12),
% 0.20/0.49    inference(avatar_split_clause,[],[f112,f93,f50,f115])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) ) | (~spl3_4 | ~spl3_12)),
% 0.20/0.49    inference(forward_demodulation,[],[f110,f51])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) ) | (~spl3_4 | ~spl3_12)),
% 0.20/0.49    inference(superposition,[],[f94,f51])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    spl3_14 | ~spl3_7 | ~spl3_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f85,f74,f64,f103])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    spl3_7 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X1,X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    spl3_9 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))) ) | (~spl3_7 | ~spl3_9)),
% 0.20/0.49    inference(resolution,[],[f75,f65])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) ) | ~spl3_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f64])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) ) | ~spl3_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f74])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    spl3_13 | ~spl3_5 | ~spl3_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f84,f74,f54,f97])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    spl3_5 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) ) | (~spl3_5 | ~spl3_9)),
% 0.20/0.49    inference(resolution,[],[f75,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl3_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f54])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    spl3_12),
% 0.20/0.49    inference(avatar_split_clause,[],[f27,f93])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    spl3_11 | ~spl3_3 | ~spl3_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f83,f74,f45,f88])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    spl3_3 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | (~spl3_3 | ~spl3_9)),
% 0.20/0.49    inference(resolution,[],[f75,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f45])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ~spl3_10 | spl3_2 | ~spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f77,f70,f40,f79])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    spl3_8 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    k1_xboole_0 != k4_xboole_0(sK0,sK1) | (spl3_2 | ~spl3_8)),
% 0.20/0.49    inference(resolution,[],[f71,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ~r1_tarski(sK0,sK1) | spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f40])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) ) | ~spl3_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f70])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    spl3_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f30,f74])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f29,f70])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    spl3_7 | ~spl3_5 | ~spl3_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f61,f58,f54,f64])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) ) | (~spl3_5 | ~spl3_6)),
% 0.20/0.49    inference(superposition,[],[f55,f59])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    spl3_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f25,f58])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    spl3_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f23,f54])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f22,f50])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f19,f45])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.20/0.49    inference(flattening,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.20/0.49    inference(negated_conjecture,[],[f10])).
% 0.20/0.49  fof(f10,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ~spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f21,f40])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ~r1_tarski(sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f20,f35])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    r1_xboole_0(sK0,sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (19894)------------------------------
% 0.20/0.49  % (19894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (19894)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (19894)Memory used [KB]: 6780
% 0.20/0.49  % (19894)Time elapsed: 0.034 s
% 0.20/0.49  % (19894)------------------------------
% 0.20/0.49  % (19894)------------------------------
% 0.20/0.49  % (19886)Success in time 0.15 s
%------------------------------------------------------------------------------
