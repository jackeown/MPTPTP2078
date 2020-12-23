%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:04 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 270 expanded)
%              Number of leaves         :   18 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          :  192 ( 516 expanded)
%              Number of equality atoms :  108 ( 363 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f892,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f237,f247,f252,f257,f719])).

fof(f719,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f714])).

fof(f714,plain,
    ( $false
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f31,f32,f708,f101])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f708,plain,
    ( r2_hidden(sK0,k2_tarski(sK2,sK3))
    | ~ spl6_1 ),
    inference(superposition,[],[f632,f526])).

fof(f526,plain,
    ( k2_tarski(sK2,sK3) = k5_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3))
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f525,f43])).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f525,plain,
    ( k5_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3))
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f524,f43])).

fof(f524,plain,
    ( k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3))
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f523,f43])).

fof(f523,plain,
    ( k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0))
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f519,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f519,plain,
    ( k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0)))
    | ~ spl6_1 ),
    inference(superposition,[],[f76,f259])).

fof(f259,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f191,f224])).

fof(f224,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl6_1
  <=> k1_xboole_0 = k2_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f191,plain,(
    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f30,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f30,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f76,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f48,f68,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f47,f59])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f632,plain,
    ( ! [X19,X18] : r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k2_tarski(X18,X19)))
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f631,f43])).

fof(f631,plain,
    ( ! [X19,X18] : r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(X18,X19),k1_xboole_0)))
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f604,f44])).

fof(f604,plain,
    ( ! [X19,X18] : r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(X18,X19),k3_xboole_0(k2_tarski(X18,X19),k1_xboole_0))))
    | ~ spl6_1 ),
    inference(superposition,[],[f95,f509])).

fof(f509,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK0)
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f507,f44])).

fof(f507,plain,
    ( k2_tarski(sK0,sK0) = k3_xboole_0(k2_tarski(sK0,sK0),k1_xboole_0)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f283,f39])).

fof(f283,plain,
    ( r1_tarski(k2_tarski(sK0,sK0),k1_xboole_0)
    | ~ spl6_1 ),
    inference(superposition,[],[f88,f224])).

fof(f88,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X1) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f35,f42])).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X1) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f95,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k5_xboole_0(k2_tarski(X4,X4),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X4,X4))))) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k5_xboole_0(k2_tarski(X4,X4),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X4,X4)))) != X3 ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3 ) ),
    inference(definition_unfolding,[],[f56,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) ),
    inference(definition_unfolding,[],[f50,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f40,f68])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f32,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f25])).

fof(f31,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f25])).

fof(f257,plain,(
    ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f100,f253])).

fof(f253,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f128,f236])).

fof(f236,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl6_4
  <=> k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f128,plain,(
    ~ r2_hidden(sK0,k2_tarski(sK2,sK2)) ),
    inference(forward_demodulation,[],[f125,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) ),
    inference(definition_unfolding,[],[f41,f70])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f125,plain,(
    ~ r2_hidden(sK0,k5_xboole_0(k2_tarski(sK2,sK2),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK2,sK2))))) ),
    inference(unit_resulting_resolution,[],[f31,f31,f31,f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3 ) ),
    inference(definition_unfolding,[],[f55,f70])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f100,plain,(
    ! [X3,X1] : r2_hidden(X3,k2_tarski(X3,X1)) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k2_tarski(X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f252,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f100,f248])).

fof(f248,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f171,f232])).

fof(f232,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK3,sK3)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl6_3
  <=> k2_tarski(sK0,sK1) = k2_tarski(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f171,plain,(
    ~ r2_hidden(sK0,k2_tarski(sK3,sK3)) ),
    inference(forward_demodulation,[],[f168,f72])).

fof(f168,plain,(
    ~ r2_hidden(sK0,k5_xboole_0(k2_tarski(sK3,sK3),k5_xboole_0(k2_tarski(sK3,sK3),k3_xboole_0(k2_tarski(sK3,sK3),k2_tarski(sK3,sK3))))) ),
    inference(unit_resulting_resolution,[],[f32,f32,f32,f96])).

fof(f247,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f100,f240])).

fof(f240,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f180,f228])).

fof(f228,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl6_2
  <=> k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f180,plain,(
    ~ r2_hidden(sK0,k2_tarski(sK2,sK3)) ),
    inference(forward_demodulation,[],[f159,f72])).

fof(f159,plain,(
    ~ r2_hidden(sK0,k5_xboole_0(k2_tarski(sK2,sK2),k5_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK2,sK2))))) ),
    inference(unit_resulting_resolution,[],[f31,f31,f32,f96])).

fof(f237,plain,
    ( spl6_1
    | spl6_2
    | spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f192,f234,f230,f226,f222])).

fof(f192,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2)
    | k2_tarski(sK0,sK1) = k2_tarski(sK3,sK3)
    | k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3)
    | k1_xboole_0 = k2_tarski(sK0,sK1) ),
    inference(resolution,[],[f30,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X1) = X0
      | k2_tarski(X2,X2) = X0
      | k2_tarski(X1,X2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f33,f42,f42])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_tarski(X1,X2) = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:13:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.46  % (17188)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.48  % (17196)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.27/0.52  % (17184)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.27/0.52  % (17195)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.27/0.52  % (17203)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.27/0.53  % (17182)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.27/0.53  % (17185)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.27/0.53  % (17205)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.27/0.53  % (17204)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.27/0.53  % (17180)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.27/0.53  % (17198)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.27/0.53  % (17194)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.27/0.53  % (17209)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.27/0.53  % (17187)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.44/0.54  % (17207)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.44/0.54  % (17181)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.44/0.54  % (17181)Refutation not found, incomplete strategy% (17181)------------------------------
% 1.44/0.54  % (17181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (17181)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (17181)Memory used [KB]: 1663
% 1.44/0.54  % (17181)Time elapsed: 0.134 s
% 1.44/0.54  % (17181)------------------------------
% 1.44/0.54  % (17181)------------------------------
% 1.44/0.54  % (17190)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.44/0.54  % (17193)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.44/0.54  % (17193)Refutation not found, incomplete strategy% (17193)------------------------------
% 1.44/0.54  % (17193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (17193)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (17193)Memory used [KB]: 10618
% 1.44/0.54  % (17193)Time elapsed: 0.140 s
% 1.44/0.54  % (17193)------------------------------
% 1.44/0.54  % (17193)------------------------------
% 1.44/0.54  % (17199)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.44/0.54  % (17210)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.44/0.54  % (17210)Refutation not found, incomplete strategy% (17210)------------------------------
% 1.44/0.54  % (17210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (17210)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (17210)Memory used [KB]: 1663
% 1.44/0.54  % (17210)Time elapsed: 0.001 s
% 1.44/0.54  % (17210)------------------------------
% 1.44/0.54  % (17210)------------------------------
% 1.44/0.54  % (17197)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.44/0.54  % (17201)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.44/0.54  % (17197)Refutation not found, incomplete strategy% (17197)------------------------------
% 1.44/0.54  % (17197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (17197)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (17197)Memory used [KB]: 10618
% 1.44/0.54  % (17197)Time elapsed: 0.148 s
% 1.44/0.54  % (17197)------------------------------
% 1.44/0.54  % (17197)------------------------------
% 1.44/0.54  % (17202)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.44/0.54  % (17183)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.44/0.55  % (17189)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.44/0.55  % (17191)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.44/0.55  % (17200)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.44/0.55  % (17192)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.44/0.56  % (17206)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.44/0.56  % (17208)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.44/0.58  % (17206)Refutation found. Thanks to Tanya!
% 1.44/0.58  % SZS status Theorem for theBenchmark
% 1.44/0.60  % SZS output start Proof for theBenchmark
% 1.44/0.60  fof(f892,plain,(
% 1.44/0.60    $false),
% 1.44/0.60    inference(avatar_sat_refutation,[],[f237,f247,f252,f257,f719])).
% 1.44/0.60  fof(f719,plain,(
% 1.44/0.60    ~spl6_1),
% 1.44/0.60    inference(avatar_contradiction_clause,[],[f714])).
% 1.44/0.60  fof(f714,plain,(
% 1.44/0.60    $false | ~spl6_1),
% 1.44/0.60    inference(unit_resulting_resolution,[],[f31,f32,f708,f101])).
% 1.44/0.60  fof(f101,plain,(
% 1.44/0.60    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_tarski(X0,X1)) | X1 = X3 | X0 = X3) )),
% 1.44/0.60    inference(equality_resolution,[],[f65])).
% 1.44/0.60  fof(f65,plain,(
% 1.44/0.60    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.44/0.60    inference(cnf_transformation,[],[f12])).
% 1.44/0.60  fof(f12,axiom,(
% 1.44/0.60    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.44/0.60  fof(f708,plain,(
% 1.44/0.60    r2_hidden(sK0,k2_tarski(sK2,sK3)) | ~spl6_1),
% 1.44/0.60    inference(superposition,[],[f632,f526])).
% 1.44/0.60  fof(f526,plain,(
% 1.44/0.60    k2_tarski(sK2,sK3) = k5_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3)) | ~spl6_1),
% 1.44/0.60    inference(forward_demodulation,[],[f525,f43])).
% 1.44/0.60  fof(f43,plain,(
% 1.44/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.44/0.60    inference(cnf_transformation,[],[f9])).
% 1.44/0.60  fof(f9,axiom,(
% 1.44/0.60    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.44/0.60  fof(f525,plain,(
% 1.44/0.60    k5_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3)) | ~spl6_1),
% 1.44/0.60    inference(forward_demodulation,[],[f524,f43])).
% 1.44/0.60  fof(f524,plain,(
% 1.44/0.60    k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3)) | ~spl6_1),
% 1.44/0.60    inference(forward_demodulation,[],[f523,f43])).
% 1.44/0.60  fof(f523,plain,(
% 1.44/0.60    k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0)) | ~spl6_1),
% 1.44/0.60    inference(forward_demodulation,[],[f519,f44])).
% 1.44/0.60  fof(f44,plain,(
% 1.44/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.44/0.60    inference(cnf_transformation,[],[f7])).
% 1.44/0.60  fof(f7,axiom,(
% 1.44/0.60    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.44/0.60  fof(f519,plain,(
% 1.44/0.60    k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0))) | ~spl6_1),
% 1.44/0.60    inference(superposition,[],[f76,f259])).
% 1.44/0.60  fof(f259,plain,(
% 1.44/0.60    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k2_tarski(sK2,sK3)) | ~spl6_1),
% 1.44/0.60    inference(backward_demodulation,[],[f191,f224])).
% 1.44/0.60  fof(f224,plain,(
% 1.44/0.60    k1_xboole_0 = k2_tarski(sK0,sK1) | ~spl6_1),
% 1.44/0.60    inference(avatar_component_clause,[],[f222])).
% 1.44/0.60  fof(f222,plain,(
% 1.44/0.60    spl6_1 <=> k1_xboole_0 = k2_tarski(sK0,sK1)),
% 1.44/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.44/0.60  fof(f191,plain,(
% 1.44/0.60    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.44/0.60    inference(unit_resulting_resolution,[],[f30,f39])).
% 1.44/0.60  fof(f39,plain,(
% 1.44/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.44/0.60    inference(cnf_transformation,[],[f28])).
% 1.44/0.60  fof(f28,plain,(
% 1.44/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.44/0.60    inference(ennf_transformation,[],[f6])).
% 1.44/0.60  fof(f6,axiom,(
% 1.44/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.44/0.60  fof(f30,plain,(
% 1.44/0.60    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.44/0.60    inference(cnf_transformation,[],[f25])).
% 1.44/0.60  fof(f25,plain,(
% 1.44/0.60    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.44/0.60    inference(ennf_transformation,[],[f23])).
% 1.44/0.60  fof(f23,negated_conjecture,(
% 1.44/0.60    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.44/0.60    inference(negated_conjecture,[],[f22])).
% 1.44/0.60  fof(f22,conjecture,(
% 1.44/0.60    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 1.44/0.60  fof(f76,plain,(
% 1.44/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.44/0.60    inference(definition_unfolding,[],[f48,f68,f68])).
% 1.44/0.60  fof(f68,plain,(
% 1.44/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.44/0.60    inference(definition_unfolding,[],[f47,f59])).
% 1.44/0.60  fof(f59,plain,(
% 1.44/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.44/0.60    inference(cnf_transformation,[],[f4])).
% 1.44/0.60  fof(f4,axiom,(
% 1.44/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.44/0.60  fof(f47,plain,(
% 1.44/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.44/0.60    inference(cnf_transformation,[],[f10])).
% 1.44/0.60  fof(f10,axiom,(
% 1.44/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.44/0.60  fof(f48,plain,(
% 1.44/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.44/0.60    inference(cnf_transformation,[],[f1])).
% 1.44/0.60  fof(f1,axiom,(
% 1.44/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.44/0.60  fof(f632,plain,(
% 1.44/0.60    ( ! [X19,X18] : (r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k2_tarski(X18,X19)))) ) | ~spl6_1),
% 1.44/0.60    inference(forward_demodulation,[],[f631,f43])).
% 1.44/0.60  fof(f631,plain,(
% 1.44/0.60    ( ! [X19,X18] : (r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(X18,X19),k1_xboole_0)))) ) | ~spl6_1),
% 1.44/0.60    inference(forward_demodulation,[],[f604,f44])).
% 1.44/0.60  fof(f604,plain,(
% 1.44/0.60    ( ! [X19,X18] : (r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(X18,X19),k3_xboole_0(k2_tarski(X18,X19),k1_xboole_0))))) ) | ~spl6_1),
% 1.44/0.60    inference(superposition,[],[f95,f509])).
% 1.44/0.60  fof(f509,plain,(
% 1.44/0.60    k1_xboole_0 = k2_tarski(sK0,sK0) | ~spl6_1),
% 1.44/0.60    inference(forward_demodulation,[],[f507,f44])).
% 1.44/0.60  fof(f507,plain,(
% 1.44/0.60    k2_tarski(sK0,sK0) = k3_xboole_0(k2_tarski(sK0,sK0),k1_xboole_0) | ~spl6_1),
% 1.44/0.60    inference(unit_resulting_resolution,[],[f283,f39])).
% 1.44/0.60  fof(f283,plain,(
% 1.44/0.60    r1_tarski(k2_tarski(sK0,sK0),k1_xboole_0) | ~spl6_1),
% 1.44/0.60    inference(superposition,[],[f88,f224])).
% 1.44/0.60  fof(f88,plain,(
% 1.44/0.60    ( ! [X2,X1] : (r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2))) )),
% 1.44/0.60    inference(equality_resolution,[],[f74])).
% 1.44/0.60  fof(f74,plain,(
% 1.44/0.60    ( ! [X2,X0,X1] : (k2_tarski(X1,X1) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.44/0.60    inference(definition_unfolding,[],[f35,f42])).
% 1.44/0.60  fof(f42,plain,(
% 1.44/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.44/0.60    inference(cnf_transformation,[],[f14])).
% 1.44/0.60  fof(f14,axiom,(
% 1.44/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.44/0.60  fof(f35,plain,(
% 1.44/0.60    ( ! [X2,X0,X1] : (k1_tarski(X1) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.44/0.60    inference(cnf_transformation,[],[f26])).
% 1.44/0.60  fof(f26,plain,(
% 1.44/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.44/0.60    inference(ennf_transformation,[],[f21])).
% 1.44/0.60  fof(f21,axiom,(
% 1.44/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.44/0.60  fof(f95,plain,(
% 1.44/0.60    ( ! [X4,X2,X1] : (r2_hidden(X4,k5_xboole_0(k2_tarski(X4,X4),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X4,X4)))))) )),
% 1.44/0.60    inference(equality_resolution,[],[f94])).
% 1.44/0.60  fof(f94,plain,(
% 1.44/0.60    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k5_xboole_0(k2_tarski(X4,X4),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X4,X4)))) != X3) )),
% 1.44/0.60    inference(equality_resolution,[],[f80])).
% 1.44/0.60  fof(f80,plain,(
% 1.44/0.60    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3) )),
% 1.44/0.60    inference(definition_unfolding,[],[f56,f70])).
% 1.44/0.60  fof(f70,plain,(
% 1.44/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) )),
% 1.44/0.60    inference(definition_unfolding,[],[f50,f69])).
% 1.44/0.60  fof(f69,plain,(
% 1.44/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))))) )),
% 1.44/0.60    inference(definition_unfolding,[],[f40,f68])).
% 1.44/0.60  fof(f40,plain,(
% 1.44/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 1.44/0.60    inference(cnf_transformation,[],[f13])).
% 1.44/0.60  fof(f13,axiom,(
% 1.44/0.60    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 1.44/0.60  fof(f50,plain,(
% 1.44/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.44/0.60    inference(cnf_transformation,[],[f16])).
% 1.44/0.60  fof(f16,axiom,(
% 1.44/0.60    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.44/0.60  fof(f56,plain,(
% 1.44/0.60    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.44/0.60    inference(cnf_transformation,[],[f29])).
% 1.44/0.60  fof(f29,plain,(
% 1.44/0.60    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.44/0.60    inference(ennf_transformation,[],[f11])).
% 1.44/0.60  fof(f11,axiom,(
% 1.44/0.60    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.44/0.60  fof(f32,plain,(
% 1.44/0.60    sK0 != sK3),
% 1.44/0.60    inference(cnf_transformation,[],[f25])).
% 1.44/0.60  fof(f31,plain,(
% 1.44/0.60    sK0 != sK2),
% 1.44/0.60    inference(cnf_transformation,[],[f25])).
% 1.44/0.60  fof(f257,plain,(
% 1.44/0.60    ~spl6_4),
% 1.44/0.60    inference(avatar_contradiction_clause,[],[f254])).
% 1.44/0.60  fof(f254,plain,(
% 1.44/0.60    $false | ~spl6_4),
% 1.44/0.60    inference(unit_resulting_resolution,[],[f100,f253])).
% 1.44/0.60  fof(f253,plain,(
% 1.44/0.60    ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | ~spl6_4),
% 1.44/0.60    inference(backward_demodulation,[],[f128,f236])).
% 1.44/0.60  fof(f236,plain,(
% 1.44/0.60    k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2) | ~spl6_4),
% 1.44/0.60    inference(avatar_component_clause,[],[f234])).
% 1.44/0.60  fof(f234,plain,(
% 1.44/0.60    spl6_4 <=> k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2)),
% 1.44/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.44/0.60  fof(f128,plain,(
% 1.44/0.60    ~r2_hidden(sK0,k2_tarski(sK2,sK2))),
% 1.44/0.60    inference(forward_demodulation,[],[f125,f72])).
% 1.44/0.60  fof(f72,plain,(
% 1.44/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0))))) )),
% 1.44/0.60    inference(definition_unfolding,[],[f41,f70])).
% 1.44/0.60  fof(f41,plain,(
% 1.44/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.44/0.60    inference(cnf_transformation,[],[f15])).
% 1.44/0.60  fof(f15,axiom,(
% 1.44/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.44/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.44/0.60  fof(f125,plain,(
% 1.44/0.60    ~r2_hidden(sK0,k5_xboole_0(k2_tarski(sK2,sK2),k5_xboole_0(k2_tarski(sK2,sK2),k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK2,sK2)))))),
% 1.44/0.60    inference(unit_resulting_resolution,[],[f31,f31,f31,f96])).
% 1.44/0.60  fof(f96,plain,(
% 1.44/0.60    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 1.44/0.60    inference(equality_resolution,[],[f81])).
% 1.44/0.60  fof(f81,plain,(
% 1.44/0.60    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3) )),
% 1.44/0.60    inference(definition_unfolding,[],[f55,f70])).
% 1.44/0.60  fof(f55,plain,(
% 1.44/0.60    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.44/0.60    inference(cnf_transformation,[],[f29])).
% 1.44/0.60  fof(f100,plain,(
% 1.44/0.60    ( ! [X3,X1] : (r2_hidden(X3,k2_tarski(X3,X1))) )),
% 1.44/0.60    inference(equality_resolution,[],[f99])).
% 1.44/0.60  fof(f99,plain,(
% 1.44/0.60    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k2_tarski(X3,X1) != X2) )),
% 1.44/0.60    inference(equality_resolution,[],[f66])).
% 1.44/0.60  fof(f66,plain,(
% 1.44/0.60    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.44/0.60    inference(cnf_transformation,[],[f12])).
% 1.44/0.60  fof(f252,plain,(
% 1.44/0.60    ~spl6_3),
% 1.44/0.60    inference(avatar_contradiction_clause,[],[f249])).
% 1.44/0.60  fof(f249,plain,(
% 1.44/0.60    $false | ~spl6_3),
% 1.44/0.60    inference(unit_resulting_resolution,[],[f100,f248])).
% 1.44/0.60  fof(f248,plain,(
% 1.44/0.60    ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | ~spl6_3),
% 1.44/0.60    inference(backward_demodulation,[],[f171,f232])).
% 1.44/0.60  fof(f232,plain,(
% 1.44/0.60    k2_tarski(sK0,sK1) = k2_tarski(sK3,sK3) | ~spl6_3),
% 1.44/0.60    inference(avatar_component_clause,[],[f230])).
% 1.44/0.60  fof(f230,plain,(
% 1.44/0.60    spl6_3 <=> k2_tarski(sK0,sK1) = k2_tarski(sK3,sK3)),
% 1.44/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.44/0.60  fof(f171,plain,(
% 1.44/0.60    ~r2_hidden(sK0,k2_tarski(sK3,sK3))),
% 1.44/0.60    inference(forward_demodulation,[],[f168,f72])).
% 1.44/0.60  fof(f168,plain,(
% 1.44/0.60    ~r2_hidden(sK0,k5_xboole_0(k2_tarski(sK3,sK3),k5_xboole_0(k2_tarski(sK3,sK3),k3_xboole_0(k2_tarski(sK3,sK3),k2_tarski(sK3,sK3)))))),
% 1.44/0.60    inference(unit_resulting_resolution,[],[f32,f32,f32,f96])).
% 1.44/0.60  fof(f247,plain,(
% 1.44/0.60    ~spl6_2),
% 1.44/0.60    inference(avatar_contradiction_clause,[],[f244])).
% 1.44/0.60  fof(f244,plain,(
% 1.44/0.60    $false | ~spl6_2),
% 1.44/0.60    inference(unit_resulting_resolution,[],[f100,f240])).
% 1.44/0.60  fof(f240,plain,(
% 1.44/0.60    ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | ~spl6_2),
% 1.44/0.60    inference(backward_demodulation,[],[f180,f228])).
% 1.44/0.60  fof(f228,plain,(
% 1.44/0.60    k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3) | ~spl6_2),
% 1.44/0.60    inference(avatar_component_clause,[],[f226])).
% 1.44/0.60  fof(f226,plain,(
% 1.44/0.60    spl6_2 <=> k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3)),
% 1.44/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.44/0.60  fof(f180,plain,(
% 1.44/0.60    ~r2_hidden(sK0,k2_tarski(sK2,sK3))),
% 1.44/0.60    inference(forward_demodulation,[],[f159,f72])).
% 1.44/0.60  fof(f159,plain,(
% 1.44/0.60    ~r2_hidden(sK0,k5_xboole_0(k2_tarski(sK2,sK2),k5_xboole_0(k2_tarski(sK2,sK3),k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK2,sK2)))))),
% 1.44/0.60    inference(unit_resulting_resolution,[],[f31,f31,f32,f96])).
% 1.44/0.60  fof(f237,plain,(
% 1.44/0.60    spl6_1 | spl6_2 | spl6_3 | spl6_4),
% 1.44/0.60    inference(avatar_split_clause,[],[f192,f234,f230,f226,f222])).
% 1.44/0.60  fof(f192,plain,(
% 1.44/0.60    k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2) | k2_tarski(sK0,sK1) = k2_tarski(sK3,sK3) | k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3) | k1_xboole_0 = k2_tarski(sK0,sK1)),
% 1.44/0.60    inference(resolution,[],[f30,f75])).
% 1.44/0.60  fof(f75,plain,(
% 1.44/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X1,X1) = X0 | k2_tarski(X2,X2) = X0 | k2_tarski(X1,X2) = X0 | k1_xboole_0 = X0) )),
% 1.44/0.60    inference(definition_unfolding,[],[f33,f42,f42])).
% 1.44/0.60  fof(f33,plain,(
% 1.44/0.60    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | k1_tarski(X2) = X0 | k2_tarski(X1,X2) = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.44/0.60    inference(cnf_transformation,[],[f26])).
% 1.44/0.60  % SZS output end Proof for theBenchmark
% 1.44/0.60  % (17206)------------------------------
% 1.44/0.60  % (17206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.60  % (17206)Termination reason: Refutation
% 1.44/0.60  
% 1.44/0.60  % (17206)Memory used [KB]: 6652
% 1.44/0.60  % (17206)Time elapsed: 0.179 s
% 1.44/0.60  % (17206)------------------------------
% 1.44/0.60  % (17206)------------------------------
% 1.44/0.61  % (17179)Success in time 0.253 s
%------------------------------------------------------------------------------
