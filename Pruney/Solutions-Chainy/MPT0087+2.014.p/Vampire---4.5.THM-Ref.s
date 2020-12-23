%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 184 expanded)
%              Number of leaves         :   23 (  83 expanded)
%              Depth                    :    9
%              Number of atoms          :  241 ( 425 expanded)
%              Number of equality atoms :   67 ( 148 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f152,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f40,f44,f48,f53,f57,f61,f67,f74,f80,f84,f119,f129,f141,f151])).

fof(f151,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_9
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_9
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f149,f43])).

fof(f43,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_4
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f149,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | ~ spl3_3
    | spl3_9
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f146,f39])).

fof(f39,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl3_3
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f146,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0))
    | ~ spl3_3
    | spl3_9
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f125,f142])).

fof(f142,plain,
    ( ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(superposition,[],[f140,f128])).

fof(f128,plain,
    ( ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl3_14
  <=> ! [X3,X4] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f140,plain,
    ( ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl3_16
  <=> ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f125,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK2)))
    | ~ spl3_3
    | spl3_9
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f66,f124])).

fof(f124,plain,
    ( ! [X1] : k4_xboole_0(sK0,k4_xboole_0(sK1,X1)) = k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X1))
    | ~ spl3_3
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f121,f85])).

fof(f85,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(superposition,[],[f83,f39])).

fof(f83,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f121,plain,
    ( ! [X1] : k4_xboole_0(sK0,k4_xboole_0(sK1,X1)) = k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X1)))
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(superposition,[],[f83,f118])).

fof(f118,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl3_13
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f66,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_9
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f141,plain,
    ( spl3_16
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f137,f127,f51,f38,f139])).

fof(f51,plain,
    ( spl3_6
  <=> ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f137,plain,
    ( ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f52,f134])).

fof(f134,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(superposition,[],[f128,f39])).

fof(f52,plain,
    ( ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f129,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f105,f82,f46,f42,f38,f127])).

fof(f46,plain,
    ( spl3_5
  <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f105,plain,
    ( ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f104,f39])).

fof(f104,plain,
    ( ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f92,f43])).

fof(f92,plain,
    ( ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k4_xboole_0(X4,X4))
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(superposition,[],[f83,f47])).

fof(f47,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f119,plain,
    ( spl3_13
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f107,f82,f77,f46,f42,f38,f116])).

fof(f77,plain,
    ( spl3_11
  <=> k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f107,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f99,f105])).

fof(f99,plain,
    ( k4_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f79,f98])).

fof(f98,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f97,f39])).

fof(f97,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f88,f43])).

fof(f88,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0))
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(superposition,[],[f83,f39])).

fof(f79,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f84,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f25,f82])).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f21,f17])).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f80,plain,
    ( spl3_11
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f75,f71,f46,f77])).

fof(f71,plain,
    ( spl3_10
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f75,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(superposition,[],[f47,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f71])).

fof(f74,plain,
    ( spl3_10
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f68,f59,f28,f71])).

fof(f28,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f59,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f68,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(resolution,[],[f60,f30])).

fof(f30,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f67,plain,
    ( ~ spl3_9
    | spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f62,f55,f33,f64])).

fof(f33,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f55,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f62,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | spl3_2
    | ~ spl3_7 ),
    inference(resolution,[],[f56,f35])).

fof(f35,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f55])).

fof(f61,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f24,f59])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f19,f17])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f57,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f20,f17])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,
    ( spl3_6
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f49,f46,f42,f51])).

fof(f49,plain,
    ( ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(superposition,[],[f47,f43])).

fof(f48,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f18,f46])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f44,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f26,f42])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f22,f16])).

fof(f16,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f15,f17])).

fof(f15,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f40,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f38])).

fof(f36,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f14,f33])).

fof(f14,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).

fof(f31,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f13,f28])).

fof(f13,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:40:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (19250)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.46  % (19265)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.46  % (19257)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (19255)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (19257)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f152,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f31,f36,f40,f44,f48,f53,f57,f61,f67,f74,f80,f84,f119,f129,f141,f151])).
% 0.22/0.47  fof(f151,plain,(
% 0.22/0.47    ~spl3_3 | ~spl3_4 | spl3_9 | ~spl3_12 | ~spl3_13 | ~spl3_14 | ~spl3_16),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f150])).
% 0.22/0.47  fof(f150,plain,(
% 0.22/0.47    $false | (~spl3_3 | ~spl3_4 | spl3_9 | ~spl3_12 | ~spl3_13 | ~spl3_14 | ~spl3_16)),
% 0.22/0.47    inference(subsumption_resolution,[],[f149,f43])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl3_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f42])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    spl3_4 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.47  fof(f149,plain,(
% 0.22/0.47    k1_xboole_0 != k4_xboole_0(sK0,sK0) | (~spl3_3 | spl3_9 | ~spl3_12 | ~spl3_13 | ~spl3_14 | ~spl3_16)),
% 0.22/0.47    inference(forward_demodulation,[],[f146,f39])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f38])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    spl3_3 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.47  fof(f146,plain,(
% 0.22/0.47    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) | (~spl3_3 | spl3_9 | ~spl3_12 | ~spl3_13 | ~spl3_14 | ~spl3_16)),
% 0.22/0.47    inference(backward_demodulation,[],[f125,f142])).
% 0.22/0.47  fof(f142,plain,(
% 0.22/0.47    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) ) | (~spl3_14 | ~spl3_16)),
% 0.22/0.47    inference(superposition,[],[f140,f128])).
% 0.22/0.47  fof(f128,plain,(
% 0.22/0.47    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3) ) | ~spl3_14),
% 0.22/0.47    inference(avatar_component_clause,[],[f127])).
% 0.22/0.47  fof(f127,plain,(
% 0.22/0.47    spl3_14 <=> ! [X3,X4] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.47  fof(f140,plain,(
% 0.22/0.47    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) ) | ~spl3_16),
% 0.22/0.47    inference(avatar_component_clause,[],[f139])).
% 0.22/0.47  fof(f139,plain,(
% 0.22/0.47    spl3_16 <=> ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.47  fof(f125,plain,(
% 0.22/0.47    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK2))) | (~spl3_3 | spl3_9 | ~spl3_12 | ~spl3_13)),
% 0.22/0.47    inference(backward_demodulation,[],[f66,f124])).
% 0.22/0.47  fof(f124,plain,(
% 0.22/0.47    ( ! [X1] : (k4_xboole_0(sK0,k4_xboole_0(sK1,X1)) = k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X1))) ) | (~spl3_3 | ~spl3_12 | ~spl3_13)),
% 0.22/0.47    inference(forward_demodulation,[],[f121,f85])).
% 0.22/0.47  fof(f85,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | (~spl3_3 | ~spl3_12)),
% 0.22/0.47    inference(superposition,[],[f83,f39])).
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ) | ~spl3_12),
% 0.22/0.47    inference(avatar_component_clause,[],[f82])).
% 0.22/0.47  fof(f82,plain,(
% 0.22/0.47    spl3_12 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.47  fof(f121,plain,(
% 0.22/0.47    ( ! [X1] : (k4_xboole_0(sK0,k4_xboole_0(sK1,X1)) = k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X1)))) ) | (~spl3_12 | ~spl3_13)),
% 0.22/0.47    inference(superposition,[],[f83,f118])).
% 0.22/0.47  fof(f118,plain,(
% 0.22/0.47    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_13),
% 0.22/0.47    inference(avatar_component_clause,[],[f116])).
% 0.22/0.47  fof(f116,plain,(
% 0.22/0.47    spl3_13 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | spl3_9),
% 0.22/0.47    inference(avatar_component_clause,[],[f64])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    spl3_9 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.47  fof(f141,plain,(
% 0.22/0.47    spl3_16 | ~spl3_3 | ~spl3_6 | ~spl3_14),
% 0.22/0.47    inference(avatar_split_clause,[],[f137,f127,f51,f38,f139])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    spl3_6 <=> ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.47  fof(f137,plain,(
% 0.22/0.47    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) ) | (~spl3_3 | ~spl3_6 | ~spl3_14)),
% 0.22/0.47    inference(backward_demodulation,[],[f52,f134])).
% 0.22/0.47  fof(f134,plain,(
% 0.22/0.47    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | (~spl3_3 | ~spl3_14)),
% 0.22/0.47    inference(superposition,[],[f128,f39])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    ( ! [X1] : (k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0)) ) | ~spl3_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f51])).
% 0.22/0.47  fof(f129,plain,(
% 0.22/0.47    spl3_14 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_12),
% 0.22/0.47    inference(avatar_split_clause,[],[f105,f82,f46,f42,f38,f127])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    spl3_5 <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.47  fof(f105,plain,(
% 0.22/0.47    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3) ) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_12)),
% 0.22/0.47    inference(forward_demodulation,[],[f104,f39])).
% 0.22/0.47  fof(f104,plain,(
% 0.22/0.47    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k1_xboole_0)) ) | (~spl3_4 | ~spl3_5 | ~spl3_12)),
% 0.22/0.47    inference(forward_demodulation,[],[f92,f43])).
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k4_xboole_0(X4,X4))) ) | (~spl3_5 | ~spl3_12)),
% 0.22/0.47    inference(superposition,[],[f83,f47])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) ) | ~spl3_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f46])).
% 0.22/0.47  fof(f119,plain,(
% 0.22/0.47    spl3_13 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12),
% 0.22/0.47    inference(avatar_split_clause,[],[f107,f82,f77,f46,f42,f38,f116])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    spl3_11 <=> k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.47  fof(f107,plain,(
% 0.22/0.47    sK0 = k4_xboole_0(sK0,sK1) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12)),
% 0.22/0.47    inference(backward_demodulation,[],[f99,f105])).
% 0.22/0.47  fof(f99,plain,(
% 0.22/0.47    k4_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) | (~spl3_3 | ~spl3_4 | ~spl3_11 | ~spl3_12)),
% 0.22/0.47    inference(backward_demodulation,[],[f79,f98])).
% 0.22/0.47  fof(f98,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ) | (~spl3_3 | ~spl3_4 | ~spl3_12)),
% 0.22/0.47    inference(forward_demodulation,[],[f97,f39])).
% 0.22/0.47  fof(f97,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ) | (~spl3_3 | ~spl3_4 | ~spl3_12)),
% 0.22/0.47    inference(forward_demodulation,[],[f88,f43])).
% 0.22/0.47  fof(f88,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0))) ) | (~spl3_3 | ~spl3_12)),
% 0.22/0.47    inference(superposition,[],[f83,f39])).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | ~spl3_11),
% 0.22/0.47    inference(avatar_component_clause,[],[f77])).
% 0.22/0.47  fof(f84,plain,(
% 0.22/0.47    spl3_12),
% 0.22/0.47    inference(avatar_split_clause,[],[f25,f82])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f21,f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    spl3_11 | ~spl3_5 | ~spl3_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f75,f71,f46,f77])).
% 0.22/0.47  fof(f71,plain,(
% 0.22/0.47    spl3_10 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.47  fof(f75,plain,(
% 0.22/0.47    k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | (~spl3_5 | ~spl3_10)),
% 0.22/0.47    inference(superposition,[],[f47,f73])).
% 0.22/0.47  fof(f73,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f71])).
% 0.22/0.47  fof(f74,plain,(
% 0.22/0.47    spl3_10 | ~spl3_1 | ~spl3_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f68,f59,f28,f71])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    spl3_8 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.47  fof(f68,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_1 | ~spl3_8)),
% 0.22/0.47    inference(resolution,[],[f60,f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    r1_xboole_0(sK0,sK1) | ~spl3_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f28])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_8),
% 0.22/0.47    inference(avatar_component_clause,[],[f59])).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    ~spl3_9 | spl3_2 | ~spl3_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f62,f55,f33,f64])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    spl3_2 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    spl3_7 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | (spl3_2 | ~spl3_7)),
% 0.22/0.47    inference(resolution,[],[f56,f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | spl3_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f33])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f55])).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    spl3_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f24,f59])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f19,f17])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.47    inference(nnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    spl3_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f23,f55])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f20,f17])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    spl3_6 | ~spl3_4 | ~spl3_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f49,f46,f42,f51])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    ( ! [X1] : (k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0)) ) | (~spl3_4 | ~spl3_5)),
% 0.22/0.47    inference(superposition,[],[f47,f43])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    spl3_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f18,f46])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    spl3_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f26,f42])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.47    inference(backward_demodulation,[],[f22,f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f15,f17])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    spl3_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f16,f38])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ~spl3_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f14,f33])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK1)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.47    inference(negated_conjecture,[],[f7])).
% 0.22/0.47  fof(f7,conjecture,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    spl3_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f13,f28])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    r1_xboole_0(sK0,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (19257)------------------------------
% 0.22/0.47  % (19257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (19257)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (19257)Memory used [KB]: 6140
% 0.22/0.47  % (19257)Time elapsed: 0.058 s
% 0.22/0.47  % (19257)------------------------------
% 0.22/0.47  % (19257)------------------------------
% 0.22/0.47  % (19249)Success in time 0.111 s
%------------------------------------------------------------------------------
