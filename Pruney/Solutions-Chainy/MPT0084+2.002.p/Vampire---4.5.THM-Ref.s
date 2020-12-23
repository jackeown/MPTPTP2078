%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:14 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 145 expanded)
%              Number of leaves         :   25 (  65 expanded)
%              Depth                    :    7
%              Number of atoms          :  216 ( 350 expanded)
%              Number of equality atoms :   50 (  83 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f175,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f49,f54,f58,f62,f66,f73,f77,f81,f85,f101,f112,f146,f158,f167,f174])).

fof(f174,plain,
    ( ~ spl3_7
    | spl3_13
    | ~ spl3_22 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl3_7
    | spl3_13
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f172,f100])).

fof(f100,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl3_13
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f172,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_7
    | ~ spl3_22 ),
    inference(resolution,[],[f166,f65])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f166,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl3_22
  <=> r1_tarski(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f167,plain,
    ( spl3_22
    | ~ spl3_19
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f162,f156,f143,f164])).

fof(f143,plain,
    ( spl3_19
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f156,plain,
    ( spl3_21
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f162,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_19
    | ~ spl3_21 ),
    inference(trivial_inequality_removal,[],[f161])).

fof(f161,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_19
    | ~ spl3_21 ),
    inference(superposition,[],[f157,f145])).

fof(f145,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f143])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))
        | r1_tarski(X0,X1) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f156])).

fof(f158,plain,
    ( spl3_21
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f113,f110,f60,f156])).

fof(f60,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f110,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ r1_tarski(X0,k2_xboole_0(k1_xboole_0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) )
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(resolution,[],[f111,f61])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k2_xboole_0(k1_xboole_0,X1))
        | r1_tarski(X0,X1) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f110])).

fof(f146,plain,
    ( spl3_19
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f141,f83,f70,f56,f51,f143])).

fof(f51,plain,
    ( spl3_4
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f56,plain,
    ( spl3_5
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f70,plain,
    ( spl3_8
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f83,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f141,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f140,f57])).

fof(f57,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f140,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0))
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f139,f72])).

fof(f72,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f70])).

fof(f139,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)))
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f137,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f30,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

fof(f137,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(resolution,[],[f84,f53])).

fof(f53,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f83])).

fof(f112,plain,
    ( spl3_15
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f87,f75,f47,f110])).

fof(f47,plain,
    ( spl3_3
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f75,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k4_xboole_0(X0,X1),X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ r1_tarski(X0,k2_xboole_0(k1_xboole_0,X1)) )
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(superposition,[],[f76,f48])).

fof(f48,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f76,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k4_xboole_0(X0,X1),X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f75])).

fof(f101,plain,
    ( ~ spl3_13
    | spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f96,f79,f37,f98])).

fof(f37,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f79,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f96,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | spl3_1
    | ~ spl3_10 ),
    inference(resolution,[],[f80,f39])).

fof(f39,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f79])).

fof(f85,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f34,f83])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f81,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f33,f79])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f77,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f31,f75])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f73,plain,
    ( spl3_8
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f67,f64,f42,f70])).

fof(f42,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f67,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(resolution,[],[f65,f44])).

fof(f44,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f66,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f27,f64])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f62,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f26,f60])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f22,f56])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f54,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f32,f51])).

fof(f32,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f20,f23])).

fof(f20,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f49,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f45,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f42])).

fof(f19,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f37])).

fof(f18,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n022.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 16:43:56 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.19/0.40  % (31332)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.40  % (31332)Refutation found. Thanks to Tanya!
% 0.19/0.40  % SZS status Theorem for theBenchmark
% 0.19/0.41  % (31336)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.41  % SZS output start Proof for theBenchmark
% 0.19/0.41  fof(f175,plain,(
% 0.19/0.41    $false),
% 0.19/0.41    inference(avatar_sat_refutation,[],[f40,f45,f49,f54,f58,f62,f66,f73,f77,f81,f85,f101,f112,f146,f158,f167,f174])).
% 0.19/0.41  fof(f174,plain,(
% 0.19/0.41    ~spl3_7 | spl3_13 | ~spl3_22),
% 0.19/0.41    inference(avatar_contradiction_clause,[],[f173])).
% 0.19/0.41  fof(f173,plain,(
% 0.19/0.41    $false | (~spl3_7 | spl3_13 | ~spl3_22)),
% 0.19/0.41    inference(subsumption_resolution,[],[f172,f100])).
% 0.19/0.41  fof(f100,plain,(
% 0.19/0.41    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | spl3_13),
% 0.19/0.41    inference(avatar_component_clause,[],[f98])).
% 0.19/0.41  fof(f98,plain,(
% 0.19/0.41    spl3_13 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.19/0.41  fof(f172,plain,(
% 0.19/0.41    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_7 | ~spl3_22)),
% 0.19/0.41    inference(resolution,[],[f166,f65])).
% 0.19/0.41  fof(f65,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) ) | ~spl3_7),
% 0.19/0.41    inference(avatar_component_clause,[],[f64])).
% 0.19/0.41  fof(f64,plain,(
% 0.19/0.41    spl3_7 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.19/0.41  fof(f166,plain,(
% 0.19/0.41    r1_tarski(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_22),
% 0.19/0.41    inference(avatar_component_clause,[],[f164])).
% 0.19/0.41  fof(f164,plain,(
% 0.19/0.41    spl3_22 <=> r1_tarski(sK0,k4_xboole_0(sK0,sK1))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.19/0.41  fof(f167,plain,(
% 0.19/0.41    spl3_22 | ~spl3_19 | ~spl3_21),
% 0.19/0.41    inference(avatar_split_clause,[],[f162,f156,f143,f164])).
% 0.19/0.41  fof(f143,plain,(
% 0.19/0.41    spl3_19 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.19/0.41  fof(f156,plain,(
% 0.19/0.41    spl3_21 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.19/0.41  fof(f162,plain,(
% 0.19/0.41    r1_tarski(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_19 | ~spl3_21)),
% 0.19/0.41    inference(trivial_inequality_removal,[],[f161])).
% 0.19/0.41  fof(f161,plain,(
% 0.19/0.41    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_19 | ~spl3_21)),
% 0.19/0.41    inference(superposition,[],[f157,f145])).
% 0.19/0.41  fof(f145,plain,(
% 0.19/0.41    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))) | ~spl3_19),
% 0.19/0.41    inference(avatar_component_clause,[],[f143])).
% 0.19/0.41  fof(f157,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) | r1_tarski(X0,X1)) ) | ~spl3_21),
% 0.19/0.41    inference(avatar_component_clause,[],[f156])).
% 0.19/0.41  fof(f158,plain,(
% 0.19/0.41    spl3_21 | ~spl3_6 | ~spl3_15),
% 0.19/0.41    inference(avatar_split_clause,[],[f113,f110,f60,f156])).
% 0.19/0.41  fof(f60,plain,(
% 0.19/0.41    spl3_6 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.41  fof(f110,plain,(
% 0.19/0.41    spl3_15 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k2_xboole_0(k1_xboole_0,X1)))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.19/0.41  fof(f113,plain,(
% 0.19/0.41    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))) ) | (~spl3_6 | ~spl3_15)),
% 0.19/0.41    inference(resolution,[],[f111,f61])).
% 0.19/0.41  fof(f61,plain,(
% 0.19/0.41    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) ) | ~spl3_6),
% 0.19/0.41    inference(avatar_component_clause,[],[f60])).
% 0.19/0.41  fof(f111,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~r1_tarski(X0,k2_xboole_0(k1_xboole_0,X1)) | r1_tarski(X0,X1)) ) | ~spl3_15),
% 0.19/0.41    inference(avatar_component_clause,[],[f110])).
% 0.19/0.41  fof(f146,plain,(
% 0.19/0.41    spl3_19 | ~spl3_4 | ~spl3_5 | ~spl3_8 | ~spl3_11),
% 0.19/0.41    inference(avatar_split_clause,[],[f141,f83,f70,f56,f51,f143])).
% 0.19/0.41  fof(f51,plain,(
% 0.19/0.41    spl3_4 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.41  fof(f56,plain,(
% 0.19/0.41    spl3_5 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.41  fof(f70,plain,(
% 0.19/0.41    spl3_8 <=> k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.19/0.41  fof(f83,plain,(
% 0.19/0.41    spl3_11 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.19/0.41  fof(f141,plain,(
% 0.19/0.41    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))) | (~spl3_4 | ~spl3_5 | ~spl3_8 | ~spl3_11)),
% 0.19/0.41    inference(forward_demodulation,[],[f140,f57])).
% 0.19/0.41  fof(f57,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_5),
% 0.19/0.41    inference(avatar_component_clause,[],[f56])).
% 0.19/0.41  fof(f140,plain,(
% 0.19/0.41    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)) | (~spl3_4 | ~spl3_8 | ~spl3_11)),
% 0.19/0.41    inference(forward_demodulation,[],[f139,f72])).
% 0.19/0.41  fof(f72,plain,(
% 0.19/0.41    k1_xboole_0 = k4_xboole_0(sK0,sK2) | ~spl3_8),
% 0.19/0.41    inference(avatar_component_clause,[],[f70])).
% 0.19/0.41  fof(f139,plain,(
% 0.19/0.41    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) | (~spl3_4 | ~spl3_11)),
% 0.19/0.41    inference(forward_demodulation,[],[f137,f35])).
% 0.19/0.41  fof(f35,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 0.19/0.41    inference(definition_unfolding,[],[f30,f23])).
% 0.19/0.41  fof(f23,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f8])).
% 0.19/0.41  fof(f8,axiom,(
% 0.19/0.41    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.41  fof(f30,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f4])).
% 0.19/0.41  fof(f4,axiom,(
% 0.19/0.41    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).
% 0.19/0.41  fof(f137,plain,(
% 0.19/0.41    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) | (~spl3_4 | ~spl3_11)),
% 0.19/0.41    inference(resolution,[],[f84,f53])).
% 0.19/0.41  fof(f53,plain,(
% 0.19/0.41    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | ~spl3_4),
% 0.19/0.41    inference(avatar_component_clause,[],[f51])).
% 0.19/0.41  fof(f84,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_11),
% 0.19/0.41    inference(avatar_component_clause,[],[f83])).
% 0.19/0.41  fof(f112,plain,(
% 0.19/0.41    spl3_15 | ~spl3_3 | ~spl3_9),
% 0.19/0.41    inference(avatar_split_clause,[],[f87,f75,f47,f110])).
% 0.19/0.41  fof(f47,plain,(
% 0.19/0.41    spl3_3 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.41  fof(f75,plain,(
% 0.19/0.41    spl3_9 <=> ! [X1,X0,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.19/0.41  fof(f87,plain,(
% 0.19/0.41    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k2_xboole_0(k1_xboole_0,X1))) ) | (~spl3_3 | ~spl3_9)),
% 0.19/0.41    inference(superposition,[],[f76,f48])).
% 0.19/0.41  fof(f48,plain,(
% 0.19/0.41    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_3),
% 0.19/0.41    inference(avatar_component_clause,[],[f47])).
% 0.19/0.41  fof(f76,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) ) | ~spl3_9),
% 0.19/0.41    inference(avatar_component_clause,[],[f75])).
% 0.19/0.41  fof(f101,plain,(
% 0.19/0.41    ~spl3_13 | spl3_1 | ~spl3_10),
% 0.19/0.41    inference(avatar_split_clause,[],[f96,f79,f37,f98])).
% 0.19/0.41  fof(f37,plain,(
% 0.19/0.41    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.41  fof(f79,plain,(
% 0.19/0.41    spl3_10 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.19/0.41  fof(f96,plain,(
% 0.19/0.41    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (spl3_1 | ~spl3_10)),
% 0.19/0.41    inference(resolution,[],[f80,f39])).
% 0.19/0.41  fof(f39,plain,(
% 0.19/0.41    ~r1_xboole_0(sK0,sK1) | spl3_1),
% 0.19/0.41    inference(avatar_component_clause,[],[f37])).
% 0.19/0.41  fof(f80,plain,(
% 0.19/0.41    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_10),
% 0.19/0.41    inference(avatar_component_clause,[],[f79])).
% 0.19/0.41  fof(f85,plain,(
% 0.19/0.41    spl3_11),
% 0.19/0.41    inference(avatar_split_clause,[],[f34,f83])).
% 0.19/0.41  fof(f34,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.41    inference(definition_unfolding,[],[f24,f23])).
% 0.19/0.41  fof(f24,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f15])).
% 0.19/0.41  fof(f15,plain,(
% 0.19/0.41    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.19/0.41    inference(nnf_transformation,[],[f2])).
% 0.19/0.41  fof(f2,axiom,(
% 0.19/0.41    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.19/0.41  fof(f81,plain,(
% 0.19/0.41    spl3_10),
% 0.19/0.41    inference(avatar_split_clause,[],[f33,f79])).
% 0.19/0.41  fof(f33,plain,(
% 0.19/0.41    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.19/0.41    inference(definition_unfolding,[],[f25,f23])).
% 0.19/0.41  fof(f25,plain,(
% 0.19/0.41    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.19/0.41    inference(cnf_transformation,[],[f15])).
% 0.19/0.41  fof(f77,plain,(
% 0.19/0.41    spl3_9),
% 0.19/0.41    inference(avatar_split_clause,[],[f31,f75])).
% 0.19/0.41  fof(f31,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f12])).
% 0.19/0.41  fof(f12,plain,(
% 0.19/0.41    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.19/0.41    inference(ennf_transformation,[],[f7])).
% 0.19/0.41  fof(f7,axiom,(
% 0.19/0.41    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.19/0.41  fof(f73,plain,(
% 0.19/0.41    spl3_8 | ~spl3_2 | ~spl3_7),
% 0.19/0.41    inference(avatar_split_clause,[],[f67,f64,f42,f70])).
% 0.19/0.41  fof(f42,plain,(
% 0.19/0.41    spl3_2 <=> r1_tarski(sK0,sK2)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.41  fof(f67,plain,(
% 0.19/0.41    k1_xboole_0 = k4_xboole_0(sK0,sK2) | (~spl3_2 | ~spl3_7)),
% 0.19/0.41    inference(resolution,[],[f65,f44])).
% 0.19/0.41  fof(f44,plain,(
% 0.19/0.41    r1_tarski(sK0,sK2) | ~spl3_2),
% 0.19/0.41    inference(avatar_component_clause,[],[f42])).
% 0.19/0.41  fof(f66,plain,(
% 0.19/0.41    spl3_7),
% 0.19/0.41    inference(avatar_split_clause,[],[f27,f64])).
% 0.19/0.41  fof(f27,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f16])).
% 0.19/0.41  fof(f16,plain,(
% 0.19/0.41    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.19/0.41    inference(nnf_transformation,[],[f3])).
% 0.19/0.41  fof(f3,axiom,(
% 0.19/0.41    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.19/0.41  fof(f62,plain,(
% 0.19/0.41    spl3_6),
% 0.19/0.41    inference(avatar_split_clause,[],[f26,f60])).
% 0.19/0.41  fof(f26,plain,(
% 0.19/0.41    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f16])).
% 0.19/0.41  fof(f58,plain,(
% 0.19/0.41    spl3_5),
% 0.19/0.41    inference(avatar_split_clause,[],[f22,f56])).
% 0.19/0.41  fof(f22,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f1])).
% 0.19/0.41  fof(f1,axiom,(
% 0.19/0.41    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.19/0.41  fof(f54,plain,(
% 0.19/0.41    spl3_4),
% 0.19/0.41    inference(avatar_split_clause,[],[f32,f51])).
% 0.19/0.41  fof(f32,plain,(
% 0.19/0.41    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.19/0.41    inference(definition_unfolding,[],[f20,f23])).
% 0.19/0.41  fof(f20,plain,(
% 0.19/0.41    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.19/0.41    inference(cnf_transformation,[],[f14])).
% 0.19/0.41  fof(f14,plain,(
% 0.19/0.41    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.19/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 0.19/0.41  fof(f13,plain,(
% 0.19/0.41    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.19/0.41    introduced(choice_axiom,[])).
% 0.19/0.41  fof(f11,plain,(
% 0.19/0.41    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.19/0.41    inference(ennf_transformation,[],[f10])).
% 0.19/0.41  fof(f10,negated_conjecture,(
% 0.19/0.41    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.19/0.41    inference(negated_conjecture,[],[f9])).
% 0.19/0.41  fof(f9,conjecture,(
% 0.19/0.41    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.19/0.41  fof(f49,plain,(
% 0.19/0.41    spl3_3),
% 0.19/0.41    inference(avatar_split_clause,[],[f21,f47])).
% 0.19/0.41  fof(f21,plain,(
% 0.19/0.41    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.41    inference(cnf_transformation,[],[f6])).
% 0.19/0.41  fof(f6,axiom,(
% 0.19/0.41    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.19/0.41  fof(f45,plain,(
% 0.19/0.41    spl3_2),
% 0.19/0.41    inference(avatar_split_clause,[],[f19,f42])).
% 0.19/0.41  fof(f19,plain,(
% 0.19/0.41    r1_tarski(sK0,sK2)),
% 0.19/0.41    inference(cnf_transformation,[],[f14])).
% 0.19/0.41  fof(f40,plain,(
% 0.19/0.41    ~spl3_1),
% 0.19/0.41    inference(avatar_split_clause,[],[f18,f37])).
% 0.19/0.41  fof(f18,plain,(
% 0.19/0.41    ~r1_xboole_0(sK0,sK1)),
% 0.19/0.41    inference(cnf_transformation,[],[f14])).
% 0.19/0.41  % SZS output end Proof for theBenchmark
% 0.19/0.41  % (31332)------------------------------
% 0.19/0.41  % (31332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.41  % (31332)Termination reason: Refutation
% 0.19/0.41  
% 0.19/0.41  % (31332)Memory used [KB]: 6140
% 0.19/0.41  % (31332)Time elapsed: 0.027 s
% 0.19/0.41  % (31332)------------------------------
% 0.19/0.41  % (31332)------------------------------
% 0.19/0.41  % (31324)Success in time 0.076 s
%------------------------------------------------------------------------------
