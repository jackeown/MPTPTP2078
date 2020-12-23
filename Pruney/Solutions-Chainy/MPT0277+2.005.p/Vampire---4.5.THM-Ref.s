%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:31 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 344 expanded)
%              Number of leaves         :   24 ( 131 expanded)
%              Depth                    :   13
%              Number of atoms          :  242 ( 556 expanded)
%              Number of equality atoms :  143 ( 420 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f953,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f114,f115,f116,f117,f721,f755,f765,f796,f805,f878,f908,f952])).

fof(f952,plain,
    ( spl4_5
    | spl4_2
    | spl4_3
    | spl4_4
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f951,f279,f106,f102,f98,f110])).

fof(f110,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f98,plain,
    ( spl4_2
  <=> sK0 = k2_enumset1(sK1,sK1,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f102,plain,
    ( spl4_3
  <=> sK0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f106,plain,
    ( spl4_4
  <=> sK0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f279,plain,
    ( spl4_15
  <=> r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f951,plain,
    ( sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | sK0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | sK0 = k2_enumset1(sK1,sK1,sK1,sK2)
    | k1_xboole_0 = sK0
    | ~ spl4_15 ),
    inference(resolution,[],[f281,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k2_enumset1(X2,X2,X2,X2) = X0
      | k2_enumset1(X1,X1,X1,X2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f38,f55,f55,f54,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f54])).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_tarski(X1,X2) = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f281,plain,
    ( r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK2))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f279])).

fof(f908,plain,
    ( spl4_15
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f907,f94,f279])).

fof(f94,plain,
    ( spl4_1
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f907,plain,
    ( r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK2))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f891,f195])).

fof(f195,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f192,f124])).

fof(f124,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f62,f26])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f62,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f27,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f192,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f56,f155])).

fof(f155,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f63,f26])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f30,f34,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f891,plain,
    ( r1_tarski(k4_xboole_0(sK0,k1_xboole_0),k2_enumset1(sK1,sK1,sK1,sK2))
    | ~ spl4_1 ),
    inference(superposition,[],[f161,f96])).

fof(f96,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f161,plain,(
    ! [X6,X5] : r1_tarski(k4_xboole_0(X6,k4_xboole_0(X6,X5)),X5) ),
    inference(superposition,[],[f29,f63])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f878,plain,
    ( spl4_1
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f877])).

fof(f877,plain,
    ( $false
    | spl4_1
    | ~ spl4_4 ),
    inference(trivial_inequality_removal,[],[f869])).

fof(f869,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl4_1
    | ~ spl4_4 ),
    inference(superposition,[],[f95,f836])).

fof(f836,plain,
    ( ! [X11] : k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,X11))
    | ~ spl4_4 ),
    inference(superposition,[],[f64,f108])).

fof(f108,plain,
    ( sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f64,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f55,f54])).

fof(f31,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

fof(f95,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f805,plain,(
    spl4_23 ),
    inference(avatar_contradiction_clause,[],[f804])).

fof(f804,plain,
    ( $false
    | spl4_23 ),
    inference(trivial_inequality_removal,[],[f803])).

fof(f803,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl4_23 ),
    inference(superposition,[],[f795,f26])).

fof(f795,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK2))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f793])).

fof(f793,plain,
    ( spl4_23
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f796,plain,
    ( ~ spl4_23
    | spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f791,f110,f94,f793])).

fof(f791,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK2))
    | spl4_1
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f95,f112])).

fof(f112,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f110])).

fof(f765,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f764])).

fof(f764,plain,
    ( $false
    | spl4_11 ),
    inference(trivial_inequality_removal,[],[f763])).

fof(f763,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl4_11 ),
    inference(superposition,[],[f204,f207])).

fof(f207,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f155,f195])).

fof(f204,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl4_11
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f755,plain,
    ( ~ spl4_11
    | spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f734,f98,f94,f203])).

fof(f734,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | spl4_1
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f95,f100])).

fof(f100,plain,
    ( sK0 = k2_enumset1(sK1,sK1,sK1,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f721,plain,
    ( spl4_1
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f720])).

fof(f720,plain,
    ( $false
    | spl4_1
    | ~ spl4_3 ),
    inference(trivial_inequality_removal,[],[f708])).

fof(f708,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl4_1
    | ~ spl4_3 ),
    inference(superposition,[],[f95,f679])).

fof(f679,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(X2,X2,X3,sK2))
    | ~ spl4_3 ),
    inference(trivial_inequality_removal,[],[f678])).

fof(f678,plain,
    ( ! [X2,X3] :
        ( sK0 != sK0
        | k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(X2,X2,X3,sK2)) )
    | ~ spl4_3 ),
    inference(superposition,[],[f661,f336])).

fof(f336,plain,
    ( ! [X0] :
        ( sK0 = k4_xboole_0(sK0,X0)
        | k1_xboole_0 = k4_xboole_0(sK0,X0) )
    | ~ spl4_3 ),
    inference(superposition,[],[f65,f104])).

fof(f104,plain,
    ( sK0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f36,f55,f55,f55])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(f661,plain,
    ( ! [X0,X1] : sK0 != k4_xboole_0(sK0,k2_enumset1(X0,X0,X1,sK2))
    | ~ spl4_3 ),
    inference(superposition,[],[f259,f104])).

fof(f259,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X0,X0,X1) != k4_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X3,X1)) ),
    inference(resolution,[],[f72,f87])).

fof(f87,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k2_enumset1(X0,X0,X1,X4)) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f53,f37])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k2_enumset1(X0,X0,X0,X1) != k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f44,f54,f54])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f117,plain,
    ( ~ spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f61,f110,f94])).

fof(f61,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f21,f54])).

fof(f21,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(f116,plain,
    ( ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f60,f106,f94])).

fof(f60,plain,
    ( sK0 != k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f22,f55,f54])).

fof(f22,plain,
    ( sK0 != k1_tarski(sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f115,plain,
    ( ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f59,f102,f94])).

fof(f59,plain,
    ( sK0 != k2_enumset1(sK2,sK2,sK2,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f23,f55,f54])).

fof(f23,plain,
    ( sK0 != k1_tarski(sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f114,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f58,f98,f94])).

fof(f58,plain,
    ( sK0 != k2_enumset1(sK1,sK1,sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f24,f54,f54])).

fof(f24,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f113,plain,
    ( spl4_1
    | spl4_2
    | spl4_3
    | spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f57,f110,f106,f102,f98,f94])).

fof(f57,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | sK0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | sK0 = k2_enumset1(sK1,sK1,sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f25,f55,f55,f54,f54])).

fof(f25,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | sK0 = k1_tarski(sK2)
    | sK0 = k2_tarski(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:24:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.56  % (6482)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.52/0.56  % (6483)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.52/0.56  % (6495)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.52/0.57  % (6486)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.52/0.57  % (6488)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.52/0.57  % (6503)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.52/0.57  % (6490)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.52/0.57  % (6503)Refutation not found, incomplete strategy% (6503)------------------------------
% 1.52/0.57  % (6503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (6511)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.52/0.58  % (6487)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.52/0.58  % (6503)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.58  
% 1.52/0.58  % (6503)Memory used [KB]: 1791
% 1.52/0.58  % (6503)Time elapsed: 0.145 s
% 1.52/0.58  % (6503)------------------------------
% 1.52/0.58  % (6503)------------------------------
% 1.52/0.58  % (6501)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.52/0.58  % (6490)Refutation not found, incomplete strategy% (6490)------------------------------
% 1.52/0.58  % (6490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.58  % (6504)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.52/0.58  % (6491)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.52/0.58  % (6482)Refutation not found, incomplete strategy% (6482)------------------------------
% 1.52/0.58  % (6482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.58  % (6482)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.58  
% 1.52/0.58  % (6482)Memory used [KB]: 1663
% 1.52/0.58  % (6482)Time elapsed: 0.155 s
% 1.52/0.58  % (6482)------------------------------
% 1.52/0.58  % (6482)------------------------------
% 1.52/0.58  % (6507)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.52/0.58  % (6497)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.52/0.58  % (6491)Refutation not found, incomplete strategy% (6491)------------------------------
% 1.52/0.58  % (6491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.58  % (6498)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.68/0.58  % (6496)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.68/0.58  % (6497)Refutation not found, incomplete strategy% (6497)------------------------------
% 1.68/0.58  % (6497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.58  % (6497)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.58  
% 1.68/0.58  % (6497)Memory used [KB]: 6268
% 1.68/0.58  % (6497)Time elapsed: 0.111 s
% 1.68/0.58  % (6497)------------------------------
% 1.68/0.58  % (6497)------------------------------
% 1.68/0.58  % (6500)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.68/0.58  % (6490)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.58  
% 1.68/0.58  % (6490)Memory used [KB]: 10874
% 1.68/0.58  % (6490)Time elapsed: 0.149 s
% 1.68/0.58  % (6490)------------------------------
% 1.68/0.58  % (6490)------------------------------
% 1.68/0.58  % (6502)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.68/0.58  % (6485)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.68/0.59  % (6493)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.68/0.59  % (6509)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.68/0.59  % (6492)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.68/0.59  % (6505)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.68/0.59  % (6494)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.68/0.59  % (6491)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.59  
% 1.68/0.59  % (6491)Memory used [KB]: 10618
% 1.68/0.59  % (6491)Time elapsed: 0.156 s
% 1.68/0.59  % (6491)------------------------------
% 1.68/0.59  % (6491)------------------------------
% 1.68/0.59  % (6506)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.68/0.59  % (6508)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.68/0.59  % (6484)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.68/0.60  % (6510)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.68/0.60  % (6499)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.68/0.60  % (6489)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.68/0.60  % (6499)Refutation not found, incomplete strategy% (6499)------------------------------
% 1.68/0.60  % (6499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.60  % (6499)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.60  
% 1.68/0.60  % (6499)Memory used [KB]: 10618
% 1.68/0.60  % (6499)Time elapsed: 0.176 s
% 1.68/0.60  % (6499)------------------------------
% 1.68/0.60  % (6499)------------------------------
% 1.68/0.60  % (6492)Refutation not found, incomplete strategy% (6492)------------------------------
% 1.68/0.60  % (6492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.61  % (6493)Refutation not found, incomplete strategy% (6493)------------------------------
% 1.68/0.61  % (6493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.61  % (6493)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.61  
% 1.68/0.61  % (6493)Memory used [KB]: 10618
% 1.68/0.61  % (6493)Time elapsed: 0.190 s
% 1.68/0.61  % (6493)------------------------------
% 1.68/0.61  % (6493)------------------------------
% 1.68/0.61  % (6492)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.61  
% 1.68/0.61  % (6492)Memory used [KB]: 10618
% 1.68/0.61  % (6492)Time elapsed: 0.181 s
% 1.68/0.61  % (6492)------------------------------
% 1.68/0.61  % (6492)------------------------------
% 1.68/0.61  % (6498)Refutation found. Thanks to Tanya!
% 1.68/0.61  % SZS status Theorem for theBenchmark
% 1.68/0.61  % SZS output start Proof for theBenchmark
% 1.68/0.61  fof(f953,plain,(
% 1.68/0.61    $false),
% 1.68/0.61    inference(avatar_sat_refutation,[],[f113,f114,f115,f116,f117,f721,f755,f765,f796,f805,f878,f908,f952])).
% 1.68/0.61  fof(f952,plain,(
% 1.68/0.61    spl4_5 | spl4_2 | spl4_3 | spl4_4 | ~spl4_15),
% 1.68/0.61    inference(avatar_split_clause,[],[f951,f279,f106,f102,f98,f110])).
% 1.68/0.61  fof(f110,plain,(
% 1.68/0.61    spl4_5 <=> k1_xboole_0 = sK0),
% 1.68/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.68/0.61  fof(f98,plain,(
% 1.68/0.61    spl4_2 <=> sK0 = k2_enumset1(sK1,sK1,sK1,sK2)),
% 1.68/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.68/0.61  fof(f102,plain,(
% 1.68/0.61    spl4_3 <=> sK0 = k2_enumset1(sK2,sK2,sK2,sK2)),
% 1.68/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.68/0.61  fof(f106,plain,(
% 1.68/0.61    spl4_4 <=> sK0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.68/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.68/0.61  fof(f279,plain,(
% 1.68/0.61    spl4_15 <=> r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.68/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.68/0.61  fof(f951,plain,(
% 1.68/0.61    sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | sK0 = k2_enumset1(sK2,sK2,sK2,sK2) | sK0 = k2_enumset1(sK1,sK1,sK1,sK2) | k1_xboole_0 = sK0 | ~spl4_15),
% 1.68/0.61    inference(resolution,[],[f281,f70])).
% 1.68/0.61  fof(f70,plain,(
% 1.68/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) | k2_enumset1(X1,X1,X1,X1) = X0 | k2_enumset1(X2,X2,X2,X2) = X0 | k2_enumset1(X1,X1,X1,X2) = X0 | k1_xboole_0 = X0) )),
% 1.68/0.61    inference(definition_unfolding,[],[f38,f55,f55,f54,f54])).
% 1.68/0.61  fof(f54,plain,(
% 1.68/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.68/0.61    inference(definition_unfolding,[],[f32,f37])).
% 1.68/0.61  fof(f37,plain,(
% 1.68/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.68/0.61    inference(cnf_transformation,[],[f11])).
% 1.68/0.61  fof(f11,axiom,(
% 1.68/0.61    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.68/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.68/0.61  fof(f32,plain,(
% 1.68/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.68/0.61    inference(cnf_transformation,[],[f10])).
% 1.68/0.61  fof(f10,axiom,(
% 1.68/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.68/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.68/0.61  fof(f55,plain,(
% 1.68/0.61    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.68/0.61    inference(definition_unfolding,[],[f28,f54])).
% 1.68/0.61  fof(f28,plain,(
% 1.68/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.68/0.61    inference(cnf_transformation,[],[f9])).
% 1.68/0.61  fof(f9,axiom,(
% 1.68/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.68/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.68/0.61  fof(f38,plain,(
% 1.68/0.61    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | k1_tarski(X2) = X0 | k2_tarski(X1,X2) = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.68/0.61    inference(cnf_transformation,[],[f19])).
% 1.68/0.61  fof(f19,plain,(
% 1.68/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.68/0.61    inference(ennf_transformation,[],[f12])).
% 1.68/0.61  fof(f12,axiom,(
% 1.68/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.68/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.68/0.61  fof(f281,plain,(
% 1.68/0.61    r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) | ~spl4_15),
% 1.68/0.61    inference(avatar_component_clause,[],[f279])).
% 1.68/0.61  fof(f908,plain,(
% 1.68/0.61    spl4_15 | ~spl4_1),
% 1.68/0.61    inference(avatar_split_clause,[],[f907,f94,f279])).
% 1.68/0.61  fof(f94,plain,(
% 1.68/0.61    spl4_1 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.68/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.68/0.61  fof(f907,plain,(
% 1.68/0.61    r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) | ~spl4_1),
% 1.68/0.61    inference(forward_demodulation,[],[f891,f195])).
% 1.68/0.61  fof(f195,plain,(
% 1.68/0.61    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 1.68/0.61    inference(forward_demodulation,[],[f192,f124])).
% 1.68/0.61  fof(f124,plain,(
% 1.68/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.68/0.61    inference(forward_demodulation,[],[f62,f26])).
% 1.68/0.61  fof(f26,plain,(
% 1.68/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.68/0.61    inference(cnf_transformation,[],[f6])).
% 1.68/0.61  fof(f6,axiom,(
% 1.68/0.61    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.68/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.68/0.61  fof(f62,plain,(
% 1.68/0.61    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 1.68/0.61    inference(definition_unfolding,[],[f27,f33])).
% 1.68/0.61  fof(f33,plain,(
% 1.68/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.68/0.61    inference(cnf_transformation,[],[f7])).
% 1.68/0.61  fof(f7,axiom,(
% 1.68/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.68/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.68/0.61  fof(f27,plain,(
% 1.68/0.61    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.68/0.61    inference(cnf_transformation,[],[f3])).
% 1.68/0.61  fof(f3,axiom,(
% 1.68/0.61    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.68/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.68/0.61  fof(f192,plain,(
% 1.68/0.61    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0)) )),
% 1.68/0.61    inference(superposition,[],[f56,f155])).
% 1.68/0.61  fof(f155,plain,(
% 1.68/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.68/0.61    inference(superposition,[],[f63,f26])).
% 1.68/0.61  fof(f63,plain,(
% 1.68/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.68/0.61    inference(definition_unfolding,[],[f30,f34,f34])).
% 1.68/0.61  fof(f34,plain,(
% 1.68/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.68/0.61    inference(cnf_transformation,[],[f5])).
% 1.68/0.61  fof(f5,axiom,(
% 1.68/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.68/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.68/0.61  fof(f30,plain,(
% 1.68/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.68/0.61    inference(cnf_transformation,[],[f1])).
% 1.68/0.61  fof(f1,axiom,(
% 1.68/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.68/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.68/0.61  fof(f56,plain,(
% 1.68/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.68/0.61    inference(definition_unfolding,[],[f35,f34])).
% 1.68/0.61  fof(f35,plain,(
% 1.68/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.68/0.61    inference(cnf_transformation,[],[f2])).
% 1.68/0.61  fof(f2,axiom,(
% 1.68/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.68/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.68/0.61  fof(f891,plain,(
% 1.68/0.61    r1_tarski(k4_xboole_0(sK0,k1_xboole_0),k2_enumset1(sK1,sK1,sK1,sK2)) | ~spl4_1),
% 1.68/0.61    inference(superposition,[],[f161,f96])).
% 1.68/0.61  fof(f96,plain,(
% 1.68/0.61    k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) | ~spl4_1),
% 1.68/0.61    inference(avatar_component_clause,[],[f94])).
% 1.68/0.61  fof(f161,plain,(
% 1.68/0.61    ( ! [X6,X5] : (r1_tarski(k4_xboole_0(X6,k4_xboole_0(X6,X5)),X5)) )),
% 1.68/0.61    inference(superposition,[],[f29,f63])).
% 1.68/0.61  fof(f29,plain,(
% 1.68/0.61    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.68/0.61    inference(cnf_transformation,[],[f4])).
% 1.68/0.61  fof(f4,axiom,(
% 1.68/0.61    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.68/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.68/0.61  fof(f878,plain,(
% 1.68/0.61    spl4_1 | ~spl4_4),
% 1.68/0.61    inference(avatar_contradiction_clause,[],[f877])).
% 1.68/0.61  fof(f877,plain,(
% 1.68/0.61    $false | (spl4_1 | ~spl4_4)),
% 1.68/0.61    inference(trivial_inequality_removal,[],[f869])).
% 1.68/0.61  fof(f869,plain,(
% 1.68/0.61    k1_xboole_0 != k1_xboole_0 | (spl4_1 | ~spl4_4)),
% 1.68/0.61    inference(superposition,[],[f95,f836])).
% 1.68/0.61  fof(f836,plain,(
% 1.68/0.61    ( ! [X11] : (k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,X11))) ) | ~spl4_4),
% 1.68/0.61    inference(superposition,[],[f64,f108])).
% 1.68/0.61  fof(f108,plain,(
% 1.68/0.61    sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl4_4),
% 1.68/0.61    inference(avatar_component_clause,[],[f106])).
% 1.68/0.61  fof(f64,plain,(
% 1.68/0.61    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1))) )),
% 1.68/0.61    inference(definition_unfolding,[],[f31,f55,f54])).
% 1.68/0.61  fof(f31,plain,(
% 1.68/0.61    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.68/0.61    inference(cnf_transformation,[],[f13])).
% 1.68/0.61  fof(f13,axiom,(
% 1.68/0.61    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.68/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).
% 1.68/0.61  fof(f95,plain,(
% 1.68/0.61    k1_xboole_0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2)) | spl4_1),
% 1.68/0.61    inference(avatar_component_clause,[],[f94])).
% 1.68/0.61  fof(f805,plain,(
% 1.68/0.61    spl4_23),
% 1.68/0.61    inference(avatar_contradiction_clause,[],[f804])).
% 1.68/0.61  fof(f804,plain,(
% 1.68/0.61    $false | spl4_23),
% 1.68/0.61    inference(trivial_inequality_removal,[],[f803])).
% 1.68/0.61  fof(f803,plain,(
% 1.68/0.61    k1_xboole_0 != k1_xboole_0 | spl4_23),
% 1.68/0.61    inference(superposition,[],[f795,f26])).
% 1.68/0.61  fof(f795,plain,(
% 1.68/0.61    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK2)) | spl4_23),
% 1.68/0.61    inference(avatar_component_clause,[],[f793])).
% 1.68/0.61  fof(f793,plain,(
% 1.68/0.61    spl4_23 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.68/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.68/0.61  fof(f796,plain,(
% 1.68/0.61    ~spl4_23 | spl4_1 | ~spl4_5),
% 1.68/0.61    inference(avatar_split_clause,[],[f791,f110,f94,f793])).
% 1.68/0.61  fof(f791,plain,(
% 1.68/0.61    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK2)) | (spl4_1 | ~spl4_5)),
% 1.68/0.61    inference(forward_demodulation,[],[f95,f112])).
% 1.68/0.61  fof(f112,plain,(
% 1.68/0.61    k1_xboole_0 = sK0 | ~spl4_5),
% 1.68/0.61    inference(avatar_component_clause,[],[f110])).
% 1.68/0.61  fof(f765,plain,(
% 1.68/0.61    spl4_11),
% 1.68/0.61    inference(avatar_contradiction_clause,[],[f764])).
% 1.68/0.61  fof(f764,plain,(
% 1.68/0.61    $false | spl4_11),
% 1.68/0.61    inference(trivial_inequality_removal,[],[f763])).
% 1.68/0.61  fof(f763,plain,(
% 1.68/0.61    k1_xboole_0 != k1_xboole_0 | spl4_11),
% 1.68/0.61    inference(superposition,[],[f204,f207])).
% 1.68/0.61  fof(f207,plain,(
% 1.68/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.68/0.61    inference(backward_demodulation,[],[f155,f195])).
% 1.68/0.61  fof(f204,plain,(
% 1.68/0.61    k1_xboole_0 != k4_xboole_0(sK0,sK0) | spl4_11),
% 1.68/0.61    inference(avatar_component_clause,[],[f203])).
% 1.68/0.61  fof(f203,plain,(
% 1.68/0.61    spl4_11 <=> k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 1.68/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.68/0.61  fof(f755,plain,(
% 1.68/0.61    ~spl4_11 | spl4_1 | ~spl4_2),
% 1.68/0.61    inference(avatar_split_clause,[],[f734,f98,f94,f203])).
% 1.68/0.61  fof(f734,plain,(
% 1.68/0.61    k1_xboole_0 != k4_xboole_0(sK0,sK0) | (spl4_1 | ~spl4_2)),
% 1.68/0.61    inference(backward_demodulation,[],[f95,f100])).
% 1.68/0.61  fof(f100,plain,(
% 1.68/0.61    sK0 = k2_enumset1(sK1,sK1,sK1,sK2) | ~spl4_2),
% 1.68/0.61    inference(avatar_component_clause,[],[f98])).
% 1.68/0.61  fof(f721,plain,(
% 1.68/0.61    spl4_1 | ~spl4_3),
% 1.68/0.61    inference(avatar_contradiction_clause,[],[f720])).
% 1.68/0.61  fof(f720,plain,(
% 1.68/0.61    $false | (spl4_1 | ~spl4_3)),
% 1.68/0.61    inference(trivial_inequality_removal,[],[f708])).
% 1.68/0.61  fof(f708,plain,(
% 1.68/0.61    k1_xboole_0 != k1_xboole_0 | (spl4_1 | ~spl4_3)),
% 1.68/0.61    inference(superposition,[],[f95,f679])).
% 1.68/0.61  fof(f679,plain,(
% 1.68/0.61    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(X2,X2,X3,sK2))) ) | ~spl4_3),
% 1.68/0.61    inference(trivial_inequality_removal,[],[f678])).
% 1.68/0.61  fof(f678,plain,(
% 1.68/0.61    ( ! [X2,X3] : (sK0 != sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(X2,X2,X3,sK2))) ) | ~spl4_3),
% 1.68/0.61    inference(superposition,[],[f661,f336])).
% 1.68/0.61  fof(f336,plain,(
% 1.68/0.61    ( ! [X0] : (sK0 = k4_xboole_0(sK0,X0) | k1_xboole_0 = k4_xboole_0(sK0,X0)) ) | ~spl4_3),
% 1.68/0.61    inference(superposition,[],[f65,f104])).
% 1.68/0.61  fof(f104,plain,(
% 1.68/0.61    sK0 = k2_enumset1(sK2,sK2,sK2,sK2) | ~spl4_3),
% 1.68/0.61    inference(avatar_component_clause,[],[f102])).
% 1.68/0.61  fof(f65,plain,(
% 1.68/0.61    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 1.68/0.61    inference(definition_unfolding,[],[f36,f55,f55,f55])).
% 1.68/0.61  fof(f36,plain,(
% 1.68/0.61    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.68/0.61    inference(cnf_transformation,[],[f14])).
% 1.68/0.61  fof(f14,axiom,(
% 1.68/0.61    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 1.68/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).
% 1.68/0.61  fof(f661,plain,(
% 1.68/0.61    ( ! [X0,X1] : (sK0 != k4_xboole_0(sK0,k2_enumset1(X0,X0,X1,sK2))) ) | ~spl4_3),
% 1.68/0.61    inference(superposition,[],[f259,f104])).
% 1.68/0.61  fof(f259,plain,(
% 1.68/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X0,X1) != k4_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X3,X1))) )),
% 1.68/0.61    inference(resolution,[],[f72,f87])).
% 1.68/0.61  fof(f87,plain,(
% 1.68/0.61    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_enumset1(X0,X0,X1,X4))) )),
% 1.68/0.61    inference(equality_resolution,[],[f86])).
% 1.68/0.61  fof(f86,plain,(
% 1.68/0.61    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X4) != X3) )),
% 1.68/0.61    inference(equality_resolution,[],[f74])).
% 1.68/0.61  fof(f74,plain,(
% 1.68/0.61    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.68/0.61    inference(definition_unfolding,[],[f53,f37])).
% 1.68/0.61  fof(f53,plain,(
% 1.68/0.61    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.68/0.61    inference(cnf_transformation,[],[f20])).
% 1.68/0.61  fof(f20,plain,(
% 1.68/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.68/0.61    inference(ennf_transformation,[],[f8])).
% 1.68/0.61  fof(f8,axiom,(
% 1.68/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.68/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.68/0.61  fof(f72,plain,(
% 1.68/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k2_enumset1(X0,X0,X0,X1) != k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)) )),
% 1.68/0.61    inference(definition_unfolding,[],[f44,f54,f54])).
% 1.68/0.61  fof(f44,plain,(
% 1.68/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.68/0.61    inference(cnf_transformation,[],[f15])).
% 1.68/0.61  fof(f15,axiom,(
% 1.68/0.61    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.68/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 1.68/0.61  fof(f117,plain,(
% 1.68/0.61    ~spl4_1 | ~spl4_5),
% 1.68/0.61    inference(avatar_split_clause,[],[f61,f110,f94])).
% 1.68/0.61  fof(f61,plain,(
% 1.68/0.61    k1_xboole_0 != sK0 | k1_xboole_0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.68/0.61    inference(definition_unfolding,[],[f21,f54])).
% 1.68/0.61  fof(f21,plain,(
% 1.68/0.61    k1_xboole_0 != sK0 | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.68/0.61    inference(cnf_transformation,[],[f18])).
% 1.68/0.61  fof(f18,plain,(
% 1.68/0.61    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <~> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.68/0.61    inference(ennf_transformation,[],[f17])).
% 1.68/0.61  fof(f17,negated_conjecture,(
% 1.68/0.61    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.68/0.61    inference(negated_conjecture,[],[f16])).
% 1.68/0.61  fof(f16,conjecture,(
% 1.68/0.61    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.68/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).
% 1.68/0.61  fof(f116,plain,(
% 1.68/0.61    ~spl4_1 | ~spl4_4),
% 1.68/0.61    inference(avatar_split_clause,[],[f60,f106,f94])).
% 1.68/0.61  fof(f60,plain,(
% 1.68/0.61    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) | k1_xboole_0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.68/0.61    inference(definition_unfolding,[],[f22,f55,f54])).
% 1.68/0.61  fof(f22,plain,(
% 1.68/0.61    sK0 != k1_tarski(sK1) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.68/0.61    inference(cnf_transformation,[],[f18])).
% 1.68/0.61  fof(f115,plain,(
% 1.68/0.61    ~spl4_1 | ~spl4_3),
% 1.68/0.61    inference(avatar_split_clause,[],[f59,f102,f94])).
% 1.68/0.61  fof(f59,plain,(
% 1.68/0.61    sK0 != k2_enumset1(sK2,sK2,sK2,sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.68/0.61    inference(definition_unfolding,[],[f23,f55,f54])).
% 1.68/0.61  fof(f23,plain,(
% 1.68/0.61    sK0 != k1_tarski(sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.68/0.61    inference(cnf_transformation,[],[f18])).
% 1.68/0.61  fof(f114,plain,(
% 1.68/0.61    ~spl4_1 | ~spl4_2),
% 1.68/0.61    inference(avatar_split_clause,[],[f58,f98,f94])).
% 1.68/0.61  fof(f58,plain,(
% 1.68/0.61    sK0 != k2_enumset1(sK1,sK1,sK1,sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.68/0.61    inference(definition_unfolding,[],[f24,f54,f54])).
% 1.68/0.61  fof(f24,plain,(
% 1.68/0.61    sK0 != k2_tarski(sK1,sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.68/0.61    inference(cnf_transformation,[],[f18])).
% 1.68/0.61  fof(f113,plain,(
% 1.68/0.61    spl4_1 | spl4_2 | spl4_3 | spl4_4 | spl4_5),
% 1.68/0.61    inference(avatar_split_clause,[],[f57,f110,f106,f102,f98,f94])).
% 1.68/0.61  fof(f57,plain,(
% 1.68/0.61    k1_xboole_0 = sK0 | sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | sK0 = k2_enumset1(sK2,sK2,sK2,sK2) | sK0 = k2_enumset1(sK1,sK1,sK1,sK2) | k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.68/0.61    inference(definition_unfolding,[],[f25,f55,f55,f54,f54])).
% 1.68/0.61  fof(f25,plain,(
% 1.68/0.61    k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1) | sK0 = k1_tarski(sK2) | sK0 = k2_tarski(sK1,sK2) | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.68/0.61    inference(cnf_transformation,[],[f18])).
% 1.68/0.61  % SZS output end Proof for theBenchmark
% 1.68/0.61  % (6498)------------------------------
% 1.68/0.61  % (6498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.61  % (6498)Termination reason: Refutation
% 1.68/0.61  
% 1.68/0.61  % (6498)Memory used [KB]: 11129
% 1.68/0.61  % (6498)Time elapsed: 0.173 s
% 1.68/0.61  % (6498)------------------------------
% 1.68/0.61  % (6498)------------------------------
% 1.68/0.62  % (6481)Success in time 0.244 s
%------------------------------------------------------------------------------
