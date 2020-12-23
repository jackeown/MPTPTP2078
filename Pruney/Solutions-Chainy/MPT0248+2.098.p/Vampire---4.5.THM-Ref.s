%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:04 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 613 expanded)
%              Number of leaves         :   31 ( 206 expanded)
%              Depth                    :   15
%              Number of atoms          :  473 (1486 expanded)
%              Number of equality atoms :  158 ( 941 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f508,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f133,f142,f149,f184,f208,f221,f247,f255,f262,f357,f390,f392,f500,f507])).

fof(f507,plain,
    ( ~ spl7_1
    | spl7_5
    | ~ spl7_17 ),
    inference(avatar_contradiction_clause,[],[f506])).

fof(f506,plain,
    ( $false
    | ~ spl7_1
    | spl7_5
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f505,f148])).

fof(f148,plain,
    ( sK2 != sK3
    | spl7_5 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl7_5
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f505,plain,
    ( sK2 = sK3
    | ~ spl7_1
    | ~ spl7_17 ),
    inference(forward_demodulation,[],[f503,f411])).

fof(f411,plain,
    ( sK2 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3))
    | ~ spl7_1 ),
    inference(backward_demodulation,[],[f97,f127])).

fof(f127,plain,
    ( sK2 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl7_1
  <=> sK2 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f97,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f49,f92,f91])).

fof(f91,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f90])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f75,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f75,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f92,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f90])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    k1_tarski(sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( k1_xboole_0 != sK3
      | sK2 != k1_tarski(sK1) )
    & ( sK3 != k1_tarski(sK1)
      | k1_xboole_0 != sK2 )
    & ( sK3 != k1_tarski(sK1)
      | sK2 != k1_tarski(sK1) )
    & k1_tarski(sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK3
        | sK2 != k1_tarski(sK1) )
      & ( sK3 != k1_tarski(sK1)
        | k1_xboole_0 != sK2 )
      & ( sK3 != k1_tarski(sK1)
        | sK2 != k1_tarski(sK1) )
      & k1_tarski(sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f503,plain,
    ( sK3 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3))
    | ~ spl7_17 ),
    inference(resolution,[],[f403,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f62,f91])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f403,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f402])).

fof(f402,plain,
    ( spl7_17
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f500,plain,
    ( ~ spl7_1
    | ~ spl7_13
    | spl7_17 ),
    inference(avatar_contradiction_clause,[],[f499])).

fof(f499,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_13
    | spl7_17 ),
    inference(subsumption_resolution,[],[f494,f404])).

fof(f404,plain,
    ( ~ r1_tarski(sK2,sK3)
    | spl7_17 ),
    inference(avatar_component_clause,[],[f402])).

fof(f494,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl7_1
    | ~ spl7_13 ),
    inference(resolution,[],[f429,f261])).

fof(f261,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl7_13
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f429,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK1,X2)
        | r1_tarski(sK2,X2) )
    | ~ spl7_1 ),
    inference(duplicate_literal_removal,[],[f423])).

fof(f423,plain,
    ( ! [X2] :
        ( r1_tarski(sK2,X2)
        | ~ r2_hidden(sK1,X2)
        | ~ r2_hidden(sK1,X2) )
    | ~ spl7_1 ),
    inference(superposition,[],[f113,f127])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f87,f90])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f392,plain,
    ( ~ spl7_7
    | spl7_1
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f185,f159,f126,f163])).

fof(f163,plain,
    ( spl7_7
  <=> r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f159,plain,
    ( spl7_6
  <=> r1_tarski(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f185,plain,
    ( sK2 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)
    | ~ spl7_6 ),
    inference(resolution,[],[f160,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f160,plain,
    ( r1_tarski(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f159])).

fof(f390,plain,
    ( spl7_7
    | ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f389])).

fof(f389,plain,
    ( $false
    | spl7_7
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f388,f254])).

fof(f254,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl7_12
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f388,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl7_7 ),
    inference(duplicate_literal_removal,[],[f387])).

fof(f387,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,sK2)
    | spl7_7 ),
    inference(resolution,[],[f165,f113])).

fof(f165,plain,
    ( ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f163])).

fof(f357,plain,
    ( ~ spl7_3
    | spl7_4
    | ~ spl7_13 ),
    inference(avatar_contradiction_clause,[],[f356])).

fof(f356,plain,
    ( $false
    | ~ spl7_3
    | spl7_4
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f352,f141])).

fof(f141,plain,
    ( sK3 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl7_4
  <=> sK3 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f352,plain,
    ( sK3 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl7_3
    | ~ spl7_13 ),
    inference(backward_demodulation,[],[f209,f337])).

fof(f337,plain,
    ( sK3 = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3))
    | ~ spl7_3
    | ~ spl7_13 ),
    inference(resolution,[],[f331,f100])).

fof(f331,plain,
    ( r1_tarski(k1_xboole_0,sK3)
    | ~ spl7_3
    | ~ spl7_13 ),
    inference(resolution,[],[f328,f261])).

fof(f328,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | r1_tarski(k1_xboole_0,X0) )
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f319])).

fof(f319,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ r2_hidden(sK1,X0)
        | r1_tarski(k1_xboole_0,X0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f113,f294])).

fof(f294,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),X2)
        | r1_tarski(k1_xboole_0,X2) )
    | ~ spl7_3 ),
    inference(superposition,[],[f110,f209])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f76,f91])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f209,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3))
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f97,f136])).

fof(f136,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl7_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f262,plain,
    ( spl7_2
    | spl7_13
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f257,f218,f259,f130])).

fof(f130,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f218,plain,
    ( spl7_11
  <=> sK1 = sK4(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f257,plain,
    ( r2_hidden(sK1,sK3)
    | k1_xboole_0 = sK3
    | ~ spl7_11 ),
    inference(superposition,[],[f56,f220])).

fof(f220,plain,
    ( sK1 = sK4(sK3)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f218])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f255,plain,
    ( spl7_3
    | spl7_12
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f250,f205,f252,f135])).

fof(f205,plain,
    ( spl7_10
  <=> sK1 = sK4(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f250,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = sK2
    | ~ spl7_10 ),
    inference(superposition,[],[f56,f207])).

fof(f207,plain,
    ( sK1 = sK4(sK2)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f205])).

fof(f247,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f243,f210])).

fof(f210,plain,
    ( k1_xboole_0 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | spl7_1
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f128,f136])).

fof(f128,plain,
    ( sK2 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f126])).

fof(f243,plain,
    ( k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f233,f240])).

fof(f240,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(resolution,[],[f100,f116])).

fof(f116,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f233,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f209,f131])).

fof(f131,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f130])).

fof(f221,plain,
    ( spl7_2
    | spl7_11 ),
    inference(avatar_split_clause,[],[f216,f218,f130])).

fof(f216,plain,
    ( sK1 = sK4(sK3)
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f202,f56])).

fof(f202,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK3)
      | sK1 = X5 ) ),
    inference(resolution,[],[f120,f189])).

fof(f189,plain,(
    ! [X0] :
      ( r2_hidden(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f181,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
              & ~ r2_hidden(sK6(X0,X1,X2),X1) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( r2_hidden(sK6(X0,X1,X2),X0)
            | r2_hidden(sK6(X0,X1,X2),X1)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X3,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X0)
            | r2_hidden(X3,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
            & ~ r2_hidden(sK6(X0,X1,X2),X1) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( r2_hidden(sK6(X0,X1,X2),X0)
          | r2_hidden(sK6(X0,X1,X2),X1)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X3,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X0)
              | r2_hidden(X3,X1)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f181,plain,(
    sP0(sK3,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f124,f97])).

fof(f124,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f83,f91])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f26])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f120,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f66,f92])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f208,plain,
    ( spl7_3
    | spl7_10 ),
    inference(avatar_split_clause,[],[f203,f205,f135])).

fof(f203,plain,
    ( sK1 = sK4(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f201,f56])).

fof(f201,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK2)
      | sK1 = X4 ) ),
    inference(resolution,[],[f120,f190])).

fof(f190,plain,(
    ! [X1] :
      ( r2_hidden(X1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f181,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f184,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | spl7_6 ),
    inference(subsumption_resolution,[],[f182,f161])).

fof(f161,plain,
    ( ~ r1_tarski(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl7_6 ),
    inference(avatar_component_clause,[],[f159])).

fof(f182,plain,(
    r1_tarski(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f99,f97])).

fof(f99,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f57,f91])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f149,plain,
    ( ~ spl7_5
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f144,f126,f146])).

fof(f144,plain,
    ( sK2 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | sK2 != sK3 ),
    inference(inner_rewriting,[],[f143])).

fof(f143,plain,
    ( sK3 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | sK2 != sK3 ),
    inference(inner_rewriting,[],[f96])).

fof(f96,plain,
    ( sK3 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | sK2 != k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f50,f92,f92])).

fof(f50,plain,
    ( sK3 != k1_tarski(sK1)
    | sK2 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f142,plain,
    ( ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f95,f139,f135])).

fof(f95,plain,
    ( sK3 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f51,f92])).

fof(f51,plain,
    ( sK3 != k1_tarski(sK1)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f29])).

fof(f133,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f94,f130,f126])).

fof(f94,plain,
    ( k1_xboole_0 != sK3
    | sK2 != k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f52,f92])).

fof(f52,plain,
    ( k1_xboole_0 != sK3
    | sK2 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:37:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.34/0.57  % (4912)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.57  % (4929)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.64/0.58  % (4921)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.64/0.59  % (4913)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.64/0.59  % (4928)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.64/0.59  % (4920)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.64/0.61  % (4912)Refutation found. Thanks to Tanya!
% 1.64/0.61  % SZS status Theorem for theBenchmark
% 1.64/0.61  % SZS output start Proof for theBenchmark
% 1.64/0.61  fof(f508,plain,(
% 1.64/0.61    $false),
% 1.64/0.61    inference(avatar_sat_refutation,[],[f133,f142,f149,f184,f208,f221,f247,f255,f262,f357,f390,f392,f500,f507])).
% 1.64/0.61  fof(f507,plain,(
% 1.64/0.61    ~spl7_1 | spl7_5 | ~spl7_17),
% 1.64/0.61    inference(avatar_contradiction_clause,[],[f506])).
% 1.64/0.61  fof(f506,plain,(
% 1.64/0.61    $false | (~spl7_1 | spl7_5 | ~spl7_17)),
% 1.64/0.61    inference(subsumption_resolution,[],[f505,f148])).
% 1.64/0.61  fof(f148,plain,(
% 1.64/0.61    sK2 != sK3 | spl7_5),
% 1.64/0.61    inference(avatar_component_clause,[],[f146])).
% 1.64/0.61  fof(f146,plain,(
% 1.64/0.61    spl7_5 <=> sK2 = sK3),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.64/0.61  fof(f505,plain,(
% 1.64/0.61    sK2 = sK3 | (~spl7_1 | ~spl7_17)),
% 1.64/0.61    inference(forward_demodulation,[],[f503,f411])).
% 1.64/0.61  fof(f411,plain,(
% 1.64/0.61    sK2 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3)) | ~spl7_1),
% 1.64/0.61    inference(backward_demodulation,[],[f97,f127])).
% 1.64/0.61  fof(f127,plain,(
% 1.64/0.61    sK2 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | ~spl7_1),
% 1.64/0.61    inference(avatar_component_clause,[],[f126])).
% 1.64/0.61  fof(f126,plain,(
% 1.64/0.61    spl7_1 <=> sK2 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.64/0.61  fof(f97,plain,(
% 1.64/0.61    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3))),
% 1.64/0.61    inference(definition_unfolding,[],[f49,f92,f91])).
% 1.64/0.61  fof(f91,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.64/0.61    inference(definition_unfolding,[],[f58,f90])).
% 1.64/0.61  fof(f90,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.64/0.61    inference(definition_unfolding,[],[f59,f89])).
% 1.64/0.61  fof(f89,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.64/0.61    inference(definition_unfolding,[],[f75,f88])).
% 1.64/0.61  fof(f88,plain,(
% 1.64/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f15])).
% 1.64/0.61  fof(f15,axiom,(
% 1.64/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.64/0.61  fof(f75,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f14])).
% 1.64/0.61  fof(f14,axiom,(
% 1.64/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.64/0.61  fof(f59,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f13])).
% 1.64/0.61  fof(f13,axiom,(
% 1.64/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.64/0.61  fof(f58,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.64/0.61    inference(cnf_transformation,[],[f17])).
% 1.64/0.61  fof(f17,axiom,(
% 1.64/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.64/0.61  fof(f92,plain,(
% 1.64/0.61    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.64/0.61    inference(definition_unfolding,[],[f55,f90])).
% 1.64/0.61  fof(f55,plain,(
% 1.64/0.61    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f12])).
% 1.64/0.61  fof(f12,axiom,(
% 1.64/0.61    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.64/0.61  fof(f49,plain,(
% 1.64/0.61    k1_tarski(sK1) = k2_xboole_0(sK2,sK3)),
% 1.64/0.61    inference(cnf_transformation,[],[f29])).
% 1.64/0.61  fof(f29,plain,(
% 1.64/0.61    (k1_xboole_0 != sK3 | sK2 != k1_tarski(sK1)) & (sK3 != k1_tarski(sK1) | k1_xboole_0 != sK2) & (sK3 != k1_tarski(sK1) | sK2 != k1_tarski(sK1)) & k1_tarski(sK1) = k2_xboole_0(sK2,sK3)),
% 1.64/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f28])).
% 1.64/0.61  fof(f28,plain,(
% 1.64/0.61    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK3 | sK2 != k1_tarski(sK1)) & (sK3 != k1_tarski(sK1) | k1_xboole_0 != sK2) & (sK3 != k1_tarski(sK1) | sK2 != k1_tarski(sK1)) & k1_tarski(sK1) = k2_xboole_0(sK2,sK3))),
% 1.64/0.61    introduced(choice_axiom,[])).
% 1.64/0.61  fof(f22,plain,(
% 1.64/0.61    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.64/0.61    inference(ennf_transformation,[],[f21])).
% 1.64/0.61  fof(f21,negated_conjecture,(
% 1.64/0.61    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.64/0.61    inference(negated_conjecture,[],[f20])).
% 1.64/0.61  fof(f20,conjecture,(
% 1.64/0.61    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.64/0.61  fof(f503,plain,(
% 1.64/0.61    sK3 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3)) | ~spl7_17),
% 1.64/0.61    inference(resolution,[],[f403,f100])).
% 1.64/0.61  fof(f100,plain,(
% 1.64/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1) )),
% 1.64/0.61    inference(definition_unfolding,[],[f62,f91])).
% 1.64/0.61  fof(f62,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f24])).
% 1.64/0.61  fof(f24,plain,(
% 1.64/0.61    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.64/0.61    inference(ennf_transformation,[],[f6])).
% 1.64/0.61  fof(f6,axiom,(
% 1.64/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.64/0.61  fof(f403,plain,(
% 1.64/0.61    r1_tarski(sK2,sK3) | ~spl7_17),
% 1.64/0.61    inference(avatar_component_clause,[],[f402])).
% 1.64/0.61  fof(f402,plain,(
% 1.64/0.61    spl7_17 <=> r1_tarski(sK2,sK3)),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 1.64/0.61  fof(f500,plain,(
% 1.64/0.61    ~spl7_1 | ~spl7_13 | spl7_17),
% 1.64/0.61    inference(avatar_contradiction_clause,[],[f499])).
% 1.64/0.61  fof(f499,plain,(
% 1.64/0.61    $false | (~spl7_1 | ~spl7_13 | spl7_17)),
% 1.64/0.61    inference(subsumption_resolution,[],[f494,f404])).
% 1.64/0.61  fof(f404,plain,(
% 1.64/0.61    ~r1_tarski(sK2,sK3) | spl7_17),
% 1.64/0.61    inference(avatar_component_clause,[],[f402])).
% 1.64/0.61  fof(f494,plain,(
% 1.64/0.61    r1_tarski(sK2,sK3) | (~spl7_1 | ~spl7_13)),
% 1.64/0.61    inference(resolution,[],[f429,f261])).
% 1.64/0.61  fof(f261,plain,(
% 1.64/0.61    r2_hidden(sK1,sK3) | ~spl7_13),
% 1.64/0.61    inference(avatar_component_clause,[],[f259])).
% 1.64/0.61  fof(f259,plain,(
% 1.64/0.61    spl7_13 <=> r2_hidden(sK1,sK3)),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.64/0.61  fof(f429,plain,(
% 1.64/0.61    ( ! [X2] : (~r2_hidden(sK1,X2) | r1_tarski(sK2,X2)) ) | ~spl7_1),
% 1.64/0.61    inference(duplicate_literal_removal,[],[f423])).
% 1.64/0.61  fof(f423,plain,(
% 1.64/0.61    ( ! [X2] : (r1_tarski(sK2,X2) | ~r2_hidden(sK1,X2) | ~r2_hidden(sK1,X2)) ) | ~spl7_1),
% 1.64/0.61    inference(superposition,[],[f113,f127])).
% 1.64/0.61  fof(f113,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.64/0.61    inference(definition_unfolding,[],[f87,f90])).
% 1.64/0.61  fof(f87,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f48])).
% 1.64/0.61  fof(f48,plain,(
% 1.64/0.61    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.64/0.61    inference(flattening,[],[f47])).
% 1.64/0.61  fof(f47,plain,(
% 1.64/0.61    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.64/0.61    inference(nnf_transformation,[],[f19])).
% 1.64/0.61  fof(f19,axiom,(
% 1.64/0.61    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.64/0.61  fof(f392,plain,(
% 1.64/0.61    ~spl7_7 | spl7_1 | ~spl7_6),
% 1.64/0.61    inference(avatar_split_clause,[],[f185,f159,f126,f163])).
% 1.64/0.61  fof(f163,plain,(
% 1.64/0.61    spl7_7 <=> r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.64/0.61  fof(f159,plain,(
% 1.64/0.61    spl7_6 <=> r1_tarski(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.64/0.61  fof(f185,plain,(
% 1.64/0.61    sK2 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | ~r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2) | ~spl7_6),
% 1.64/0.61    inference(resolution,[],[f160,f65])).
% 1.64/0.61  fof(f65,plain,(
% 1.64/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f33])).
% 1.64/0.61  fof(f33,plain,(
% 1.64/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.64/0.61    inference(flattening,[],[f32])).
% 1.64/0.61  fof(f32,plain,(
% 1.64/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.64/0.61    inference(nnf_transformation,[],[f3])).
% 1.64/0.61  fof(f3,axiom,(
% 1.64/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.64/0.61  fof(f160,plain,(
% 1.64/0.61    r1_tarski(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl7_6),
% 1.64/0.61    inference(avatar_component_clause,[],[f159])).
% 1.64/0.61  fof(f390,plain,(
% 1.64/0.61    spl7_7 | ~spl7_12),
% 1.64/0.61    inference(avatar_contradiction_clause,[],[f389])).
% 1.64/0.61  fof(f389,plain,(
% 1.64/0.61    $false | (spl7_7 | ~spl7_12)),
% 1.64/0.61    inference(subsumption_resolution,[],[f388,f254])).
% 1.64/0.61  fof(f254,plain,(
% 1.64/0.61    r2_hidden(sK1,sK2) | ~spl7_12),
% 1.64/0.61    inference(avatar_component_clause,[],[f252])).
% 1.64/0.61  fof(f252,plain,(
% 1.64/0.61    spl7_12 <=> r2_hidden(sK1,sK2)),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.64/0.61  fof(f388,plain,(
% 1.64/0.61    ~r2_hidden(sK1,sK2) | spl7_7),
% 1.64/0.61    inference(duplicate_literal_removal,[],[f387])).
% 1.64/0.61  fof(f387,plain,(
% 1.64/0.61    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK1,sK2) | spl7_7),
% 1.64/0.61    inference(resolution,[],[f165,f113])).
% 1.64/0.61  fof(f165,plain,(
% 1.64/0.61    ~r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2) | spl7_7),
% 1.64/0.61    inference(avatar_component_clause,[],[f163])).
% 1.64/0.61  fof(f357,plain,(
% 1.64/0.61    ~spl7_3 | spl7_4 | ~spl7_13),
% 1.64/0.61    inference(avatar_contradiction_clause,[],[f356])).
% 1.64/0.61  fof(f356,plain,(
% 1.64/0.61    $false | (~spl7_3 | spl7_4 | ~spl7_13)),
% 1.64/0.61    inference(subsumption_resolution,[],[f352,f141])).
% 1.64/0.61  fof(f141,plain,(
% 1.64/0.61    sK3 != k3_enumset1(sK1,sK1,sK1,sK1,sK1) | spl7_4),
% 1.64/0.61    inference(avatar_component_clause,[],[f139])).
% 1.64/0.61  fof(f139,plain,(
% 1.64/0.61    spl7_4 <=> sK3 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.64/0.61  fof(f352,plain,(
% 1.64/0.61    sK3 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | (~spl7_3 | ~spl7_13)),
% 1.64/0.61    inference(backward_demodulation,[],[f209,f337])).
% 1.64/0.61  fof(f337,plain,(
% 1.64/0.61    sK3 = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3)) | (~spl7_3 | ~spl7_13)),
% 1.64/0.61    inference(resolution,[],[f331,f100])).
% 1.64/0.61  fof(f331,plain,(
% 1.64/0.61    r1_tarski(k1_xboole_0,sK3) | (~spl7_3 | ~spl7_13)),
% 1.64/0.61    inference(resolution,[],[f328,f261])).
% 1.64/0.61  fof(f328,plain,(
% 1.64/0.61    ( ! [X0] : (~r2_hidden(sK1,X0) | r1_tarski(k1_xboole_0,X0)) ) | ~spl7_3),
% 1.64/0.61    inference(duplicate_literal_removal,[],[f319])).
% 1.64/0.61  fof(f319,plain,(
% 1.64/0.61    ( ! [X0] : (~r2_hidden(sK1,X0) | ~r2_hidden(sK1,X0) | r1_tarski(k1_xboole_0,X0)) ) | ~spl7_3),
% 1.64/0.61    inference(resolution,[],[f113,f294])).
% 1.64/0.61  fof(f294,plain,(
% 1.64/0.61    ( ! [X2] : (~r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),X2) | r1_tarski(k1_xboole_0,X2)) ) | ~spl7_3),
% 1.64/0.61    inference(superposition,[],[f110,f209])).
% 1.64/0.61  fof(f110,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X2) | r1_tarski(X0,X2)) )),
% 1.64/0.61    inference(definition_unfolding,[],[f76,f91])).
% 1.64/0.61  fof(f76,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f25])).
% 1.64/0.61  fof(f25,plain,(
% 1.64/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.64/0.61    inference(ennf_transformation,[],[f5])).
% 1.64/0.61  fof(f5,axiom,(
% 1.64/0.61    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.64/0.61  fof(f209,plain,(
% 1.64/0.61    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3)) | ~spl7_3),
% 1.64/0.61    inference(backward_demodulation,[],[f97,f136])).
% 1.64/0.61  fof(f136,plain,(
% 1.64/0.61    k1_xboole_0 = sK2 | ~spl7_3),
% 1.64/0.61    inference(avatar_component_clause,[],[f135])).
% 1.64/0.61  fof(f135,plain,(
% 1.64/0.61    spl7_3 <=> k1_xboole_0 = sK2),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.64/0.61  fof(f262,plain,(
% 1.64/0.61    spl7_2 | spl7_13 | ~spl7_11),
% 1.64/0.61    inference(avatar_split_clause,[],[f257,f218,f259,f130])).
% 1.64/0.61  fof(f130,plain,(
% 1.64/0.61    spl7_2 <=> k1_xboole_0 = sK3),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.64/0.61  fof(f218,plain,(
% 1.64/0.61    spl7_11 <=> sK1 = sK4(sK3)),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.64/0.61  fof(f257,plain,(
% 1.64/0.61    r2_hidden(sK1,sK3) | k1_xboole_0 = sK3 | ~spl7_11),
% 1.64/0.61    inference(superposition,[],[f56,f220])).
% 1.64/0.61  fof(f220,plain,(
% 1.64/0.61    sK1 = sK4(sK3) | ~spl7_11),
% 1.64/0.61    inference(avatar_component_clause,[],[f218])).
% 1.64/0.61  fof(f56,plain,(
% 1.64/0.61    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.64/0.61    inference(cnf_transformation,[],[f31])).
% 1.64/0.61  fof(f31,plain,(
% 1.64/0.61    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 1.64/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f30])).
% 1.64/0.61  fof(f30,plain,(
% 1.64/0.61    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.64/0.61    introduced(choice_axiom,[])).
% 1.64/0.61  fof(f23,plain,(
% 1.64/0.61    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.64/0.61    inference(ennf_transformation,[],[f2])).
% 1.64/0.61  fof(f2,axiom,(
% 1.64/0.61    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.64/0.61  fof(f255,plain,(
% 1.64/0.61    spl7_3 | spl7_12 | ~spl7_10),
% 1.64/0.61    inference(avatar_split_clause,[],[f250,f205,f252,f135])).
% 1.64/0.61  fof(f205,plain,(
% 1.64/0.61    spl7_10 <=> sK1 = sK4(sK2)),
% 1.64/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.64/0.61  fof(f250,plain,(
% 1.64/0.61    r2_hidden(sK1,sK2) | k1_xboole_0 = sK2 | ~spl7_10),
% 1.64/0.61    inference(superposition,[],[f56,f207])).
% 1.64/0.61  fof(f207,plain,(
% 1.64/0.61    sK1 = sK4(sK2) | ~spl7_10),
% 1.64/0.61    inference(avatar_component_clause,[],[f205])).
% 1.64/0.61  fof(f247,plain,(
% 1.64/0.61    spl7_1 | ~spl7_2 | ~spl7_3),
% 1.64/0.61    inference(avatar_contradiction_clause,[],[f246])).
% 1.64/0.61  fof(f246,plain,(
% 1.64/0.61    $false | (spl7_1 | ~spl7_2 | ~spl7_3)),
% 1.64/0.61    inference(subsumption_resolution,[],[f243,f210])).
% 1.64/0.61  fof(f210,plain,(
% 1.64/0.61    k1_xboole_0 != k3_enumset1(sK1,sK1,sK1,sK1,sK1) | (spl7_1 | ~spl7_3)),
% 1.64/0.61    inference(backward_demodulation,[],[f128,f136])).
% 1.64/0.61  fof(f128,plain,(
% 1.64/0.61    sK2 != k3_enumset1(sK1,sK1,sK1,sK1,sK1) | spl7_1),
% 1.64/0.61    inference(avatar_component_clause,[],[f126])).
% 1.64/0.61  fof(f243,plain,(
% 1.64/0.61    k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | (~spl7_2 | ~spl7_3)),
% 1.64/0.61    inference(backward_demodulation,[],[f233,f240])).
% 1.64/0.61  fof(f240,plain,(
% 1.64/0.61    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0) )),
% 1.64/0.61    inference(resolution,[],[f100,f116])).
% 1.64/0.61  fof(f116,plain,(
% 1.64/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.64/0.61    inference(equality_resolution,[],[f64])).
% 1.64/0.61  fof(f64,plain,(
% 1.64/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.64/0.61    inference(cnf_transformation,[],[f33])).
% 1.64/0.61  fof(f233,plain,(
% 1.64/0.61    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | (~spl7_2 | ~spl7_3)),
% 1.64/0.61    inference(forward_demodulation,[],[f209,f131])).
% 1.64/0.61  fof(f131,plain,(
% 1.64/0.61    k1_xboole_0 = sK3 | ~spl7_2),
% 1.64/0.61    inference(avatar_component_clause,[],[f130])).
% 1.64/0.61  fof(f221,plain,(
% 1.64/0.61    spl7_2 | spl7_11),
% 1.64/0.61    inference(avatar_split_clause,[],[f216,f218,f130])).
% 1.64/0.61  fof(f216,plain,(
% 1.64/0.61    sK1 = sK4(sK3) | k1_xboole_0 = sK3),
% 1.64/0.61    inference(resolution,[],[f202,f56])).
% 1.64/0.61  fof(f202,plain,(
% 1.64/0.61    ( ! [X5] : (~r2_hidden(X5,sK3) | sK1 = X5) )),
% 1.64/0.61    inference(resolution,[],[f120,f189])).
% 1.64/0.61  fof(f189,plain,(
% 1.64/0.61    ( ! [X0] : (r2_hidden(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~r2_hidden(X0,sK3)) )),
% 1.64/0.61    inference(resolution,[],[f181,f79])).
% 1.64/0.61  fof(f79,plain,(
% 1.64/0.61    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X0) | r2_hidden(X4,X2)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f45])).
% 1.64/0.61  fof(f45,plain,(
% 1.64/0.61    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((~r2_hidden(sK6(X0,X1,X2),X0) & ~r2_hidden(sK6(X0,X1,X2),X1)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.64/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).
% 1.64/0.62  fof(f44,plain,(
% 1.64/0.62    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2))) => (((~r2_hidden(sK6(X0,X1,X2),X0) & ~r2_hidden(sK6(X0,X1,X2),X1)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.64/0.62    introduced(choice_axiom,[])).
% 1.64/0.62  fof(f43,plain,(
% 1.64/0.62    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.64/0.62    inference(rectify,[],[f42])).
% 1.64/0.62  fof(f42,plain,(
% 1.64/0.62    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.64/0.62    inference(flattening,[],[f41])).
% 1.64/0.62  fof(f41,plain,(
% 1.64/0.62    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.64/0.62    inference(nnf_transformation,[],[f26])).
% 1.64/0.62  fof(f26,plain,(
% 1.64/0.62    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.64/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.64/0.62  fof(f181,plain,(
% 1.64/0.62    sP0(sK3,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 1.64/0.62    inference(superposition,[],[f124,f97])).
% 1.64/0.62  fof(f124,plain,(
% 1.64/0.62    ( ! [X0,X1] : (sP0(X1,X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.64/0.62    inference(equality_resolution,[],[f112])).
% 1.64/0.62  fof(f112,plain,(
% 1.64/0.62    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 1.64/0.62    inference(definition_unfolding,[],[f83,f91])).
% 1.64/0.62  fof(f83,plain,(
% 1.64/0.62    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.64/0.62    inference(cnf_transformation,[],[f46])).
% 1.64/0.62  fof(f46,plain,(
% 1.64/0.62    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2))),
% 1.64/0.62    inference(nnf_transformation,[],[f27])).
% 1.64/0.62  fof(f27,plain,(
% 1.64/0.62    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.64/0.62    inference(definition_folding,[],[f1,f26])).
% 1.64/0.62  fof(f1,axiom,(
% 1.64/0.62    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.64/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.64/0.62  fof(f120,plain,(
% 1.64/0.62    ( ! [X0,X3] : (~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X3) )),
% 1.64/0.62    inference(equality_resolution,[],[f104])).
% 1.64/0.62  fof(f104,plain,(
% 1.64/0.62    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.64/0.62    inference(definition_unfolding,[],[f66,f92])).
% 1.64/0.62  fof(f66,plain,(
% 1.64/0.62    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.64/0.62    inference(cnf_transformation,[],[f37])).
% 1.64/0.62  fof(f37,plain,(
% 1.64/0.62    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.64/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).
% 1.64/0.62  fof(f36,plain,(
% 1.64/0.62    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.64/0.62    introduced(choice_axiom,[])).
% 1.64/0.62  fof(f35,plain,(
% 1.64/0.62    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.64/0.62    inference(rectify,[],[f34])).
% 1.64/0.62  fof(f34,plain,(
% 1.64/0.62    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.64/0.62    inference(nnf_transformation,[],[f11])).
% 1.64/0.62  fof(f11,axiom,(
% 1.64/0.62    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.64/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.64/0.62  fof(f208,plain,(
% 1.64/0.62    spl7_3 | spl7_10),
% 1.64/0.62    inference(avatar_split_clause,[],[f203,f205,f135])).
% 1.64/0.62  fof(f203,plain,(
% 1.64/0.62    sK1 = sK4(sK2) | k1_xboole_0 = sK2),
% 1.64/0.62    inference(resolution,[],[f201,f56])).
% 1.64/0.62  fof(f201,plain,(
% 1.64/0.62    ( ! [X4] : (~r2_hidden(X4,sK2) | sK1 = X4) )),
% 1.64/0.62    inference(resolution,[],[f120,f190])).
% 1.64/0.62  fof(f190,plain,(
% 1.64/0.62    ( ! [X1] : (r2_hidden(X1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~r2_hidden(X1,sK2)) )),
% 1.64/0.62    inference(resolution,[],[f181,f78])).
% 1.64/0.62  fof(f78,plain,(
% 1.64/0.62    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X1) | r2_hidden(X4,X2)) )),
% 1.64/0.62    inference(cnf_transformation,[],[f45])).
% 1.64/0.62  fof(f184,plain,(
% 1.64/0.62    spl7_6),
% 1.64/0.62    inference(avatar_contradiction_clause,[],[f183])).
% 1.64/0.62  fof(f183,plain,(
% 1.64/0.62    $false | spl7_6),
% 1.64/0.62    inference(subsumption_resolution,[],[f182,f161])).
% 1.64/0.62  fof(f161,plain,(
% 1.64/0.62    ~r1_tarski(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | spl7_6),
% 1.64/0.62    inference(avatar_component_clause,[],[f159])).
% 1.64/0.62  fof(f182,plain,(
% 1.64/0.62    r1_tarski(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 1.64/0.62    inference(superposition,[],[f99,f97])).
% 1.64/0.62  fof(f99,plain,(
% 1.64/0.62    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.64/0.62    inference(definition_unfolding,[],[f57,f91])).
% 1.64/0.62  fof(f57,plain,(
% 1.64/0.62    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.64/0.62    inference(cnf_transformation,[],[f10])).
% 1.64/0.62  fof(f10,axiom,(
% 1.64/0.62    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.64/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.64/0.62  fof(f149,plain,(
% 1.64/0.62    ~spl7_5 | ~spl7_1),
% 1.64/0.62    inference(avatar_split_clause,[],[f144,f126,f146])).
% 1.64/0.62  fof(f144,plain,(
% 1.64/0.62    sK2 != k3_enumset1(sK1,sK1,sK1,sK1,sK1) | sK2 != sK3),
% 1.64/0.62    inference(inner_rewriting,[],[f143])).
% 1.64/0.62  fof(f143,plain,(
% 1.64/0.62    sK3 != k3_enumset1(sK1,sK1,sK1,sK1,sK1) | sK2 != sK3),
% 1.64/0.62    inference(inner_rewriting,[],[f96])).
% 1.64/0.62  fof(f96,plain,(
% 1.64/0.62    sK3 != k3_enumset1(sK1,sK1,sK1,sK1,sK1) | sK2 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 1.64/0.62    inference(definition_unfolding,[],[f50,f92,f92])).
% 1.64/0.62  fof(f50,plain,(
% 1.64/0.62    sK3 != k1_tarski(sK1) | sK2 != k1_tarski(sK1)),
% 1.64/0.62    inference(cnf_transformation,[],[f29])).
% 1.64/0.62  fof(f142,plain,(
% 1.64/0.62    ~spl7_3 | ~spl7_4),
% 1.64/0.62    inference(avatar_split_clause,[],[f95,f139,f135])).
% 1.64/0.62  fof(f95,plain,(
% 1.64/0.62    sK3 != k3_enumset1(sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 != sK2),
% 1.64/0.62    inference(definition_unfolding,[],[f51,f92])).
% 1.64/0.62  fof(f51,plain,(
% 1.64/0.62    sK3 != k1_tarski(sK1) | k1_xboole_0 != sK2),
% 1.64/0.62    inference(cnf_transformation,[],[f29])).
% 1.64/0.62  fof(f133,plain,(
% 1.64/0.62    ~spl7_1 | ~spl7_2),
% 1.64/0.62    inference(avatar_split_clause,[],[f94,f130,f126])).
% 1.64/0.62  fof(f94,plain,(
% 1.64/0.62    k1_xboole_0 != sK3 | sK2 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 1.64/0.62    inference(definition_unfolding,[],[f52,f92])).
% 1.64/0.62  fof(f52,plain,(
% 1.64/0.62    k1_xboole_0 != sK3 | sK2 != k1_tarski(sK1)),
% 1.64/0.62    inference(cnf_transformation,[],[f29])).
% 1.64/0.62  % SZS output end Proof for theBenchmark
% 1.64/0.62  % (4912)------------------------------
% 1.64/0.62  % (4912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.62  % (4912)Termination reason: Refutation
% 1.64/0.62  
% 1.64/0.62  % (4912)Memory used [KB]: 10874
% 1.64/0.62  % (4912)Time elapsed: 0.182 s
% 1.64/0.62  % (4912)------------------------------
% 1.64/0.62  % (4912)------------------------------
% 1.64/0.62  % (4905)Success in time 0.256 s
%------------------------------------------------------------------------------
