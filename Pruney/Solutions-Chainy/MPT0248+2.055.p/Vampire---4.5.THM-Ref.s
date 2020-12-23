%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 352 expanded)
%              Number of leaves         :   35 ( 129 expanded)
%              Depth                    :   11
%              Number of atoms          :  352 ( 822 expanded)
%              Number of equality atoms :  107 ( 388 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f792,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f97,f102,f118,f132,f166,f199,f261,f407,f411,f413,f450,f507,f601,f787,f790,f791])).

fof(f791,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK1 = sK2 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f790,plain,
    ( ~ spl5_20
    | spl5_29 ),
    inference(avatar_split_clause,[],[f624,f598,f370])).

fof(f370,plain,
    ( spl5_20
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f598,plain,
    ( spl5_29
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f624,plain,
    ( ~ v1_xboole_0(sK2)
    | spl5_29 ),
    inference(resolution,[],[f603,f78])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f603,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ v1_xboole_0(X0) )
    | spl5_29 ),
    inference(superposition,[],[f600,f45])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f600,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl5_29 ),
    inference(avatar_component_clause,[],[f598])).

fof(f787,plain,
    ( ~ spl5_5
    | spl5_12
    | spl5_20 ),
    inference(avatar_contradiction_clause,[],[f784])).

fof(f784,plain,
    ( $false
    | ~ spl5_5
    | spl5_12
    | spl5_20 ),
    inference(unit_resulting_resolution,[],[f371,f260,f78,f778])).

fof(f778,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | v1_xboole_0(X0)
        | r2_hidden(sK0,X0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f398,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f67])).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f61,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f398,plain,
    ( ! [X8] :
        ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X8)
        | v1_xboole_0(X8)
        | ~ r1_tarski(X8,sK2) )
    | ~ spl5_5 ),
    inference(resolution,[],[f140,f204])).

fof(f204,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r1_tarski(X0,sK2) )
    | ~ spl5_5 ),
    inference(superposition,[],[f73,f101])).

fof(f101,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl5_5
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f62,f65])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f140,plain,(
    ! [X10,X9] :
      ( ~ r1_tarski(X10,X9)
      | ~ r1_xboole_0(X9,X10)
      | v1_xboole_0(X10) ) ),
    inference(superposition,[],[f109,f105])).

fof(f105,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f58,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f109,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f60,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f260,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl5_12
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f371,plain,
    ( ~ v1_xboole_0(sK2)
    | spl5_20 ),
    inference(avatar_component_clause,[],[f370])).

fof(f601,plain,
    ( ~ spl5_29
    | ~ spl5_3
    | spl5_11 ),
    inference(avatar_split_clause,[],[f527,f196,f90,f598])).

fof(f90,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f196,plain,
    ( spl5_11
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f527,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl5_3
    | spl5_11 ),
    inference(superposition,[],[f198,f91])).

fof(f91,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f198,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f196])).

fof(f507,plain,
    ( ~ spl5_1
    | ~ spl5_25
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f483,f81,f504,f81])).

fof(f504,plain,
    ( spl5_25
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f81,plain,
    ( spl5_1
  <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f483,plain,
    ( sK1 != sK2
    | sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f70,f82])).

fof(f82,plain,
    ( sK1 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f70,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK1 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f42,f67,f67])).

fof(f42,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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

fof(f450,plain,
    ( spl5_3
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f449])).

fof(f449,plain,
    ( $false
    | spl5_3
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f92,f186,f45])).

fof(f186,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl5_9
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f92,plain,
    ( k1_xboole_0 != sK1
    | spl5_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f413,plain,
    ( spl5_2
    | ~ spl5_20 ),
    inference(avatar_contradiction_clause,[],[f412])).

fof(f412,plain,
    ( $false
    | spl5_2
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f372,f87,f45])).

fof(f87,plain,
    ( k1_xboole_0 != sK2
    | spl5_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f372,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f370])).

fof(f411,plain,
    ( spl5_8
    | spl5_22 ),
    inference(avatar_contradiction_clause,[],[f408])).

fof(f408,plain,
    ( $false
    | spl5_8
    | spl5_22 ),
    inference(unit_resulting_resolution,[],[f165,f406,f77])).

fof(f406,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | spl5_22 ),
    inference(avatar_component_clause,[],[f404])).

fof(f404,plain,
    ( spl5_22
  <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f165,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl5_8
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f407,plain,
    ( spl5_9
    | ~ spl5_22
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f401,f115,f404,f184])).

fof(f115,plain,
    ( spl5_6
  <=> r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f401,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | v1_xboole_0(sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f140,f117])).

fof(f117,plain,
    ( r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f261,plain,
    ( ~ spl5_12
    | spl5_11
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f255,f115,f99,f196,f258])).

fof(f255,plain,
    ( r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(resolution,[],[f229,f78])).

fof(f229,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK2)
        | r1_tarski(sK1,X1)
        | ~ r2_hidden(sK0,X1) )
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(superposition,[],[f117,f221])).

fof(f221,plain,
    ( ! [X0] :
        ( k2_enumset1(sK0,sK0,sK0,sK0) = X0
        | ~ r1_tarski(X0,sK2)
        | ~ r2_hidden(sK0,X0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f207,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f67])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f207,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),X1)
        | k2_enumset1(sK0,sK0,sK0,sK0) = X1
        | ~ r1_tarski(X1,sK2) )
    | ~ spl5_5 ),
    inference(resolution,[],[f204,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f199,plain,
    ( ~ spl5_11
    | spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f192,f99,f94,f196])).

fof(f94,plain,
    ( spl5_4
  <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f192,plain,
    ( sK2 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ r1_tarski(sK1,sK2)
    | ~ spl5_5 ),
    inference(superposition,[],[f72,f101])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f66])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f166,plain,
    ( ~ spl5_8
    | spl5_7 ),
    inference(avatar_split_clause,[],[f160,f129,f163])).

fof(f129,plain,
    ( spl5_7
  <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f160,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl5_7 ),
    inference(resolution,[],[f75,f131])).

fof(f131,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f132,plain,
    ( ~ spl5_7
    | spl5_1
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f127,f115,f81,f129])).

fof(f127,plain,
    ( sK1 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f48,f117])).

fof(f118,plain,
    ( spl5_6
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f113,f99,f115])).

fof(f113,plain,
    ( r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl5_5 ),
    inference(superposition,[],[f74,f101])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f51,f66])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f102,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f71,f99])).

fof(f71,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f41,f67,f66])).

fof(f41,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f97,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f69,f94,f90])).

fof(f69,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f43,f67])).

fof(f43,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f88,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f68,f85,f81])).

fof(f68,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f44,f67])).

fof(f44,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:48:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (30866)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (30859)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (30847)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (30853)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (30868)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (30846)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (30845)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (30860)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (30848)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (30859)Refutation not found, incomplete strategy% (30859)------------------------------
% 0.21/0.54  % (30859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (30859)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (30859)Memory used [KB]: 1791
% 0.21/0.54  % (30859)Time elapsed: 0.116 s
% 0.21/0.54  % (30859)------------------------------
% 0.21/0.54  % (30859)------------------------------
% 0.21/0.54  % (30843)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (30852)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (30851)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (30870)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (30872)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (30844)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (30873)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (30844)Refutation not found, incomplete strategy% (30844)------------------------------
% 0.21/0.54  % (30844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (30844)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (30844)Memory used [KB]: 1663
% 0.21/0.54  % (30844)Time elapsed: 0.133 s
% 0.21/0.54  % (30844)------------------------------
% 0.21/0.54  % (30844)------------------------------
% 0.21/0.54  % (30871)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (30849)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (30862)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (30863)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (30854)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (30865)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (30869)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (30867)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (30864)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.56  % (30856)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (30874)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (30874)Refutation not found, incomplete strategy% (30874)------------------------------
% 0.21/0.56  % (30874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (30874)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (30874)Memory used [KB]: 1663
% 0.21/0.56  % (30874)Time elapsed: 0.149 s
% 0.21/0.56  % (30874)------------------------------
% 0.21/0.56  % (30874)------------------------------
% 0.21/0.56  % (30855)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (30863)Refutation not found, incomplete strategy% (30863)------------------------------
% 0.21/0.56  % (30863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (30863)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (30863)Memory used [KB]: 1791
% 0.21/0.56  % (30863)Time elapsed: 0.152 s
% 0.21/0.56  % (30863)------------------------------
% 0.21/0.56  % (30863)------------------------------
% 0.21/0.56  % (30858)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (30861)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.56  % (30861)Refutation not found, incomplete strategy% (30861)------------------------------
% 0.21/0.56  % (30861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (30861)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (30861)Memory used [KB]: 10618
% 0.21/0.57  % (30861)Time elapsed: 0.159 s
% 0.21/0.57  % (30861)------------------------------
% 0.21/0.57  % (30861)------------------------------
% 0.21/0.57  % (30862)Refutation not found, incomplete strategy% (30862)------------------------------
% 0.21/0.57  % (30862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (30862)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (30862)Memory used [KB]: 1791
% 0.21/0.57  % (30862)Time elapsed: 0.166 s
% 0.21/0.57  % (30862)------------------------------
% 0.21/0.57  % (30862)------------------------------
% 0.21/0.57  % (30869)Refutation not found, incomplete strategy% (30869)------------------------------
% 0.21/0.57  % (30869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (30869)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (30869)Memory used [KB]: 10746
% 0.21/0.57  % (30869)Time elapsed: 0.151 s
% 0.21/0.57  % (30869)------------------------------
% 0.21/0.57  % (30869)------------------------------
% 0.21/0.59  % (30868)Refutation found. Thanks to Tanya!
% 0.21/0.59  % SZS status Theorem for theBenchmark
% 0.21/0.59  % SZS output start Proof for theBenchmark
% 0.21/0.59  fof(f792,plain,(
% 0.21/0.59    $false),
% 0.21/0.59    inference(avatar_sat_refutation,[],[f88,f97,f102,f118,f132,f166,f199,f261,f407,f411,f413,f450,f507,f601,f787,f790,f791])).
% 0.21/0.59  fof(f791,plain,(
% 0.21/0.59    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | sK1 = sK2),
% 0.21/0.59    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.59  fof(f790,plain,(
% 0.21/0.59    ~spl5_20 | spl5_29),
% 0.21/0.59    inference(avatar_split_clause,[],[f624,f598,f370])).
% 0.21/0.59  fof(f370,plain,(
% 0.21/0.59    spl5_20 <=> v1_xboole_0(sK2)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.59  fof(f598,plain,(
% 0.21/0.59    spl5_29 <=> r1_tarski(k1_xboole_0,sK2)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.21/0.59  fof(f624,plain,(
% 0.21/0.59    ~v1_xboole_0(sK2) | spl5_29),
% 0.21/0.59    inference(resolution,[],[f603,f78])).
% 0.21/0.59  fof(f78,plain,(
% 0.21/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.59    inference(equality_resolution,[],[f47])).
% 0.21/0.59  fof(f47,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.59    inference(cnf_transformation,[],[f33])).
% 0.21/0.59  fof(f33,plain,(
% 0.21/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.59    inference(flattening,[],[f32])).
% 0.21/0.59  fof(f32,plain,(
% 0.21/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.59    inference(nnf_transformation,[],[f5])).
% 0.21/0.59  fof(f5,axiom,(
% 0.21/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.59  fof(f603,plain,(
% 0.21/0.59    ( ! [X0] : (~r1_tarski(X0,sK2) | ~v1_xboole_0(X0)) ) | spl5_29),
% 0.21/0.59    inference(superposition,[],[f600,f45])).
% 0.21/0.59  fof(f45,plain,(
% 0.21/0.59    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f24])).
% 0.21/0.59  fof(f24,plain,(
% 0.21/0.59    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.59    inference(ennf_transformation,[],[f3])).
% 0.21/0.59  fof(f3,axiom,(
% 0.21/0.59    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.59  fof(f600,plain,(
% 0.21/0.59    ~r1_tarski(k1_xboole_0,sK2) | spl5_29),
% 0.21/0.59    inference(avatar_component_clause,[],[f598])).
% 0.21/0.59  fof(f787,plain,(
% 0.21/0.59    ~spl5_5 | spl5_12 | spl5_20),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f784])).
% 0.21/0.59  fof(f784,plain,(
% 0.21/0.59    $false | (~spl5_5 | spl5_12 | spl5_20)),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f371,f260,f78,f778])).
% 0.21/0.59  fof(f778,plain,(
% 0.21/0.59    ( ! [X0] : (~r1_tarski(X0,sK2) | v1_xboole_0(X0) | r2_hidden(sK0,X0)) ) | ~spl5_5),
% 0.21/0.59    inference(resolution,[],[f398,f77])).
% 0.21/0.59  fof(f77,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.59    inference(definition_unfolding,[],[f54,f67])).
% 0.21/0.59  fof(f67,plain,(
% 0.21/0.59    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.59    inference(definition_unfolding,[],[f55,f65])).
% 0.21/0.59  fof(f65,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.59    inference(definition_unfolding,[],[f61,f64])).
% 0.21/0.59  fof(f64,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f12])).
% 0.21/0.59  fof(f12,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.59  fof(f61,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f11])).
% 0.21/0.59  fof(f11,axiom,(
% 0.21/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.59  fof(f55,plain,(
% 0.21/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f10])).
% 0.21/0.59  fof(f10,axiom,(
% 0.21/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.59  fof(f54,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f27])).
% 0.21/0.59  fof(f27,plain,(
% 0.21/0.59    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.59    inference(ennf_transformation,[],[f18])).
% 0.21/0.59  fof(f18,axiom,(
% 0.21/0.59    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.59  fof(f398,plain,(
% 0.21/0.59    ( ! [X8] : (~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X8) | v1_xboole_0(X8) | ~r1_tarski(X8,sK2)) ) | ~spl5_5),
% 0.21/0.59    inference(resolution,[],[f140,f204])).
% 0.21/0.59  fof(f204,plain,(
% 0.21/0.59    ( ! [X0] : (r1_tarski(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r1_tarski(X0,sK2)) ) | ~spl5_5),
% 0.21/0.59    inference(superposition,[],[f73,f101])).
% 0.21/0.59  fof(f101,plain,(
% 0.21/0.59    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) | ~spl5_5),
% 0.21/0.59    inference(avatar_component_clause,[],[f99])).
% 0.21/0.59  fof(f99,plain,(
% 0.21/0.59    spl5_5 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.59  fof(f73,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 0.21/0.59    inference(definition_unfolding,[],[f50,f66])).
% 0.21/0.59  fof(f66,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.59    inference(definition_unfolding,[],[f62,f65])).
% 0.21/0.59  fof(f62,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f19])).
% 0.21/0.59  fof(f19,axiom,(
% 0.21/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.59  fof(f50,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f26])).
% 0.21/0.59  fof(f26,plain,(
% 0.21/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.59    inference(ennf_transformation,[],[f6])).
% 0.21/0.59  fof(f6,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.59  fof(f140,plain,(
% 0.21/0.59    ( ! [X10,X9] : (~r1_tarski(X10,X9) | ~r1_xboole_0(X9,X10) | v1_xboole_0(X10)) )),
% 0.21/0.59    inference(superposition,[],[f109,f105])).
% 0.21/0.59  fof(f105,plain,(
% 0.21/0.59    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 0.21/0.59    inference(superposition,[],[f58,f63])).
% 0.21/0.59  fof(f63,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f1])).
% 0.21/0.59  fof(f1,axiom,(
% 0.21/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.59  fof(f58,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f28])).
% 0.21/0.59  fof(f28,plain,(
% 0.21/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.59    inference(ennf_transformation,[],[f8])).
% 0.21/0.59  fof(f8,axiom,(
% 0.21/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.59  fof(f109,plain,(
% 0.21/0.59    ( ! [X0,X1] : (v1_xboole_0(k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.59    inference(resolution,[],[f60,f57])).
% 0.21/0.59  fof(f57,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f38])).
% 0.21/0.59  fof(f38,plain,(
% 0.21/0.59    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 0.21/0.59  fof(f37,plain,(
% 0.21/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f36,plain,(
% 0.21/0.59    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.59    inference(rectify,[],[f35])).
% 0.21/0.59  fof(f35,plain,(
% 0.21/0.59    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.59    inference(nnf_transformation,[],[f2])).
% 0.21/0.59  fof(f2,axiom,(
% 0.21/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.59  fof(f60,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f40])).
% 0.21/0.59  fof(f40,plain,(
% 0.21/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f39])).
% 0.21/0.59  fof(f39,plain,(
% 0.21/0.59    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f29,plain,(
% 0.21/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.59    inference(ennf_transformation,[],[f22])).
% 0.21/0.59  fof(f22,plain,(
% 0.21/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.59    inference(rectify,[],[f4])).
% 0.21/0.59  fof(f4,axiom,(
% 0.21/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.59  fof(f260,plain,(
% 0.21/0.59    ~r2_hidden(sK0,sK2) | spl5_12),
% 0.21/0.59    inference(avatar_component_clause,[],[f258])).
% 0.21/0.59  fof(f258,plain,(
% 0.21/0.59    spl5_12 <=> r2_hidden(sK0,sK2)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.59  fof(f371,plain,(
% 0.21/0.59    ~v1_xboole_0(sK2) | spl5_20),
% 0.21/0.59    inference(avatar_component_clause,[],[f370])).
% 0.21/0.59  fof(f601,plain,(
% 0.21/0.59    ~spl5_29 | ~spl5_3 | spl5_11),
% 0.21/0.59    inference(avatar_split_clause,[],[f527,f196,f90,f598])).
% 0.21/0.59  fof(f90,plain,(
% 0.21/0.59    spl5_3 <=> k1_xboole_0 = sK1),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.59  fof(f196,plain,(
% 0.21/0.59    spl5_11 <=> r1_tarski(sK1,sK2)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.59  fof(f527,plain,(
% 0.21/0.59    ~r1_tarski(k1_xboole_0,sK2) | (~spl5_3 | spl5_11)),
% 0.21/0.59    inference(superposition,[],[f198,f91])).
% 0.21/0.59  fof(f91,plain,(
% 0.21/0.59    k1_xboole_0 = sK1 | ~spl5_3),
% 0.21/0.59    inference(avatar_component_clause,[],[f90])).
% 0.21/0.59  fof(f198,plain,(
% 0.21/0.59    ~r1_tarski(sK1,sK2) | spl5_11),
% 0.21/0.59    inference(avatar_component_clause,[],[f196])).
% 0.21/0.59  fof(f507,plain,(
% 0.21/0.59    ~spl5_1 | ~spl5_25 | ~spl5_1),
% 0.21/0.59    inference(avatar_split_clause,[],[f483,f81,f504,f81])).
% 0.21/0.59  fof(f504,plain,(
% 0.21/0.59    spl5_25 <=> sK1 = sK2),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.59  fof(f81,plain,(
% 0.21/0.59    spl5_1 <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.59  fof(f483,plain,(
% 0.21/0.59    sK1 != sK2 | sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | ~spl5_1),
% 0.21/0.59    inference(forward_demodulation,[],[f70,f82])).
% 0.21/0.59  fof(f82,plain,(
% 0.21/0.59    sK1 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl5_1),
% 0.21/0.59    inference(avatar_component_clause,[],[f81])).
% 0.21/0.59  fof(f70,plain,(
% 0.21/0.59    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | sK1 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.59    inference(definition_unfolding,[],[f42,f67,f67])).
% 0.21/0.59  fof(f42,plain,(
% 0.21/0.59    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f31])).
% 0.21/0.59  fof(f31,plain,(
% 0.21/0.59    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.21/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f30])).
% 0.21/0.59  fof(f30,plain,(
% 0.21/0.59    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f23,plain,(
% 0.21/0.59    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.59    inference(ennf_transformation,[],[f21])).
% 0.21/0.59  fof(f21,negated_conjecture,(
% 0.21/0.59    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.59    inference(negated_conjecture,[],[f20])).
% 0.21/0.59  fof(f20,conjecture,(
% 0.21/0.59    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.21/0.59  fof(f450,plain,(
% 0.21/0.59    spl5_3 | ~spl5_9),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f449])).
% 0.21/0.59  fof(f449,plain,(
% 0.21/0.59    $false | (spl5_3 | ~spl5_9)),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f92,f186,f45])).
% 0.21/0.59  fof(f186,plain,(
% 0.21/0.59    v1_xboole_0(sK1) | ~spl5_9),
% 0.21/0.59    inference(avatar_component_clause,[],[f184])).
% 0.21/0.59  fof(f184,plain,(
% 0.21/0.59    spl5_9 <=> v1_xboole_0(sK1)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.59  fof(f92,plain,(
% 0.21/0.59    k1_xboole_0 != sK1 | spl5_3),
% 0.21/0.59    inference(avatar_component_clause,[],[f90])).
% 0.21/0.59  fof(f413,plain,(
% 0.21/0.59    spl5_2 | ~spl5_20),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f412])).
% 0.21/0.59  fof(f412,plain,(
% 0.21/0.59    $false | (spl5_2 | ~spl5_20)),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f372,f87,f45])).
% 0.21/0.59  fof(f87,plain,(
% 0.21/0.59    k1_xboole_0 != sK2 | spl5_2),
% 0.21/0.59    inference(avatar_component_clause,[],[f85])).
% 0.21/0.59  fof(f85,plain,(
% 0.21/0.59    spl5_2 <=> k1_xboole_0 = sK2),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.59  fof(f372,plain,(
% 0.21/0.59    v1_xboole_0(sK2) | ~spl5_20),
% 0.21/0.59    inference(avatar_component_clause,[],[f370])).
% 0.21/0.59  fof(f411,plain,(
% 0.21/0.59    spl5_8 | spl5_22),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f408])).
% 0.21/0.59  fof(f408,plain,(
% 0.21/0.59    $false | (spl5_8 | spl5_22)),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f165,f406,f77])).
% 0.21/0.59  fof(f406,plain,(
% 0.21/0.59    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | spl5_22),
% 0.21/0.59    inference(avatar_component_clause,[],[f404])).
% 0.21/0.59  fof(f404,plain,(
% 0.21/0.59    spl5_22 <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.59  fof(f165,plain,(
% 0.21/0.59    ~r2_hidden(sK0,sK1) | spl5_8),
% 0.21/0.59    inference(avatar_component_clause,[],[f163])).
% 0.21/0.59  fof(f163,plain,(
% 0.21/0.59    spl5_8 <=> r2_hidden(sK0,sK1)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.59  fof(f407,plain,(
% 0.21/0.59    spl5_9 | ~spl5_22 | ~spl5_6),
% 0.21/0.59    inference(avatar_split_clause,[],[f401,f115,f404,f184])).
% 0.21/0.59  fof(f115,plain,(
% 0.21/0.59    spl5_6 <=> r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.59  fof(f401,plain,(
% 0.21/0.59    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | v1_xboole_0(sK1) | ~spl5_6),
% 0.21/0.59    inference(resolution,[],[f140,f117])).
% 0.21/0.59  fof(f117,plain,(
% 0.21/0.59    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_6),
% 0.21/0.59    inference(avatar_component_clause,[],[f115])).
% 0.21/0.59  fof(f261,plain,(
% 0.21/0.59    ~spl5_12 | spl5_11 | ~spl5_5 | ~spl5_6),
% 0.21/0.59    inference(avatar_split_clause,[],[f255,f115,f99,f196,f258])).
% 0.21/0.59  fof(f255,plain,(
% 0.21/0.59    r1_tarski(sK1,sK2) | ~r2_hidden(sK0,sK2) | (~spl5_5 | ~spl5_6)),
% 0.21/0.59    inference(resolution,[],[f229,f78])).
% 1.86/0.60  fof(f229,plain,(
% 1.86/0.60    ( ! [X1] : (~r1_tarski(X1,sK2) | r1_tarski(sK1,X1) | ~r2_hidden(sK0,X1)) ) | (~spl5_5 | ~spl5_6)),
% 1.86/0.60    inference(superposition,[],[f117,f221])).
% 1.86/0.60  fof(f221,plain,(
% 1.86/0.60    ( ! [X0] : (k2_enumset1(sK0,sK0,sK0,sK0) = X0 | ~r1_tarski(X0,sK2) | ~r2_hidden(sK0,X0)) ) | ~spl5_5),
% 1.86/0.60    inference(resolution,[],[f207,f75])).
% 1.86/0.60  fof(f75,plain,(
% 1.86/0.60    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.86/0.60    inference(definition_unfolding,[],[f53,f67])).
% 1.86/0.60  fof(f53,plain,(
% 1.86/0.60    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.86/0.60    inference(cnf_transformation,[],[f34])).
% 1.86/0.60  fof(f34,plain,(
% 1.86/0.60    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.86/0.60    inference(nnf_transformation,[],[f17])).
% 1.86/0.60  fof(f17,axiom,(
% 1.86/0.60    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.86/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.86/0.60  fof(f207,plain,(
% 1.86/0.60    ( ! [X1] : (~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),X1) | k2_enumset1(sK0,sK0,sK0,sK0) = X1 | ~r1_tarski(X1,sK2)) ) | ~spl5_5),
% 1.86/0.60    inference(resolution,[],[f204,f48])).
% 1.86/0.60  fof(f48,plain,(
% 1.86/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.86/0.60    inference(cnf_transformation,[],[f33])).
% 1.86/0.60  fof(f199,plain,(
% 1.86/0.60    ~spl5_11 | spl5_4 | ~spl5_5),
% 1.86/0.60    inference(avatar_split_clause,[],[f192,f99,f94,f196])).
% 1.86/0.60  fof(f94,plain,(
% 1.86/0.60    spl5_4 <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.86/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.86/0.60  fof(f192,plain,(
% 1.86/0.60    sK2 = k2_enumset1(sK0,sK0,sK0,sK0) | ~r1_tarski(sK1,sK2) | ~spl5_5),
% 1.86/0.60    inference(superposition,[],[f72,f101])).
% 1.86/0.60  fof(f72,plain,(
% 1.86/0.60    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.86/0.60    inference(definition_unfolding,[],[f49,f66])).
% 1.86/0.60  fof(f49,plain,(
% 1.86/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.86/0.60    inference(cnf_transformation,[],[f25])).
% 1.86/0.60  fof(f25,plain,(
% 1.86/0.60    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.86/0.60    inference(ennf_transformation,[],[f7])).
% 1.86/0.60  fof(f7,axiom,(
% 1.86/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.86/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.86/0.60  fof(f166,plain,(
% 1.86/0.60    ~spl5_8 | spl5_7),
% 1.86/0.60    inference(avatar_split_clause,[],[f160,f129,f163])).
% 1.86/0.60  fof(f129,plain,(
% 1.86/0.60    spl5_7 <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.86/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.86/0.60  fof(f160,plain,(
% 1.86/0.60    ~r2_hidden(sK0,sK1) | spl5_7),
% 1.86/0.60    inference(resolution,[],[f75,f131])).
% 1.86/0.60  fof(f131,plain,(
% 1.86/0.60    ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | spl5_7),
% 1.86/0.60    inference(avatar_component_clause,[],[f129])).
% 1.86/0.60  fof(f132,plain,(
% 1.86/0.60    ~spl5_7 | spl5_1 | ~spl5_6),
% 1.86/0.60    inference(avatar_split_clause,[],[f127,f115,f81,f129])).
% 1.86/0.60  fof(f127,plain,(
% 1.86/0.60    sK1 = k2_enumset1(sK0,sK0,sK0,sK0) | ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl5_6),
% 1.86/0.60    inference(resolution,[],[f48,f117])).
% 1.86/0.60  fof(f118,plain,(
% 1.86/0.60    spl5_6 | ~spl5_5),
% 1.86/0.60    inference(avatar_split_clause,[],[f113,f99,f115])).
% 1.86/0.60  fof(f113,plain,(
% 1.86/0.60    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl5_5),
% 1.86/0.60    inference(superposition,[],[f74,f101])).
% 1.86/0.60  fof(f74,plain,(
% 1.86/0.60    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.86/0.60    inference(definition_unfolding,[],[f51,f66])).
% 1.86/0.60  fof(f51,plain,(
% 1.86/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.86/0.60    inference(cnf_transformation,[],[f9])).
% 1.86/0.60  fof(f9,axiom,(
% 1.86/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.86/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.86/0.60  fof(f102,plain,(
% 1.86/0.60    spl5_5),
% 1.86/0.60    inference(avatar_split_clause,[],[f71,f99])).
% 1.86/0.60  fof(f71,plain,(
% 1.86/0.60    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.86/0.60    inference(definition_unfolding,[],[f41,f67,f66])).
% 1.86/0.60  fof(f41,plain,(
% 1.86/0.60    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.86/0.60    inference(cnf_transformation,[],[f31])).
% 1.86/0.60  fof(f97,plain,(
% 1.86/0.60    ~spl5_3 | ~spl5_4),
% 1.86/0.60    inference(avatar_split_clause,[],[f69,f94,f90])).
% 1.86/0.60  fof(f69,plain,(
% 1.86/0.60    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 1.86/0.60    inference(definition_unfolding,[],[f43,f67])).
% 1.86/0.60  fof(f43,plain,(
% 1.86/0.60    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 1.86/0.60    inference(cnf_transformation,[],[f31])).
% 1.86/0.60  fof(f88,plain,(
% 1.86/0.60    ~spl5_1 | ~spl5_2),
% 1.86/0.60    inference(avatar_split_clause,[],[f68,f85,f81])).
% 1.86/0.60  fof(f68,plain,(
% 1.86/0.60    k1_xboole_0 != sK2 | sK1 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.86/0.60    inference(definition_unfolding,[],[f44,f67])).
% 1.86/0.60  fof(f44,plain,(
% 1.86/0.60    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 1.86/0.60    inference(cnf_transformation,[],[f31])).
% 1.86/0.60  % SZS output end Proof for theBenchmark
% 1.86/0.60  % (30868)------------------------------
% 1.86/0.60  % (30868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.86/0.60  % (30868)Termination reason: Refutation
% 1.86/0.60  
% 1.86/0.60  % (30868)Memory used [KB]: 11129
% 1.86/0.60  % (30868)Time elapsed: 0.121 s
% 1.86/0.60  % (30868)------------------------------
% 1.86/0.60  % (30868)------------------------------
% 1.86/0.60  % (30841)Success in time 0.24 s
%------------------------------------------------------------------------------
