%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:03 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 613 expanded)
%              Number of leaves         :   33 ( 207 expanded)
%              Depth                    :   12
%              Number of atoms          :  482 (1474 expanded)
%              Number of equality atoms :  160 ( 935 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f511,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f132,f141,f148,f186,f209,f219,f251,f262,f268,f310,f392,f397,f432,f468,f510])).

fof(f510,plain,
    ( ~ spl7_3
    | spl7_4
    | ~ spl7_14 ),
    inference(avatar_contradiction_clause,[],[f509])).

fof(f509,plain,
    ( $false
    | ~ spl7_3
    | spl7_4
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f504,f140])).

fof(f140,plain,
    ( sK3 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl7_4
  <=> sK3 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f504,plain,
    ( sK3 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl7_3
    | ~ spl7_14 ),
    inference(backward_demodulation,[],[f428,f469])).

fof(f469,plain,
    ( sK3 = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3))
    | ~ spl7_14 ),
    inference(resolution,[],[f319,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f61,f90])).

fof(f90,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f89])).

fof(f89,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f74,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f74,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f319,plain,
    ( r1_tarski(k1_xboole_0,sK3)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl7_14
  <=> r1_tarski(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f428,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3))
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f95,f135])).

fof(f135,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl7_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f95,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f49,f91,f90])).

fof(f91,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f89])).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f468,plain,
    ( ~ spl7_3
    | ~ spl7_9
    | spl7_14 ),
    inference(avatar_contradiction_clause,[],[f467])).

fof(f467,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_9
    | spl7_14 ),
    inference(subsumption_resolution,[],[f463,f320])).

fof(f320,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | spl7_14 ),
    inference(avatar_component_clause,[],[f318])).

fof(f463,plain,
    ( r1_tarski(k1_xboole_0,sK3)
    | ~ spl7_3
    | ~ spl7_9 ),
    inference(resolution,[],[f438,f172])).

fof(f172,plain,
    ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK3)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl7_9
  <=> r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f438,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),X0)
        | r1_tarski(k1_xboole_0,X0) )
    | ~ spl7_3 ),
    inference(superposition,[],[f109,f428])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f75,f90])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f432,plain,
    ( spl7_9
    | ~ spl7_11 ),
    inference(avatar_contradiction_clause,[],[f431])).

fof(f431,plain,
    ( $false
    | spl7_9
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f430,f218])).

fof(f218,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl7_11
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f430,plain,
    ( ~ r2_hidden(sK1,sK3)
    | spl7_9 ),
    inference(duplicate_literal_removal,[],[f429])).

fof(f429,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK1,sK3)
    | spl7_9 ),
    inference(resolution,[],[f173,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f86,f89])).

fof(f86,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f173,plain,
    ( ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK3)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f171])).

fof(f397,plain,
    ( ~ spl7_6
    | ~ spl7_7
    | spl7_1 ),
    inference(avatar_split_clause,[],[f150,f125,f161,f157])).

fof(f157,plain,
    ( spl7_6
  <=> r1_tarski(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f161,plain,
    ( spl7_7
  <=> r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f125,plain,
    ( spl7_1
  <=> sK2 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f150,plain,
    ( ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)
    | ~ r1_tarski(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl7_1 ),
    inference(extensionality_resolution,[],[f64,f127])).

fof(f127,plain,
    ( sK2 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f125])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f392,plain,
    ( ~ spl7_1
    | spl7_5
    | ~ spl7_11 ),
    inference(avatar_contradiction_clause,[],[f391])).

fof(f391,plain,
    ( $false
    | ~ spl7_1
    | spl7_5
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f390,f147])).

fof(f147,plain,
    ( sK2 != sK3
    | spl7_5 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl7_5
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f390,plain,
    ( sK2 = sK3
    | ~ spl7_1
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f388,f366])).

fof(f366,plain,
    ( sK2 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3))
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f95,f126])).

fof(f126,plain,
    ( sK2 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f125])).

fof(f388,plain,
    ( sK3 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3))
    | ~ spl7_1
    | ~ spl7_11 ),
    inference(resolution,[],[f380,f99])).

fof(f380,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl7_1
    | ~ spl7_11 ),
    inference(resolution,[],[f356,f218])).

fof(f356,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK1,X2)
        | r1_tarski(sK2,X2) )
    | ~ spl7_1 ),
    inference(duplicate_literal_removal,[],[f350])).

fof(f350,plain,
    ( ! [X2] :
        ( r1_tarski(sK2,X2)
        | ~ r2_hidden(sK1,X2)
        | ~ r2_hidden(sK1,X2) )
    | ~ spl7_1 ),
    inference(superposition,[],[f112,f126])).

fof(f310,plain,
    ( spl7_7
    | ~ spl7_13 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | spl7_7
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f306,f267])).

fof(f267,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl7_13
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f306,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl7_7 ),
    inference(duplicate_literal_removal,[],[f303])).

fof(f303,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,sK2)
    | spl7_7 ),
    inference(resolution,[],[f112,f163])).

fof(f163,plain,
    ( ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f161])).

fof(f268,plain,
    ( spl7_3
    | spl7_13
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f263,f248,f265,f134])).

fof(f248,plain,
    ( spl7_12
  <=> sK1 = sK4(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f263,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = sK2
    | ~ spl7_12 ),
    inference(superposition,[],[f54,f250])).

fof(f250,plain,
    ( sK1 = sK4(sK2)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f248])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f262,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | spl7_4 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4 ),
    inference(subsumption_resolution,[],[f260,f221])).

fof(f221,plain,
    ( k1_xboole_0 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl7_2
    | spl7_4 ),
    inference(backward_demodulation,[],[f140,f130])).

fof(f130,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f260,plain,
    ( k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f256,f96])).

fof(f96,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f55,f90])).

fof(f55,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f256,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f220,f135])).

fof(f220,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k1_xboole_0))
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f95,f130])).

fof(f251,plain,
    ( spl7_3
    | spl7_12 ),
    inference(avatar_split_clause,[],[f246,f248,f134])).

fof(f246,plain,
    ( sK1 = sK4(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f245,f54])).

fof(f245,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | sK1 = X0 ) ),
    inference(resolution,[],[f194,f119])).

fof(f119,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f65,f91])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f194,plain,(
    ! [X1] :
      ( r2_hidden(X1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f183,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
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

fof(f183,plain,(
    sP0(sK3,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f123,f95])).

fof(f123,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f82,f90])).

fof(f82,plain,(
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

fof(f219,plain,
    ( spl7_2
    | spl7_11
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f214,f206,f216,f129])).

fof(f206,plain,
    ( spl7_10
  <=> sK1 = sK4(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f214,plain,
    ( r2_hidden(sK1,sK3)
    | k1_xboole_0 = sK3
    | ~ spl7_10 ),
    inference(superposition,[],[f54,f208])).

fof(f208,plain,
    ( sK1 = sK4(sK3)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f206])).

fof(f209,plain,
    ( spl7_2
    | spl7_10 ),
    inference(avatar_split_clause,[],[f204,f206,f129])).

fof(f204,plain,
    ( sK1 = sK4(sK3)
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f203,f54])).

fof(f203,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | sK1 = X0 ) ),
    inference(resolution,[],[f193,f119])).

fof(f193,plain,(
    ! [X0] :
      ( r2_hidden(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f183,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f186,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl7_6 ),
    inference(subsumption_resolution,[],[f184,f159])).

fof(f159,plain,
    ( ~ r1_tarski(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl7_6 ),
    inference(avatar_component_clause,[],[f157])).

fof(f184,plain,(
    r1_tarski(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f97,f95])).

fof(f97,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f56,f90])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f148,plain,
    ( ~ spl7_5
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f143,f125,f145])).

fof(f143,plain,
    ( sK2 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | sK2 != sK3 ),
    inference(inner_rewriting,[],[f142])).

fof(f142,plain,
    ( sK3 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | sK2 != sK3 ),
    inference(inner_rewriting,[],[f94])).

fof(f94,plain,
    ( sK3 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | sK2 != k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f50,f91,f91])).

fof(f50,plain,
    ( sK3 != k1_tarski(sK1)
    | sK2 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f141,plain,
    ( ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f93,f138,f134])).

fof(f93,plain,
    ( sK3 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f51,f91])).

fof(f51,plain,
    ( sK3 != k1_tarski(sK1)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f29])).

fof(f132,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f92,f129,f125])).

% (3991)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f92,plain,
    ( k1_xboole_0 != sK3
    | sK2 != k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f52,f91])).

fof(f52,plain,
    ( k1_xboole_0 != sK3
    | sK2 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:49:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (3992)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.48  % (4008)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.27/0.53  % (3985)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.27/0.53  % (4006)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.27/0.53  % (3988)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.27/0.53  % (3998)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.27/0.53  % (3986)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.27/0.54  % (3989)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.27/0.54  % (3987)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.27/0.54  % (3990)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.54  % (3984)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.47/0.54  % (4007)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.47/0.54  % (4012)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.47/0.54  % (4010)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.47/0.55  % (4013)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.47/0.55  % (4013)Refutation not found, incomplete strategy% (4013)------------------------------
% 1.47/0.55  % (4013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (4013)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (4013)Memory used [KB]: 1663
% 1.47/0.55  % (4013)Time elapsed: 0.138 s
% 1.47/0.55  % (4013)------------------------------
% 1.47/0.55  % (4013)------------------------------
% 1.47/0.55  % (4011)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.47/0.55  % (3999)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.47/0.55  % (3996)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.47/0.55  % (4005)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.47/0.55  % (4002)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.47/0.55  % (3997)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.47/0.55  % (3995)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.47/0.55  % (4004)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.47/0.55  % (4001)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.47/0.55  % (3993)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.47/0.56  % (4000)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.47/0.56  % (4000)Refutation not found, incomplete strategy% (4000)------------------------------
% 1.47/0.56  % (4000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (4000)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (4000)Memory used [KB]: 10618
% 1.47/0.56  % (4000)Time elapsed: 0.147 s
% 1.47/0.56  % (4000)------------------------------
% 1.47/0.56  % (4000)------------------------------
% 1.47/0.56  % (3994)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.47/0.56  % (4003)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.47/0.56  % (3990)Refutation found. Thanks to Tanya!
% 1.47/0.56  % SZS status Theorem for theBenchmark
% 1.47/0.56  % SZS output start Proof for theBenchmark
% 1.47/0.56  fof(f511,plain,(
% 1.47/0.56    $false),
% 1.47/0.56    inference(avatar_sat_refutation,[],[f132,f141,f148,f186,f209,f219,f251,f262,f268,f310,f392,f397,f432,f468,f510])).
% 1.47/0.56  fof(f510,plain,(
% 1.47/0.56    ~spl7_3 | spl7_4 | ~spl7_14),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f509])).
% 1.47/0.56  fof(f509,plain,(
% 1.47/0.56    $false | (~spl7_3 | spl7_4 | ~spl7_14)),
% 1.47/0.56    inference(subsumption_resolution,[],[f504,f140])).
% 1.47/0.56  fof(f140,plain,(
% 1.47/0.56    sK3 != k3_enumset1(sK1,sK1,sK1,sK1,sK1) | spl7_4),
% 1.47/0.56    inference(avatar_component_clause,[],[f138])).
% 1.47/0.56  fof(f138,plain,(
% 1.47/0.56    spl7_4 <=> sK3 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.47/0.56  fof(f504,plain,(
% 1.47/0.56    sK3 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | (~spl7_3 | ~spl7_14)),
% 1.47/0.56    inference(backward_demodulation,[],[f428,f469])).
% 1.47/0.56  fof(f469,plain,(
% 1.47/0.56    sK3 = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3)) | ~spl7_14),
% 1.47/0.56    inference(resolution,[],[f319,f99])).
% 1.47/0.56  fof(f99,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1) )),
% 1.47/0.56    inference(definition_unfolding,[],[f61,f90])).
% 1.47/0.56  fof(f90,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.47/0.56    inference(definition_unfolding,[],[f58,f89])).
% 1.47/0.56  fof(f89,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.47/0.56    inference(definition_unfolding,[],[f59,f88])).
% 1.47/0.56  fof(f88,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.47/0.56    inference(definition_unfolding,[],[f74,f87])).
% 1.47/0.56  fof(f87,plain,(
% 1.47/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f14])).
% 1.47/0.56  fof(f14,axiom,(
% 1.47/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.47/0.56  fof(f74,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f13])).
% 1.47/0.56  fof(f13,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.47/0.56  fof(f59,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f12])).
% 1.47/0.56  fof(f12,axiom,(
% 1.47/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.47/0.56  fof(f58,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f16])).
% 1.47/0.56  fof(f16,axiom,(
% 1.47/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.47/0.56  fof(f61,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f24])).
% 1.47/0.56  fof(f24,plain,(
% 1.47/0.56    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.47/0.56    inference(ennf_transformation,[],[f7])).
% 1.47/0.56  fof(f7,axiom,(
% 1.47/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.47/0.56  fof(f319,plain,(
% 1.47/0.56    r1_tarski(k1_xboole_0,sK3) | ~spl7_14),
% 1.47/0.56    inference(avatar_component_clause,[],[f318])).
% 1.47/0.56  fof(f318,plain,(
% 1.47/0.56    spl7_14 <=> r1_tarski(k1_xboole_0,sK3)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.47/0.56  fof(f428,plain,(
% 1.47/0.56    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3)) | ~spl7_3),
% 1.47/0.56    inference(forward_demodulation,[],[f95,f135])).
% 1.47/0.56  fof(f135,plain,(
% 1.47/0.56    k1_xboole_0 = sK2 | ~spl7_3),
% 1.47/0.56    inference(avatar_component_clause,[],[f134])).
% 1.47/0.56  fof(f134,plain,(
% 1.47/0.56    spl7_3 <=> k1_xboole_0 = sK2),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.47/0.56  fof(f95,plain,(
% 1.47/0.56    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3))),
% 1.47/0.56    inference(definition_unfolding,[],[f49,f91,f90])).
% 1.47/0.56  fof(f91,plain,(
% 1.47/0.56    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.47/0.56    inference(definition_unfolding,[],[f53,f89])).
% 1.47/0.56  fof(f53,plain,(
% 1.47/0.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f11])).
% 1.47/0.56  fof(f11,axiom,(
% 1.47/0.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.47/0.56  fof(f49,plain,(
% 1.47/0.56    k1_tarski(sK1) = k2_xboole_0(sK2,sK3)),
% 1.47/0.56    inference(cnf_transformation,[],[f29])).
% 1.47/0.56  fof(f29,plain,(
% 1.47/0.56    (k1_xboole_0 != sK3 | sK2 != k1_tarski(sK1)) & (sK3 != k1_tarski(sK1) | k1_xboole_0 != sK2) & (sK3 != k1_tarski(sK1) | sK2 != k1_tarski(sK1)) & k1_tarski(sK1) = k2_xboole_0(sK2,sK3)),
% 1.47/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f28])).
% 1.47/0.56  fof(f28,plain,(
% 1.47/0.56    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK3 | sK2 != k1_tarski(sK1)) & (sK3 != k1_tarski(sK1) | k1_xboole_0 != sK2) & (sK3 != k1_tarski(sK1) | sK2 != k1_tarski(sK1)) & k1_tarski(sK1) = k2_xboole_0(sK2,sK3))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  fof(f22,plain,(
% 1.47/0.56    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.47/0.56    inference(ennf_transformation,[],[f20])).
% 1.47/0.56  fof(f20,negated_conjecture,(
% 1.47/0.56    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.47/0.56    inference(negated_conjecture,[],[f19])).
% 1.47/0.56  fof(f19,conjecture,(
% 1.47/0.56    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.47/0.56  fof(f468,plain,(
% 1.47/0.56    ~spl7_3 | ~spl7_9 | spl7_14),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f467])).
% 1.47/0.56  fof(f467,plain,(
% 1.47/0.56    $false | (~spl7_3 | ~spl7_9 | spl7_14)),
% 1.47/0.56    inference(subsumption_resolution,[],[f463,f320])).
% 1.47/0.56  fof(f320,plain,(
% 1.47/0.56    ~r1_tarski(k1_xboole_0,sK3) | spl7_14),
% 1.47/0.56    inference(avatar_component_clause,[],[f318])).
% 1.47/0.56  fof(f463,plain,(
% 1.47/0.56    r1_tarski(k1_xboole_0,sK3) | (~spl7_3 | ~spl7_9)),
% 1.47/0.56    inference(resolution,[],[f438,f172])).
% 1.47/0.56  fof(f172,plain,(
% 1.47/0.56    r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK3) | ~spl7_9),
% 1.47/0.56    inference(avatar_component_clause,[],[f171])).
% 1.47/0.56  fof(f171,plain,(
% 1.47/0.56    spl7_9 <=> r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK3)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.47/0.56  fof(f438,plain,(
% 1.47/0.56    ( ! [X0] : (~r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),X0) | r1_tarski(k1_xboole_0,X0)) ) | ~spl7_3),
% 1.47/0.56    inference(superposition,[],[f109,f428])).
% 1.47/0.56  fof(f109,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X2) | r1_tarski(X0,X2)) )),
% 1.47/0.56    inference(definition_unfolding,[],[f75,f90])).
% 1.47/0.56  fof(f75,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f25])).
% 1.47/0.56  fof(f25,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.47/0.56    inference(ennf_transformation,[],[f6])).
% 1.47/0.56  fof(f6,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.47/0.56  fof(f432,plain,(
% 1.47/0.56    spl7_9 | ~spl7_11),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f431])).
% 1.47/0.56  fof(f431,plain,(
% 1.47/0.56    $false | (spl7_9 | ~spl7_11)),
% 1.47/0.56    inference(subsumption_resolution,[],[f430,f218])).
% 1.47/0.56  fof(f218,plain,(
% 1.47/0.56    r2_hidden(sK1,sK3) | ~spl7_11),
% 1.47/0.56    inference(avatar_component_clause,[],[f216])).
% 1.47/0.56  fof(f216,plain,(
% 1.47/0.56    spl7_11 <=> r2_hidden(sK1,sK3)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.47/0.56  fof(f430,plain,(
% 1.47/0.56    ~r2_hidden(sK1,sK3) | spl7_9),
% 1.47/0.56    inference(duplicate_literal_removal,[],[f429])).
% 1.47/0.56  fof(f429,plain,(
% 1.47/0.56    ~r2_hidden(sK1,sK3) | ~r2_hidden(sK1,sK3) | spl7_9),
% 1.47/0.56    inference(resolution,[],[f173,f112])).
% 1.47/0.56  fof(f112,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.47/0.56    inference(definition_unfolding,[],[f86,f89])).
% 1.47/0.56  fof(f86,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f48])).
% 1.47/0.56  fof(f48,plain,(
% 1.47/0.56    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.47/0.56    inference(flattening,[],[f47])).
% 1.47/0.56  fof(f47,plain,(
% 1.47/0.56    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.47/0.56    inference(nnf_transformation,[],[f18])).
% 1.47/0.56  fof(f18,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.47/0.56  fof(f173,plain,(
% 1.47/0.56    ~r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK3) | spl7_9),
% 1.47/0.56    inference(avatar_component_clause,[],[f171])).
% 1.47/0.56  fof(f397,plain,(
% 1.47/0.56    ~spl7_6 | ~spl7_7 | spl7_1),
% 1.47/0.56    inference(avatar_split_clause,[],[f150,f125,f161,f157])).
% 1.47/0.56  fof(f157,plain,(
% 1.47/0.56    spl7_6 <=> r1_tarski(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.47/0.56  fof(f161,plain,(
% 1.47/0.56    spl7_7 <=> r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.47/0.56  fof(f125,plain,(
% 1.47/0.56    spl7_1 <=> sK2 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.47/0.56  fof(f150,plain,(
% 1.47/0.56    ~r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2) | ~r1_tarski(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | spl7_1),
% 1.47/0.56    inference(extensionality_resolution,[],[f64,f127])).
% 1.47/0.56  fof(f127,plain,(
% 1.47/0.56    sK2 != k3_enumset1(sK1,sK1,sK1,sK1,sK1) | spl7_1),
% 1.47/0.56    inference(avatar_component_clause,[],[f125])).
% 1.47/0.56  fof(f64,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f33])).
% 1.47/0.56  fof(f33,plain,(
% 1.47/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.56    inference(flattening,[],[f32])).
% 1.47/0.56  fof(f32,plain,(
% 1.47/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.56    inference(nnf_transformation,[],[f4])).
% 1.47/0.56  fof(f4,axiom,(
% 1.47/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.47/0.56  fof(f392,plain,(
% 1.47/0.56    ~spl7_1 | spl7_5 | ~spl7_11),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f391])).
% 1.47/0.56  fof(f391,plain,(
% 1.47/0.56    $false | (~spl7_1 | spl7_5 | ~spl7_11)),
% 1.47/0.56    inference(subsumption_resolution,[],[f390,f147])).
% 1.47/0.56  fof(f147,plain,(
% 1.47/0.56    sK2 != sK3 | spl7_5),
% 1.47/0.56    inference(avatar_component_clause,[],[f145])).
% 1.47/0.56  fof(f145,plain,(
% 1.47/0.56    spl7_5 <=> sK2 = sK3),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.47/0.56  fof(f390,plain,(
% 1.47/0.56    sK2 = sK3 | (~spl7_1 | ~spl7_11)),
% 1.47/0.56    inference(forward_demodulation,[],[f388,f366])).
% 1.47/0.56  fof(f366,plain,(
% 1.47/0.56    sK2 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3)) | ~spl7_1),
% 1.47/0.56    inference(forward_demodulation,[],[f95,f126])).
% 1.47/0.56  fof(f126,plain,(
% 1.47/0.56    sK2 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | ~spl7_1),
% 1.47/0.56    inference(avatar_component_clause,[],[f125])).
% 1.47/0.56  fof(f388,plain,(
% 1.47/0.56    sK3 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3)) | (~spl7_1 | ~spl7_11)),
% 1.47/0.56    inference(resolution,[],[f380,f99])).
% 1.47/0.56  fof(f380,plain,(
% 1.47/0.56    r1_tarski(sK2,sK3) | (~spl7_1 | ~spl7_11)),
% 1.47/0.56    inference(resolution,[],[f356,f218])).
% 1.47/0.56  fof(f356,plain,(
% 1.47/0.56    ( ! [X2] : (~r2_hidden(sK1,X2) | r1_tarski(sK2,X2)) ) | ~spl7_1),
% 1.47/0.56    inference(duplicate_literal_removal,[],[f350])).
% 1.47/0.56  fof(f350,plain,(
% 1.47/0.56    ( ! [X2] : (r1_tarski(sK2,X2) | ~r2_hidden(sK1,X2) | ~r2_hidden(sK1,X2)) ) | ~spl7_1),
% 1.47/0.56    inference(superposition,[],[f112,f126])).
% 1.47/0.56  fof(f310,plain,(
% 1.47/0.56    spl7_7 | ~spl7_13),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f309])).
% 1.47/0.56  fof(f309,plain,(
% 1.47/0.56    $false | (spl7_7 | ~spl7_13)),
% 1.47/0.56    inference(subsumption_resolution,[],[f306,f267])).
% 1.47/0.56  fof(f267,plain,(
% 1.47/0.56    r2_hidden(sK1,sK2) | ~spl7_13),
% 1.47/0.56    inference(avatar_component_clause,[],[f265])).
% 1.47/0.56  fof(f265,plain,(
% 1.47/0.56    spl7_13 <=> r2_hidden(sK1,sK2)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.47/0.56  fof(f306,plain,(
% 1.47/0.56    ~r2_hidden(sK1,sK2) | spl7_7),
% 1.47/0.56    inference(duplicate_literal_removal,[],[f303])).
% 1.47/0.56  fof(f303,plain,(
% 1.47/0.56    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK1,sK2) | spl7_7),
% 1.47/0.56    inference(resolution,[],[f112,f163])).
% 1.47/0.56  fof(f163,plain,(
% 1.47/0.56    ~r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2) | spl7_7),
% 1.47/0.56    inference(avatar_component_clause,[],[f161])).
% 1.47/0.56  fof(f268,plain,(
% 1.47/0.56    spl7_3 | spl7_13 | ~spl7_12),
% 1.47/0.56    inference(avatar_split_clause,[],[f263,f248,f265,f134])).
% 1.47/0.56  fof(f248,plain,(
% 1.47/0.56    spl7_12 <=> sK1 = sK4(sK2)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.47/0.56  fof(f263,plain,(
% 1.47/0.56    r2_hidden(sK1,sK2) | k1_xboole_0 = sK2 | ~spl7_12),
% 1.47/0.56    inference(superposition,[],[f54,f250])).
% 1.47/0.56  fof(f250,plain,(
% 1.47/0.56    sK1 = sK4(sK2) | ~spl7_12),
% 1.47/0.56    inference(avatar_component_clause,[],[f248])).
% 1.47/0.56  fof(f54,plain,(
% 1.47/0.56    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.47/0.56    inference(cnf_transformation,[],[f31])).
% 1.47/0.56  fof(f31,plain,(
% 1.47/0.56    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 1.47/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f30])).
% 1.47/0.56  fof(f30,plain,(
% 1.47/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  fof(f23,plain,(
% 1.47/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.47/0.56    inference(ennf_transformation,[],[f3])).
% 1.47/0.56  fof(f3,axiom,(
% 1.47/0.56    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.47/0.56  fof(f262,plain,(
% 1.47/0.56    ~spl7_2 | ~spl7_3 | spl7_4),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f261])).
% 1.47/0.56  fof(f261,plain,(
% 1.47/0.56    $false | (~spl7_2 | ~spl7_3 | spl7_4)),
% 1.47/0.56    inference(subsumption_resolution,[],[f260,f221])).
% 1.47/0.56  fof(f221,plain,(
% 1.47/0.56    k1_xboole_0 != k3_enumset1(sK1,sK1,sK1,sK1,sK1) | (~spl7_2 | spl7_4)),
% 1.47/0.56    inference(backward_demodulation,[],[f140,f130])).
% 1.47/0.56  fof(f130,plain,(
% 1.47/0.56    k1_xboole_0 = sK3 | ~spl7_2),
% 1.47/0.56    inference(avatar_component_clause,[],[f129])).
% 1.47/0.56  fof(f129,plain,(
% 1.47/0.56    spl7_2 <=> k1_xboole_0 = sK3),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.47/0.56  fof(f260,plain,(
% 1.47/0.56    k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | (~spl7_2 | ~spl7_3)),
% 1.47/0.56    inference(forward_demodulation,[],[f256,f96])).
% 1.47/0.56  fof(f96,plain,(
% 1.47/0.56    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0) )),
% 1.47/0.56    inference(definition_unfolding,[],[f55,f90])).
% 1.47/0.56  fof(f55,plain,(
% 1.47/0.56    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.47/0.56    inference(cnf_transformation,[],[f21])).
% 1.47/0.56  fof(f21,plain,(
% 1.47/0.56    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.47/0.56    inference(rectify,[],[f2])).
% 1.47/0.56  fof(f2,axiom,(
% 1.47/0.56    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.47/0.56  fof(f256,plain,(
% 1.47/0.56    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | (~spl7_2 | ~spl7_3)),
% 1.47/0.56    inference(backward_demodulation,[],[f220,f135])).
% 1.47/0.56  fof(f220,plain,(
% 1.47/0.56    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k1_xboole_0)) | ~spl7_2),
% 1.47/0.56    inference(backward_demodulation,[],[f95,f130])).
% 1.47/0.56  fof(f251,plain,(
% 1.47/0.56    spl7_3 | spl7_12),
% 1.47/0.56    inference(avatar_split_clause,[],[f246,f248,f134])).
% 1.47/0.56  fof(f246,plain,(
% 1.47/0.56    sK1 = sK4(sK2) | k1_xboole_0 = sK2),
% 1.47/0.56    inference(resolution,[],[f245,f54])).
% 1.47/0.56  fof(f245,plain,(
% 1.47/0.56    ( ! [X0] : (~r2_hidden(X0,sK2) | sK1 = X0) )),
% 1.47/0.56    inference(resolution,[],[f194,f119])).
% 1.47/0.56  fof(f119,plain,(
% 1.47/0.56    ( ! [X0,X3] : (~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X3) )),
% 1.47/0.56    inference(equality_resolution,[],[f103])).
% 1.47/0.56  fof(f103,plain,(
% 1.47/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.47/0.56    inference(definition_unfolding,[],[f65,f91])).
% 1.47/0.56  fof(f65,plain,(
% 1.47/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.47/0.56    inference(cnf_transformation,[],[f37])).
% 1.47/0.56  fof(f37,plain,(
% 1.47/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.47/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).
% 1.47/0.56  fof(f36,plain,(
% 1.47/0.56    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  fof(f35,plain,(
% 1.47/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.47/0.56    inference(rectify,[],[f34])).
% 1.47/0.56  fof(f34,plain,(
% 1.47/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.47/0.56    inference(nnf_transformation,[],[f10])).
% 1.47/0.56  fof(f10,axiom,(
% 1.47/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.47/0.56  fof(f194,plain,(
% 1.47/0.56    ( ! [X1] : (r2_hidden(X1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~r2_hidden(X1,sK2)) )),
% 1.47/0.56    inference(resolution,[],[f183,f77])).
% 1.47/0.56  fof(f77,plain,(
% 1.47/0.56    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X1) | r2_hidden(X4,X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f45])).
% 1.47/0.56  fof(f45,plain,(
% 1.47/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((~r2_hidden(sK6(X0,X1,X2),X0) & ~r2_hidden(sK6(X0,X1,X2),X1)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.47/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).
% 1.47/0.56  fof(f44,plain,(
% 1.47/0.56    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2))) => (((~r2_hidden(sK6(X0,X1,X2),X0) & ~r2_hidden(sK6(X0,X1,X2),X1)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  fof(f43,plain,(
% 1.47/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.47/0.56    inference(rectify,[],[f42])).
% 1.47/0.56  fof(f42,plain,(
% 1.47/0.56    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.47/0.56    inference(flattening,[],[f41])).
% 1.47/0.56  fof(f41,plain,(
% 1.47/0.56    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.47/0.56    inference(nnf_transformation,[],[f26])).
% 1.47/0.56  fof(f26,plain,(
% 1.47/0.56    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.47/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.47/0.56  fof(f183,plain,(
% 1.47/0.56    sP0(sK3,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 1.47/0.56    inference(superposition,[],[f123,f95])).
% 1.47/0.56  fof(f123,plain,(
% 1.47/0.56    ( ! [X0,X1] : (sP0(X1,X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.47/0.56    inference(equality_resolution,[],[f111])).
% 1.47/0.56  fof(f111,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 1.47/0.56    inference(definition_unfolding,[],[f82,f90])).
% 1.47/0.56  fof(f82,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.47/0.56    inference(cnf_transformation,[],[f46])).
% 1.47/0.56  fof(f46,plain,(
% 1.47/0.56    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2))),
% 1.47/0.56    inference(nnf_transformation,[],[f27])).
% 1.47/0.56  fof(f27,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.47/0.56    inference(definition_folding,[],[f1,f26])).
% 1.47/0.56  fof(f1,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.47/0.56  fof(f219,plain,(
% 1.47/0.56    spl7_2 | spl7_11 | ~spl7_10),
% 1.47/0.56    inference(avatar_split_clause,[],[f214,f206,f216,f129])).
% 1.47/0.56  fof(f206,plain,(
% 1.47/0.56    spl7_10 <=> sK1 = sK4(sK3)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.47/0.56  fof(f214,plain,(
% 1.47/0.56    r2_hidden(sK1,sK3) | k1_xboole_0 = sK3 | ~spl7_10),
% 1.47/0.56    inference(superposition,[],[f54,f208])).
% 1.47/0.56  fof(f208,plain,(
% 1.47/0.56    sK1 = sK4(sK3) | ~spl7_10),
% 1.47/0.56    inference(avatar_component_clause,[],[f206])).
% 1.47/0.56  fof(f209,plain,(
% 1.47/0.56    spl7_2 | spl7_10),
% 1.47/0.56    inference(avatar_split_clause,[],[f204,f206,f129])).
% 1.47/0.56  fof(f204,plain,(
% 1.47/0.56    sK1 = sK4(sK3) | k1_xboole_0 = sK3),
% 1.47/0.56    inference(resolution,[],[f203,f54])).
% 1.47/0.56  fof(f203,plain,(
% 1.47/0.56    ( ! [X0] : (~r2_hidden(X0,sK3) | sK1 = X0) )),
% 1.47/0.56    inference(resolution,[],[f193,f119])).
% 1.47/0.56  fof(f193,plain,(
% 1.47/0.56    ( ! [X0] : (r2_hidden(X0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~r2_hidden(X0,sK3)) )),
% 1.47/0.56    inference(resolution,[],[f183,f78])).
% 1.47/0.56  fof(f78,plain,(
% 1.47/0.56    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X0) | r2_hidden(X4,X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f45])).
% 1.47/0.56  fof(f186,plain,(
% 1.47/0.56    spl7_6),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f185])).
% 1.47/0.56  fof(f185,plain,(
% 1.47/0.56    $false | spl7_6),
% 1.47/0.56    inference(subsumption_resolution,[],[f184,f159])).
% 1.47/0.56  fof(f159,plain,(
% 1.47/0.56    ~r1_tarski(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | spl7_6),
% 1.47/0.56    inference(avatar_component_clause,[],[f157])).
% 1.47/0.56  fof(f184,plain,(
% 1.47/0.56    r1_tarski(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 1.47/0.56    inference(superposition,[],[f97,f95])).
% 1.47/0.56  fof(f97,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.47/0.56    inference(definition_unfolding,[],[f56,f90])).
% 1.47/0.56  fof(f56,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f9])).
% 1.47/0.56  fof(f9,axiom,(
% 1.47/0.56    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.47/0.56  fof(f148,plain,(
% 1.47/0.56    ~spl7_5 | ~spl7_1),
% 1.47/0.56    inference(avatar_split_clause,[],[f143,f125,f145])).
% 1.47/0.56  fof(f143,plain,(
% 1.47/0.56    sK2 != k3_enumset1(sK1,sK1,sK1,sK1,sK1) | sK2 != sK3),
% 1.47/0.56    inference(inner_rewriting,[],[f142])).
% 1.47/0.56  fof(f142,plain,(
% 1.47/0.56    sK3 != k3_enumset1(sK1,sK1,sK1,sK1,sK1) | sK2 != sK3),
% 1.47/0.56    inference(inner_rewriting,[],[f94])).
% 1.47/0.56  fof(f94,plain,(
% 1.47/0.56    sK3 != k3_enumset1(sK1,sK1,sK1,sK1,sK1) | sK2 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 1.47/0.56    inference(definition_unfolding,[],[f50,f91,f91])).
% 1.47/0.56  fof(f50,plain,(
% 1.47/0.56    sK3 != k1_tarski(sK1) | sK2 != k1_tarski(sK1)),
% 1.47/0.56    inference(cnf_transformation,[],[f29])).
% 1.47/0.56  fof(f141,plain,(
% 1.47/0.56    ~spl7_3 | ~spl7_4),
% 1.47/0.56    inference(avatar_split_clause,[],[f93,f138,f134])).
% 1.47/0.56  fof(f93,plain,(
% 1.47/0.56    sK3 != k3_enumset1(sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 != sK2),
% 1.47/0.56    inference(definition_unfolding,[],[f51,f91])).
% 1.47/0.56  fof(f51,plain,(
% 1.47/0.56    sK3 != k1_tarski(sK1) | k1_xboole_0 != sK2),
% 1.47/0.56    inference(cnf_transformation,[],[f29])).
% 1.47/0.56  fof(f132,plain,(
% 1.47/0.56    ~spl7_1 | ~spl7_2),
% 1.47/0.56    inference(avatar_split_clause,[],[f92,f129,f125])).
% 1.47/0.56  % (3991)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.47/0.56  fof(f92,plain,(
% 1.47/0.56    k1_xboole_0 != sK3 | sK2 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 1.47/0.56    inference(definition_unfolding,[],[f52,f91])).
% 1.47/0.56  fof(f52,plain,(
% 1.47/0.56    k1_xboole_0 != sK3 | sK2 != k1_tarski(sK1)),
% 1.47/0.56    inference(cnf_transformation,[],[f29])).
% 1.47/0.56  % SZS output end Proof for theBenchmark
% 1.47/0.56  % (3990)------------------------------
% 1.47/0.56  % (3990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (3990)Termination reason: Refutation
% 1.47/0.56  
% 1.47/0.56  % (3990)Memory used [KB]: 10874
% 1.47/0.56  % (3990)Time elapsed: 0.108 s
% 1.47/0.56  % (3990)------------------------------
% 1.47/0.56  % (3990)------------------------------
% 1.47/0.56  % (4009)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.47/0.57  % (3983)Success in time 0.204 s
%------------------------------------------------------------------------------
