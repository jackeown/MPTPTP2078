%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:18 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 959 expanded)
%              Number of leaves         :   33 ( 283 expanded)
%              Depth                    :   15
%              Number of atoms          :  629 (2747 expanded)
%              Number of equality atoms :  242 (1436 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2511,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f139,f417,f495,f624,f1816,f1832,f1838,f1892,f2107,f2115,f2131,f2154,f2166,f2172,f2185,f2495,f2510])).

fof(f2510,plain,
    ( ~ spl5_23
    | spl5_24 ),
    inference(avatar_contradiction_clause,[],[f2497])).

fof(f2497,plain,
    ( $false
    | ~ spl5_23
    | spl5_24 ),
    inference(unit_resulting_resolution,[],[f2184,f2184,f2494,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X2) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f70,f90,f90])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f79,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f81,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f79,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f2494,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl5_24 ),
    inference(avatar_component_clause,[],[f2492])).

fof(f2492,plain,
    ( spl5_24
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f2184,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f2182])).

fof(f2182,plain,
    ( spl5_23
  <=> r2_hidden(sK0,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f2495,plain,
    ( ~ spl5_24
    | spl5_21 ),
    inference(avatar_split_clause,[],[f2193,f2169,f2492])).

fof(f2169,plain,
    ( spl5_21
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f2193,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl5_21 ),
    inference(forward_demodulation,[],[f2189,f655])).

fof(f655,plain,(
    ! [X8,X7] : k5_xboole_0(X7,X8) = k5_xboole_0(X8,X7) ),
    inference(forward_demodulation,[],[f629,f315])).

fof(f315,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f299,f84])).

fof(f84,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f299,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f239,f143])).

fof(f143,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(global_subsumption,[],[f127,f140])).

fof(f140,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f113,f74])).

fof(f74,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f113,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f76,f77])).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f127,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f239,plain,(
    ! [X8,X9] : k5_xboole_0(X8,k5_xboole_0(X8,X9)) = k5_xboole_0(k1_xboole_0,X9) ),
    inference(superposition,[],[f83,f143])).

fof(f83,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f629,plain,(
    ! [X8,X7] : k5_xboole_0(X7,X8) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X8),X7) ),
    inference(superposition,[],[f563,f239])).

fof(f563,plain,(
    ! [X12,X11] : k5_xboole_0(k5_xboole_0(X12,X11),X12) = X11 ),
    inference(superposition,[],[f511,f511])).

fof(f511,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X3,X2)) = X3 ),
    inference(superposition,[],[f485,f315])).

fof(f485,plain,(
    ! [X17,X18] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X18,k5_xboole_0(X17,X18))) = X17 ),
    inference(forward_demodulation,[],[f453,f84])).

fof(f453,plain,(
    ! [X17,X18] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X18,k5_xboole_0(X17,X18))) = k5_xboole_0(X17,k1_xboole_0) ),
    inference(superposition,[],[f239,f244])).

fof(f244,plain,(
    ! [X12,X11] : k1_xboole_0 = k5_xboole_0(X11,k5_xboole_0(X12,k5_xboole_0(X11,X12))) ),
    inference(superposition,[],[f83,f143])).

fof(f2189,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2))
    | spl5_21 ),
    inference(superposition,[],[f2171,f691])).

fof(f691,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f664,f73])).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f664,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f82,f74])).

fof(f82,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f2171,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl5_21 ),
    inference(avatar_component_clause,[],[f2169])).

fof(f2185,plain,
    ( spl5_23
    | ~ spl5_3
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f2136,f1825,f414,f2182])).

fof(f414,plain,
    ( spl5_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1825,plain,
    ( spl5_13
  <=> r2_hidden(sK0,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f2136,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | ~ spl5_3
    | ~ spl5_13 ),
    inference(superposition,[],[f1826,f415])).

fof(f415,plain,
    ( sK0 = sK1
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f414])).

fof(f1826,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f1825])).

fof(f2172,plain,
    ( ~ spl5_21
    | spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f2133,f414,f136,f2169])).

fof(f136,plain,
    ( spl5_2
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f2133,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl5_2
    | ~ spl5_3 ),
    inference(superposition,[],[f137,f415])).

fof(f137,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f136])).

fof(f2166,plain,(
    spl5_20 ),
    inference(avatar_contradiction_clause,[],[f2156])).

fof(f2156,plain,
    ( $false
    | spl5_20 ),
    inference(unit_resulting_resolution,[],[f117,f127,f2153,f765])).

fof(f765,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1) ) ),
    inference(global_subsumption,[],[f153,f756])).

fof(f756,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_xboole_0)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f123,f113])).

fof(f123,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f66,f77])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f153,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(condensation,[],[f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(forward_demodulation,[],[f148,f143])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(X0,X0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f124,f74])).

fof(f124,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f65,f77])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2153,plain,
    ( ~ r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl5_20 ),
    inference(avatar_component_clause,[],[f2151])).

fof(f2151,plain,
    ( spl5_20
  <=> r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f117,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f55,f89])).

fof(f55,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f2154,plain,
    ( ~ spl5_20
    | ~ spl5_3
    | spl5_18 ),
    inference(avatar_split_clause,[],[f2139,f2104,f414,f2151])).

fof(f2104,plain,
    ( spl5_18
  <=> r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f2139,plain,
    ( ~ r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_3
    | spl5_18 ),
    inference(superposition,[],[f2105,f415])).

fof(f2105,plain,
    ( ~ r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl5_18 ),
    inference(avatar_component_clause,[],[f2104])).

fof(f2131,plain,
    ( ~ spl5_6
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f2126])).

fof(f2126,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f494,f117,f1831,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f1831,plain,
    ( r2_hidden(sK1,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f1829])).

fof(f1829,plain,
    ( spl5_14
  <=> r2_hidden(sK1,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f494,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f492])).

fof(f492,plain,
    ( spl5_6
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f2115,plain,
    ( spl5_3
    | ~ spl5_18 ),
    inference(avatar_contradiction_clause,[],[f2108])).

fof(f2108,plain,
    ( $false
    | spl5_3
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f416,f416,f416,f2106,f122])).

fof(f122,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f52,f89])).

fof(f52,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2106,plain,
    ( r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f2104])).

fof(f416,plain,
    ( sK0 != sK1
    | spl5_3 ),
    inference(avatar_component_clause,[],[f414])).

fof(f2107,plain,
    ( spl5_6
    | spl5_18
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f2097,f136,f2104,f492])).

fof(f2097,plain,
    ( r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | r2_hidden(sK1,sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f2091,f117])).

fof(f2091,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
        | r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | r2_hidden(X2,sK2) )
    | ~ spl5_2 ),
    inference(resolution,[],[f1853,f227])).

fof(f227,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
      | r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k3_xboole_0(X1,X2))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f63,f125])).

fof(f125,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f64,f77])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1853,plain,
    ( ! [X4] :
        ( r2_hidden(X4,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
        | r2_hidden(X4,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X4,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) )
    | ~ spl5_2 ),
    inference(superposition,[],[f62,f138])).

fof(f138,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f136])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1892,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f1884])).

fof(f1884,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f133,f121,f1848])).

fof(f1848,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X1,sK2) )
    | ~ spl5_2 ),
    inference(superposition,[],[f149,f138])).

fof(f149,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k5_xboole_0(X2,k3_xboole_0(X3,X2)))
      | ~ r2_hidden(X4,X3) ) ),
    inference(superposition,[],[f124,f73])).

fof(f121,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f53,f89])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f133,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl5_1
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1838,plain,
    ( spl5_1
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f1833])).

fof(f1833,plain,
    ( $false
    | spl5_1
    | spl5_13 ),
    inference(unit_resulting_resolution,[],[f134,f119,f1827,f63])).

fof(f1827,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f1825])).

fof(f119,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f54,f89])).

fof(f54,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f134,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f132])).

fof(f1832,plain,
    ( ~ spl5_13
    | spl5_14
    | spl5_12 ),
    inference(avatar_split_clause,[],[f1822,f1813,f1829,f1825])).

fof(f1813,plain,
    ( spl5_12
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f1822,plain,
    ( r2_hidden(sK1,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK0,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | spl5_12 ),
    inference(trivial_inequality_removal,[],[f1818])).

fof(f1818,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | r2_hidden(sK1,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK0,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | spl5_12 ),
    inference(superposition,[],[f1815,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f71,f91,f90])).

fof(f91,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f80,f90])).

fof(f80,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(f1815,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f1813])).

fof(f1816,plain,
    ( ~ spl5_12
    | spl5_2 ),
    inference(avatar_split_clause,[],[f1811,f136,f1813])).

fof(f1811,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | spl5_2 ),
    inference(forward_demodulation,[],[f1780,f655])).

fof(f1780,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | spl5_2 ),
    inference(superposition,[],[f137,f691])).

fof(f624,plain,
    ( spl5_1
    | ~ spl5_6
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f623,f136,f492,f132])).

fof(f623,plain,
    ( ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | ~ spl5_2 ),
    inference(trivial_inequality_removal,[],[f622])).

fof(f622,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f345,f138])).

fof(f345,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f93,f73])).

fof(f93,plain,
    ( ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f50,f91,f77,f90])).

fof(f50,plain,
    ( ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ( sK0 != sK1
        & ~ r2_hidden(sK1,sK2) )
      | r2_hidden(sK0,sK2)
      | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( ( sK0 = sK1
          | r2_hidden(sK1,sK2) )
        & ~ r2_hidden(sK0,sK2) )
      | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ( ( X0 != X1
            & ~ r2_hidden(X1,X2) )
          | r2_hidden(X0,X2)
          | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ( X0 = X1
              | r2_hidden(X1,X2) )
            & ~ r2_hidden(X0,X2) )
          | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( ( sK0 != sK1
          & ~ r2_hidden(sK1,sK2) )
        | r2_hidden(sK0,sK2)
        | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( ( sK0 = sK1
            | r2_hidden(sK1,sK2) )
          & ~ r2_hidden(sK0,sK2) )
        | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2)
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2)
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_zfmisc_1)).

fof(f495,plain,
    ( spl5_6
    | spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f399,f136,f414,f492])).

fof(f399,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | sK0 = sK1
    | r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f94,f73])).

fof(f94,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f49,f91,f77,f90])).

fof(f49,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK2)
    | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f417,plain,
    ( spl5_1
    | ~ spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f278,f136,f414,f132])).

fof(f278,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | sK0 != sK1
    | r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f92,f73])).

fof(f92,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f51,f91,f77,f90])).

fof(f51,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,sK2)
    | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f139,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f130,f136,f132])).

fof(f130,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f95,f73])).

fof(f95,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f48,f91,f77,f90])).

fof(f48,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:53:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (17066)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (17069)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (17067)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.51  % (17080)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (17071)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (17072)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (17079)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (17078)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (17089)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  % (17081)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (17075)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (17088)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (17083)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (17095)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (17073)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (17082)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.53  % (17068)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (17082)Refutation not found, incomplete strategy% (17082)------------------------------
% 0.22/0.53  % (17082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (17082)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (17082)Memory used [KB]: 10746
% 0.22/0.53  % (17082)Time elapsed: 0.119 s
% 0.22/0.53  % (17082)------------------------------
% 0.22/0.53  % (17082)------------------------------
% 0.22/0.53  % (17087)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (17092)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (17070)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (17091)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (17093)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (17090)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (17074)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (17085)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (17076)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (17084)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (17094)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (17077)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (17086)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 2.03/0.68  % (17069)Refutation not found, incomplete strategy% (17069)------------------------------
% 2.03/0.68  % (17069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.70  % (17069)Termination reason: Refutation not found, incomplete strategy
% 2.03/0.70  
% 2.03/0.70  % (17069)Memory used [KB]: 6268
% 2.03/0.70  % (17069)Time elapsed: 0.264 s
% 2.03/0.70  % (17069)------------------------------
% 2.03/0.70  % (17069)------------------------------
% 2.03/0.71  % (17089)Refutation found. Thanks to Tanya!
% 2.03/0.71  % SZS status Theorem for theBenchmark
% 2.03/0.71  % SZS output start Proof for theBenchmark
% 2.03/0.71  fof(f2511,plain,(
% 2.03/0.71    $false),
% 2.03/0.71    inference(avatar_sat_refutation,[],[f139,f417,f495,f624,f1816,f1832,f1838,f1892,f2107,f2115,f2131,f2154,f2166,f2172,f2185,f2495,f2510])).
% 2.03/0.71  fof(f2510,plain,(
% 2.03/0.71    ~spl5_23 | spl5_24),
% 2.03/0.71    inference(avatar_contradiction_clause,[],[f2497])).
% 2.03/0.71  fof(f2497,plain,(
% 2.03/0.71    $false | (~spl5_23 | spl5_24)),
% 2.03/0.71    inference(unit_resulting_resolution,[],[f2184,f2184,f2494,f110])).
% 2.03/0.71  fof(f110,plain,(
% 2.03/0.71    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X0,X2) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 2.03/0.71    inference(definition_unfolding,[],[f70,f90,f90])).
% 2.03/0.71  fof(f90,plain,(
% 2.03/0.71    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.03/0.71    inference(definition_unfolding,[],[f79,f89])).
% 2.03/0.71  fof(f89,plain,(
% 2.03/0.71    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.03/0.71    inference(definition_unfolding,[],[f81,f88])).
% 2.03/0.71  fof(f88,plain,(
% 2.03/0.71    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.03/0.71    inference(cnf_transformation,[],[f15])).
% 2.03/0.71  fof(f15,axiom,(
% 2.03/0.71    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.03/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.03/0.71  fof(f81,plain,(
% 2.03/0.71    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.03/0.71    inference(cnf_transformation,[],[f14])).
% 2.03/0.71  fof(f14,axiom,(
% 2.03/0.71    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.03/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.03/0.71  fof(f79,plain,(
% 2.03/0.71    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.03/0.71    inference(cnf_transformation,[],[f13])).
% 2.03/0.71  fof(f13,axiom,(
% 2.03/0.71    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.03/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.03/0.71  fof(f70,plain,(
% 2.03/0.71    ( ! [X2,X0,X1] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 2.03/0.71    inference(cnf_transformation,[],[f26])).
% 2.03/0.71  fof(f26,plain,(
% 2.03/0.71    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 2.03/0.71    inference(flattening,[],[f25])).
% 2.03/0.71  fof(f25,plain,(
% 2.03/0.71    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 2.03/0.71    inference(ennf_transformation,[],[f16])).
% 2.03/0.71  fof(f16,axiom,(
% 2.03/0.71    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 2.03/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 2.03/0.71  fof(f2494,plain,(
% 2.03/0.71    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | spl5_24),
% 2.03/0.71    inference(avatar_component_clause,[],[f2492])).
% 2.03/0.71  fof(f2492,plain,(
% 2.03/0.71    spl5_24 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 2.03/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 2.03/0.71  fof(f2184,plain,(
% 2.03/0.71    r2_hidden(sK0,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | ~spl5_23),
% 2.03/0.71    inference(avatar_component_clause,[],[f2182])).
% 2.03/0.71  fof(f2182,plain,(
% 2.03/0.71    spl5_23 <=> r2_hidden(sK0,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 2.03/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 2.03/0.71  fof(f2495,plain,(
% 2.03/0.71    ~spl5_24 | spl5_21),
% 2.03/0.71    inference(avatar_split_clause,[],[f2193,f2169,f2492])).
% 2.03/0.71  fof(f2169,plain,(
% 2.03/0.71    spl5_21 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 2.03/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 2.03/0.71  fof(f2193,plain,(
% 2.03/0.71    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | spl5_21),
% 2.03/0.71    inference(forward_demodulation,[],[f2189,f655])).
% 2.03/0.71  fof(f655,plain,(
% 2.03/0.71    ( ! [X8,X7] : (k5_xboole_0(X7,X8) = k5_xboole_0(X8,X7)) )),
% 2.03/0.71    inference(forward_demodulation,[],[f629,f315])).
% 2.03/0.71  fof(f315,plain,(
% 2.03/0.71    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.03/0.71    inference(forward_demodulation,[],[f299,f84])).
% 2.03/0.71  fof(f84,plain,(
% 2.03/0.71    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.03/0.71    inference(cnf_transformation,[],[f9])).
% 2.03/0.71  fof(f9,axiom,(
% 2.03/0.71    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.03/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.03/0.71  fof(f299,plain,(
% 2.03/0.71    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 2.03/0.71    inference(superposition,[],[f239,f143])).
% 2.03/0.71  fof(f143,plain,(
% 2.03/0.71    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.03/0.71    inference(global_subsumption,[],[f127,f140])).
% 2.03/0.71  fof(f140,plain,(
% 2.03/0.71    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X0)) )),
% 2.03/0.71    inference(superposition,[],[f113,f74])).
% 2.03/0.71  fof(f74,plain,(
% 2.03/0.71    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.03/0.71    inference(cnf_transformation,[],[f21])).
% 2.03/0.71  fof(f21,plain,(
% 2.03/0.71    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.03/0.71    inference(rectify,[],[f3])).
% 2.03/0.71  fof(f3,axiom,(
% 2.03/0.71    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.03/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.03/0.71  fof(f113,plain,(
% 2.03/0.71    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 2.03/0.71    inference(definition_unfolding,[],[f76,f77])).
% 2.03/0.71  fof(f77,plain,(
% 2.03/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.03/0.71    inference(cnf_transformation,[],[f7])).
% 2.03/0.71  fof(f7,axiom,(
% 2.03/0.71    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.03/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.03/0.71  fof(f76,plain,(
% 2.03/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.03/0.71    inference(cnf_transformation,[],[f45])).
% 2.03/0.71  fof(f45,plain,(
% 2.03/0.71    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.03/0.71    inference(nnf_transformation,[],[f6])).
% 2.03/0.71  fof(f6,axiom,(
% 2.03/0.71    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.03/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.03/0.71  fof(f127,plain,(
% 2.03/0.71    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.03/0.71    inference(equality_resolution,[],[f86])).
% 2.03/0.71  fof(f86,plain,(
% 2.03/0.71    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.03/0.71    inference(cnf_transformation,[],[f47])).
% 2.03/0.71  fof(f47,plain,(
% 2.03/0.71    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.03/0.71    inference(flattening,[],[f46])).
% 2.03/0.71  fof(f46,plain,(
% 2.03/0.71    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.03/0.71    inference(nnf_transformation,[],[f5])).
% 2.03/0.71  fof(f5,axiom,(
% 2.03/0.71    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.03/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.03/0.71  fof(f239,plain,(
% 2.03/0.71    ( ! [X8,X9] : (k5_xboole_0(X8,k5_xboole_0(X8,X9)) = k5_xboole_0(k1_xboole_0,X9)) )),
% 2.03/0.71    inference(superposition,[],[f83,f143])).
% 2.03/0.71  fof(f83,plain,(
% 2.03/0.71    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.03/0.71    inference(cnf_transformation,[],[f10])).
% 2.03/0.71  fof(f10,axiom,(
% 2.03/0.71    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.03/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.03/0.71  fof(f629,plain,(
% 2.03/0.71    ( ! [X8,X7] : (k5_xboole_0(X7,X8) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X8),X7)) )),
% 2.03/0.71    inference(superposition,[],[f563,f239])).
% 2.03/0.71  fof(f563,plain,(
% 2.03/0.71    ( ! [X12,X11] : (k5_xboole_0(k5_xboole_0(X12,X11),X12) = X11) )),
% 2.03/0.71    inference(superposition,[],[f511,f511])).
% 2.03/0.71  fof(f511,plain,(
% 2.03/0.71    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X3,X2)) = X3) )),
% 2.03/0.71    inference(superposition,[],[f485,f315])).
% 2.03/0.71  fof(f485,plain,(
% 2.03/0.71    ( ! [X17,X18] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X18,k5_xboole_0(X17,X18))) = X17) )),
% 2.03/0.71    inference(forward_demodulation,[],[f453,f84])).
% 2.03/0.71  fof(f453,plain,(
% 2.03/0.71    ( ! [X17,X18] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X18,k5_xboole_0(X17,X18))) = k5_xboole_0(X17,k1_xboole_0)) )),
% 2.03/0.71    inference(superposition,[],[f239,f244])).
% 2.03/0.71  fof(f244,plain,(
% 2.03/0.71    ( ! [X12,X11] : (k1_xboole_0 = k5_xboole_0(X11,k5_xboole_0(X12,k5_xboole_0(X11,X12)))) )),
% 2.03/0.71    inference(superposition,[],[f83,f143])).
% 2.03/0.71  fof(f2189,plain,(
% 2.03/0.71    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)) | spl5_21),
% 2.03/0.71    inference(superposition,[],[f2171,f691])).
% 2.03/0.71  fof(f691,plain,(
% 2.03/0.71    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.03/0.71    inference(forward_demodulation,[],[f664,f73])).
% 2.03/0.71  fof(f73,plain,(
% 2.03/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.03/0.71    inference(cnf_transformation,[],[f1])).
% 2.03/0.71  fof(f1,axiom,(
% 2.03/0.71    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.03/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.03/0.71  fof(f664,plain,(
% 2.03/0.71    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0)) )),
% 2.03/0.71    inference(superposition,[],[f82,f74])).
% 2.03/0.71  fof(f82,plain,(
% 2.03/0.71    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 2.03/0.71    inference(cnf_transformation,[],[f8])).
% 2.03/0.71  fof(f8,axiom,(
% 2.03/0.71    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 2.03/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 2.03/0.71  fof(f2171,plain,(
% 2.03/0.71    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | spl5_21),
% 2.03/0.71    inference(avatar_component_clause,[],[f2169])).
% 2.03/0.71  fof(f2185,plain,(
% 2.03/0.71    spl5_23 | ~spl5_3 | ~spl5_13),
% 2.03/0.71    inference(avatar_split_clause,[],[f2136,f1825,f414,f2182])).
% 2.03/0.71  fof(f414,plain,(
% 2.03/0.71    spl5_3 <=> sK0 = sK1),
% 2.03/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.03/0.71  fof(f1825,plain,(
% 2.03/0.71    spl5_13 <=> r2_hidden(sK0,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 2.03/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 2.03/0.71  fof(f2136,plain,(
% 2.03/0.71    r2_hidden(sK0,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | (~spl5_3 | ~spl5_13)),
% 2.03/0.71    inference(superposition,[],[f1826,f415])).
% 2.03/0.71  fof(f415,plain,(
% 2.03/0.71    sK0 = sK1 | ~spl5_3),
% 2.03/0.71    inference(avatar_component_clause,[],[f414])).
% 2.03/0.71  fof(f1826,plain,(
% 2.03/0.71    r2_hidden(sK0,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~spl5_13),
% 2.03/0.71    inference(avatar_component_clause,[],[f1825])).
% 2.03/0.71  fof(f2172,plain,(
% 2.03/0.71    ~spl5_21 | spl5_2 | ~spl5_3),
% 2.03/0.71    inference(avatar_split_clause,[],[f2133,f414,f136,f2169])).
% 2.03/0.71  fof(f136,plain,(
% 2.03/0.71    spl5_2 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 2.03/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.03/0.71  fof(f2133,plain,(
% 2.03/0.71    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | (spl5_2 | ~spl5_3)),
% 2.03/0.71    inference(superposition,[],[f137,f415])).
% 2.03/0.71  fof(f137,plain,(
% 2.03/0.71    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | spl5_2),
% 2.03/0.71    inference(avatar_component_clause,[],[f136])).
% 2.03/0.71  fof(f2166,plain,(
% 2.03/0.71    spl5_20),
% 2.03/0.71    inference(avatar_contradiction_clause,[],[f2156])).
% 2.03/0.71  fof(f2156,plain,(
% 2.03/0.71    $false | spl5_20),
% 2.03/0.71    inference(unit_resulting_resolution,[],[f117,f127,f2153,f765])).
% 2.03/0.71  fof(f765,plain,(
% 2.03/0.71    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(X2,X1)) )),
% 2.03/0.71    inference(global_subsumption,[],[f153,f756])).
% 2.03/0.71  fof(f756,plain,(
% 2.03/0.71    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_xboole_0) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 2.03/0.71    inference(superposition,[],[f123,f113])).
% 2.03/0.71  fof(f123,plain,(
% 2.03/0.71    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.03/0.71    inference(equality_resolution,[],[f107])).
% 2.03/0.71  fof(f107,plain,(
% 2.03/0.71    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.03/0.71    inference(definition_unfolding,[],[f66,f77])).
% 2.03/0.71  fof(f66,plain,(
% 2.03/0.71    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.03/0.71    inference(cnf_transformation,[],[f44])).
% 2.03/0.71  fof(f44,plain,(
% 2.03/0.71    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.03/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).
% 2.03/0.71  fof(f43,plain,(
% 2.03/0.71    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.03/0.71    introduced(choice_axiom,[])).
% 2.03/0.71  fof(f42,plain,(
% 2.03/0.71    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.03/0.71    inference(rectify,[],[f41])).
% 2.03/0.71  fof(f41,plain,(
% 2.03/0.71    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.03/0.71    inference(flattening,[],[f40])).
% 2.03/0.71  fof(f40,plain,(
% 2.03/0.71    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.03/0.71    inference(nnf_transformation,[],[f2])).
% 2.03/0.71  fof(f2,axiom,(
% 2.03/0.71    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.03/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.03/0.71  fof(f153,plain,(
% 2.03/0.71    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 2.03/0.71    inference(condensation,[],[f152])).
% 2.03/0.71  fof(f152,plain,(
% 2.03/0.71    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 2.03/0.71    inference(forward_demodulation,[],[f148,f143])).
% 2.03/0.71  fof(f148,plain,(
% 2.03/0.71    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,X0)) | ~r2_hidden(X1,X0)) )),
% 2.03/0.71    inference(superposition,[],[f124,f74])).
% 2.03/0.71  fof(f124,plain,(
% 2.03/0.71    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 2.03/0.71    inference(equality_resolution,[],[f108])).
% 2.03/0.71  fof(f108,plain,(
% 2.03/0.71    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.03/0.71    inference(definition_unfolding,[],[f65,f77])).
% 2.03/0.71  fof(f65,plain,(
% 2.03/0.71    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.03/0.71    inference(cnf_transformation,[],[f44])).
% 2.03/0.71  fof(f2153,plain,(
% 2.03/0.71    ~r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl5_20),
% 2.03/0.71    inference(avatar_component_clause,[],[f2151])).
% 2.03/0.71  fof(f2151,plain,(
% 2.03/0.71    spl5_20 <=> r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 2.03/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 2.03/0.71  fof(f117,plain,(
% 2.03/0.71    ( ! [X0,X5,X1] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5))) )),
% 2.03/0.71    inference(equality_resolution,[],[f116])).
% 2.03/0.71  fof(f116,plain,(
% 2.03/0.71    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X5) != X3) )),
% 2.03/0.71    inference(equality_resolution,[],[f100])).
% 2.03/0.71  fof(f100,plain,(
% 2.03/0.71    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 2.03/0.71    inference(definition_unfolding,[],[f55,f89])).
% 2.03/0.71  fof(f55,plain,(
% 2.03/0.71    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.03/0.71    inference(cnf_transformation,[],[f38])).
% 2.03/0.71  fof(f38,plain,(
% 2.03/0.71    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.03/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 2.03/0.71  fof(f37,plain,(
% 2.03/0.71    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 2.03/0.71    introduced(choice_axiom,[])).
% 2.03/0.71  fof(f36,plain,(
% 2.03/0.71    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.03/0.71    inference(rectify,[],[f35])).
% 2.03/0.71  fof(f35,plain,(
% 2.03/0.71    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.03/0.71    inference(flattening,[],[f34])).
% 2.03/0.71  fof(f34,plain,(
% 2.03/0.71    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.03/0.71    inference(nnf_transformation,[],[f23])).
% 2.03/0.71  fof(f23,plain,(
% 2.03/0.71    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.03/0.71    inference(ennf_transformation,[],[f11])).
% 2.03/0.71  fof(f11,axiom,(
% 2.03/0.71    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.03/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 2.03/0.71  fof(f2154,plain,(
% 2.03/0.71    ~spl5_20 | ~spl5_3 | spl5_18),
% 2.03/0.71    inference(avatar_split_clause,[],[f2139,f2104,f414,f2151])).
% 2.03/0.71  fof(f2104,plain,(
% 2.03/0.71    spl5_18 <=> r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 2.03/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 2.03/0.71  fof(f2139,plain,(
% 2.03/0.71    ~r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | (~spl5_3 | spl5_18)),
% 2.03/0.71    inference(superposition,[],[f2105,f415])).
% 2.03/0.71  fof(f2105,plain,(
% 2.03/0.71    ~r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl5_18),
% 2.03/0.71    inference(avatar_component_clause,[],[f2104])).
% 2.03/0.71  fof(f2131,plain,(
% 2.03/0.71    ~spl5_6 | ~spl5_14),
% 2.03/0.71    inference(avatar_contradiction_clause,[],[f2126])).
% 2.03/0.71  fof(f2126,plain,(
% 2.03/0.71    $false | (~spl5_6 | ~spl5_14)),
% 2.03/0.71    inference(unit_resulting_resolution,[],[f494,f117,f1831,f61])).
% 2.03/0.71  fof(f61,plain,(
% 2.03/0.71    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 2.03/0.71    inference(cnf_transformation,[],[f39])).
% 2.03/0.71  fof(f39,plain,(
% 2.03/0.71    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 2.03/0.71    inference(nnf_transformation,[],[f24])).
% 2.03/0.71  fof(f24,plain,(
% 2.03/0.71    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.03/0.71    inference(ennf_transformation,[],[f4])).
% 2.03/0.71  fof(f4,axiom,(
% 2.03/0.71    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 2.03/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 2.03/0.71  fof(f1831,plain,(
% 2.03/0.71    r2_hidden(sK1,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~spl5_14),
% 2.03/0.71    inference(avatar_component_clause,[],[f1829])).
% 2.03/0.71  fof(f1829,plain,(
% 2.03/0.71    spl5_14 <=> r2_hidden(sK1,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 2.03/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 2.03/0.71  fof(f494,plain,(
% 2.03/0.71    r2_hidden(sK1,sK2) | ~spl5_6),
% 2.03/0.71    inference(avatar_component_clause,[],[f492])).
% 2.03/0.71  fof(f492,plain,(
% 2.03/0.71    spl5_6 <=> r2_hidden(sK1,sK2)),
% 2.03/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.03/0.71  fof(f2115,plain,(
% 2.03/0.71    spl5_3 | ~spl5_18),
% 2.03/0.71    inference(avatar_contradiction_clause,[],[f2108])).
% 2.03/0.71  fof(f2108,plain,(
% 2.03/0.71    $false | (spl5_3 | ~spl5_18)),
% 2.03/0.71    inference(unit_resulting_resolution,[],[f416,f416,f416,f2106,f122])).
% 2.03/0.71  fof(f122,plain,(
% 2.03/0.71    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 2.03/0.71    inference(equality_resolution,[],[f103])).
% 2.03/0.71  fof(f103,plain,(
% 2.03/0.71    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 2.03/0.71    inference(definition_unfolding,[],[f52,f89])).
% 2.03/0.71  fof(f52,plain,(
% 2.03/0.71    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.03/0.71    inference(cnf_transformation,[],[f38])).
% 2.03/0.71  fof(f2106,plain,(
% 2.03/0.71    r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl5_18),
% 2.03/0.71    inference(avatar_component_clause,[],[f2104])).
% 2.03/0.71  fof(f416,plain,(
% 2.03/0.71    sK0 != sK1 | spl5_3),
% 2.03/0.71    inference(avatar_component_clause,[],[f414])).
% 2.03/0.71  fof(f2107,plain,(
% 2.03/0.71    spl5_6 | spl5_18 | ~spl5_2),
% 2.03/0.71    inference(avatar_split_clause,[],[f2097,f136,f2104,f492])).
% 2.03/0.71  fof(f2097,plain,(
% 2.03/0.71    r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK1,sK2) | ~spl5_2),
% 2.03/0.71    inference(resolution,[],[f2091,f117])).
% 2.03/0.71  fof(f2091,plain,(
% 2.03/0.71    ( ! [X2] : (~r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(X2,sK2)) ) | ~spl5_2),
% 2.03/0.71    inference(resolution,[],[f1853,f227])).
% 2.03/0.71  fof(f227,plain,(
% 2.03/0.71    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,X2)) | r2_hidden(X0,X1)) )),
% 2.03/0.71    inference(duplicate_literal_removal,[],[f213])).
% 2.03/0.71  fof(f213,plain,(
% 2.03/0.71    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k3_xboole_0(X1,X2)) | r2_hidden(X0,X1)) )),
% 2.03/0.71    inference(resolution,[],[f63,f125])).
% 2.03/0.71  fof(f125,plain,(
% 2.03/0.71    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X0)) )),
% 2.03/0.71    inference(equality_resolution,[],[f109])).
% 2.03/0.71  fof(f109,plain,(
% 2.03/0.71    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.03/0.71    inference(definition_unfolding,[],[f64,f77])).
% 2.03/0.71  fof(f64,plain,(
% 2.03/0.71    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.03/0.71    inference(cnf_transformation,[],[f44])).
% 2.03/0.71  fof(f63,plain,(
% 2.03/0.71    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 2.03/0.71    inference(cnf_transformation,[],[f39])).
% 2.03/0.71  fof(f1853,plain,(
% 2.03/0.71    ( ! [X4] : (r2_hidden(X4,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | r2_hidden(X4,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X4,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ) | ~spl5_2),
% 2.03/0.71    inference(superposition,[],[f62,f138])).
% 2.03/0.71  fof(f138,plain,(
% 2.03/0.71    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~spl5_2),
% 2.03/0.71    inference(avatar_component_clause,[],[f136])).
% 2.03/0.71  fof(f62,plain,(
% 2.03/0.71    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 2.03/0.71    inference(cnf_transformation,[],[f39])).
% 2.03/0.71  fof(f1892,plain,(
% 2.03/0.71    ~spl5_1 | ~spl5_2),
% 2.03/0.71    inference(avatar_contradiction_clause,[],[f1884])).
% 2.03/0.71  fof(f1884,plain,(
% 2.03/0.71    $false | (~spl5_1 | ~spl5_2)),
% 2.03/0.71    inference(unit_resulting_resolution,[],[f133,f121,f1848])).
% 2.03/0.71  fof(f1848,plain,(
% 2.03/0.71    ( ! [X1] : (~r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X1,sK2)) ) | ~spl5_2),
% 2.03/0.71    inference(superposition,[],[f149,f138])).
% 2.03/0.71  fof(f149,plain,(
% 2.03/0.71    ( ! [X4,X2,X3] : (~r2_hidden(X4,k5_xboole_0(X2,k3_xboole_0(X3,X2))) | ~r2_hidden(X4,X3)) )),
% 2.03/0.71    inference(superposition,[],[f124,f73])).
% 2.03/0.71  fof(f121,plain,(
% 2.03/0.71    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 2.03/0.71    inference(equality_resolution,[],[f120])).
% 2.03/0.71  fof(f120,plain,(
% 2.03/0.71    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 2.03/0.71    inference(equality_resolution,[],[f102])).
% 2.03/0.71  fof(f102,plain,(
% 2.03/0.71    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 2.03/0.71    inference(definition_unfolding,[],[f53,f89])).
% 2.03/0.71  fof(f53,plain,(
% 2.03/0.71    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.03/0.71    inference(cnf_transformation,[],[f38])).
% 2.03/0.71  fof(f133,plain,(
% 2.03/0.71    r2_hidden(sK0,sK2) | ~spl5_1),
% 2.03/0.71    inference(avatar_component_clause,[],[f132])).
% 2.03/0.71  fof(f132,plain,(
% 2.03/0.71    spl5_1 <=> r2_hidden(sK0,sK2)),
% 2.03/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.03/0.71  fof(f1838,plain,(
% 2.03/0.71    spl5_1 | spl5_13),
% 2.03/0.71    inference(avatar_contradiction_clause,[],[f1833])).
% 2.03/0.71  fof(f1833,plain,(
% 2.03/0.71    $false | (spl5_1 | spl5_13)),
% 2.03/0.71    inference(unit_resulting_resolution,[],[f134,f119,f1827,f63])).
% 2.03/0.71  fof(f1827,plain,(
% 2.03/0.71    ~r2_hidden(sK0,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | spl5_13),
% 2.03/0.71    inference(avatar_component_clause,[],[f1825])).
% 2.03/0.71  fof(f119,plain,(
% 2.03/0.71    ( ! [X2,X0,X5] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X5,X2))) )),
% 2.03/0.71    inference(equality_resolution,[],[f118])).
% 2.03/0.71  fof(f118,plain,(
% 2.03/0.71    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X5,X2) != X3) )),
% 2.03/0.71    inference(equality_resolution,[],[f101])).
% 2.03/0.71  fof(f101,plain,(
% 2.03/0.71    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 2.03/0.71    inference(definition_unfolding,[],[f54,f89])).
% 2.03/0.71  fof(f54,plain,(
% 2.03/0.71    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.03/0.71    inference(cnf_transformation,[],[f38])).
% 2.03/0.71  fof(f134,plain,(
% 2.03/0.71    ~r2_hidden(sK0,sK2) | spl5_1),
% 2.03/0.71    inference(avatar_component_clause,[],[f132])).
% 2.03/0.71  fof(f1832,plain,(
% 2.03/0.71    ~spl5_13 | spl5_14 | spl5_12),
% 2.03/0.71    inference(avatar_split_clause,[],[f1822,f1813,f1829,f1825])).
% 2.03/0.71  fof(f1813,plain,(
% 2.03/0.71    spl5_12 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 2.03/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 2.03/0.71  fof(f1822,plain,(
% 2.03/0.71    r2_hidden(sK1,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK0,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | spl5_12),
% 2.03/0.71    inference(trivial_inequality_removal,[],[f1818])).
% 2.03/0.71  fof(f1818,plain,(
% 2.03/0.71    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | r2_hidden(sK1,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK0,k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | spl5_12),
% 2.03/0.71    inference(superposition,[],[f1815,f112])).
% 2.03/0.71  fof(f112,plain,(
% 2.03/0.71    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1) | r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 2.03/0.71    inference(definition_unfolding,[],[f71,f91,f90])).
% 2.03/0.71  fof(f91,plain,(
% 2.03/0.71    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.03/0.71    inference(definition_unfolding,[],[f80,f90])).
% 2.03/0.71  fof(f80,plain,(
% 2.03/0.71    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.03/0.71    inference(cnf_transformation,[],[f12])).
% 2.03/0.71  fof(f12,axiom,(
% 2.03/0.71    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.03/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.03/0.71  fof(f71,plain,(
% 2.03/0.71    ( ! [X2,X0,X1] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 2.03/0.71    inference(cnf_transformation,[],[f28])).
% 2.03/0.71  fof(f28,plain,(
% 2.03/0.71    ! [X0,X1,X2] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 2.03/0.71    inference(flattening,[],[f27])).
% 2.03/0.71  fof(f27,plain,(
% 2.03/0.71    ! [X0,X1,X2] : ((k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))) | ~r2_hidden(X0,X1))),
% 2.03/0.71    inference(ennf_transformation,[],[f17])).
% 2.03/0.71  fof(f17,axiom,(
% 2.03/0.71    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 2.03/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).
% 2.03/0.71  fof(f1815,plain,(
% 2.03/0.71    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | spl5_12),
% 2.03/0.71    inference(avatar_component_clause,[],[f1813])).
% 2.03/0.71  fof(f1816,plain,(
% 2.03/0.71    ~spl5_12 | spl5_2),
% 2.03/0.71    inference(avatar_split_clause,[],[f1811,f136,f1813])).
% 2.03/0.71  fof(f1811,plain,(
% 2.03/0.71    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | spl5_2),
% 2.03/0.71    inference(forward_demodulation,[],[f1780,f655])).
% 2.03/0.71  fof(f1780,plain,(
% 2.03/0.71    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | spl5_2),
% 2.03/0.71    inference(superposition,[],[f137,f691])).
% 2.03/0.71  fof(f624,plain,(
% 2.03/0.71    spl5_1 | ~spl5_6 | ~spl5_2),
% 2.03/0.71    inference(avatar_split_clause,[],[f623,f136,f492,f132])).
% 2.03/0.71  fof(f623,plain,(
% 2.03/0.71    ~r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | ~spl5_2),
% 2.03/0.71    inference(trivial_inequality_removal,[],[f622])).
% 2.03/0.71  fof(f622,plain,(
% 2.03/0.71    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | ~spl5_2),
% 2.03/0.71    inference(forward_demodulation,[],[f345,f138])).
% 2.03/0.71  fof(f345,plain,(
% 2.03/0.71    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2)),
% 2.03/0.71    inference(forward_demodulation,[],[f93,f73])).
% 2.03/0.71  fof(f93,plain,(
% 2.03/0.71    ~r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 2.03/0.71    inference(definition_unfolding,[],[f50,f91,f77,f90])).
% 2.03/0.71  fof(f50,plain,(
% 2.03/0.71    ~r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.03/0.71    inference(cnf_transformation,[],[f33])).
% 2.03/0.71  fof(f33,plain,(
% 2.03/0.71    ((sK0 != sK1 & ~r2_hidden(sK1,sK2)) | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & (((sK0 = sK1 | r2_hidden(sK1,sK2)) & ~r2_hidden(sK0,sK2)) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.03/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f32])).
% 2.03/0.71  fof(f32,plain,(
% 2.03/0.71    ? [X0,X1,X2] : (((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2))) => (((sK0 != sK1 & ~r2_hidden(sK1,sK2)) | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & (((sK0 = sK1 | r2_hidden(sK1,sK2)) & ~r2_hidden(sK0,sK2)) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 2.03/0.71    introduced(choice_axiom,[])).
% 2.03/0.71  fof(f31,plain,(
% 2.03/0.71    ? [X0,X1,X2] : (((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 2.03/0.71    inference(flattening,[],[f30])).
% 2.03/0.71  fof(f30,plain,(
% 2.03/0.71    ? [X0,X1,X2] : ((((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 2.03/0.71    inference(nnf_transformation,[],[f22])).
% 2.03/0.71  fof(f22,plain,(
% 2.03/0.71    ? [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 2.03/0.71    inference(ennf_transformation,[],[f20])).
% 2.03/0.71  fof(f20,negated_conjecture,(
% 2.03/0.71    ~! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 2.03/0.71    inference(negated_conjecture,[],[f19])).
% 2.03/0.71  fof(f19,conjecture,(
% 2.03/0.71    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 2.03/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_zfmisc_1)).
% 2.03/0.71  fof(f495,plain,(
% 2.03/0.71    spl5_6 | spl5_3 | spl5_2),
% 2.03/0.71    inference(avatar_split_clause,[],[f399,f136,f414,f492])).
% 2.03/0.71  fof(f399,plain,(
% 2.03/0.71    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | sK0 = sK1 | r2_hidden(sK1,sK2)),
% 2.03/0.71    inference(forward_demodulation,[],[f94,f73])).
% 2.03/0.71  fof(f94,plain,(
% 2.03/0.71    sK0 = sK1 | r2_hidden(sK1,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 2.03/0.71    inference(definition_unfolding,[],[f49,f91,f77,f90])).
% 2.03/0.71  fof(f49,plain,(
% 2.03/0.71    sK0 = sK1 | r2_hidden(sK1,sK2) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.03/0.71    inference(cnf_transformation,[],[f33])).
% 2.03/0.71  fof(f417,plain,(
% 2.03/0.71    spl5_1 | ~spl5_3 | ~spl5_2),
% 2.03/0.71    inference(avatar_split_clause,[],[f278,f136,f414,f132])).
% 2.03/0.71  fof(f278,plain,(
% 2.03/0.71    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | sK0 != sK1 | r2_hidden(sK0,sK2)),
% 2.03/0.71    inference(forward_demodulation,[],[f92,f73])).
% 2.03/0.71  fof(f92,plain,(
% 2.03/0.71    sK0 != sK1 | r2_hidden(sK0,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 2.03/0.71    inference(definition_unfolding,[],[f51,f91,f77,f90])).
% 2.03/0.71  fof(f51,plain,(
% 2.03/0.71    sK0 != sK1 | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.03/0.71    inference(cnf_transformation,[],[f33])).
% 2.03/0.71  fof(f139,plain,(
% 2.03/0.71    ~spl5_1 | spl5_2),
% 2.03/0.71    inference(avatar_split_clause,[],[f130,f136,f132])).
% 2.03/0.71  fof(f130,plain,(
% 2.03/0.71    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK0,sK2)),
% 2.03/0.71    inference(forward_demodulation,[],[f95,f73])).
% 2.03/0.71  fof(f95,plain,(
% 2.03/0.71    ~r2_hidden(sK0,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 2.03/0.71    inference(definition_unfolding,[],[f48,f91,f77,f90])).
% 2.03/0.71  fof(f48,plain,(
% 2.03/0.71    ~r2_hidden(sK0,sK2) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.03/0.71    inference(cnf_transformation,[],[f33])).
% 2.03/0.71  % SZS output end Proof for theBenchmark
% 2.03/0.71  % (17089)------------------------------
% 2.03/0.71  % (17089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.71  % (17089)Termination reason: Refutation
% 2.03/0.71  
% 2.03/0.71  % (17089)Memory used [KB]: 12537
% 2.03/0.71  % (17089)Time elapsed: 0.258 s
% 2.03/0.71  % (17089)------------------------------
% 2.03/0.71  % (17089)------------------------------
% 2.03/0.71  % (17065)Success in time 0.346 s
%------------------------------------------------------------------------------
