%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:01 EST 2020

% Result     : Theorem 2.24s
% Output     : Refutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 190 expanded)
%              Number of leaves         :   29 (  77 expanded)
%              Depth                    :    8
%              Number of atoms          :  257 ( 497 expanded)
%              Number of equality atoms :  135 ( 330 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f548,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f70,f79,f85,f102,f120,f130,f176,f218,f299,f327,f447,f480,f512,f516,f547])).

fof(f547,plain,
    ( ~ spl3_10
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f544,f72,f139])).

fof(f139,plain,
    ( spl3_10
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f72,plain,
    ( spl3_4
  <=> sK1 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f544,plain,
    ( sK1 != sK2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f543,f73])).

fof(f73,plain,
    ( sK1 = k1_tarski(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f543,plain,
    ( sK2 != k1_tarski(sK0)
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f35,f73])).

fof(f35,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f30])).

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

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f516,plain,
    ( k5_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(sK1,sK2)
    | sK2 != k3_xboole_0(sK1,sK2)
    | k3_xboole_0(sK1,sK2) != k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)
    | sK2 = k5_xboole_0(k1_xboole_0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f512,plain,
    ( spl3_10
    | ~ spl3_31 ),
    inference(avatar_contradiction_clause,[],[f511])).

fof(f511,plain,
    ( $false
    | spl3_10
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f510,f141])).

fof(f141,plain,
    ( sK1 != sK2
    | spl3_10 ),
    inference(avatar_component_clause,[],[f139])).

fof(f510,plain,
    ( sK1 = sK2
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f503,f87])).

fof(f87,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f49,f41])).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f503,plain,
    ( sK2 = k5_xboole_0(k1_xboole_0,sK1)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f501])).

fof(f501,plain,
    ( spl3_31
  <=> sK2 = k5_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f480,plain,
    ( spl3_5
    | ~ spl3_23 ),
    inference(avatar_contradiction_clause,[],[f479])).

fof(f479,plain,
    ( $false
    | spl3_5
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f478,f78])).

fof(f78,plain,
    ( k1_xboole_0 != sK2
    | spl3_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f478,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f468,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f468,plain,
    ( sK2 = k5_xboole_0(sK1,sK1)
    | ~ spl3_23 ),
    inference(superposition,[],[f213,f446])).

fof(f446,plain,
    ( sK1 = k5_xboole_0(sK1,sK2)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f444])).

fof(f444,plain,
    ( spl3_23
  <=> sK1 = k5_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f213,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f189,f87])).

fof(f189,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f48,f42])).

fof(f48,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f447,plain,
    ( spl3_22
    | spl3_23
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f328,f324,f72,f444,f440])).

fof(f440,plain,
    ( spl3_22
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f324,plain,
    ( spl3_18
  <=> k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f328,plain,
    ( sK1 = k5_xboole_0(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(superposition,[],[f326,f149])).

fof(f149,plain,
    ( ! [X0] :
        ( sK1 = k4_xboole_0(sK1,X0)
        | k1_xboole_0 = k4_xboole_0(sK1,X0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f137,f53])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f137,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k1_xboole_0 = X0
        | sK1 = X0 )
    | ~ spl3_4 ),
    inference(superposition,[],[f38,f73])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f326,plain,
    ( k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK2)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f324])).

fof(f327,plain,
    ( spl3_18
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f301,f283,f324])).

fof(f283,plain,
    ( spl3_14
  <=> sK2 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f301,plain,
    ( k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK2)
    | ~ spl3_14 ),
    inference(superposition,[],[f50,f285])).

fof(f285,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f283])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f299,plain,
    ( spl3_14
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f276,f183,f283])).

fof(f183,plain,
    ( spl3_12
  <=> k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f276,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl3_12 ),
    inference(superposition,[],[f185,f213])).

fof(f185,plain,
    ( k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f183])).

fof(f218,plain,
    ( spl3_12
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f181,f173,f183])).

fof(f173,plain,
    ( spl3_11
  <=> k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f181,plain,
    ( k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ spl3_11 ),
    inference(superposition,[],[f49,f175])).

fof(f175,plain,
    ( k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f173])).

fof(f176,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f168,f72,f58,f173])).

fof(f58,plain,
    ( spl3_1
  <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f168,plain,
    ( k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f163,f73])).

fof(f163,plain,
    ( k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0))
    | ~ spl3_1 ),
    inference(superposition,[],[f44,f60])).

fof(f60,plain,
    ( k1_tarski(sK0) = k2_xboole_0(sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f130,plain,
    ( ~ spl3_2
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | ~ spl3_2
    | spl3_7 ),
    inference(subsumption_resolution,[],[f126,f107])).

fof(f107,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f53,f106])).

fof(f106,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f103,f42])).

fof(f103,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f50,f51])).

fof(f51,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f126,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl3_2
    | spl3_7 ),
    inference(superposition,[],[f101,f64])).

fof(f64,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f101,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl3_7
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f120,plain,
    ( spl3_2
    | spl3_4
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl3_2
    | spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f118,f74])).

fof(f74,plain,
    ( sK1 != k1_tarski(sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f118,plain,
    ( sK1 = k1_tarski(sK0)
    | spl3_2
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f116,f65])).

fof(f65,plain,
    ( k1_xboole_0 != sK1
    | spl3_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f116,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k1_tarski(sK0)
    | ~ spl3_6 ),
    inference(resolution,[],[f38,f84])).

fof(f84,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_6
  <=> r1_tarski(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f102,plain,
    ( ~ spl3_7
    | spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f95,f58,f67,f99])).

fof(f67,plain,
    ( spl3_3
  <=> sK2 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f95,plain,
    ( sK2 = k1_tarski(sK0)
    | ~ r1_tarski(sK1,sK2)
    | ~ spl3_1 ),
    inference(superposition,[],[f43,f60])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f85,plain,
    ( spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f80,f58,f82])).

fof(f80,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl3_1 ),
    inference(superposition,[],[f45,f60])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f79,plain,
    ( ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f37,f76,f72])).

fof(f37,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f36,f67,f63])).

fof(f36,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f34,f58])).

fof(f34,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:12:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (8418)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.50  % (8424)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (8440)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (8440)Refutation not found, incomplete strategy% (8440)------------------------------
% 0.22/0.51  % (8440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (8440)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (8440)Memory used [KB]: 10746
% 0.22/0.51  % (8440)Time elapsed: 0.097 s
% 0.22/0.51  % (8440)------------------------------
% 0.22/0.51  % (8440)------------------------------
% 0.22/0.52  % (8431)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (8422)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (8419)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (8420)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (8433)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (8433)Refutation not found, incomplete strategy% (8433)------------------------------
% 0.22/0.53  % (8433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (8433)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (8433)Memory used [KB]: 6140
% 0.22/0.53  % (8433)Time elapsed: 0.002 s
% 0.22/0.53  % (8433)------------------------------
% 0.22/0.53  % (8433)------------------------------
% 0.22/0.54  % (8446)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (8442)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (8421)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (8423)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (8443)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (8425)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (8429)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (8427)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (8429)Refutation not found, incomplete strategy% (8429)------------------------------
% 0.22/0.55  % (8429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (8429)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (8429)Memory used [KB]: 10618
% 0.22/0.55  % (8429)Time elapsed: 0.132 s
% 0.22/0.55  % (8429)------------------------------
% 0.22/0.55  % (8429)------------------------------
% 0.22/0.55  % (8426)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (8434)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (8445)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (8439)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (8444)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (8437)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (8436)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (8430)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (8428)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (8435)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (8428)Refutation not found, incomplete strategy% (8428)------------------------------
% 0.22/0.56  % (8428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (8428)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (8428)Memory used [KB]: 10618
% 0.22/0.56  % (8428)Time elapsed: 0.148 s
% 0.22/0.56  % (8428)------------------------------
% 0.22/0.56  % (8428)------------------------------
% 0.22/0.56  % (8435)Refutation not found, incomplete strategy% (8435)------------------------------
% 0.22/0.56  % (8435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (8435)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (8435)Memory used [KB]: 10618
% 0.22/0.56  % (8435)Time elapsed: 0.142 s
% 0.22/0.56  % (8435)------------------------------
% 0.22/0.56  % (8435)------------------------------
% 0.22/0.56  % (8438)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.57  % (8441)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.58  % (8432)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.58  % (8447)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.82/0.62  % (8453)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.24/0.66  % (8458)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.24/0.68  % (8455)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.24/0.68  % (8454)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.24/0.69  % (8458)Refutation found. Thanks to Tanya!
% 2.24/0.69  % SZS status Theorem for theBenchmark
% 2.24/0.70  % SZS output start Proof for theBenchmark
% 2.24/0.70  fof(f548,plain,(
% 2.24/0.70    $false),
% 2.24/0.70    inference(avatar_sat_refutation,[],[f61,f70,f79,f85,f102,f120,f130,f176,f218,f299,f327,f447,f480,f512,f516,f547])).
% 2.24/0.70  fof(f547,plain,(
% 2.24/0.70    ~spl3_10 | ~spl3_4),
% 2.24/0.70    inference(avatar_split_clause,[],[f544,f72,f139])).
% 2.24/0.70  fof(f139,plain,(
% 2.24/0.70    spl3_10 <=> sK1 = sK2),
% 2.24/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.24/0.70  fof(f72,plain,(
% 2.24/0.70    spl3_4 <=> sK1 = k1_tarski(sK0)),
% 2.24/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.24/0.70  fof(f544,plain,(
% 2.24/0.70    sK1 != sK2 | ~spl3_4),
% 2.24/0.70    inference(forward_demodulation,[],[f543,f73])).
% 2.24/0.70  fof(f73,plain,(
% 2.24/0.70    sK1 = k1_tarski(sK0) | ~spl3_4),
% 2.24/0.70    inference(avatar_component_clause,[],[f72])).
% 2.24/0.70  fof(f543,plain,(
% 2.24/0.70    sK2 != k1_tarski(sK0) | ~spl3_4),
% 2.24/0.70    inference(subsumption_resolution,[],[f35,f73])).
% 2.24/0.70  fof(f35,plain,(
% 2.24/0.70    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 2.24/0.70    inference(cnf_transformation,[],[f31])).
% 2.24/0.70  fof(f31,plain,(
% 2.24/0.70    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.24/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f30])).
% 2.24/0.70  fof(f30,plain,(
% 2.24/0.70    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 2.24/0.70    introduced(choice_axiom,[])).
% 2.24/0.70  fof(f28,plain,(
% 2.24/0.70    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.24/0.70    inference(ennf_transformation,[],[f25])).
% 2.24/0.70  fof(f25,negated_conjecture,(
% 2.24/0.70    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.24/0.70    inference(negated_conjecture,[],[f24])).
% 2.24/0.70  fof(f24,conjecture,(
% 2.24/0.70    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.24/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.24/0.70  fof(f516,plain,(
% 2.24/0.70    k5_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2) | k1_xboole_0 != k4_xboole_0(sK1,sK2) | sK2 != k3_xboole_0(sK1,sK2) | k3_xboole_0(sK1,sK2) != k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) | sK2 = k5_xboole_0(k1_xboole_0,sK1)),
% 2.24/0.70    introduced(theory_tautology_sat_conflict,[])).
% 2.24/0.70  fof(f512,plain,(
% 2.24/0.70    spl3_10 | ~spl3_31),
% 2.24/0.70    inference(avatar_contradiction_clause,[],[f511])).
% 2.24/0.70  fof(f511,plain,(
% 2.24/0.70    $false | (spl3_10 | ~spl3_31)),
% 2.24/0.70    inference(subsumption_resolution,[],[f510,f141])).
% 2.24/0.70  fof(f141,plain,(
% 2.24/0.70    sK1 != sK2 | spl3_10),
% 2.24/0.70    inference(avatar_component_clause,[],[f139])).
% 2.24/0.70  fof(f510,plain,(
% 2.24/0.70    sK1 = sK2 | ~spl3_31),
% 2.24/0.70    inference(forward_demodulation,[],[f503,f87])).
% 2.24/0.70  fof(f87,plain,(
% 2.24/0.70    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.24/0.70    inference(superposition,[],[f49,f41])).
% 2.24/0.70  fof(f41,plain,(
% 2.24/0.70    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.24/0.70    inference(cnf_transformation,[],[f9])).
% 2.24/0.70  fof(f9,axiom,(
% 2.24/0.70    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.24/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.24/0.70  fof(f49,plain,(
% 2.24/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.24/0.70    inference(cnf_transformation,[],[f1])).
% 2.24/0.70  fof(f1,axiom,(
% 2.24/0.70    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.24/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.24/0.70  fof(f503,plain,(
% 2.24/0.70    sK2 = k5_xboole_0(k1_xboole_0,sK1) | ~spl3_31),
% 2.24/0.70    inference(avatar_component_clause,[],[f501])).
% 2.24/0.70  fof(f501,plain,(
% 2.24/0.70    spl3_31 <=> sK2 = k5_xboole_0(k1_xboole_0,sK1)),
% 2.24/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 2.24/0.70  fof(f480,plain,(
% 2.24/0.70    spl3_5 | ~spl3_23),
% 2.24/0.70    inference(avatar_contradiction_clause,[],[f479])).
% 2.24/0.70  fof(f479,plain,(
% 2.24/0.70    $false | (spl3_5 | ~spl3_23)),
% 2.24/0.70    inference(subsumption_resolution,[],[f478,f78])).
% 2.24/0.70  fof(f78,plain,(
% 2.24/0.70    k1_xboole_0 != sK2 | spl3_5),
% 2.24/0.70    inference(avatar_component_clause,[],[f76])).
% 2.24/0.70  fof(f76,plain,(
% 2.24/0.70    spl3_5 <=> k1_xboole_0 = sK2),
% 2.24/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.24/0.70  fof(f478,plain,(
% 2.24/0.70    k1_xboole_0 = sK2 | ~spl3_23),
% 2.24/0.70    inference(forward_demodulation,[],[f468,f42])).
% 2.24/0.70  fof(f42,plain,(
% 2.24/0.70    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.24/0.70    inference(cnf_transformation,[],[f13])).
% 2.24/0.70  fof(f13,axiom,(
% 2.24/0.70    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.24/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.24/0.70  fof(f468,plain,(
% 2.24/0.70    sK2 = k5_xboole_0(sK1,sK1) | ~spl3_23),
% 2.24/0.70    inference(superposition,[],[f213,f446])).
% 2.24/0.70  fof(f446,plain,(
% 2.24/0.70    sK1 = k5_xboole_0(sK1,sK2) | ~spl3_23),
% 2.24/0.70    inference(avatar_component_clause,[],[f444])).
% 2.24/0.70  fof(f444,plain,(
% 2.24/0.70    spl3_23 <=> sK1 = k5_xboole_0(sK1,sK2)),
% 2.24/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 2.24/0.70  fof(f213,plain,(
% 2.24/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.24/0.70    inference(forward_demodulation,[],[f189,f87])).
% 2.24/0.70  fof(f189,plain,(
% 2.24/0.70    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.24/0.70    inference(superposition,[],[f48,f42])).
% 2.24/0.70  fof(f48,plain,(
% 2.24/0.70    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.24/0.70    inference(cnf_transformation,[],[f12])).
% 2.24/0.70  fof(f12,axiom,(
% 2.24/0.70    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.24/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.24/0.70  fof(f447,plain,(
% 2.24/0.70    spl3_22 | spl3_23 | ~spl3_4 | ~spl3_18),
% 2.24/0.70    inference(avatar_split_clause,[],[f328,f324,f72,f444,f440])).
% 2.24/0.70  fof(f440,plain,(
% 2.24/0.70    spl3_22 <=> k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 2.24/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 2.24/0.70  fof(f324,plain,(
% 2.24/0.70    spl3_18 <=> k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK2)),
% 2.24/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 2.24/0.70  fof(f328,plain,(
% 2.24/0.70    sK1 = k5_xboole_0(sK1,sK2) | k1_xboole_0 = k4_xboole_0(sK1,sK2) | (~spl3_4 | ~spl3_18)),
% 2.24/0.70    inference(superposition,[],[f326,f149])).
% 2.24/0.70  fof(f149,plain,(
% 2.24/0.70    ( ! [X0] : (sK1 = k4_xboole_0(sK1,X0) | k1_xboole_0 = k4_xboole_0(sK1,X0)) ) | ~spl3_4),
% 2.24/0.70    inference(resolution,[],[f137,f53])).
% 2.24/0.70  fof(f53,plain,(
% 2.24/0.70    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.24/0.70    inference(cnf_transformation,[],[f8])).
% 2.24/0.70  fof(f8,axiom,(
% 2.24/0.70    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.24/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.24/0.70  fof(f137,plain,(
% 2.24/0.70    ( ! [X0] : (~r1_tarski(X0,sK1) | k1_xboole_0 = X0 | sK1 = X0) ) | ~spl3_4),
% 2.24/0.70    inference(superposition,[],[f38,f73])).
% 2.24/0.70  fof(f38,plain,(
% 2.24/0.70    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 2.24/0.70    inference(cnf_transformation,[],[f33])).
% 2.24/0.70  fof(f33,plain,(
% 2.24/0.70    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.24/0.70    inference(flattening,[],[f32])).
% 2.24/0.70  fof(f32,plain,(
% 2.24/0.70    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.24/0.70    inference(nnf_transformation,[],[f22])).
% 2.24/0.70  fof(f22,axiom,(
% 2.24/0.70    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.24/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.24/0.70  fof(f326,plain,(
% 2.24/0.70    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK2) | ~spl3_18),
% 2.24/0.70    inference(avatar_component_clause,[],[f324])).
% 2.24/0.70  fof(f327,plain,(
% 2.24/0.70    spl3_18 | ~spl3_14),
% 2.24/0.70    inference(avatar_split_clause,[],[f301,f283,f324])).
% 2.24/0.70  fof(f283,plain,(
% 2.24/0.70    spl3_14 <=> sK2 = k3_xboole_0(sK1,sK2)),
% 2.24/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 2.24/0.70  fof(f301,plain,(
% 2.24/0.70    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK2) | ~spl3_14),
% 2.24/0.70    inference(superposition,[],[f50,f285])).
% 2.24/0.70  fof(f285,plain,(
% 2.24/0.70    sK2 = k3_xboole_0(sK1,sK2) | ~spl3_14),
% 2.24/0.70    inference(avatar_component_clause,[],[f283])).
% 2.24/0.70  fof(f50,plain,(
% 2.24/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.24/0.70    inference(cnf_transformation,[],[f6])).
% 2.24/0.70  fof(f6,axiom,(
% 2.24/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.24/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.24/0.70  fof(f299,plain,(
% 2.24/0.70    spl3_14 | ~spl3_12),
% 2.24/0.70    inference(avatar_split_clause,[],[f276,f183,f283])).
% 2.24/0.70  fof(f183,plain,(
% 2.24/0.70    spl3_12 <=> k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),
% 2.24/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 2.24/0.70  fof(f276,plain,(
% 2.24/0.70    sK2 = k3_xboole_0(sK1,sK2) | ~spl3_12),
% 2.24/0.70    inference(superposition,[],[f185,f213])).
% 2.24/0.70  fof(f185,plain,(
% 2.24/0.70    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | ~spl3_12),
% 2.24/0.70    inference(avatar_component_clause,[],[f183])).
% 2.24/0.70  fof(f218,plain,(
% 2.24/0.70    spl3_12 | ~spl3_11),
% 2.24/0.70    inference(avatar_split_clause,[],[f181,f173,f183])).
% 2.24/0.70  fof(f173,plain,(
% 2.24/0.70    spl3_11 <=> k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)),
% 2.24/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 2.24/0.70  fof(f181,plain,(
% 2.24/0.70    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | ~spl3_11),
% 2.24/0.70    inference(superposition,[],[f49,f175])).
% 2.24/0.70  fof(f175,plain,(
% 2.24/0.70    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) | ~spl3_11),
% 2.24/0.70    inference(avatar_component_clause,[],[f173])).
% 2.24/0.70  fof(f176,plain,(
% 2.24/0.70    spl3_11 | ~spl3_1 | ~spl3_4),
% 2.24/0.70    inference(avatar_split_clause,[],[f168,f72,f58,f173])).
% 2.24/0.70  fof(f58,plain,(
% 2.24/0.70    spl3_1 <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.24/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.24/0.70  fof(f168,plain,(
% 2.24/0.70    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) | (~spl3_1 | ~spl3_4)),
% 2.24/0.70    inference(forward_demodulation,[],[f163,f73])).
% 2.24/0.70  fof(f163,plain,(
% 2.24/0.70    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0)) | ~spl3_1),
% 2.24/0.70    inference(superposition,[],[f44,f60])).
% 2.24/0.70  fof(f60,plain,(
% 2.24/0.70    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) | ~spl3_1),
% 2.24/0.70    inference(avatar_component_clause,[],[f58])).
% 2.24/0.70  fof(f44,plain,(
% 2.24/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.24/0.70    inference(cnf_transformation,[],[f14])).
% 2.24/0.70  fof(f14,axiom,(
% 2.24/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.24/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.24/0.70  fof(f130,plain,(
% 2.24/0.70    ~spl3_2 | spl3_7),
% 2.24/0.70    inference(avatar_contradiction_clause,[],[f129])).
% 2.24/0.70  fof(f129,plain,(
% 2.24/0.70    $false | (~spl3_2 | spl3_7)),
% 2.24/0.70    inference(subsumption_resolution,[],[f126,f107])).
% 2.24/0.70  fof(f107,plain,(
% 2.24/0.70    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.24/0.70    inference(superposition,[],[f53,f106])).
% 2.24/0.70  fof(f106,plain,(
% 2.24/0.70    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.24/0.70    inference(forward_demodulation,[],[f103,f42])).
% 2.24/0.70  fof(f103,plain,(
% 2.24/0.70    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 2.24/0.70    inference(superposition,[],[f50,f51])).
% 2.24/0.70  fof(f51,plain,(
% 2.24/0.70    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.24/0.70    inference(cnf_transformation,[],[f27])).
% 2.24/0.70  fof(f27,plain,(
% 2.24/0.70    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.24/0.70    inference(rectify,[],[f4])).
% 2.24/0.70  fof(f4,axiom,(
% 2.24/0.70    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.24/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.24/0.70  fof(f126,plain,(
% 2.24/0.70    ~r1_tarski(k1_xboole_0,sK2) | (~spl3_2 | spl3_7)),
% 2.24/0.70    inference(superposition,[],[f101,f64])).
% 2.24/0.70  fof(f64,plain,(
% 2.24/0.70    k1_xboole_0 = sK1 | ~spl3_2),
% 2.24/0.70    inference(avatar_component_clause,[],[f63])).
% 2.24/0.70  fof(f63,plain,(
% 2.24/0.70    spl3_2 <=> k1_xboole_0 = sK1),
% 2.24/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.24/0.70  fof(f101,plain,(
% 2.24/0.70    ~r1_tarski(sK1,sK2) | spl3_7),
% 2.24/0.70    inference(avatar_component_clause,[],[f99])).
% 2.24/0.70  fof(f99,plain,(
% 2.24/0.70    spl3_7 <=> r1_tarski(sK1,sK2)),
% 2.24/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.24/0.70  fof(f120,plain,(
% 2.24/0.70    spl3_2 | spl3_4 | ~spl3_6),
% 2.24/0.70    inference(avatar_contradiction_clause,[],[f119])).
% 2.24/0.70  fof(f119,plain,(
% 2.24/0.70    $false | (spl3_2 | spl3_4 | ~spl3_6)),
% 2.24/0.70    inference(subsumption_resolution,[],[f118,f74])).
% 2.24/0.70  fof(f74,plain,(
% 2.24/0.70    sK1 != k1_tarski(sK0) | spl3_4),
% 2.24/0.70    inference(avatar_component_clause,[],[f72])).
% 2.24/0.70  fof(f118,plain,(
% 2.24/0.70    sK1 = k1_tarski(sK0) | (spl3_2 | ~spl3_6)),
% 2.24/0.70    inference(subsumption_resolution,[],[f116,f65])).
% 2.24/0.70  fof(f65,plain,(
% 2.24/0.70    k1_xboole_0 != sK1 | spl3_2),
% 2.24/0.70    inference(avatar_component_clause,[],[f63])).
% 2.24/0.70  fof(f116,plain,(
% 2.24/0.70    k1_xboole_0 = sK1 | sK1 = k1_tarski(sK0) | ~spl3_6),
% 2.24/0.70    inference(resolution,[],[f38,f84])).
% 2.24/0.70  fof(f84,plain,(
% 2.24/0.70    r1_tarski(sK1,k1_tarski(sK0)) | ~spl3_6),
% 2.24/0.70    inference(avatar_component_clause,[],[f82])).
% 2.24/0.70  fof(f82,plain,(
% 2.24/0.70    spl3_6 <=> r1_tarski(sK1,k1_tarski(sK0))),
% 2.24/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.24/0.70  fof(f102,plain,(
% 2.24/0.70    ~spl3_7 | spl3_3 | ~spl3_1),
% 2.24/0.70    inference(avatar_split_clause,[],[f95,f58,f67,f99])).
% 2.24/0.70  fof(f67,plain,(
% 2.24/0.70    spl3_3 <=> sK2 = k1_tarski(sK0)),
% 2.24/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.24/0.70  fof(f95,plain,(
% 2.24/0.70    sK2 = k1_tarski(sK0) | ~r1_tarski(sK1,sK2) | ~spl3_1),
% 2.24/0.70    inference(superposition,[],[f43,f60])).
% 2.24/0.70  fof(f43,plain,(
% 2.24/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.24/0.70    inference(cnf_transformation,[],[f29])).
% 2.24/0.70  fof(f29,plain,(
% 2.24/0.70    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.24/0.70    inference(ennf_transformation,[],[f7])).
% 2.24/0.70  fof(f7,axiom,(
% 2.24/0.70    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.24/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.24/0.70  fof(f85,plain,(
% 2.24/0.70    spl3_6 | ~spl3_1),
% 2.24/0.70    inference(avatar_split_clause,[],[f80,f58,f82])).
% 2.24/0.70  fof(f80,plain,(
% 2.24/0.70    r1_tarski(sK1,k1_tarski(sK0)) | ~spl3_1),
% 2.24/0.70    inference(superposition,[],[f45,f60])).
% 2.24/0.70  fof(f45,plain,(
% 2.24/0.70    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.24/0.70    inference(cnf_transformation,[],[f11])).
% 2.24/0.70  fof(f11,axiom,(
% 2.24/0.70    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.24/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.24/0.70  fof(f79,plain,(
% 2.24/0.70    ~spl3_4 | ~spl3_5),
% 2.24/0.70    inference(avatar_split_clause,[],[f37,f76,f72])).
% 2.24/0.70  fof(f37,plain,(
% 2.24/0.70    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 2.24/0.70    inference(cnf_transformation,[],[f31])).
% 2.24/0.70  fof(f70,plain,(
% 2.24/0.70    ~spl3_2 | ~spl3_3),
% 2.24/0.70    inference(avatar_split_clause,[],[f36,f67,f63])).
% 2.24/0.70  fof(f36,plain,(
% 2.24/0.70    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 2.24/0.70    inference(cnf_transformation,[],[f31])).
% 2.24/0.70  fof(f61,plain,(
% 2.24/0.70    spl3_1),
% 2.24/0.70    inference(avatar_split_clause,[],[f34,f58])).
% 2.24/0.70  fof(f34,plain,(
% 2.24/0.70    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.24/0.70    inference(cnf_transformation,[],[f31])).
% 2.24/0.70  % SZS output end Proof for theBenchmark
% 2.24/0.70  % (8458)------------------------------
% 2.24/0.70  % (8458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.24/0.70  % (8458)Termination reason: Refutation
% 2.24/0.70  
% 2.24/0.70  % (8458)Memory used [KB]: 11001
% 2.24/0.70  % (8458)Time elapsed: 0.097 s
% 2.24/0.70  % (8458)------------------------------
% 2.24/0.70  % (8458)------------------------------
% 2.24/0.70  % (8417)Success in time 0.331 s
%------------------------------------------------------------------------------
