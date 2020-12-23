%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0248+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 116 expanded)
%              Number of leaves         :   17 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :  179 ( 381 expanded)
%              Number of equality atoms :  102 ( 267 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f631,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f462,f469,f475,f479,f492,f516,f545,f617,f620,f621,f630])).

fof(f630,plain,
    ( ~ spl6_3
    | spl6_4
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f629])).

fof(f629,plain,
    ( $false
    | ~ spl6_3
    | spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f628,f468])).

fof(f468,plain,
    ( sK2 != k1_tarski(sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f467])).

fof(f467,plain,
    ( spl6_4
  <=> sK2 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f628,plain,
    ( sK2 = k1_tarski(sK0)
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f626,f493])).

fof(f493,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f441,f428])).

fof(f428,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f76])).

fof(f76,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f441,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f626,plain,
    ( k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(backward_demodulation,[],[f478,f563])).

fof(f563,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f464])).

fof(f464,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f478,plain,
    ( k1_tarski(sK0) = k2_xboole_0(sK1,sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f477])).

fof(f477,plain,
    ( spl6_6
  <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f621,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0)
    | sK1 = sK2 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f620,plain,
    ( spl6_2
    | spl6_4
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f618,f543,f467,f460])).

fof(f460,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f543,plain,
    ( spl6_10
  <=> r1_tarski(sK2,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f618,plain,
    ( k1_xboole_0 = sK2
    | spl6_4
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f615,f468])).

fof(f615,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k1_tarski(sK0)
    | ~ spl6_10 ),
    inference(resolution,[],[f411,f544])).

fof(f544,plain,
    ( r1_tarski(sK2,k1_tarski(sK0))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f543])).

fof(f411,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f381])).

fof(f381,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f380])).

fof(f380,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f305])).

fof(f305,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f617,plain,
    ( spl6_3
    | spl6_1
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f616,f514,f457,f464])).

% (15293)lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=input_only:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_11 on theBenchmark
fof(f457,plain,
    ( spl6_1
  <=> sK1 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f514,plain,
    ( spl6_9
  <=> r1_tarski(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f616,plain,
    ( k1_xboole_0 = sK1
    | spl6_1
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f614,f458])).

fof(f458,plain,
    ( sK1 != k1_tarski(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f457])).

fof(f614,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k1_tarski(sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f411,f515])).

fof(f515,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f514])).

fof(f545,plain,
    ( spl6_10
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f536,f477,f543])).

fof(f536,plain,
    ( r1_tarski(sK2,k1_tarski(sK0))
    | ~ spl6_6 ),
    inference(superposition,[],[f530,f478])).

fof(f530,plain,(
    ! [X2,X3] : r1_tarski(X2,k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f512,f441])).

fof(f512,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(trivial_inequality_removal,[],[f505])).

fof(f505,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X1,k2_xboole_0(X1,X2)) ) ),
    inference(superposition,[],[f407,f423])).

fof(f423,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f407,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f378])).

fof(f378,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f516,plain,
    ( spl6_9
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f509,f490,f514])).

fof(f490,plain,
    ( spl6_8
  <=> k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f509,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl6_8 ),
    inference(trivial_inequality_removal,[],[f508])).

fof(f508,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl6_8 ),
    inference(superposition,[],[f407,f491])).

fof(f491,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f490])).

fof(f492,plain,
    ( spl6_8
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f486,f477,f490])).

fof(f486,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl6_6 ),
    inference(superposition,[],[f423,f478])).

fof(f479,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f387,f477])).

fof(f387,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f369])).

fof(f369,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f351,f368])).

fof(f368,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f351,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f345])).

fof(f345,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f344])).

fof(f344,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f475,plain,
    ( ~ spl6_5
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f471,f457,f473])).

fof(f473,plain,
    ( spl6_5
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f471,plain,
    ( sK1 != k1_tarski(sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f470])).

fof(f470,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f388])).

fof(f388,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f369])).

fof(f469,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f389,f467,f464])).

fof(f389,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f369])).

fof(f462,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f390,f460,f457])).

fof(f390,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f369])).
%------------------------------------------------------------------------------
