%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:25 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 230 expanded)
%              Number of leaves         :   24 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :  247 ( 585 expanded)
%              Number of equality atoms :   33 (  90 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3297,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2428,f2444,f2445,f2446,f2551,f3021,f3296])).

fof(f3296,plain,(
    spl6_48 ),
    inference(avatar_contradiction_clause,[],[f3292])).

fof(f3292,plain,
    ( $false
    | spl6_48 ),
    inference(resolution,[],[f2754,f38])).

fof(f38,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f2754,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl6_48 ),
    inference(resolution,[],[f2364,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f2364,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl6_48 ),
    inference(avatar_component_clause,[],[f2362])).

fof(f2362,plain,
    ( spl6_48
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f3021,plain,
    ( ~ spl6_18
    | spl6_62 ),
    inference(avatar_contradiction_clause,[],[f3017])).

fof(f3017,plain,
    ( $false
    | ~ spl6_18
    | spl6_62 ),
    inference(resolution,[],[f2535,f2453])).

fof(f2453,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl6_18 ),
    inference(resolution,[],[f351,f174])).

fof(f174,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK4(X4,X5),k3_xboole_0(X5,X4))
      | r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f47,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f351,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK1))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl6_18
  <=> ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f2535,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl6_62 ),
    inference(avatar_component_clause,[],[f2533])).

fof(f2533,plain,
    ( spl6_62
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f2551,plain,
    ( ~ spl6_48
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f1418,f2533,f2362])).

fof(f1418,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f236,f74])).

fof(f74,plain,(
    ~ r1_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK0,sK2)))) ),
    inference(backward_demodulation,[],[f72,f43])).

fof(f72,plain,(
    ~ r1_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)))) ),
    inference(resolution,[],[f65,f54])).

fof(f65,plain,(
    ~ r1_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))),sK1) ),
    inference(definition_unfolding,[],[f39,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f46,f45])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f39,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f236,plain,(
    ! [X6,X8,X7] :
      ( r1_xboole_0(X8,k5_xboole_0(X7,k5_xboole_0(X6,k3_xboole_0(X7,X6))))
      | ~ r1_xboole_0(X8,X7)
      | ~ r1_xboole_0(X8,X6) ) ),
    inference(superposition,[],[f71,f43])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(definition_unfolding,[],[f59,f62])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f2446,plain,
    ( ~ spl6_20
    | spl6_50 ),
    inference(avatar_split_clause,[],[f1125,f2433,f402])).

fof(f402,plain,
    ( spl6_20
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f2433,plain,
    ( spl6_50
  <=> r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f1125,plain,
    ( r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1))
    | k1_xboole_0 != k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f277,f66])).

fof(f66,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f36,f64])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f277,plain,(
    ! [X14,X13] :
      ( ~ r1_tarski(X14,X13)
      | r1_xboole_0(X13,X14)
      | k1_xboole_0 != X14 ) ),
    inference(superposition,[],[f56,f82])).

fof(f82,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f53,f43])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f2445,plain,
    ( spl6_20
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f370,f353,f402])).

fof(f353,plain,
    ( spl6_19
  <=> r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f370,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f113,f66])).

fof(f113,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | ~ r1_xboole_0(X2,X3)
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f55,f53])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2444,plain,
    ( spl6_18
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f991,f2433,f350])).

fof(f991,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1))
      | ~ r2_hidden(X0,k3_xboole_0(sK0,sK1)) ) ),
    inference(resolution,[],[f245,f66])).

fof(f245,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,X4)
      | ~ r1_xboole_0(X4,X3)
      | ~ r2_hidden(X5,X3) ) ),
    inference(superposition,[],[f78,f53])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X1,X0))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f48,f43])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2428,plain,(
    spl6_19 ),
    inference(avatar_contradiction_clause,[],[f2424])).

fof(f2424,plain,
    ( $false
    | spl6_19 ),
    inference(resolution,[],[f2343,f38])).

fof(f2343,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl6_19 ),
    inference(resolution,[],[f2286,f242])).

fof(f242,plain,(
    ! [X4,X5,X3] :
      ( r1_xboole_0(X5,k3_xboole_0(X4,X3))
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f78,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f2286,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | spl6_19 ),
    inference(resolution,[],[f985,f371])).

fof(f371,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | spl6_19 ),
    inference(resolution,[],[f363,f161])).

fof(f161,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f51,f37])).

fof(f37,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f363,plain,
    ( r2_hidden(sK3,k3_xboole_0(sK0,sK1))
    | spl6_19 ),
    inference(resolution,[],[f358,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f64])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f358,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1))
    | spl6_19 ),
    inference(resolution,[],[f355,f54])).

fof(f355,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))
    | spl6_19 ),
    inference(avatar_component_clause,[],[f353])).

fof(f985,plain,(
    ! [X23,X21,X22] :
      ( r1_xboole_0(k3_xboole_0(X21,X22),X23)
      | ~ r1_xboole_0(X21,k3_xboole_0(X22,X23)) ) ),
    inference(trivial_inequality_removal,[],[f979])).

fof(f979,plain,(
    ! [X23,X21,X22] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k3_xboole_0(X21,X22),X23)
      | ~ r1_xboole_0(X21,k3_xboole_0(X22,X23)) ) ),
    inference(superposition,[],[f195,f55])).

fof(f195,plain,(
    ! [X21,X19,X20] :
      ( k1_xboole_0 != k3_xboole_0(X19,k3_xboole_0(X20,X21))
      | r1_xboole_0(k3_xboole_0(X19,X20),X21) ) ),
    inference(superposition,[],[f56,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (19102)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.46  % (19093)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (19109)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.46  % (19097)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (19098)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (19103)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (19107)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (19106)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (19100)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (19105)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (19095)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (19094)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (19096)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (19099)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (19104)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (19101)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (19110)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (19108)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.53/0.58  % (19097)Refutation found. Thanks to Tanya!
% 1.53/0.58  % SZS status Theorem for theBenchmark
% 1.53/0.58  % SZS output start Proof for theBenchmark
% 1.53/0.58  fof(f3297,plain,(
% 1.53/0.58    $false),
% 1.53/0.58    inference(avatar_sat_refutation,[],[f2428,f2444,f2445,f2446,f2551,f3021,f3296])).
% 1.53/0.58  fof(f3296,plain,(
% 1.53/0.58    spl6_48),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f3292])).
% 1.53/0.58  fof(f3292,plain,(
% 1.53/0.58    $false | spl6_48),
% 1.53/0.58    inference(resolution,[],[f2754,f38])).
% 1.53/0.58  fof(f38,plain,(
% 1.53/0.58    r1_xboole_0(sK2,sK1)),
% 1.53/0.58    inference(cnf_transformation,[],[f30])).
% 1.53/0.58  fof(f30,plain,(
% 1.53/0.58    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.53/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f29])).
% 1.53/0.58  fof(f29,plain,(
% 1.53/0.58    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 1.53/0.58    introduced(choice_axiom,[])).
% 1.53/0.58  fof(f22,plain,(
% 1.53/0.58    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.53/0.58    inference(flattening,[],[f21])).
% 1.53/0.58  fof(f21,plain,(
% 1.53/0.58    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.53/0.58    inference(ennf_transformation,[],[f18])).
% 1.53/0.58  fof(f18,negated_conjecture,(
% 1.53/0.58    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.53/0.58    inference(negated_conjecture,[],[f17])).
% 1.53/0.58  fof(f17,conjecture,(
% 1.53/0.58    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.53/0.58  fof(f2754,plain,(
% 1.53/0.58    ~r1_xboole_0(sK2,sK1) | spl6_48),
% 1.53/0.58    inference(resolution,[],[f2364,f54])).
% 1.53/0.58  fof(f54,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f27])).
% 1.53/0.58  fof(f27,plain,(
% 1.53/0.58    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.53/0.58    inference(ennf_transformation,[],[f4])).
% 1.53/0.58  fof(f4,axiom,(
% 1.53/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.53/0.58  fof(f2364,plain,(
% 1.53/0.58    ~r1_xboole_0(sK1,sK2) | spl6_48),
% 1.53/0.58    inference(avatar_component_clause,[],[f2362])).
% 1.53/0.58  fof(f2362,plain,(
% 1.53/0.58    spl6_48 <=> r1_xboole_0(sK1,sK2)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 1.53/0.58  fof(f3021,plain,(
% 1.53/0.58    ~spl6_18 | spl6_62),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f3017])).
% 1.53/0.58  fof(f3017,plain,(
% 1.53/0.58    $false | (~spl6_18 | spl6_62)),
% 1.53/0.58    inference(resolution,[],[f2535,f2453])).
% 1.53/0.58  fof(f2453,plain,(
% 1.53/0.58    r1_xboole_0(sK1,sK0) | ~spl6_18),
% 1.53/0.58    inference(resolution,[],[f351,f174])).
% 1.53/0.58  fof(f174,plain,(
% 1.53/0.58    ( ! [X4,X5] : (r2_hidden(sK4(X4,X5),k3_xboole_0(X5,X4)) | r1_xboole_0(X4,X5)) )),
% 1.53/0.58    inference(superposition,[],[f47,f43])).
% 1.53/0.58  fof(f43,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f2])).
% 1.53/0.58  fof(f2,axiom,(
% 1.53/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.53/0.58  fof(f47,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f32])).
% 1.53/0.58  fof(f32,plain,(
% 1.53/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.53/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f31])).
% 1.53/0.58  fof(f31,plain,(
% 1.53/0.58    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.53/0.58    introduced(choice_axiom,[])).
% 1.53/0.58  fof(f23,plain,(
% 1.53/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.53/0.58    inference(ennf_transformation,[],[f19])).
% 1.53/0.58  fof(f19,plain,(
% 1.53/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.53/0.58    inference(rectify,[],[f6])).
% 1.53/0.58  fof(f6,axiom,(
% 1.53/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.53/0.58  fof(f351,plain,(
% 1.53/0.58    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,sK1))) ) | ~spl6_18),
% 1.53/0.58    inference(avatar_component_clause,[],[f350])).
% 1.53/0.58  fof(f350,plain,(
% 1.53/0.58    spl6_18 <=> ! [X0] : ~r2_hidden(X0,k3_xboole_0(sK0,sK1))),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.53/0.58  fof(f2535,plain,(
% 1.53/0.58    ~r1_xboole_0(sK1,sK0) | spl6_62),
% 1.53/0.58    inference(avatar_component_clause,[],[f2533])).
% 1.53/0.58  fof(f2533,plain,(
% 1.53/0.58    spl6_62 <=> r1_xboole_0(sK1,sK0)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 1.53/0.58  fof(f2551,plain,(
% 1.53/0.58    ~spl6_48 | ~spl6_62),
% 1.53/0.58    inference(avatar_split_clause,[],[f1418,f2533,f2362])).
% 1.53/0.58  fof(f1418,plain,(
% 1.53/0.58    ~r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK1,sK2)),
% 1.53/0.58    inference(resolution,[],[f236,f74])).
% 1.53/0.58  fof(f74,plain,(
% 1.53/0.58    ~r1_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK0,sK2))))),
% 1.53/0.58    inference(backward_demodulation,[],[f72,f43])).
% 1.53/0.58  fof(f72,plain,(
% 1.53/0.58    ~r1_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))))),
% 1.53/0.58    inference(resolution,[],[f65,f54])).
% 1.53/0.58  fof(f65,plain,(
% 1.53/0.58    ~r1_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))),sK1)),
% 1.53/0.58    inference(definition_unfolding,[],[f39,f62])).
% 1.53/0.58  fof(f62,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.53/0.58    inference(definition_unfolding,[],[f46,f45])).
% 1.53/0.58  fof(f45,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.53/0.58    inference(cnf_transformation,[],[f7])).
% 1.53/0.58  fof(f7,axiom,(
% 1.53/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.53/0.58  fof(f46,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.53/0.58    inference(cnf_transformation,[],[f12])).
% 1.53/0.58  fof(f12,axiom,(
% 1.53/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.53/0.58  fof(f39,plain,(
% 1.53/0.58    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.53/0.58    inference(cnf_transformation,[],[f30])).
% 1.53/0.58  fof(f236,plain,(
% 1.53/0.58    ( ! [X6,X8,X7] : (r1_xboole_0(X8,k5_xboole_0(X7,k5_xboole_0(X6,k3_xboole_0(X7,X6)))) | ~r1_xboole_0(X8,X7) | ~r1_xboole_0(X8,X6)) )),
% 1.53/0.58    inference(superposition,[],[f71,f43])).
% 1.53/0.58  fof(f71,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 1.53/0.58    inference(definition_unfolding,[],[f59,f62])).
% 1.53/0.58  fof(f59,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.53/0.58    inference(cnf_transformation,[],[f28])).
% 1.53/0.58  fof(f28,plain,(
% 1.53/0.58    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.53/0.58    inference(ennf_transformation,[],[f11])).
% 1.53/0.58  fof(f11,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.53/0.58  fof(f2446,plain,(
% 1.53/0.58    ~spl6_20 | spl6_50),
% 1.53/0.58    inference(avatar_split_clause,[],[f1125,f2433,f402])).
% 1.53/0.58  fof(f402,plain,(
% 1.53/0.58    spl6_20 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.53/0.58  fof(f2433,plain,(
% 1.53/0.58    spl6_50 <=> r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1))),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 1.53/0.58  fof(f1125,plain,(
% 1.53/0.58    r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1)) | k1_xboole_0 != k3_xboole_0(sK0,sK1)),
% 1.53/0.58    inference(resolution,[],[f277,f66])).
% 1.53/0.58  fof(f66,plain,(
% 1.53/0.58    r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.53/0.58    inference(definition_unfolding,[],[f36,f64])).
% 1.53/0.58  fof(f64,plain,(
% 1.53/0.58    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.53/0.58    inference(definition_unfolding,[],[f41,f63])).
% 1.53/0.58  fof(f63,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.53/0.58    inference(definition_unfolding,[],[f44,f57])).
% 1.53/0.58  fof(f57,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f15])).
% 1.53/0.58  fof(f15,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.53/0.58  fof(f44,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f14])).
% 1.53/0.58  fof(f14,axiom,(
% 1.53/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.53/0.58  fof(f41,plain,(
% 1.53/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f13])).
% 1.53/0.58  fof(f13,axiom,(
% 1.53/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.53/0.58  fof(f36,plain,(
% 1.53/0.58    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.53/0.58    inference(cnf_transformation,[],[f30])).
% 1.53/0.58  fof(f277,plain,(
% 1.53/0.58    ( ! [X14,X13] : (~r1_tarski(X14,X13) | r1_xboole_0(X13,X14) | k1_xboole_0 != X14) )),
% 1.53/0.58    inference(superposition,[],[f56,f82])).
% 1.53/0.58  fof(f82,plain,(
% 1.53/0.58    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 1.53/0.58    inference(superposition,[],[f53,f43])).
% 1.53/0.58  fof(f53,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f26])).
% 1.53/0.58  fof(f26,plain,(
% 1.53/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.53/0.58    inference(ennf_transformation,[],[f9])).
% 1.53/0.58  fof(f9,axiom,(
% 1.53/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.53/0.58  fof(f56,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f35])).
% 1.53/0.58  fof(f35,plain,(
% 1.53/0.58    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.53/0.58    inference(nnf_transformation,[],[f3])).
% 1.53/0.58  fof(f3,axiom,(
% 1.53/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.53/0.58  fof(f2445,plain,(
% 1.53/0.58    spl6_20 | ~spl6_19),
% 1.53/0.58    inference(avatar_split_clause,[],[f370,f353,f402])).
% 1.53/0.58  fof(f353,plain,(
% 1.53/0.58    spl6_19 <=> r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.53/0.58  fof(f370,plain,(
% 1.53/0.58    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) | k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.53/0.58    inference(resolution,[],[f113,f66])).
% 1.53/0.58  fof(f113,plain,(
% 1.53/0.58    ( ! [X2,X3] : (~r1_tarski(X2,X3) | ~r1_xboole_0(X2,X3) | k1_xboole_0 = X2) )),
% 1.53/0.58    inference(superposition,[],[f55,f53])).
% 1.53/0.58  fof(f55,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f35])).
% 1.53/0.58  fof(f2444,plain,(
% 1.53/0.58    spl6_18 | ~spl6_50),
% 1.53/0.58    inference(avatar_split_clause,[],[f991,f2433,f350])).
% 1.53/0.58  fof(f991,plain,(
% 1.53/0.58    ( ! [X0] : (~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1)) | ~r2_hidden(X0,k3_xboole_0(sK0,sK1))) )),
% 1.53/0.58    inference(resolution,[],[f245,f66])).
% 1.53/0.58  fof(f245,plain,(
% 1.53/0.58    ( ! [X4,X5,X3] : (~r1_tarski(X3,X4) | ~r1_xboole_0(X4,X3) | ~r2_hidden(X5,X3)) )),
% 1.53/0.58    inference(superposition,[],[f78,f53])).
% 1.53/0.58  fof(f78,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X1,X0)) | ~r1_xboole_0(X0,X1)) )),
% 1.53/0.58    inference(superposition,[],[f48,f43])).
% 1.53/0.58  fof(f48,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f32])).
% 1.53/0.58  fof(f2428,plain,(
% 1.53/0.58    spl6_19),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f2424])).
% 1.53/0.58  fof(f2424,plain,(
% 1.53/0.58    $false | spl6_19),
% 1.53/0.58    inference(resolution,[],[f2343,f38])).
% 1.53/0.58  fof(f2343,plain,(
% 1.53/0.58    ~r1_xboole_0(sK2,sK1) | spl6_19),
% 1.53/0.58    inference(resolution,[],[f2286,f242])).
% 1.53/0.58  fof(f242,plain,(
% 1.53/0.58    ( ! [X4,X5,X3] : (r1_xboole_0(X5,k3_xboole_0(X4,X3)) | ~r1_xboole_0(X3,X4)) )),
% 1.53/0.58    inference(resolution,[],[f78,f50])).
% 1.53/0.58  fof(f50,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f34])).
% 1.53/0.58  fof(f34,plain,(
% 1.53/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.53/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f33])).
% 1.53/0.58  fof(f33,plain,(
% 1.53/0.58    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.53/0.58    introduced(choice_axiom,[])).
% 1.53/0.58  fof(f24,plain,(
% 1.53/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.53/0.58    inference(ennf_transformation,[],[f20])).
% 1.53/0.58  fof(f20,plain,(
% 1.53/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.53/0.58    inference(rectify,[],[f5])).
% 1.53/0.58  fof(f5,axiom,(
% 1.53/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.53/0.58  fof(f2286,plain,(
% 1.53/0.58    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | spl6_19),
% 1.53/0.58    inference(resolution,[],[f985,f371])).
% 1.53/0.58  fof(f371,plain,(
% 1.53/0.58    ~r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) | spl6_19),
% 1.53/0.58    inference(resolution,[],[f363,f161])).
% 1.53/0.58  fof(f161,plain,(
% 1.53/0.58    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(X0,sK2)) )),
% 1.53/0.58    inference(resolution,[],[f51,f37])).
% 1.53/0.58  fof(f37,plain,(
% 1.53/0.58    r2_hidden(sK3,sK2)),
% 1.53/0.58    inference(cnf_transformation,[],[f30])).
% 1.53/0.58  fof(f51,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f34])).
% 1.53/0.58  fof(f363,plain,(
% 1.53/0.58    r2_hidden(sK3,k3_xboole_0(sK0,sK1)) | spl6_19),
% 1.53/0.58    inference(resolution,[],[f358,f68])).
% 1.53/0.58  fof(f68,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.53/0.58    inference(definition_unfolding,[],[f52,f64])).
% 1.53/0.58  fof(f52,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f25])).
% 1.53/0.58  fof(f25,plain,(
% 1.53/0.58    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.53/0.58    inference(ennf_transformation,[],[f16])).
% 1.53/0.58  fof(f16,axiom,(
% 1.53/0.58    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.53/0.58  fof(f358,plain,(
% 1.53/0.58    ~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1)) | spl6_19),
% 1.53/0.58    inference(resolution,[],[f355,f54])).
% 1.53/0.58  fof(f355,plain,(
% 1.53/0.58    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) | spl6_19),
% 1.53/0.58    inference(avatar_component_clause,[],[f353])).
% 1.53/0.58  fof(f985,plain,(
% 1.53/0.58    ( ! [X23,X21,X22] : (r1_xboole_0(k3_xboole_0(X21,X22),X23) | ~r1_xboole_0(X21,k3_xboole_0(X22,X23))) )),
% 1.53/0.58    inference(trivial_inequality_removal,[],[f979])).
% 1.53/0.58  fof(f979,plain,(
% 1.53/0.58    ( ! [X23,X21,X22] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k3_xboole_0(X21,X22),X23) | ~r1_xboole_0(X21,k3_xboole_0(X22,X23))) )),
% 1.53/0.58    inference(superposition,[],[f195,f55])).
% 1.53/0.58  fof(f195,plain,(
% 1.53/0.58    ( ! [X21,X19,X20] : (k1_xboole_0 != k3_xboole_0(X19,k3_xboole_0(X20,X21)) | r1_xboole_0(k3_xboole_0(X19,X20),X21)) )),
% 1.53/0.58    inference(superposition,[],[f56,f58])).
% 1.53/0.58  fof(f58,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.53/0.58    inference(cnf_transformation,[],[f8])).
% 1.53/0.58  fof(f8,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.53/0.58  % SZS output end Proof for theBenchmark
% 1.53/0.58  % (19097)------------------------------
% 1.53/0.58  % (19097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (19097)Termination reason: Refutation
% 1.53/0.58  
% 1.53/0.58  % (19097)Memory used [KB]: 7931
% 1.53/0.58  % (19097)Time elapsed: 0.155 s
% 1.53/0.58  % (19097)------------------------------
% 1.53/0.58  % (19097)------------------------------
% 1.53/0.59  % (19092)Success in time 0.228 s
%------------------------------------------------------------------------------
