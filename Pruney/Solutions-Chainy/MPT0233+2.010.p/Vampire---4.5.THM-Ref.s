%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:05 EST 2020

% Result     : Theorem 3.21s
% Output     : Refutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 767 expanded)
%              Number of leaves         :   31 ( 254 expanded)
%              Depth                    :   23
%              Number of atoms          :  302 (1185 expanded)
%              Number of equality atoms :  182 ( 880 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2218,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1936,f2073,f2217])).

fof(f2217,plain,(
    ~ spl8_17 ),
    inference(avatar_contradiction_clause,[],[f2216])).

fof(f2216,plain,
    ( $false
    | ~ spl8_17 ),
    inference(trivial_inequality_removal,[],[f2215])).

fof(f2215,plain,
    ( sK1 != sK1
    | ~ spl8_17 ),
    inference(superposition,[],[f49,f1935])).

fof(f1935,plain,
    ( sK1 = sK3
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f1933])).

fof(f1933,plain,
    ( spl8_17
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f49,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( sK1 != sK4
    & sK1 != sK3
    & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f28,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK1 != sK4
      & sK1 != sK3
      & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f2073,plain,(
    ~ spl8_16 ),
    inference(avatar_contradiction_clause,[],[f2072])).

fof(f2072,plain,
    ( $false
    | ~ spl8_16 ),
    inference(trivial_inequality_removal,[],[f2071])).

fof(f2071,plain,
    ( sK1 != sK1
    | ~ spl8_16 ),
    inference(superposition,[],[f50,f1931])).

fof(f1931,plain,
    ( sK1 = sK4
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f1929])).

fof(f1929,plain,
    ( spl8_16
  <=> sK1 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f50,plain,(
    sK1 != sK4 ),
    inference(cnf_transformation,[],[f37])).

fof(f1936,plain,
    ( spl8_16
    | spl8_17 ),
    inference(avatar_split_clause,[],[f1923,f1933,f1929])).

fof(f1923,plain,
    ( sK1 = sK3
    | sK1 = sK4 ),
    inference(resolution,[],[f1820,f389])).

fof(f389,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(resolution,[],[f101,f100])).

fof(f100,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK7(X0,X1,X2,X3) != X0
              & sK7(X0,X1,X2,X3) != X1
              & sK7(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
          & ( sK7(X0,X1,X2,X3) = X0
            | sK7(X0,X1,X2,X3) = X1
            | sK7(X0,X1,X2,X3) = X2
            | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).

fof(f45,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK7(X0,X1,X2,X3) != X0
            & sK7(X0,X1,X2,X3) != X1
            & sK7(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
        & ( sK7(X0,X1,X2,X3) = X0
          | sK7(X0,X1,X2,X3) = X1
          | sK7(X0,X1,X2,X3) = X2
          | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f101,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f79,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f67,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f81,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f82,f83])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f33,f34])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f1820,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK3,sK4))
      | sK3 = X4
      | sK4 = X4 ) ),
    inference(backward_demodulation,[],[f693,f1783])).

fof(f1783,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK3,sK4) ),
    inference(superposition,[],[f1704,f52])).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

% (2488)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
fof(f1704,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4),k1_xboole_0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK3,sK4) ),
    inference(forward_demodulation,[],[f1703,f1569])).

fof(f1569,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,sK3,sK4) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(superposition,[],[f95,f485])).

fof(f485,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4) ),
    inference(forward_demodulation,[],[f484,f95])).

fof(f484,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) ),
    inference(forward_demodulation,[],[f483,f52])).

fof(f483,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k1_xboole_0) ),
    inference(forward_demodulation,[],[f461,f269])).

fof(f269,plain,(
    ! [X9] : k1_xboole_0 = k5_xboole_0(X9,X9) ),
    inference(forward_demodulation,[],[f268,f55])).

fof(f55,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f268,plain,(
    ! [X9] : k1_xboole_0 = k5_xboole_0(X9,k3_xboole_0(X9,X9)) ),
    inference(forward_demodulation,[],[f261,f52])).

fof(f261,plain,(
    ! [X9] : k1_xboole_0 = k5_xboole_0(X9,k3_xboole_0(X9,k5_xboole_0(X9,k1_xboole_0))) ),
    inference(superposition,[],[f91,f109])).

fof(f109,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f108,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f108,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(resolution,[],[f65,f51])).

fof(f51,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f91,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f63,f62,f62])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f461,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ),
    inference(superposition,[],[f93,f131])).

fof(f131,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(resolution,[],[f66,f92])).

fof(f92,plain,(
    r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f48,f89,f89])).

fof(f89,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f88])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f93,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f57,f84,f84])).

fof(f84,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f95,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f70,f87,f84,f89,f89])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f1703,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4),k1_xboole_0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(forward_demodulation,[],[f1684,f269])).

fof(f1684,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[],[f93,f1352])).

fof(f1352,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4)) ),
    inference(resolution,[],[f1323,f102])).

fof(f102,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f56,f55])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1323,plain,(
    ! [X10] :
      ( ~ r1_tarski(X10,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
      | k3_xboole_0(X10,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4)) = X10 ) ),
    inference(superposition,[],[f496,f94])).

fof(f94,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f60,f90,f90,f89])).

fof(f90,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f89])).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f60,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(f496,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,k3_xboole_0(X2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
      | k3_xboole_0(X3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4)) = X3 ) ),
    inference(backward_demodulation,[],[f251,f485])).

fof(f251,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,k3_xboole_0(X2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
      | k3_xboole_0(X3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = X3 ) ),
    inference(superposition,[],[f243,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f243,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),X3))
      | k3_xboole_0(X2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = X2 ) ),
    inference(resolution,[],[f238,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f238,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
      | k3_xboole_0(X1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = X1 ) ),
    inference(superposition,[],[f201,f131])).

fof(f201,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,k3_xboole_0(X3,X2))
      | k3_xboole_0(X4,X2) = X4 ) ),
    inference(superposition,[],[f133,f58])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f68,f66])).

fof(f693,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4))
      | sK3 = X4
      | sK4 = X4 ) ),
    inference(duplicate_literal_removal,[],[f692])).

fof(f692,plain,(
    ! [X4] :
      ( sK3 = X4
      | sK3 = X4
      | ~ r2_hidden(X4,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4))
      | sK4 = X4 ) ),
    inference(resolution,[],[f71,f568])).

fof(f568,plain,(
    sP0(sK4,sK3,sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4)) ),
    inference(superposition,[],[f101,f485])).

fof(f71,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | X1 = X5
      | X2 = X5
      | ~ r2_hidden(X5,X3)
      | X0 = X5 ) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:42:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.50  % (2416)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (2446)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (2438)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (2421)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (2433)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (2417)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (2424)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (2426)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (2426)Refutation not found, incomplete strategy% (2426)------------------------------
% 0.20/0.52  % (2426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (2426)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (2426)Memory used [KB]: 10618
% 0.20/0.52  % (2426)Time elapsed: 0.127 s
% 0.20/0.52  % (2426)------------------------------
% 0.20/0.52  % (2426)------------------------------
% 0.20/0.52  % (2441)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (2420)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (2415)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (2415)Refutation not found, incomplete strategy% (2415)------------------------------
% 0.20/0.53  % (2415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2415)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (2415)Memory used [KB]: 1663
% 0.20/0.53  % (2415)Time elapsed: 0.113 s
% 0.20/0.53  % (2415)------------------------------
% 0.20/0.53  % (2415)------------------------------
% 0.20/0.53  % (2437)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (2439)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (2430)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (2418)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (2419)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (2440)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (2442)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (2422)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (2432)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (2432)Refutation not found, incomplete strategy% (2432)------------------------------
% 0.20/0.54  % (2432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (2432)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (2432)Memory used [KB]: 6268
% 0.20/0.54  % (2432)Time elapsed: 0.129 s
% 0.20/0.54  % (2432)------------------------------
% 0.20/0.54  % (2432)------------------------------
% 0.20/0.54  % (2445)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (2435)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (2425)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (2425)Refutation not found, incomplete strategy% (2425)------------------------------
% 0.20/0.54  % (2425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (2425)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (2425)Memory used [KB]: 10618
% 0.20/0.54  % (2425)Time elapsed: 0.141 s
% 0.20/0.54  % (2425)------------------------------
% 0.20/0.54  % (2425)------------------------------
% 0.20/0.54  % (2431)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (2443)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (2444)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (2434)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (2440)Refutation not found, incomplete strategy% (2440)------------------------------
% 0.20/0.55  % (2440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (2440)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (2440)Memory used [KB]: 1791
% 0.20/0.55  % (2440)Time elapsed: 0.129 s
% 0.20/0.55  % (2440)------------------------------
% 0.20/0.55  % (2440)------------------------------
% 0.20/0.55  % (2428)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (2427)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (2437)Refutation not found, incomplete strategy% (2437)------------------------------
% 0.20/0.55  % (2437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (2437)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (2437)Memory used [KB]: 10746
% 0.20/0.55  % (2437)Time elapsed: 0.153 s
% 0.20/0.55  % (2437)------------------------------
% 0.20/0.55  % (2437)------------------------------
% 0.20/0.55  % (2436)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 2.20/0.65  % (2478)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.20/0.66  % (2477)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.20/0.66  % (2479)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.20/0.66  % (2477)Refutation not found, incomplete strategy% (2477)------------------------------
% 2.20/0.66  % (2477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.66  % (2477)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.66  
% 2.20/0.66  % (2477)Memory used [KB]: 6140
% 2.20/0.66  % (2477)Time elapsed: 0.108 s
% 2.20/0.66  % (2477)------------------------------
% 2.20/0.66  % (2477)------------------------------
% 2.20/0.67  % (2480)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.20/0.68  % (2481)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.20/0.69  % (2482)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 3.21/0.79  % (2428)Refutation found. Thanks to Tanya!
% 3.21/0.79  % SZS status Theorem for theBenchmark
% 3.21/0.79  % SZS output start Proof for theBenchmark
% 3.21/0.79  fof(f2218,plain,(
% 3.21/0.79    $false),
% 3.21/0.79    inference(avatar_sat_refutation,[],[f1936,f2073,f2217])).
% 3.21/0.79  fof(f2217,plain,(
% 3.21/0.79    ~spl8_17),
% 3.21/0.79    inference(avatar_contradiction_clause,[],[f2216])).
% 3.21/0.79  fof(f2216,plain,(
% 3.21/0.79    $false | ~spl8_17),
% 3.21/0.79    inference(trivial_inequality_removal,[],[f2215])).
% 3.21/0.79  fof(f2215,plain,(
% 3.21/0.79    sK1 != sK1 | ~spl8_17),
% 3.21/0.79    inference(superposition,[],[f49,f1935])).
% 3.21/0.79  fof(f1935,plain,(
% 3.21/0.79    sK1 = sK3 | ~spl8_17),
% 3.21/0.79    inference(avatar_component_clause,[],[f1933])).
% 3.21/0.79  fof(f1933,plain,(
% 3.21/0.79    spl8_17 <=> sK1 = sK3),
% 3.21/0.79    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 3.21/0.79  fof(f49,plain,(
% 3.21/0.79    sK1 != sK3),
% 3.21/0.79    inference(cnf_transformation,[],[f37])).
% 3.21/0.79  fof(f37,plain,(
% 3.21/0.79    sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 3.21/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f28,f36])).
% 3.21/0.79  fof(f36,plain,(
% 3.21/0.79    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK1 != sK4 & sK1 != sK3 & r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 3.21/0.79    introduced(choice_axiom,[])).
% 3.21/0.79  fof(f28,plain,(
% 3.21/0.79    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 3.21/0.79    inference(ennf_transformation,[],[f25])).
% 3.21/0.79  fof(f25,negated_conjecture,(
% 3.21/0.79    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 3.21/0.79    inference(negated_conjecture,[],[f24])).
% 3.21/0.79  fof(f24,conjecture,(
% 3.21/0.79    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 3.21/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 3.21/0.79  fof(f2073,plain,(
% 3.21/0.79    ~spl8_16),
% 3.21/0.79    inference(avatar_contradiction_clause,[],[f2072])).
% 3.21/0.79  fof(f2072,plain,(
% 3.21/0.79    $false | ~spl8_16),
% 3.21/0.79    inference(trivial_inequality_removal,[],[f2071])).
% 3.21/0.79  fof(f2071,plain,(
% 3.21/0.79    sK1 != sK1 | ~spl8_16),
% 3.21/0.79    inference(superposition,[],[f50,f1931])).
% 3.21/0.79  fof(f1931,plain,(
% 3.21/0.79    sK1 = sK4 | ~spl8_16),
% 3.21/0.79    inference(avatar_component_clause,[],[f1929])).
% 3.21/0.79  fof(f1929,plain,(
% 3.21/0.79    spl8_16 <=> sK1 = sK4),
% 3.21/0.79    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 3.21/0.79  fof(f50,plain,(
% 3.21/0.79    sK1 != sK4),
% 3.21/0.79    inference(cnf_transformation,[],[f37])).
% 3.21/0.79  fof(f1936,plain,(
% 3.21/0.79    spl8_16 | spl8_17),
% 3.21/0.79    inference(avatar_split_clause,[],[f1923,f1933,f1929])).
% 3.21/0.79  fof(f1923,plain,(
% 3.21/0.79    sK1 = sK3 | sK1 = sK4),
% 3.21/0.79    inference(resolution,[],[f1820,f389])).
% 3.21/0.79  fof(f389,plain,(
% 3.21/0.79    ( ! [X2,X0,X1] : (r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 3.21/0.79    inference(resolution,[],[f101,f100])).
% 3.21/0.79  fof(f100,plain,(
% 3.21/0.79    ( ! [X0,X5,X3,X1] : (~sP0(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 3.21/0.79    inference(equality_resolution,[],[f72])).
% 3.21/0.79  fof(f72,plain,(
% 3.21/0.79    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 3.21/0.79    inference(cnf_transformation,[],[f46])).
% 3.21/0.79  fof(f46,plain,(
% 3.21/0.79    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK7(X0,X1,X2,X3) != X0 & sK7(X0,X1,X2,X3) != X1 & sK7(X0,X1,X2,X3) != X2) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sK7(X0,X1,X2,X3) = X0 | sK7(X0,X1,X2,X3) = X1 | sK7(X0,X1,X2,X3) = X2 | r2_hidden(sK7(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 3.21/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).
% 3.21/0.79  fof(f45,plain,(
% 3.21/0.79    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK7(X0,X1,X2,X3) != X0 & sK7(X0,X1,X2,X3) != X1 & sK7(X0,X1,X2,X3) != X2) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sK7(X0,X1,X2,X3) = X0 | sK7(X0,X1,X2,X3) = X1 | sK7(X0,X1,X2,X3) = X2 | r2_hidden(sK7(X0,X1,X2,X3),X3))))),
% 3.21/0.79    introduced(choice_axiom,[])).
% 3.21/0.79  fof(f44,plain,(
% 3.21/0.79    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 3.21/0.79    inference(rectify,[],[f43])).
% 3.21/0.79  fof(f43,plain,(
% 3.21/0.79    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 3.21/0.79    inference(flattening,[],[f42])).
% 3.21/0.79  fof(f42,plain,(
% 3.21/0.79    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 3.21/0.79    inference(nnf_transformation,[],[f34])).
% 3.21/0.79  fof(f34,plain,(
% 3.21/0.79    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.21/0.79    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.21/0.79  fof(f101,plain,(
% 3.21/0.79    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 3.21/0.79    inference(equality_resolution,[],[f97])).
% 3.21/0.79  fof(f97,plain,(
% 3.21/0.79    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.21/0.79    inference(definition_unfolding,[],[f79,f88])).
% 3.21/0.79  fof(f88,plain,(
% 3.21/0.79    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.21/0.79    inference(definition_unfolding,[],[f67,f87])).
% 3.21/0.79  fof(f87,plain,(
% 3.21/0.79    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.21/0.79    inference(definition_unfolding,[],[f69,f86])).
% 3.21/0.79  fof(f86,plain,(
% 3.21/0.79    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.21/0.79    inference(definition_unfolding,[],[f81,f85])).
% 3.21/0.79  fof(f85,plain,(
% 3.21/0.79    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.21/0.79    inference(definition_unfolding,[],[f82,f83])).
% 3.21/0.79  fof(f83,plain,(
% 3.21/0.79    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.21/0.79    inference(cnf_transformation,[],[f22])).
% 3.21/0.79  fof(f22,axiom,(
% 3.21/0.79    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.21/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 3.21/0.79  fof(f82,plain,(
% 3.21/0.79    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.21/0.79    inference(cnf_transformation,[],[f21])).
% 3.21/0.79  fof(f21,axiom,(
% 3.21/0.79    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.21/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 3.21/0.79  fof(f81,plain,(
% 3.21/0.79    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.21/0.79    inference(cnf_transformation,[],[f20])).
% 3.21/0.79  fof(f20,axiom,(
% 3.21/0.79    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.21/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 3.21/0.79  fof(f69,plain,(
% 3.21/0.79    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.21/0.79    inference(cnf_transformation,[],[f19])).
% 3.21/0.79  fof(f19,axiom,(
% 3.21/0.79    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.21/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 3.21/0.79  fof(f67,plain,(
% 3.21/0.79    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.21/0.79    inference(cnf_transformation,[],[f18])).
% 3.21/0.79  fof(f18,axiom,(
% 3.21/0.79    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.21/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 3.21/0.79  fof(f79,plain,(
% 3.21/0.79    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.21/0.79    inference(cnf_transformation,[],[f47])).
% 3.21/0.79  fof(f47,plain,(
% 3.21/0.79    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 3.21/0.79    inference(nnf_transformation,[],[f35])).
% 3.21/0.79  fof(f35,plain,(
% 3.21/0.79    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 3.21/0.79    inference(definition_folding,[],[f33,f34])).
% 3.21/0.79  fof(f33,plain,(
% 3.21/0.79    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.21/0.79    inference(ennf_transformation,[],[f14])).
% 3.21/0.79  fof(f14,axiom,(
% 3.21/0.79    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.21/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 3.21/0.79  fof(f1820,plain,(
% 3.21/0.79    ( ! [X4] : (~r2_hidden(X4,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK3,sK4)) | sK3 = X4 | sK4 = X4) )),
% 3.21/0.79    inference(backward_demodulation,[],[f693,f1783])).
% 3.21/0.79  fof(f1783,plain,(
% 3.21/0.79    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK3,sK4)),
% 3.21/0.79    inference(superposition,[],[f1704,f52])).
% 3.21/0.79  fof(f52,plain,(
% 3.21/0.79    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.21/0.79    inference(cnf_transformation,[],[f11])).
% 3.21/0.79  fof(f11,axiom,(
% 3.21/0.79    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.21/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 3.21/0.80  % (2488)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 3.21/0.81  fof(f1704,plain,(
% 3.21/0.81    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4),k1_xboole_0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK3,sK4)),
% 3.21/0.81    inference(forward_demodulation,[],[f1703,f1569])).
% 3.21/0.81  fof(f1569,plain,(
% 3.21/0.81    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,sK3,sK4) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 3.21/0.81    inference(superposition,[],[f95,f485])).
% 3.21/0.81  fof(f485,plain,(
% 3.21/0.81    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4)),
% 3.21/0.81    inference(forward_demodulation,[],[f484,f95])).
% 3.21/0.81  fof(f484,plain,(
% 3.21/0.81    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))),
% 3.21/0.81    inference(forward_demodulation,[],[f483,f52])).
% 3.21/0.81  fof(f483,plain,(
% 3.21/0.81    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k1_xboole_0)),
% 3.21/0.81    inference(forward_demodulation,[],[f461,f269])).
% 3.21/0.81  fof(f269,plain,(
% 3.21/0.81    ( ! [X9] : (k1_xboole_0 = k5_xboole_0(X9,X9)) )),
% 3.21/0.81    inference(forward_demodulation,[],[f268,f55])).
% 3.21/0.81  fof(f55,plain,(
% 3.21/0.81    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.21/0.81    inference(cnf_transformation,[],[f26])).
% 3.21/0.81  fof(f26,plain,(
% 3.21/0.81    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.21/0.81    inference(rectify,[],[f3])).
% 3.21/0.81  fof(f3,axiom,(
% 3.21/0.81    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.21/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 3.21/0.81  fof(f268,plain,(
% 3.21/0.81    ( ! [X9] : (k1_xboole_0 = k5_xboole_0(X9,k3_xboole_0(X9,X9))) )),
% 3.21/0.81    inference(forward_demodulation,[],[f261,f52])).
% 3.21/0.81  fof(f261,plain,(
% 3.21/0.81    ( ! [X9] : (k1_xboole_0 = k5_xboole_0(X9,k3_xboole_0(X9,k5_xboole_0(X9,k1_xboole_0)))) )),
% 3.21/0.81    inference(superposition,[],[f91,f109])).
% 3.21/0.81  fof(f109,plain,(
% 3.21/0.81    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.21/0.81    inference(resolution,[],[f108,f54])).
% 3.21/0.81  fof(f54,plain,(
% 3.21/0.81    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 3.21/0.81    inference(cnf_transformation,[],[f39])).
% 3.21/0.81  fof(f39,plain,(
% 3.21/0.81    ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0)),
% 3.21/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f38])).
% 3.21/0.81  fof(f38,plain,(
% 3.21/0.81    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 3.21/0.81    introduced(choice_axiom,[])).
% 3.21/0.81  fof(f29,plain,(
% 3.21/0.81    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.21/0.81    inference(ennf_transformation,[],[f5])).
% 3.21/0.81  fof(f5,axiom,(
% 3.21/0.81    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.21/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 3.21/0.81  fof(f108,plain,(
% 3.21/0.81    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 3.21/0.81    inference(resolution,[],[f65,f51])).
% 3.21/0.81  fof(f51,plain,(
% 3.21/0.81    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.21/0.81    inference(cnf_transformation,[],[f12])).
% 3.21/0.81  fof(f12,axiom,(
% 3.21/0.81    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.21/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 3.21/0.81  fof(f65,plain,(
% 3.21/0.81    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.21/0.81    inference(cnf_transformation,[],[f41])).
% 3.21/0.81  fof(f41,plain,(
% 3.21/0.81    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.21/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f40])).
% 3.21/0.81  fof(f40,plain,(
% 3.21/0.81    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)))),
% 3.21/0.81    introduced(choice_axiom,[])).
% 3.21/0.81  fof(f30,plain,(
% 3.21/0.81    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.21/0.81    inference(ennf_transformation,[],[f27])).
% 3.21/0.81  fof(f27,plain,(
% 3.21/0.81    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.21/0.81    inference(rectify,[],[f4])).
% 3.21/0.81  fof(f4,axiom,(
% 3.21/0.81    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.21/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 3.21/0.81  fof(f91,plain,(
% 3.21/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 3.21/0.81    inference(definition_unfolding,[],[f63,f62,f62])).
% 3.21/0.81  fof(f62,plain,(
% 3.21/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.21/0.81    inference(cnf_transformation,[],[f6])).
% 3.21/0.81  fof(f6,axiom,(
% 3.21/0.81    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.21/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.21/0.81  fof(f63,plain,(
% 3.21/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.21/0.81    inference(cnf_transformation,[],[f10])).
% 3.21/0.81  fof(f10,axiom,(
% 3.21/0.81    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.21/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.21/0.81  fof(f461,plain,(
% 3.21/0.81    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))),
% 3.21/0.81    inference(superposition,[],[f93,f131])).
% 3.21/0.81  fof(f131,plain,(
% 3.21/0.81    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 3.21/0.81    inference(resolution,[],[f66,f92])).
% 3.21/0.81  fof(f92,plain,(
% 3.21/0.81    r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 3.21/0.81    inference(definition_unfolding,[],[f48,f89,f89])).
% 3.21/0.81  fof(f89,plain,(
% 3.21/0.81    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.21/0.81    inference(definition_unfolding,[],[f59,f88])).
% 3.21/0.81  fof(f59,plain,(
% 3.21/0.81    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.21/0.81    inference(cnf_transformation,[],[f17])).
% 3.21/0.81  fof(f17,axiom,(
% 3.21/0.81    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.21/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.21/0.81  fof(f48,plain,(
% 3.21/0.81    r1_tarski(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 3.21/0.81    inference(cnf_transformation,[],[f37])).
% 3.21/0.81  fof(f66,plain,(
% 3.21/0.81    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 3.21/0.81    inference(cnf_transformation,[],[f31])).
% 3.21/0.81  fof(f31,plain,(
% 3.21/0.81    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.21/0.81    inference(ennf_transformation,[],[f9])).
% 3.21/0.81  fof(f9,axiom,(
% 3.21/0.81    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.21/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.21/0.81  fof(f93,plain,(
% 3.21/0.81    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.21/0.81    inference(definition_unfolding,[],[f57,f84,f84])).
% 3.21/0.81  fof(f84,plain,(
% 3.21/0.81    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.21/0.81    inference(definition_unfolding,[],[f61,f62])).
% 3.21/0.81  fof(f61,plain,(
% 3.21/0.81    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.21/0.81    inference(cnf_transformation,[],[f13])).
% 3.21/0.81  fof(f13,axiom,(
% 3.21/0.81    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.21/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 3.21/0.81  fof(f57,plain,(
% 3.21/0.81    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.21/0.81    inference(cnf_transformation,[],[f1])).
% 3.21/0.81  fof(f1,axiom,(
% 3.21/0.81    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.21/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.21/0.81  fof(f95,plain,(
% 3.21/0.81    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 3.21/0.81    inference(definition_unfolding,[],[f70,f87,f84,f89,f89])).
% 3.21/0.81  fof(f70,plain,(
% 3.21/0.81    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 3.21/0.81    inference(cnf_transformation,[],[f15])).
% 3.21/0.81  fof(f15,axiom,(
% 3.21/0.81    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 3.21/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 3.21/0.81  fof(f1703,plain,(
% 3.21/0.81    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4),k1_xboole_0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 3.21/0.81    inference(forward_demodulation,[],[f1684,f269])).
% 3.21/0.81  fof(f1684,plain,(
% 3.21/0.81    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 3.21/0.81    inference(superposition,[],[f93,f1352])).
% 3.21/0.81  fof(f1352,plain,(
% 3.21/0.81    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4))),
% 3.21/0.81    inference(resolution,[],[f1323,f102])).
% 3.21/0.81  fof(f102,plain,(
% 3.21/0.81    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 3.21/0.81    inference(superposition,[],[f56,f55])).
% 3.21/0.81  fof(f56,plain,(
% 3.21/0.81    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.21/0.81    inference(cnf_transformation,[],[f7])).
% 3.21/0.81  fof(f7,axiom,(
% 3.21/0.81    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.21/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 3.21/0.81  fof(f1323,plain,(
% 3.21/0.81    ( ! [X10] : (~r1_tarski(X10,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | k3_xboole_0(X10,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4)) = X10) )),
% 3.21/0.81    inference(superposition,[],[f496,f94])).
% 3.21/0.81  fof(f94,plain,(
% 3.21/0.81    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.21/0.81    inference(definition_unfolding,[],[f60,f90,f90,f89])).
% 3.21/0.81  fof(f90,plain,(
% 3.21/0.81    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.21/0.81    inference(definition_unfolding,[],[f53,f89])).
% 3.21/0.81  fof(f53,plain,(
% 3.21/0.81    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.21/0.81    inference(cnf_transformation,[],[f16])).
% 3.21/0.81  fof(f16,axiom,(
% 3.21/0.81    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.21/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 3.21/0.81  fof(f60,plain,(
% 3.21/0.81    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 3.21/0.81    inference(cnf_transformation,[],[f23])).
% 3.21/0.81  fof(f23,axiom,(
% 3.21/0.81    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 3.21/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 3.21/0.81  fof(f496,plain,(
% 3.21/0.81    ( ! [X2,X3] : (~r1_tarski(X3,k3_xboole_0(X2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) | k3_xboole_0(X3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4)) = X3) )),
% 3.21/0.81    inference(backward_demodulation,[],[f251,f485])).
% 3.21/0.81  fof(f251,plain,(
% 3.21/0.81    ( ! [X2,X3] : (~r1_tarski(X3,k3_xboole_0(X2,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) | k3_xboole_0(X3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = X3) )),
% 3.21/0.81    inference(superposition,[],[f243,f58])).
% 3.21/0.81  fof(f58,plain,(
% 3.21/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.21/0.81    inference(cnf_transformation,[],[f2])).
% 3.21/0.81  fof(f2,axiom,(
% 3.21/0.81    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.21/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.21/0.81  fof(f243,plain,(
% 3.21/0.81    ( ! [X2,X3] : (~r1_tarski(X2,k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),X3)) | k3_xboole_0(X2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = X2) )),
% 3.21/0.81    inference(resolution,[],[f238,f68])).
% 3.21/0.81  fof(f68,plain,(
% 3.21/0.81    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 3.21/0.81    inference(cnf_transformation,[],[f32])).
% 3.21/0.81  fof(f32,plain,(
% 3.21/0.81    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.21/0.81    inference(ennf_transformation,[],[f8])).
% 3.21/0.81  fof(f8,axiom,(
% 3.21/0.81    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 3.21/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 3.21/0.81  fof(f238,plain,(
% 3.21/0.81    ( ! [X1] : (~r1_tarski(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | k3_xboole_0(X1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = X1) )),
% 3.21/0.81    inference(superposition,[],[f201,f131])).
% 3.21/0.81  fof(f201,plain,(
% 3.21/0.81    ( ! [X4,X2,X3] : (~r1_tarski(X4,k3_xboole_0(X3,X2)) | k3_xboole_0(X4,X2) = X4) )),
% 3.21/0.81    inference(superposition,[],[f133,f58])).
% 3.21/0.81  fof(f133,plain,(
% 3.21/0.81    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | k3_xboole_0(X0,X1) = X0) )),
% 3.21/0.81    inference(resolution,[],[f68,f66])).
% 3.21/0.81  fof(f693,plain,(
% 3.21/0.81    ( ! [X4] : (~r2_hidden(X4,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4)) | sK3 = X4 | sK4 = X4) )),
% 3.21/0.81    inference(duplicate_literal_removal,[],[f692])).
% 3.21/0.81  fof(f692,plain,(
% 3.21/0.81    ( ! [X4] : (sK3 = X4 | sK3 = X4 | ~r2_hidden(X4,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4)) | sK4 = X4) )),
% 3.21/0.81    inference(resolution,[],[f71,f568])).
% 3.21/0.81  fof(f568,plain,(
% 3.21/0.81    sP0(sK4,sK3,sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK3,sK4))),
% 3.21/0.81    inference(superposition,[],[f101,f485])).
% 3.21/0.81  fof(f71,plain,(
% 3.21/0.81    ( ! [X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3) | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3) | X0 = X5) )),
% 3.21/0.81    inference(cnf_transformation,[],[f46])).
% 3.21/0.81  % SZS output end Proof for theBenchmark
% 3.21/0.81  % (2428)------------------------------
% 3.21/0.81  % (2428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.21/0.81  % (2428)Termination reason: Refutation
% 3.21/0.81  
% 3.21/0.81  % (2428)Memory used [KB]: 7419
% 3.21/0.81  % (2428)Time elapsed: 0.392 s
% 3.21/0.81  % (2428)------------------------------
% 3.21/0.81  % (2428)------------------------------
% 3.21/0.81  % (2409)Success in time 0.456 s
%------------------------------------------------------------------------------
