%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:34 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 244 expanded)
%              Number of leaves         :   21 (  84 expanded)
%              Depth                    :   13
%              Number of atoms          :  190 ( 454 expanded)
%              Number of equality atoms :   49 ( 153 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f382,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f82,f219,f257,f346,f378,f381])).

fof(f381,plain,
    ( spl5_2
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f379])).

fof(f379,plain,
    ( $false
    | spl5_2
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f75,f370,f65])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f39,f56])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f370,plain,
    ( r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_4 ),
    inference(resolution,[],[f218,f188])).

fof(f188,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k3_xboole_0(X4,X5))
      | r2_hidden(X3,X5) ) ),
    inference(resolution,[],[f183,f83])).

fof(f83,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f28,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f183,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(X6,X7)
      | ~ r2_hidden(X8,X6)
      | r2_hidden(X8,X7) ) ),
    inference(duplicate_literal_removal,[],[f181])).

fof(f181,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(X6,X7)
      | ~ r2_hidden(X8,X6)
      | ~ r2_hidden(X8,X6)
      | r2_hidden(X8,X7) ) ),
    inference(resolution,[],[f128,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(resolution,[],[f100,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f100,plain,(
    ! [X6,X7] :
      ( r1_xboole_0(X6,k5_xboole_0(X6,X7))
      | ~ r1_tarski(X6,X7) ) ),
    inference(superposition,[],[f31,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f218,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl5_4
  <=> r2_hidden(sK0,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f75,plain,
    ( sK0 != sK2
    | spl5_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl5_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f378,plain,
    ( ~ spl5_1
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f369])).

fof(f369,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f331,f83,f218,f183])).

fof(f331,plain,
    ( ~ r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_1 ),
    inference(resolution,[],[f71,f113])).

fof(f113,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X6,k5_xboole_0(X8,k3_xboole_0(X8,X7)))
      | ~ r2_hidden(X6,X7) ) ),
    inference(resolution,[],[f34,f60])).

fof(f60,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f29,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f71,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl5_1
  <=> r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f346,plain,
    ( spl5_4
    | spl5_3
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f337,f69,f78,f216])).

fof(f78,plain,
    ( spl5_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f337,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | ~ spl5_1 ),
    inference(resolution,[],[f71,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f257,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f67,f60,f244,f34])).

fof(f244,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f71,f74])).

fof(f74,plain,
    ( sK0 = sK2
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f67,plain,(
    ! [X2] : r2_hidden(X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f38,f56])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f219,plain,
    ( spl5_4
    | ~ spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f211,f69,f78,f216])).

fof(f211,plain,
    ( ~ r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | spl5_1 ),
    inference(resolution,[],[f70,f46])).

fof(f70,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f82,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f59,f78,f73,f69])).

fof(f59,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 = sK2
    | ~ r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f24,f33,f56])).

fof(f24,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 = sK2
    | ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <~> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      <=> ( X0 != X2
          & r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f81,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f58,f78,f69])).

fof(f58,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f25,f33,f56])).

fof(f25,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f20])).

fof(f76,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f57,f73,f69])).

fof(f57,plain,
    ( sK0 != sK2
    | r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f26,f33,f56])).

fof(f26,plain,
    ( sK0 != sK2
    | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:43:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.52  % (2958)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.52  % (2958)Refutation not found, incomplete strategy% (2958)------------------------------
% 0.22/0.52  % (2958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (2958)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (2958)Memory used [KB]: 6140
% 0.22/0.52  % (2958)Time elapsed: 0.105 s
% 0.22/0.52  % (2958)------------------------------
% 0.22/0.52  % (2958)------------------------------
% 0.22/0.52  % (2952)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (2959)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (2950)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (2962)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (2949)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (2957)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (2953)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (2966)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (2965)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (2954)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (2948)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (2948)Refutation not found, incomplete strategy% (2948)------------------------------
% 0.22/0.53  % (2948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (2948)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (2948)Memory used [KB]: 1663
% 0.22/0.53  % (2948)Time elapsed: 0.115 s
% 0.22/0.53  % (2948)------------------------------
% 0.22/0.53  % (2948)------------------------------
% 0.22/0.53  % (2970)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (2972)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (2951)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (2947)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (2969)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (2976)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (2961)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (2975)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (2973)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (2968)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (2961)Refutation not found, incomplete strategy% (2961)------------------------------
% 0.22/0.55  % (2961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (2955)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (2961)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (2961)Memory used [KB]: 1663
% 0.22/0.55  % (2961)Time elapsed: 0.126 s
% 0.22/0.55  % (2961)------------------------------
% 0.22/0.55  % (2961)------------------------------
% 1.47/0.55  % (2960)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.47/0.55  % (2971)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.47/0.55  % (2967)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.47/0.55  % (2964)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.47/0.56  % (2964)Refutation not found, incomplete strategy% (2964)------------------------------
% 1.47/0.56  % (2964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (2964)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (2964)Memory used [KB]: 1663
% 1.47/0.56  % (2964)Time elapsed: 0.147 s
% 1.47/0.56  % (2964)------------------------------
% 1.47/0.56  % (2964)------------------------------
% 1.47/0.56  % (2956)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.47/0.56  % (2960)Refutation found. Thanks to Tanya!
% 1.47/0.56  % SZS status Theorem for theBenchmark
% 1.47/0.56  % SZS output start Proof for theBenchmark
% 1.47/0.56  fof(f382,plain,(
% 1.47/0.56    $false),
% 1.47/0.56    inference(avatar_sat_refutation,[],[f76,f81,f82,f219,f257,f346,f378,f381])).
% 1.47/0.56  fof(f381,plain,(
% 1.47/0.56    spl5_2 | ~spl5_4),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f379])).
% 1.47/0.56  fof(f379,plain,(
% 1.47/0.56    $false | (spl5_2 | ~spl5_4)),
% 1.47/0.56    inference(unit_resulting_resolution,[],[f75,f370,f65])).
% 1.47/0.56  fof(f65,plain,(
% 1.47/0.56    ( ! [X2,X0] : (~r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X2) )),
% 1.47/0.56    inference(equality_resolution,[],[f63])).
% 1.47/0.56  fof(f63,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.47/0.56    inference(definition_unfolding,[],[f39,f56])).
% 1.47/0.56  fof(f56,plain,(
% 1.47/0.56    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.47/0.56    inference(definition_unfolding,[],[f27,f55])).
% 1.47/0.56  fof(f55,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.47/0.56    inference(definition_unfolding,[],[f32,f54])).
% 1.47/0.56  fof(f54,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.47/0.56    inference(definition_unfolding,[],[f42,f53])).
% 1.47/0.56  fof(f53,plain,(
% 1.47/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.47/0.56    inference(definition_unfolding,[],[f47,f52])).
% 1.47/0.56  fof(f52,plain,(
% 1.47/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.47/0.56    inference(definition_unfolding,[],[f48,f51])).
% 1.47/0.56  fof(f51,plain,(
% 1.47/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.47/0.56    inference(definition_unfolding,[],[f49,f50])).
% 1.47/0.56  fof(f50,plain,(
% 1.47/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f16])).
% 1.47/0.56  fof(f16,axiom,(
% 1.47/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.47/0.56  fof(f49,plain,(
% 1.47/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f15])).
% 1.47/0.56  fof(f15,axiom,(
% 1.47/0.56    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.47/0.56  fof(f48,plain,(
% 1.47/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f14])).
% 1.47/0.56  fof(f14,axiom,(
% 1.47/0.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.47/0.56  fof(f47,plain,(
% 1.47/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f13])).
% 1.47/0.56  fof(f13,axiom,(
% 1.47/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.47/0.56  fof(f42,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f12])).
% 1.47/0.56  fof(f12,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.47/0.56  fof(f32,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f11])).
% 1.47/0.56  fof(f11,axiom,(
% 1.47/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.47/0.56  fof(f27,plain,(
% 1.47/0.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f10])).
% 1.47/0.56  fof(f10,axiom,(
% 1.47/0.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.47/0.56  fof(f39,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.47/0.56    inference(cnf_transformation,[],[f9])).
% 1.47/0.56  fof(f9,axiom,(
% 1.47/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.47/0.56  fof(f370,plain,(
% 1.47/0.56    r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_4),
% 1.47/0.56    inference(resolution,[],[f218,f188])).
% 1.47/0.56  fof(f188,plain,(
% 1.47/0.56    ( ! [X4,X5,X3] : (~r2_hidden(X3,k3_xboole_0(X4,X5)) | r2_hidden(X3,X5)) )),
% 1.47/0.56    inference(resolution,[],[f183,f83])).
% 1.47/0.56  fof(f83,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 1.47/0.56    inference(superposition,[],[f28,f30])).
% 1.47/0.56  fof(f30,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f1])).
% 1.47/0.56  fof(f1,axiom,(
% 1.47/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.47/0.56  fof(f28,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f6])).
% 1.47/0.56  fof(f6,axiom,(
% 1.47/0.56    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.47/0.56  fof(f183,plain,(
% 1.47/0.56    ( ! [X6,X8,X7] : (~r1_tarski(X6,X7) | ~r2_hidden(X8,X6) | r2_hidden(X8,X7)) )),
% 1.47/0.56    inference(duplicate_literal_removal,[],[f181])).
% 1.47/0.56  fof(f181,plain,(
% 1.47/0.56    ( ! [X6,X8,X7] : (~r1_tarski(X6,X7) | ~r2_hidden(X8,X6) | ~r2_hidden(X8,X6) | r2_hidden(X8,X7)) )),
% 1.47/0.56    inference(resolution,[],[f128,f46])).
% 1.47/0.56  fof(f46,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f23])).
% 1.47/0.56  fof(f23,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.47/0.56    inference(ennf_transformation,[],[f2])).
% 1.47/0.56  fof(f2,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.47/0.56  fof(f128,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_xboole_0(X0,X1)) | ~r1_tarski(X0,X1) | ~r2_hidden(X2,X0)) )),
% 1.47/0.56    inference(resolution,[],[f100,f34])).
% 1.47/0.56  fof(f34,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f21])).
% 1.47/0.56  fof(f21,plain,(
% 1.47/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.47/0.56    inference(ennf_transformation,[],[f19])).
% 1.47/0.56  fof(f19,plain,(
% 1.47/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.47/0.56    inference(rectify,[],[f3])).
% 1.47/0.56  fof(f3,axiom,(
% 1.47/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.47/0.56  fof(f100,plain,(
% 1.47/0.56    ( ! [X6,X7] : (r1_xboole_0(X6,k5_xboole_0(X6,X7)) | ~r1_tarski(X6,X7)) )),
% 1.47/0.56    inference(superposition,[],[f31,f37])).
% 1.47/0.56  fof(f37,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f22])).
% 1.47/0.56  fof(f22,plain,(
% 1.47/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.47/0.56    inference(ennf_transformation,[],[f7])).
% 1.47/0.56  fof(f7,axiom,(
% 1.47/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.47/0.56  fof(f31,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f4])).
% 1.47/0.56  fof(f4,axiom,(
% 1.47/0.56    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 1.47/0.56  fof(f218,plain,(
% 1.47/0.56    r2_hidden(sK0,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | ~spl5_4),
% 1.47/0.56    inference(avatar_component_clause,[],[f216])).
% 1.47/0.56  fof(f216,plain,(
% 1.47/0.56    spl5_4 <=> r2_hidden(sK0,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.47/0.56  fof(f75,plain,(
% 1.47/0.56    sK0 != sK2 | spl5_2),
% 1.47/0.56    inference(avatar_component_clause,[],[f73])).
% 1.47/0.56  fof(f73,plain,(
% 1.47/0.56    spl5_2 <=> sK0 = sK2),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.47/0.56  fof(f378,plain,(
% 1.47/0.56    ~spl5_1 | ~spl5_4),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f369])).
% 1.47/0.56  fof(f369,plain,(
% 1.47/0.56    $false | (~spl5_1 | ~spl5_4)),
% 1.47/0.56    inference(unit_resulting_resolution,[],[f331,f83,f218,f183])).
% 1.47/0.56  fof(f331,plain,(
% 1.47/0.56    ~r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_1),
% 1.47/0.56    inference(resolution,[],[f71,f113])).
% 1.47/0.56  fof(f113,plain,(
% 1.47/0.56    ( ! [X6,X8,X7] : (~r2_hidden(X6,k5_xboole_0(X8,k3_xboole_0(X8,X7))) | ~r2_hidden(X6,X7)) )),
% 1.47/0.56    inference(resolution,[],[f34,f60])).
% 1.47/0.56  fof(f60,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 1.47/0.56    inference(definition_unfolding,[],[f29,f33])).
% 1.47/0.56  fof(f33,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f5])).
% 1.47/0.56  fof(f5,axiom,(
% 1.47/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.47/0.56  fof(f29,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f8])).
% 1.47/0.56  fof(f8,axiom,(
% 1.47/0.56    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.47/0.56  fof(f71,plain,(
% 1.47/0.56    r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | ~spl5_1),
% 1.47/0.56    inference(avatar_component_clause,[],[f69])).
% 1.47/0.56  fof(f69,plain,(
% 1.47/0.56    spl5_1 <=> r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.47/0.56  fof(f346,plain,(
% 1.47/0.56    spl5_4 | spl5_3 | ~spl5_1),
% 1.47/0.56    inference(avatar_split_clause,[],[f337,f69,f78,f216])).
% 1.47/0.56  fof(f78,plain,(
% 1.47/0.56    spl5_3 <=> r2_hidden(sK0,sK1)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.47/0.56  fof(f337,plain,(
% 1.47/0.56    r2_hidden(sK0,sK1) | r2_hidden(sK0,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | ~spl5_1),
% 1.47/0.56    inference(resolution,[],[f71,f43])).
% 1.47/0.56  fof(f43,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f23])).
% 1.47/0.56  fof(f257,plain,(
% 1.47/0.56    ~spl5_1 | ~spl5_2),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f246])).
% 1.47/0.56  fof(f246,plain,(
% 1.47/0.56    $false | (~spl5_1 | ~spl5_2)),
% 1.47/0.56    inference(unit_resulting_resolution,[],[f67,f60,f244,f34])).
% 1.47/0.56  fof(f244,plain,(
% 1.47/0.56    r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | (~spl5_1 | ~spl5_2)),
% 1.47/0.56    inference(forward_demodulation,[],[f71,f74])).
% 1.47/0.56  fof(f74,plain,(
% 1.47/0.56    sK0 = sK2 | ~spl5_2),
% 1.47/0.56    inference(avatar_component_clause,[],[f73])).
% 1.47/0.56  fof(f67,plain,(
% 1.47/0.56    ( ! [X2] : (r2_hidden(X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) )),
% 1.47/0.56    inference(equality_resolution,[],[f66])).
% 1.47/0.56  fof(f66,plain,(
% 1.47/0.56    ( ! [X2,X1] : (r2_hidden(X2,X1) | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1) )),
% 1.47/0.56    inference(equality_resolution,[],[f64])).
% 1.47/0.56  fof(f64,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.47/0.56    inference(definition_unfolding,[],[f38,f56])).
% 1.47/0.56  fof(f38,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.47/0.56    inference(cnf_transformation,[],[f9])).
% 1.47/0.56  fof(f219,plain,(
% 1.47/0.56    spl5_4 | ~spl5_3 | spl5_1),
% 1.47/0.56    inference(avatar_split_clause,[],[f211,f69,f78,f216])).
% 1.47/0.56  fof(f211,plain,(
% 1.47/0.56    ~r2_hidden(sK0,sK1) | r2_hidden(sK0,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | spl5_1),
% 1.47/0.56    inference(resolution,[],[f70,f46])).
% 1.47/0.56  fof(f70,plain,(
% 1.47/0.56    ~r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | spl5_1),
% 1.47/0.56    inference(avatar_component_clause,[],[f69])).
% 1.47/0.56  fof(f82,plain,(
% 1.47/0.56    ~spl5_1 | spl5_2 | ~spl5_3),
% 1.47/0.56    inference(avatar_split_clause,[],[f59,f78,f73,f69])).
% 1.47/0.56  fof(f59,plain,(
% 1.47/0.56    ~r2_hidden(sK0,sK1) | sK0 = sK2 | ~r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.47/0.56    inference(definition_unfolding,[],[f24,f33,f56])).
% 1.47/0.56  fof(f24,plain,(
% 1.47/0.56    ~r2_hidden(sK0,sK1) | sK0 = sK2 | ~r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 1.47/0.56    inference(cnf_transformation,[],[f20])).
% 1.47/0.56  fof(f20,plain,(
% 1.47/0.56    ? [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <~> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.47/0.56    inference(ennf_transformation,[],[f18])).
% 1.47/0.56  fof(f18,negated_conjecture,(
% 1.47/0.56    ~! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.47/0.56    inference(negated_conjecture,[],[f17])).
% 1.47/0.56  fof(f17,conjecture,(
% 1.47/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.47/0.56  fof(f81,plain,(
% 1.47/0.56    spl5_1 | spl5_3),
% 1.47/0.56    inference(avatar_split_clause,[],[f58,f78,f69])).
% 1.47/0.56  fof(f58,plain,(
% 1.47/0.56    r2_hidden(sK0,sK1) | r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.47/0.56    inference(definition_unfolding,[],[f25,f33,f56])).
% 1.47/0.56  fof(f25,plain,(
% 1.47/0.56    r2_hidden(sK0,sK1) | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 1.47/0.56    inference(cnf_transformation,[],[f20])).
% 1.47/0.56  fof(f76,plain,(
% 1.47/0.56    spl5_1 | ~spl5_2),
% 1.47/0.56    inference(avatar_split_clause,[],[f57,f73,f69])).
% 1.47/0.56  fof(f57,plain,(
% 1.47/0.56    sK0 != sK2 | r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.47/0.56    inference(definition_unfolding,[],[f26,f33,f56])).
% 1.47/0.56  fof(f26,plain,(
% 1.47/0.56    sK0 != sK2 | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 1.47/0.56    inference(cnf_transformation,[],[f20])).
% 1.47/0.56  % SZS output end Proof for theBenchmark
% 1.47/0.56  % (2960)------------------------------
% 1.47/0.56  % (2960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (2960)Termination reason: Refutation
% 1.47/0.56  
% 1.47/0.56  % (2960)Memory used [KB]: 6396
% 1.47/0.56  % (2960)Time elapsed: 0.157 s
% 1.47/0.56  % (2960)------------------------------
% 1.47/0.56  % (2960)------------------------------
% 1.47/0.56  % (2963)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.47/0.56  % (2963)Refutation not found, incomplete strategy% (2963)------------------------------
% 1.47/0.56  % (2963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (2963)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (2963)Memory used [KB]: 10618
% 1.47/0.56  % (2963)Time elapsed: 0.149 s
% 1.47/0.56  % (2963)------------------------------
% 1.47/0.56  % (2963)------------------------------
% 1.47/0.56  % (2946)Success in time 0.201 s
%------------------------------------------------------------------------------
