%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:07 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 448 expanded)
%              Number of leaves         :   21 ( 152 expanded)
%              Depth                    :   12
%              Number of atoms          :  276 ( 963 expanded)
%              Number of equality atoms :  119 ( 653 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f451,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f62,f107,f144,f167,f175,f217,f225,f234,f380,f381,f398,f413,f441,f446])).

fof(f446,plain,
    ( spl5_4
    | spl5_6
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f399,f367,f82,f59])).

fof(f59,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f82,plain,
    ( spl5_6
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f367,plain,
    ( spl5_16
  <=> sK0 = sK4(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f399,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK2
    | ~ spl5_16 ),
    inference(superposition,[],[f354,f369])).

fof(f369,plain,
    ( sK0 = sK4(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f367])).

fof(f354,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0,k1_xboole_0,k1_xboole_0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f348,f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f348,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0,k1_xboole_0,k1_xboole_0),X0)
      | k1_xboole_0 = k2_xboole_0(X0,k1_xboole_0) ) ),
    inference(condensation,[],[f342])).

fof(f342,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK4(X8,k1_xboole_0,k1_xboole_0),X8)
      | k1_xboole_0 = k2_xboole_0(X8,k1_xboole_0)
      | r2_hidden(sK4(X8,k1_xboole_0,k1_xboole_0),X9) ) ),
    inference(resolution,[],[f123,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f41,f14])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f123,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X1),X1)
      | r2_hidden(sK4(X0,X1,X1),X0)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(factoring,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f441,plain,
    ( spl5_9
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f439])).

fof(f439,plain,
    ( $false
    | spl5_9
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f138,f143,f71])).

fof(f71,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | sK0 = X1 ) ),
    inference(resolution,[],[f69,f41])).

fof(f69,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_xboole_0(sK1,sK2))
      | sK0 = X0 ) ),
    inference(superposition,[],[f38,f30])).

fof(f30,plain,(
    k2_xboole_0(sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f13,f29])).

fof(f29,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f15,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f16,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f16,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f15,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f13,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f38,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f18,f29])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f143,plain,
    ( r2_hidden(sK3(sK0,sK2),sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl5_10
  <=> r2_hidden(sK3(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f138,plain,
    ( sK0 != sK3(sK0,sK2)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl5_9
  <=> sK0 = sK3(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f413,plain,
    ( spl5_3
    | spl5_5
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f406,f377,f78,f54])).

fof(f54,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f78,plain,
    ( spl5_5
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f377,plain,
    ( spl5_18
  <=> sK0 = sK4(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f406,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ spl5_18 ),
    inference(superposition,[],[f354,f379])).

fof(f379,plain,
    ( sK0 = sK4(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f377])).

fof(f398,plain,
    ( ~ spl5_4
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f395])).

fof(f395,plain,
    ( $false
    | ~ spl5_4
    | spl5_5 ),
    inference(subsumption_resolution,[],[f79,f393])).

fof(f393,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f382,f14])).

fof(f382,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k1_xboole_0))
    | ~ spl5_4 ),
    inference(superposition,[],[f67,f60])).

fof(f60,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f67,plain,(
    r2_hidden(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f40,f30])).

fof(f40,plain,(
    ! [X2] : r2_hidden(X2,k2_enumset1(X2,X2,X2,X2)) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k2_enumset1(X2,X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f17,f29])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f79,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f381,plain,
    ( spl5_16
    | spl5_4 ),
    inference(avatar_split_clause,[],[f363,f59,f367])).

fof(f363,plain,
    ( k1_xboole_0 = sK2
    | sK0 = sK4(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f354,f71])).

fof(f380,plain,
    ( spl5_18
    | spl5_3 ),
    inference(avatar_split_clause,[],[f362,f54,f377])).

fof(f362,plain,
    ( k1_xboole_0 = sK1
    | sK0 = sK4(sK1,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f354,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK0 = X0 ) ),
    inference(resolution,[],[f69,f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f234,plain,
    ( spl5_1
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | spl5_1
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f176,f174])).

fof(f174,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl5_12
  <=> sK2 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f176,plain,
    ( sK2 != k2_xboole_0(sK1,sK2)
    | spl5_1 ),
    inference(superposition,[],[f47,f30])).

fof(f47,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl5_1
  <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f225,plain,
    ( spl5_2
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | spl5_2
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f212,f151])).

fof(f151,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl5_11
  <=> sK1 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f212,plain,
    ( sK1 != k2_xboole_0(sK1,sK2)
    | spl5_2 ),
    inference(superposition,[],[f51,f30])).

fof(f51,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl5_2
  <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f217,plain,
    ( ~ spl5_5
    | spl5_11
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f216,f100,f149,f78])).

fof(f100,plain,
    ( spl5_7
  <=> sK0 = sK3(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f216,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ r2_hidden(sK0,sK1)
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f215,f30])).

fof(f215,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK1 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl5_7 ),
    inference(trivial_inequality_removal,[],[f214])).

fof(f214,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK0,sK1)
    | sK1 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl5_7 ),
    inference(superposition,[],[f34,f102])).

fof(f102,plain,
    ( sK0 = sK3(sK0,sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f34,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != X0
      | ~ r2_hidden(sK3(X0,X1),X1)
      | k2_enumset1(X0,X0,X0,X0) = X1 ) ),
    inference(definition_unfolding,[],[f20,f29])).

fof(f20,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != X0
      | ~ r2_hidden(sK3(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f175,plain,
    ( ~ spl5_6
    | spl5_12
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f170,f137,f172,f82])).

fof(f170,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f169,f30])).

fof(f169,plain,
    ( ~ r2_hidden(sK0,sK2)
    | sK2 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl5_9 ),
    inference(trivial_inequality_removal,[],[f168])).

fof(f168,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK0,sK2)
    | sK2 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl5_9 ),
    inference(superposition,[],[f34,f139])).

fof(f139,plain,
    ( sK0 = sK3(sK0,sK2)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f137])).

fof(f167,plain,
    ( spl5_7
    | ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl5_7
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f101,f106,f70])).

fof(f106,plain,
    ( r2_hidden(sK3(sK0,sK1),sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_8
  <=> r2_hidden(sK3(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f101,plain,
    ( sK0 != sK3(sK0,sK1)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f144,plain,
    ( spl5_9
    | spl5_10
    | spl5_1 ),
    inference(avatar_split_clause,[],[f135,f45,f141,f137])).

fof(f135,plain,
    ( r2_hidden(sK3(sK0,sK2),sK2)
    | sK0 = sK3(sK0,sK2)
    | spl5_1 ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,
    ( ! [X2] :
        ( sK2 != X2
        | r2_hidden(sK3(sK0,X2),X2)
        | sK0 = sK3(sK0,X2) )
    | spl5_1 ),
    inference(superposition,[],[f47,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | r2_hidden(sK3(X0,X1),X1)
      | sK3(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f19,f29])).

fof(f19,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f107,plain,
    ( spl5_7
    | spl5_8
    | spl5_2 ),
    inference(avatar_split_clause,[],[f98,f49,f104,f100])).

fof(f98,plain,
    ( r2_hidden(sK3(sK0,sK1),sK1)
    | sK0 = sK3(sK0,sK1)
    | spl5_2 ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,
    ( ! [X1] :
        ( sK1 != X1
        | r2_hidden(sK3(sK0,X1),X1)
        | sK0 = sK3(sK0,X1) )
    | spl5_2 ),
    inference(superposition,[],[f51,f35])).

fof(f62,plain,
    ( ~ spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f33,f49,f59])).

fof(f33,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f10,f29])).

fof(f10,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,
    ( ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f32,f54,f45])).

fof(f32,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f11,f29])).

fof(f11,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f52,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f31,f49,f45])).

fof(f31,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK2 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f12,f29,f29])).

fof(f12,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:25:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.13/0.51  % (5584)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.13/0.52  % (5612)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.13/0.52  % (5602)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.13/0.52  % (5592)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.13/0.52  % (5588)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.13/0.52  % (5594)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.13/0.52  % (5609)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.13/0.52  % (5600)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.13/0.53  % (5600)Refutation not found, incomplete strategy% (5600)------------------------------
% 1.13/0.53  % (5600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.53  % (5600)Termination reason: Refutation not found, incomplete strategy
% 1.13/0.53  
% 1.13/0.53  % (5600)Memory used [KB]: 10618
% 1.13/0.53  % (5600)Time elapsed: 0.117 s
% 1.13/0.53  % (5600)------------------------------
% 1.13/0.53  % (5600)------------------------------
% 1.13/0.53  % (5607)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.29/0.53  % (5605)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.29/0.53  % (5599)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.29/0.53  % (5598)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.29/0.53  % (5608)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.29/0.53  % (5593)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.29/0.53  % (5610)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.29/0.54  % (5597)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.29/0.54  % (5591)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.29/0.54  % (5586)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.29/0.54  % (5590)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.54  % (5611)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.29/0.54  % (5585)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.29/0.54  % (5606)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.29/0.54  % (5613)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.29/0.54  % (5587)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.29/0.55  % (5601)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.29/0.55  % (5595)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.29/0.55  % (5603)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.29/0.55  % (5604)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.29/0.55  % (5589)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.29/0.55  % (5596)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.29/0.55  % (5585)Refutation not found, incomplete strategy% (5585)------------------------------
% 1.29/0.55  % (5585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (5585)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (5585)Memory used [KB]: 1663
% 1.29/0.55  % (5585)Time elapsed: 0.131 s
% 1.29/0.55  % (5585)------------------------------
% 1.29/0.55  % (5585)------------------------------
% 1.29/0.56  % (5613)Refutation not found, incomplete strategy% (5613)------------------------------
% 1.29/0.56  % (5613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.56  % (5613)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.56  
% 1.29/0.56  % (5613)Memory used [KB]: 1663
% 1.29/0.56  % (5613)Time elapsed: 0.002 s
% 1.29/0.56  % (5613)------------------------------
% 1.29/0.56  % (5613)------------------------------
% 1.29/0.57  % (5596)Refutation not found, incomplete strategy% (5596)------------------------------
% 1.29/0.57  % (5596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.57  % (5596)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.57  
% 1.29/0.57  % (5596)Memory used [KB]: 10618
% 1.29/0.57  % (5596)Time elapsed: 0.159 s
% 1.29/0.57  % (5596)------------------------------
% 1.29/0.57  % (5596)------------------------------
% 1.29/0.57  % (5597)Refutation found. Thanks to Tanya!
% 1.29/0.57  % SZS status Theorem for theBenchmark
% 1.29/0.57  % SZS output start Proof for theBenchmark
% 1.29/0.57  fof(f451,plain,(
% 1.29/0.57    $false),
% 1.29/0.57    inference(avatar_sat_refutation,[],[f52,f57,f62,f107,f144,f167,f175,f217,f225,f234,f380,f381,f398,f413,f441,f446])).
% 1.29/0.57  fof(f446,plain,(
% 1.29/0.57    spl5_4 | spl5_6 | ~spl5_16),
% 1.29/0.57    inference(avatar_split_clause,[],[f399,f367,f82,f59])).
% 1.29/0.57  fof(f59,plain,(
% 1.29/0.57    spl5_4 <=> k1_xboole_0 = sK2),
% 1.29/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.29/0.57  fof(f82,plain,(
% 1.29/0.57    spl5_6 <=> r2_hidden(sK0,sK2)),
% 1.29/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.29/0.57  fof(f367,plain,(
% 1.29/0.57    spl5_16 <=> sK0 = sK4(sK2,k1_xboole_0,k1_xboole_0)),
% 1.29/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.29/0.57  fof(f399,plain,(
% 1.29/0.57    r2_hidden(sK0,sK2) | k1_xboole_0 = sK2 | ~spl5_16),
% 1.29/0.57    inference(superposition,[],[f354,f369])).
% 1.29/0.57  fof(f369,plain,(
% 1.29/0.57    sK0 = sK4(sK2,k1_xboole_0,k1_xboole_0) | ~spl5_16),
% 1.29/0.57    inference(avatar_component_clause,[],[f367])).
% 1.29/0.57  fof(f354,plain,(
% 1.29/0.57    ( ! [X0] : (r2_hidden(sK4(X0,k1_xboole_0,k1_xboole_0),X0) | k1_xboole_0 = X0) )),
% 1.29/0.57    inference(forward_demodulation,[],[f348,f14])).
% 1.29/0.57  fof(f14,plain,(
% 1.29/0.57    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.29/0.57    inference(cnf_transformation,[],[f2])).
% 1.29/0.57  fof(f2,axiom,(
% 1.29/0.57    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.29/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.29/0.57  fof(f348,plain,(
% 1.29/0.57    ( ! [X0] : (r2_hidden(sK4(X0,k1_xboole_0,k1_xboole_0),X0) | k1_xboole_0 = k2_xboole_0(X0,k1_xboole_0)) )),
% 1.29/0.57    inference(condensation,[],[f342])).
% 1.29/0.57  fof(f342,plain,(
% 1.29/0.57    ( ! [X8,X9] : (r2_hidden(sK4(X8,k1_xboole_0,k1_xboole_0),X8) | k1_xboole_0 = k2_xboole_0(X8,k1_xboole_0) | r2_hidden(sK4(X8,k1_xboole_0,k1_xboole_0),X9)) )),
% 1.29/0.57    inference(resolution,[],[f123,f63])).
% 1.29/0.57  fof(f63,plain,(
% 1.29/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,X0)) )),
% 1.29/0.57    inference(superposition,[],[f41,f14])).
% 1.29/0.57  fof(f41,plain,(
% 1.29/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 1.29/0.57    inference(equality_resolution,[],[f27])).
% 1.29/0.57  fof(f27,plain,(
% 1.29/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.29/0.57    inference(cnf_transformation,[],[f1])).
% 1.29/0.57  fof(f1,axiom,(
% 1.29/0.57    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.29/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.29/0.57  fof(f123,plain,(
% 1.29/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X1),X1) | r2_hidden(sK4(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) )),
% 1.29/0.57    inference(factoring,[],[f24])).
% 1.29/0.57  fof(f24,plain,(
% 1.29/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) )),
% 1.29/0.57    inference(cnf_transformation,[],[f1])).
% 1.29/0.57  fof(f441,plain,(
% 1.29/0.57    spl5_9 | ~spl5_10),
% 1.29/0.57    inference(avatar_contradiction_clause,[],[f439])).
% 1.29/0.57  fof(f439,plain,(
% 1.29/0.57    $false | (spl5_9 | ~spl5_10)),
% 1.29/0.57    inference(unit_resulting_resolution,[],[f138,f143,f71])).
% 1.29/0.57  fof(f71,plain,(
% 1.29/0.57    ( ! [X1] : (~r2_hidden(X1,sK2) | sK0 = X1) )),
% 1.29/0.57    inference(resolution,[],[f69,f41])).
% 1.29/0.57  fof(f69,plain,(
% 1.29/0.57    ( ! [X0] : (~r2_hidden(X0,k2_xboole_0(sK1,sK2)) | sK0 = X0) )),
% 1.29/0.57    inference(superposition,[],[f38,f30])).
% 1.29/0.57  fof(f30,plain,(
% 1.29/0.57    k2_xboole_0(sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.29/0.57    inference(definition_unfolding,[],[f13,f29])).
% 1.29/0.57  fof(f29,plain,(
% 1.29/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.29/0.57    inference(definition_unfolding,[],[f15,f28])).
% 1.29/0.57  fof(f28,plain,(
% 1.29/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.29/0.57    inference(definition_unfolding,[],[f16,f21])).
% 1.29/0.57  fof(f21,plain,(
% 1.29/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.29/0.57    inference(cnf_transformation,[],[f6])).
% 1.29/0.57  fof(f6,axiom,(
% 1.29/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.29/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.29/0.57  fof(f16,plain,(
% 1.29/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.29/0.57    inference(cnf_transformation,[],[f5])).
% 1.29/0.57  fof(f5,axiom,(
% 1.29/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.29/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.29/0.57  fof(f15,plain,(
% 1.29/0.57    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.29/0.57    inference(cnf_transformation,[],[f4])).
% 1.29/0.57  fof(f4,axiom,(
% 1.29/0.57    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.29/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.29/0.57  fof(f13,plain,(
% 1.29/0.57    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.29/0.57    inference(cnf_transformation,[],[f9])).
% 1.29/0.57  fof(f9,plain,(
% 1.29/0.57    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.29/0.57    inference(ennf_transformation,[],[f8])).
% 1.29/0.57  fof(f8,negated_conjecture,(
% 1.29/0.57    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.29/0.57    inference(negated_conjecture,[],[f7])).
% 1.29/0.57  fof(f7,conjecture,(
% 1.29/0.57    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.29/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.29/0.57  fof(f38,plain,(
% 1.29/0.57    ( ! [X2,X0] : (~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) | X0 = X2) )),
% 1.29/0.57    inference(equality_resolution,[],[f36])).
% 1.29/0.57  fof(f36,plain,(
% 1.29/0.57    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.29/0.57    inference(definition_unfolding,[],[f18,f29])).
% 1.29/0.57  fof(f18,plain,(
% 1.29/0.57    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.29/0.57    inference(cnf_transformation,[],[f3])).
% 1.29/0.57  fof(f3,axiom,(
% 1.29/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.29/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.29/0.57  fof(f143,plain,(
% 1.29/0.57    r2_hidden(sK3(sK0,sK2),sK2) | ~spl5_10),
% 1.29/0.57    inference(avatar_component_clause,[],[f141])).
% 1.29/0.57  fof(f141,plain,(
% 1.29/0.57    spl5_10 <=> r2_hidden(sK3(sK0,sK2),sK2)),
% 1.29/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.29/0.57  fof(f138,plain,(
% 1.29/0.57    sK0 != sK3(sK0,sK2) | spl5_9),
% 1.29/0.57    inference(avatar_component_clause,[],[f137])).
% 1.29/0.57  fof(f137,plain,(
% 1.29/0.57    spl5_9 <=> sK0 = sK3(sK0,sK2)),
% 1.29/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.29/0.57  fof(f413,plain,(
% 1.29/0.57    spl5_3 | spl5_5 | ~spl5_18),
% 1.29/0.57    inference(avatar_split_clause,[],[f406,f377,f78,f54])).
% 1.29/0.57  fof(f54,plain,(
% 1.29/0.57    spl5_3 <=> k1_xboole_0 = sK1),
% 1.29/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.29/0.57  fof(f78,plain,(
% 1.29/0.57    spl5_5 <=> r2_hidden(sK0,sK1)),
% 1.29/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.29/0.57  fof(f377,plain,(
% 1.29/0.57    spl5_18 <=> sK0 = sK4(sK1,k1_xboole_0,k1_xboole_0)),
% 1.29/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.29/0.57  fof(f406,plain,(
% 1.29/0.57    r2_hidden(sK0,sK1) | k1_xboole_0 = sK1 | ~spl5_18),
% 1.29/0.57    inference(superposition,[],[f354,f379])).
% 1.29/0.57  fof(f379,plain,(
% 1.29/0.57    sK0 = sK4(sK1,k1_xboole_0,k1_xboole_0) | ~spl5_18),
% 1.29/0.57    inference(avatar_component_clause,[],[f377])).
% 1.29/0.57  fof(f398,plain,(
% 1.29/0.57    ~spl5_4 | spl5_5),
% 1.29/0.57    inference(avatar_contradiction_clause,[],[f395])).
% 1.29/0.57  fof(f395,plain,(
% 1.29/0.57    $false | (~spl5_4 | spl5_5)),
% 1.29/0.57    inference(subsumption_resolution,[],[f79,f393])).
% 1.29/0.57  fof(f393,plain,(
% 1.29/0.57    r2_hidden(sK0,sK1) | ~spl5_4),
% 1.29/0.57    inference(forward_demodulation,[],[f382,f14])).
% 1.29/0.57  fof(f382,plain,(
% 1.29/0.57    r2_hidden(sK0,k2_xboole_0(sK1,k1_xboole_0)) | ~spl5_4),
% 1.29/0.57    inference(superposition,[],[f67,f60])).
% 1.29/0.57  fof(f60,plain,(
% 1.29/0.57    k1_xboole_0 = sK2 | ~spl5_4),
% 1.29/0.57    inference(avatar_component_clause,[],[f59])).
% 1.29/0.57  fof(f67,plain,(
% 1.29/0.57    r2_hidden(sK0,k2_xboole_0(sK1,sK2))),
% 1.29/0.57    inference(superposition,[],[f40,f30])).
% 1.29/0.57  fof(f40,plain,(
% 1.29/0.57    ( ! [X2] : (r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))) )),
% 1.29/0.57    inference(equality_resolution,[],[f39])).
% 1.29/0.57  fof(f39,plain,(
% 1.29/0.57    ( ! [X2,X1] : (r2_hidden(X2,X1) | k2_enumset1(X2,X2,X2,X2) != X1) )),
% 1.29/0.57    inference(equality_resolution,[],[f37])).
% 1.29/0.57  fof(f37,plain,(
% 1.29/0.57    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.29/0.57    inference(definition_unfolding,[],[f17,f29])).
% 1.29/0.57  fof(f17,plain,(
% 1.29/0.57    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.29/0.57    inference(cnf_transformation,[],[f3])).
% 1.29/0.57  fof(f79,plain,(
% 1.29/0.57    ~r2_hidden(sK0,sK1) | spl5_5),
% 1.29/0.57    inference(avatar_component_clause,[],[f78])).
% 1.29/0.57  fof(f381,plain,(
% 1.29/0.57    spl5_16 | spl5_4),
% 1.29/0.57    inference(avatar_split_clause,[],[f363,f59,f367])).
% 1.29/0.57  fof(f363,plain,(
% 1.29/0.57    k1_xboole_0 = sK2 | sK0 = sK4(sK2,k1_xboole_0,k1_xboole_0)),
% 1.29/0.57    inference(resolution,[],[f354,f71])).
% 1.29/0.57  fof(f380,plain,(
% 1.29/0.57    spl5_18 | spl5_3),
% 1.29/0.57    inference(avatar_split_clause,[],[f362,f54,f377])).
% 1.29/0.57  fof(f362,plain,(
% 1.29/0.57    k1_xboole_0 = sK1 | sK0 = sK4(sK1,k1_xboole_0,k1_xboole_0)),
% 1.29/0.57    inference(resolution,[],[f354,f70])).
% 1.29/0.57  fof(f70,plain,(
% 1.29/0.57    ( ! [X0] : (~r2_hidden(X0,sK1) | sK0 = X0) )),
% 1.29/0.57    inference(resolution,[],[f69,f42])).
% 1.29/0.57  fof(f42,plain,(
% 1.29/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X0)) )),
% 1.29/0.57    inference(equality_resolution,[],[f26])).
% 1.29/0.57  fof(f26,plain,(
% 1.29/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.29/0.57    inference(cnf_transformation,[],[f1])).
% 1.29/0.57  fof(f234,plain,(
% 1.29/0.57    spl5_1 | ~spl5_12),
% 1.29/0.57    inference(avatar_contradiction_clause,[],[f227])).
% 1.29/0.57  fof(f227,plain,(
% 1.29/0.57    $false | (spl5_1 | ~spl5_12)),
% 1.29/0.57    inference(subsumption_resolution,[],[f176,f174])).
% 1.29/0.57  fof(f174,plain,(
% 1.29/0.57    sK2 = k2_xboole_0(sK1,sK2) | ~spl5_12),
% 1.29/0.57    inference(avatar_component_clause,[],[f172])).
% 1.29/0.57  fof(f172,plain,(
% 1.29/0.57    spl5_12 <=> sK2 = k2_xboole_0(sK1,sK2)),
% 1.29/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.29/0.57  fof(f176,plain,(
% 1.29/0.57    sK2 != k2_xboole_0(sK1,sK2) | spl5_1),
% 1.29/0.57    inference(superposition,[],[f47,f30])).
% 1.29/0.57  fof(f47,plain,(
% 1.29/0.57    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | spl5_1),
% 1.29/0.57    inference(avatar_component_clause,[],[f45])).
% 1.29/0.57  fof(f45,plain,(
% 1.29/0.57    spl5_1 <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.29/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.29/0.57  fof(f225,plain,(
% 1.29/0.57    spl5_2 | ~spl5_11),
% 1.29/0.57    inference(avatar_contradiction_clause,[],[f218])).
% 1.29/0.57  fof(f218,plain,(
% 1.29/0.57    $false | (spl5_2 | ~spl5_11)),
% 1.29/0.57    inference(subsumption_resolution,[],[f212,f151])).
% 1.29/0.57  fof(f151,plain,(
% 1.29/0.57    sK1 = k2_xboole_0(sK1,sK2) | ~spl5_11),
% 1.29/0.57    inference(avatar_component_clause,[],[f149])).
% 1.29/0.57  fof(f149,plain,(
% 1.29/0.57    spl5_11 <=> sK1 = k2_xboole_0(sK1,sK2)),
% 1.29/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.29/0.57  fof(f212,plain,(
% 1.29/0.57    sK1 != k2_xboole_0(sK1,sK2) | spl5_2),
% 1.29/0.57    inference(superposition,[],[f51,f30])).
% 1.29/0.57  fof(f51,plain,(
% 1.29/0.57    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | spl5_2),
% 1.29/0.57    inference(avatar_component_clause,[],[f49])).
% 1.29/0.57  fof(f49,plain,(
% 1.29/0.57    spl5_2 <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.29/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.29/0.57  fof(f217,plain,(
% 1.29/0.57    ~spl5_5 | spl5_11 | ~spl5_7),
% 1.29/0.57    inference(avatar_split_clause,[],[f216,f100,f149,f78])).
% 1.29/0.57  fof(f100,plain,(
% 1.29/0.57    spl5_7 <=> sK0 = sK3(sK0,sK1)),
% 1.29/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.29/0.57  fof(f216,plain,(
% 1.29/0.57    sK1 = k2_xboole_0(sK1,sK2) | ~r2_hidden(sK0,sK1) | ~spl5_7),
% 1.29/0.57    inference(forward_demodulation,[],[f215,f30])).
% 1.29/0.57  fof(f215,plain,(
% 1.29/0.57    ~r2_hidden(sK0,sK1) | sK1 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl5_7),
% 1.29/0.57    inference(trivial_inequality_removal,[],[f214])).
% 1.29/0.57  fof(f214,plain,(
% 1.29/0.57    sK0 != sK0 | ~r2_hidden(sK0,sK1) | sK1 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl5_7),
% 1.29/0.57    inference(superposition,[],[f34,f102])).
% 1.29/0.57  fof(f102,plain,(
% 1.29/0.57    sK0 = sK3(sK0,sK1) | ~spl5_7),
% 1.29/0.57    inference(avatar_component_clause,[],[f100])).
% 1.29/0.57  fof(f34,plain,(
% 1.29/0.57    ( ! [X0,X1] : (sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1) | k2_enumset1(X0,X0,X0,X0) = X1) )),
% 1.29/0.57    inference(definition_unfolding,[],[f20,f29])).
% 1.29/0.57  fof(f20,plain,(
% 1.29/0.57    ( ! [X0,X1] : (sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 1.29/0.57    inference(cnf_transformation,[],[f3])).
% 1.29/0.57  fof(f175,plain,(
% 1.29/0.57    ~spl5_6 | spl5_12 | ~spl5_9),
% 1.29/0.57    inference(avatar_split_clause,[],[f170,f137,f172,f82])).
% 1.29/0.57  fof(f170,plain,(
% 1.29/0.57    sK2 = k2_xboole_0(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~spl5_9),
% 1.29/0.57    inference(forward_demodulation,[],[f169,f30])).
% 1.29/0.57  fof(f169,plain,(
% 1.29/0.57    ~r2_hidden(sK0,sK2) | sK2 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl5_9),
% 1.29/0.57    inference(trivial_inequality_removal,[],[f168])).
% 1.29/0.57  fof(f168,plain,(
% 1.29/0.57    sK0 != sK0 | ~r2_hidden(sK0,sK2) | sK2 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl5_9),
% 1.29/0.57    inference(superposition,[],[f34,f139])).
% 1.29/0.57  fof(f139,plain,(
% 1.29/0.57    sK0 = sK3(sK0,sK2) | ~spl5_9),
% 1.29/0.57    inference(avatar_component_clause,[],[f137])).
% 1.29/0.57  fof(f167,plain,(
% 1.29/0.57    spl5_7 | ~spl5_8),
% 1.29/0.57    inference(avatar_contradiction_clause,[],[f165])).
% 1.29/0.57  fof(f165,plain,(
% 1.29/0.57    $false | (spl5_7 | ~spl5_8)),
% 1.29/0.57    inference(unit_resulting_resolution,[],[f101,f106,f70])).
% 1.29/0.57  fof(f106,plain,(
% 1.29/0.57    r2_hidden(sK3(sK0,sK1),sK1) | ~spl5_8),
% 1.29/0.57    inference(avatar_component_clause,[],[f104])).
% 1.29/0.57  fof(f104,plain,(
% 1.29/0.57    spl5_8 <=> r2_hidden(sK3(sK0,sK1),sK1)),
% 1.29/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.29/0.57  fof(f101,plain,(
% 1.29/0.57    sK0 != sK3(sK0,sK1) | spl5_7),
% 1.29/0.57    inference(avatar_component_clause,[],[f100])).
% 1.29/0.57  fof(f144,plain,(
% 1.29/0.57    spl5_9 | spl5_10 | spl5_1),
% 1.29/0.57    inference(avatar_split_clause,[],[f135,f45,f141,f137])).
% 1.29/0.57  fof(f135,plain,(
% 1.29/0.57    r2_hidden(sK3(sK0,sK2),sK2) | sK0 = sK3(sK0,sK2) | spl5_1),
% 1.29/0.57    inference(equality_resolution,[],[f95])).
% 1.29/0.57  fof(f95,plain,(
% 1.29/0.57    ( ! [X2] : (sK2 != X2 | r2_hidden(sK3(sK0,X2),X2) | sK0 = sK3(sK0,X2)) ) | spl5_1),
% 1.29/0.57    inference(superposition,[],[f47,f35])).
% 1.29/0.57  fof(f35,plain,(
% 1.29/0.57    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | r2_hidden(sK3(X0,X1),X1) | sK3(X0,X1) = X0) )),
% 1.29/0.57    inference(definition_unfolding,[],[f19,f29])).
% 1.29/0.57  fof(f19,plain,(
% 1.29/0.57    ( ! [X0,X1] : (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 1.29/0.57    inference(cnf_transformation,[],[f3])).
% 1.29/0.57  fof(f107,plain,(
% 1.29/0.57    spl5_7 | spl5_8 | spl5_2),
% 1.29/0.57    inference(avatar_split_clause,[],[f98,f49,f104,f100])).
% 1.29/0.57  fof(f98,plain,(
% 1.29/0.57    r2_hidden(sK3(sK0,sK1),sK1) | sK0 = sK3(sK0,sK1) | spl5_2),
% 1.29/0.57    inference(equality_resolution,[],[f94])).
% 1.29/0.57  fof(f94,plain,(
% 1.29/0.57    ( ! [X1] : (sK1 != X1 | r2_hidden(sK3(sK0,X1),X1) | sK0 = sK3(sK0,X1)) ) | spl5_2),
% 1.29/0.57    inference(superposition,[],[f51,f35])).
% 1.29/0.57  fof(f62,plain,(
% 1.29/0.57    ~spl5_4 | ~spl5_2),
% 1.29/0.57    inference(avatar_split_clause,[],[f33,f49,f59])).
% 1.29/0.57  fof(f33,plain,(
% 1.29/0.57    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 1.29/0.57    inference(definition_unfolding,[],[f10,f29])).
% 1.29/0.57  fof(f10,plain,(
% 1.29/0.57    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.29/0.57    inference(cnf_transformation,[],[f9])).
% 1.29/0.57  fof(f57,plain,(
% 1.29/0.57    ~spl5_1 | ~spl5_3),
% 1.29/0.57    inference(avatar_split_clause,[],[f32,f54,f45])).
% 1.29/0.57  fof(f32,plain,(
% 1.29/0.57    k1_xboole_0 != sK1 | sK2 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.29/0.57    inference(definition_unfolding,[],[f11,f29])).
% 1.29/0.57  fof(f11,plain,(
% 1.29/0.57    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 1.29/0.57    inference(cnf_transformation,[],[f9])).
% 1.29/0.57  fof(f52,plain,(
% 1.29/0.57    ~spl5_1 | ~spl5_2),
% 1.29/0.57    inference(avatar_split_clause,[],[f31,f49,f45])).
% 1.29/0.57  fof(f31,plain,(
% 1.29/0.57    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | sK2 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.29/0.57    inference(definition_unfolding,[],[f12,f29,f29])).
% 1.29/0.57  fof(f12,plain,(
% 1.29/0.57    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 1.29/0.57    inference(cnf_transformation,[],[f9])).
% 1.29/0.57  % SZS output end Proof for theBenchmark
% 1.29/0.57  % (5597)------------------------------
% 1.29/0.57  % (5597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.57  % (5597)Termination reason: Refutation
% 1.29/0.57  
% 1.29/0.57  % (5597)Memory used [KB]: 6396
% 1.29/0.57  % (5597)Time elapsed: 0.111 s
% 1.29/0.57  % (5597)------------------------------
% 1.29/0.57  % (5597)------------------------------
% 1.29/0.57  % (5583)Success in time 0.205 s
%------------------------------------------------------------------------------
