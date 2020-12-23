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
% DateTime   : Thu Dec  3 12:40:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 187 expanded)
%              Number of leaves         :   32 (  78 expanded)
%              Depth                    :    9
%              Number of atoms          :  253 ( 388 expanded)
%              Number of equality atoms :   56 ( 118 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f371,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f61,f65,f69,f73,f80,f101,f108,f265,f269,f288,f290,f298,f318,f329,f349,f369])).

fof(f369,plain,
    ( ~ spl4_23
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(avatar_contradiction_clause,[],[f368])).

fof(f368,plain,
    ( $false
    | ~ spl4_23
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f363,f287])).

fof(f287,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl4_24
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f363,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl4_23
    | ~ spl4_25 ),
    inference(superposition,[],[f297,f282])).

fof(f282,plain,
    ( sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl4_23
  <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f297,plain,
    ( ! [X2,X3] : ~ r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,k3_enumset1(X2,X2,X2,X2,X2))))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl4_25
  <=> ! [X3,X2] : ~ r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,k3_enumset1(X2,X2,X2,X2,X2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f349,plain,
    ( ~ spl4_1
    | ~ spl4_4
    | spl4_23
    | ~ spl4_28 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_4
    | spl4_23
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f347,f56])).

fof(f56,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl4_1
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f347,plain,
    ( sK0 != k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl4_4
    | spl4_23
    | ~ spl4_28 ),
    inference(backward_demodulation,[],[f283,f330])).

fof(f330,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl4_4
    | ~ spl4_28 ),
    inference(superposition,[],[f328,f68])).

fof(f68,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl4_4
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f328,plain,
    ( k1_xboole_0 = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl4_28
  <=> k1_xboole_0 = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f283,plain,
    ( sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f281])).

fof(f329,plain,
    ( spl4_28
    | spl4_24
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f324,f316,f285,f326])).

fof(f316,plain,
    ( spl4_27
  <=> ! [X3,X2] :
        ( r2_hidden(X2,X3)
        | k1_xboole_0 = k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f324,plain,
    ( k1_xboole_0 = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
    | spl4_24
    | ~ spl4_27 ),
    inference(resolution,[],[f317,f286])).

fof(f286,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl4_24 ),
    inference(avatar_component_clause,[],[f285])).

fof(f317,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,X3)
        | k1_xboole_0 = k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),X3) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f316])).

fof(f318,plain,
    ( spl4_27
    | ~ spl4_10
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f271,f263,f106,f316])).

fof(f106,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f263,plain,
    ( spl4_20
  <=> ! [X1,X0] :
        ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f271,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,X3)
        | k1_xboole_0 = k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),X3) )
    | ~ spl4_10
    | ~ spl4_20 ),
    inference(resolution,[],[f264,f107])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f106])).

fof(f264,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
        | r2_hidden(X0,X1) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f263])).

fof(f298,plain,
    ( spl4_25
    | ~ spl4_6
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f274,f267,f78,f296])).

fof(f78,plain,
    ( spl4_6
  <=> ! [X1,X0] : r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f267,plain,
    ( spl4_21
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f274,plain,
    ( ! [X2,X3] : ~ r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,k3_enumset1(X2,X2,X2,X2,X2))))
    | ~ spl4_6
    | ~ spl4_21 ),
    inference(resolution,[],[f268,f79])).

fof(f79,plain,
    ( ! [X0,X1] : r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f268,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f267])).

fof(f290,plain,
    ( ~ spl4_24
    | spl4_23 ),
    inference(avatar_split_clause,[],[f289,f281,f285])).

fof(f289,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl4_23 ),
    inference(subsumption_resolution,[],[f50,f283])).

fof(f50,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f30,f38,f48])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f30,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( r2_hidden(sK1,sK0)
      | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
    & ( ~ r2_hidden(sK1,sK0)
      | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK1,sK0)
        | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
      & ( ~ r2_hidden(sK1,sK0)
        | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f288,plain,
    ( ~ spl4_23
    | spl4_24 ),
    inference(avatar_split_clause,[],[f49,f285,f281])).

fof(f49,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f31,f38,f48])).

fof(f31,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f269,plain,(
    spl4_21 ),
    inference(avatar_split_clause,[],[f53,f267])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f43,f48])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f265,plain,(
    spl4_20 ),
    inference(avatar_split_clause,[],[f52,f263])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f48])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f108,plain,
    ( spl4_10
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f102,f99,f63,f106])).

fof(f63,plain,
    ( spl4_3
  <=> ! [X0] :
        ( r2_hidden(sK2(X0),X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f99,plain,
    ( spl4_9
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(resolution,[],[f100,f64])).

fof(f64,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f100,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f101,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f40,f99])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f80,plain,
    ( spl4_6
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f74,f71,f59,f78])).

fof(f59,plain,
    ( spl4_2
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f71,plain,
    ( spl4_5
  <=> ! [X1,X0] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f74,plain,
    ( ! [X0,X1] : r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(resolution,[],[f72,f60])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f72,plain,
    ( ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f73,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f51,f71])).

fof(f51,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f35,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f69,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f36,f67])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f65,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f34,f63])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f61,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f42,f59])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f57,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f32,f55])).

fof(f32,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (18570)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.43  % (18570)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f371,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f57,f61,f65,f69,f73,f80,f101,f108,f265,f269,f288,f290,f298,f318,f329,f349,f369])).
% 0.20/0.43  fof(f369,plain,(
% 0.20/0.43    ~spl4_23 | ~spl4_24 | ~spl4_25),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f368])).
% 0.20/0.43  fof(f368,plain,(
% 0.20/0.43    $false | (~spl4_23 | ~spl4_24 | ~spl4_25)),
% 0.20/0.43    inference(subsumption_resolution,[],[f363,f287])).
% 0.20/0.43  fof(f287,plain,(
% 0.20/0.43    r2_hidden(sK1,sK0) | ~spl4_24),
% 0.20/0.43    inference(avatar_component_clause,[],[f285])).
% 0.20/0.43  fof(f285,plain,(
% 0.20/0.43    spl4_24 <=> r2_hidden(sK1,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.43  fof(f363,plain,(
% 0.20/0.43    ~r2_hidden(sK1,sK0) | (~spl4_23 | ~spl4_25)),
% 0.20/0.43    inference(superposition,[],[f297,f282])).
% 0.20/0.43  fof(f282,plain,(
% 0.20/0.43    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | ~spl4_23),
% 0.20/0.43    inference(avatar_component_clause,[],[f281])).
% 0.20/0.43  fof(f281,plain,(
% 0.20/0.43    spl4_23 <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.43  fof(f297,plain,(
% 0.20/0.43    ( ! [X2,X3] : (~r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,k3_enumset1(X2,X2,X2,X2,X2))))) ) | ~spl4_25),
% 0.20/0.43    inference(avatar_component_clause,[],[f296])).
% 0.20/0.43  fof(f296,plain,(
% 0.20/0.43    spl4_25 <=> ! [X3,X2] : ~r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,k3_enumset1(X2,X2,X2,X2,X2))))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.20/0.43  fof(f349,plain,(
% 0.20/0.43    ~spl4_1 | ~spl4_4 | spl4_23 | ~spl4_28),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f348])).
% 0.20/0.43  fof(f348,plain,(
% 0.20/0.43    $false | (~spl4_1 | ~spl4_4 | spl4_23 | ~spl4_28)),
% 0.20/0.43    inference(subsumption_resolution,[],[f347,f56])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl4_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f55])).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    spl4_1 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.43  fof(f347,plain,(
% 0.20/0.43    sK0 != k5_xboole_0(sK0,k1_xboole_0) | (~spl4_4 | spl4_23 | ~spl4_28)),
% 0.20/0.43    inference(backward_demodulation,[],[f283,f330])).
% 0.20/0.43  fof(f330,plain,(
% 0.20/0.43    k1_xboole_0 = k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | (~spl4_4 | ~spl4_28)),
% 0.20/0.43    inference(superposition,[],[f328,f68])).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl4_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f67])).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    spl4_4 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.43  fof(f328,plain,(
% 0.20/0.43    k1_xboole_0 = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) | ~spl4_28),
% 0.20/0.43    inference(avatar_component_clause,[],[f326])).
% 0.20/0.43  fof(f326,plain,(
% 0.20/0.43    spl4_28 <=> k1_xboole_0 = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.20/0.43  fof(f283,plain,(
% 0.20/0.43    sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | spl4_23),
% 0.20/0.43    inference(avatar_component_clause,[],[f281])).
% 0.20/0.43  fof(f329,plain,(
% 0.20/0.43    spl4_28 | spl4_24 | ~spl4_27),
% 0.20/0.43    inference(avatar_split_clause,[],[f324,f316,f285,f326])).
% 0.20/0.43  fof(f316,plain,(
% 0.20/0.43    spl4_27 <=> ! [X3,X2] : (r2_hidden(X2,X3) | k1_xboole_0 = k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),X3))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.20/0.43  fof(f324,plain,(
% 0.20/0.43    k1_xboole_0 = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) | (spl4_24 | ~spl4_27)),
% 0.20/0.43    inference(resolution,[],[f317,f286])).
% 0.20/0.43  fof(f286,plain,(
% 0.20/0.43    ~r2_hidden(sK1,sK0) | spl4_24),
% 0.20/0.43    inference(avatar_component_clause,[],[f285])).
% 0.20/0.43  fof(f317,plain,(
% 0.20/0.43    ( ! [X2,X3] : (r2_hidden(X2,X3) | k1_xboole_0 = k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),X3)) ) | ~spl4_27),
% 0.20/0.43    inference(avatar_component_clause,[],[f316])).
% 0.20/0.43  fof(f318,plain,(
% 0.20/0.43    spl4_27 | ~spl4_10 | ~spl4_20),
% 0.20/0.43    inference(avatar_split_clause,[],[f271,f263,f106,f316])).
% 0.20/0.43  fof(f106,plain,(
% 0.20/0.43    spl4_10 <=> ! [X1,X0] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.43  fof(f263,plain,(
% 0.20/0.43    spl4_20 <=> ! [X1,X0] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.43  fof(f271,plain,(
% 0.20/0.43    ( ! [X2,X3] : (r2_hidden(X2,X3) | k1_xboole_0 = k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),X3)) ) | (~spl4_10 | ~spl4_20)),
% 0.20/0.43    inference(resolution,[],[f264,f107])).
% 0.20/0.43  fof(f107,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl4_10),
% 0.20/0.43    inference(avatar_component_clause,[],[f106])).
% 0.20/0.43  fof(f264,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) ) | ~spl4_20),
% 0.20/0.43    inference(avatar_component_clause,[],[f263])).
% 0.20/0.43  fof(f298,plain,(
% 0.20/0.43    spl4_25 | ~spl4_6 | ~spl4_21),
% 0.20/0.43    inference(avatar_split_clause,[],[f274,f267,f78,f296])).
% 0.20/0.43  fof(f78,plain,(
% 0.20/0.43    spl4_6 <=> ! [X1,X0] : r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.43  fof(f267,plain,(
% 0.20/0.43    spl4_21 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.20/0.43  fof(f274,plain,(
% 0.20/0.43    ( ! [X2,X3] : (~r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,k3_enumset1(X2,X2,X2,X2,X2))))) ) | (~spl4_6 | ~spl4_21)),
% 0.20/0.43    inference(resolution,[],[f268,f79])).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ) | ~spl4_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f78])).
% 0.20/0.43  fof(f268,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) ) | ~spl4_21),
% 0.20/0.43    inference(avatar_component_clause,[],[f267])).
% 0.20/0.43  fof(f290,plain,(
% 0.20/0.43    ~spl4_24 | spl4_23),
% 0.20/0.43    inference(avatar_split_clause,[],[f289,f281,f285])).
% 0.20/0.43  fof(f289,plain,(
% 0.20/0.43    ~r2_hidden(sK1,sK0) | spl4_23),
% 0.20/0.43    inference(subsumption_resolution,[],[f50,f283])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    ~r2_hidden(sK1,sK0) | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 0.20/0.43    inference(definition_unfolding,[],[f30,f38,f48])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f33,f47])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f37,f46])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f44,f45])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,axiom,(
% 0.20/0.43    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,axiom,(
% 0.20/0.43    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.20/0.43    inference(cnf_transformation,[],[f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    (r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 0.20/0.43    inference(nnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f15])).
% 0.20/0.43  fof(f15,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.20/0.43    inference(negated_conjecture,[],[f14])).
% 0.20/0.43  fof(f14,conjecture,(
% 0.20/0.43    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.20/0.43  fof(f288,plain,(
% 0.20/0.43    ~spl4_23 | spl4_24),
% 0.20/0.43    inference(avatar_split_clause,[],[f49,f285,f281])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    r2_hidden(sK1,sK0) | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 0.20/0.43    inference(definition_unfolding,[],[f31,f38,f48])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.20/0.43    inference(cnf_transformation,[],[f25])).
% 0.20/0.43  fof(f269,plain,(
% 0.20/0.43    spl4_21),
% 0.20/0.43    inference(avatar_split_clause,[],[f53,f267])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f43,f48])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f22])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,axiom,(
% 0.20/0.43    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.20/0.43  fof(f265,plain,(
% 0.20/0.43    spl4_20),
% 0.20/0.43    inference(avatar_split_clause,[],[f52,f263])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f41,f48])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,axiom,(
% 0.20/0.43    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.20/0.43  fof(f108,plain,(
% 0.20/0.43    spl4_10 | ~spl4_3 | ~spl4_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f102,f99,f63,f106])).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    spl4_3 <=> ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.43  fof(f99,plain,(
% 0.20/0.43    spl4_9 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.43  fof(f102,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) ) | (~spl4_3 | ~spl4_9)),
% 0.20/0.43    inference(resolution,[],[f100,f64])).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) ) | ~spl4_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f63])).
% 0.20/0.43  fof(f100,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl4_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f99])).
% 0.20/0.43  fof(f101,plain,(
% 0.20/0.43    spl4_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f40,f99])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f28])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.43    inference(ennf_transformation,[],[f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.43    inference(rectify,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.43  fof(f80,plain,(
% 0.20/0.43    spl4_6 | ~spl4_2 | ~spl4_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f74,f71,f59,f78])).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    spl4_2 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    spl4_5 <=> ! [X1,X0] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.43  fof(f74,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ) | (~spl4_2 | ~spl4_5)),
% 0.20/0.43    inference(resolution,[],[f72,f60])).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl4_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f59])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) ) | ~spl4_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f71])).
% 0.20/0.43  fof(f73,plain,(
% 0.20/0.43    spl4_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f51,f71])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f35,f38])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    spl4_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f36,f67])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    spl4_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f34,f63])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.43  fof(f61,plain,(
% 0.20/0.43    spl4_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f42,f59])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    spl4_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f32,f55])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (18570)------------------------------
% 0.20/0.43  % (18570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (18570)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (18570)Memory used [KB]: 6268
% 0.20/0.43  % (18570)Time elapsed: 0.014 s
% 0.20/0.43  % (18570)------------------------------
% 0.20/0.43  % (18570)------------------------------
% 0.20/0.43  % (18562)Success in time 0.077 s
%------------------------------------------------------------------------------
