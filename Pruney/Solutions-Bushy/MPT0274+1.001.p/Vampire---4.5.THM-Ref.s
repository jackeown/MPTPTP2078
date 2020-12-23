%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0274+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 142 expanded)
%              Number of leaves         :   20 (  62 expanded)
%              Depth                    :    8
%              Number of atoms          :  235 ( 428 expanded)
%              Number of equality atoms :   41 (  91 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f164,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f36,f37,f41,f45,f49,f53,f57,f64,f75,f110,f115,f132,f138,f147,f157,f163])).

fof(f163,plain,
    ( ~ spl3_20
    | ~ spl3_22 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | ~ spl3_20
    | ~ spl3_22 ),
    inference(resolution,[],[f155,f137])).

fof(f137,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl3_20
  <=> r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f155,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_tarski(X0,sK1),sK2)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl3_22
  <=> ! [X0] : ~ r1_xboole_0(k2_tarski(X0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f157,plain,
    ( spl3_22
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f151,f145,f39,f154])).

fof(f39,plain,
    ( spl3_4
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f145,plain,
    ( spl3_21
  <=> ! [X0] : ~ r1_xboole_0(k2_tarski(sK1,X0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f151,plain,
    ( ! [X1] : ~ r1_xboole_0(k2_tarski(X1,sK1),sK2)
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(superposition,[],[f146,f40])).

fof(f40,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f146,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_tarski(sK1,X0),sK2)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f145])).

fof(f147,plain,
    ( spl3_21
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f143,f55,f32,f145])).

fof(f32,plain,
    ( spl3_3
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f55,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X2)
        | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f143,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_tarski(sK1,X0),sK2)
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f34,f56])).

fof(f56,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X2)
        | ~ r1_xboole_0(k2_tarski(X0,X1),X2) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f55])).

fof(f34,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f138,plain,
    ( spl3_20
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f130,f43,f24,f135])).

fof(f24,plain,
    ( spl3_1
  <=> k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f43,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f130,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(trivial_inequality_removal,[],[f129])).

fof(f129,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(superposition,[],[f44,f25])).

fof(f25,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f44,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != X0
        | r1_xboole_0(X0,X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f43])).

fof(f132,plain,
    ( ~ spl3_1
    | ~ spl3_5
    | ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f130,f114])).

fof(f114,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_tarski(sK0,X0),sK2)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl3_18
  <=> ! [X0] : ~ r1_xboole_0(k2_tarski(sK0,X0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f115,plain,
    ( spl3_18
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f111,f55,f28,f113])).

fof(f28,plain,
    ( spl3_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f111,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_tarski(sK0,X0),sK2)
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(resolution,[],[f30,f56])).

fof(f30,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f110,plain,
    ( spl3_1
    | spl3_3
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl3_1
    | spl3_3
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f108,f26])).

fof(f26,plain,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f108,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | spl3_3
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f101,f40])).

fof(f101,plain,
    ( k2_tarski(sK1,sK0) = k4_xboole_0(k2_tarski(sK1,sK0),sK2)
    | spl3_3
    | ~ spl3_10 ),
    inference(resolution,[],[f74,f33])).

fof(f33,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f74,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | k2_tarski(X0,sK0) = k4_xboole_0(k2_tarski(X0,sK0),sK2) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_10
  <=> ! [X0] :
        ( r2_hidden(X0,sK2)
        | k2_tarski(X0,sK0) = k4_xboole_0(k2_tarski(X0,sK0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f75,plain,
    ( spl3_10
    | spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f65,f62,f28,f73])).

fof(f62,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,X1)
        | r2_hidden(X2,X1)
        | k2_tarski(X2,X0) = k4_xboole_0(k2_tarski(X2,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f65,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | k2_tarski(X0,sK0) = k4_xboole_0(k2_tarski(X0,sK0),sK2) )
    | spl3_2
    | ~ spl3_9 ),
    inference(resolution,[],[f63,f29])).

fof(f29,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f63,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,X1)
        | r2_hidden(X2,X1)
        | k2_tarski(X2,X0) = k4_xboole_0(k2_tarski(X2,X0),X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f64,plain,
    ( spl3_9
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f58,f51,f47,f62])).

fof(f47,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f51,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(k2_tarski(X0,X2),X1)
        | r2_hidden(X2,X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f58,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,X1)
        | r2_hidden(X2,X1)
        | k2_tarski(X2,X0) = k4_xboole_0(k2_tarski(X2,X0),X1) )
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(resolution,[],[f52,f48])).

fof(f48,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f52,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(k2_tarski(X0,X2),X1)
        | r2_hidden(X2,X1)
        | r2_hidden(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f51])).

fof(f57,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f22,f55])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f53,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f21,f51])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f49,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f19,f47])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f45,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f20,f43])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f37,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f15,f28,f24])).

fof(f15,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( r2_hidden(sK1,sK2)
      | r2_hidden(sK0,sK2)
      | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( ~ r2_hidden(sK1,sK2)
        & ~ r2_hidden(sK0,sK2) )
      | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( r2_hidden(sK1,sK2)
        | r2_hidden(sK0,sK2)
        | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( ~ r2_hidden(sK1,sK2)
          & ~ r2_hidden(sK0,sK2) )
        | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f36,plain,
    ( spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f16,f32,f24])).

fof(f16,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,
    ( ~ spl3_1
    | spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f17,f32,f28,f24])).

fof(f17,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
