%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0751+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 205 expanded)
%              Number of leaves         :   25 (  82 expanded)
%              Depth                    :   17
%              Number of atoms          :  408 ( 858 expanded)
%              Number of equality atoms :   38 ( 112 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f316,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f71,f75,f76,f80,f85,f92,f128,f131,f157,f179,f235,f248,f300])).

fof(f300,plain,
    ( ~ spl3_5
    | spl3_2
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f296,f123,f63,f78])).

fof(f78,plain,
    ( spl3_5
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f63,plain,
    ( spl3_2
  <=> v4_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f123,plain,
    ( spl3_10
  <=> r2_hidden(k1_ordinal1(sK2(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f296,plain,
    ( v4_ordinal1(sK0)
    | ~ v3_ordinal1(sK0)
    | ~ spl3_10 ),
    inference(resolution,[],[f124,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
      | v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ( ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
            & r2_hidden(sK2(X0),X0)
            & v3_ordinal1(sK2(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
        & r2_hidden(sK2(X0),X0)
        & v3_ordinal1(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X1] :
              ( r2_hidden(k1_ordinal1(X1),X0)
              | ~ r2_hidden(X1,X0)
              | ~ v3_ordinal1(X1) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).

fof(f124,plain,
    ( r2_hidden(k1_ordinal1(sK2(sK0)),sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f248,plain,
    ( ~ spl3_12
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f238,f146,f146])).

fof(f146,plain,
    ( spl3_12
  <=> r2_hidden(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f238,plain,
    ( ~ r2_hidden(sK0,sK0)
    | ~ spl3_12 ),
    inference(resolution,[],[f234,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f234,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f146])).

fof(f235,plain,
    ( ~ spl3_4
    | spl3_12
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f233,f177,f83,f67,f146,f73])).

fof(f73,plain,
    ( spl3_4
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f67,plain,
    ( spl3_3
  <=> sK0 = k1_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f83,plain,
    ( spl3_6
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f177,plain,
    ( spl3_19
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_ordinal1(X0),sK0)
        | ~ v3_ordinal1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f233,plain,
    ( r2_hidden(sK0,sK0)
    | ~ v3_ordinal1(sK1)
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f232,f68])).

fof(f68,plain,
    ( sK0 = k1_ordinal1(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f232,plain,
    ( r2_hidden(k1_ordinal1(sK1),sK0)
    | ~ v3_ordinal1(sK1)
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(resolution,[],[f178,f84])).

fof(f84,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f178,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_ordinal1(X0),sK0)
        | ~ v3_ordinal1(X0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f177])).

fof(f179,plain,
    ( ~ spl3_5
    | spl3_19
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f175,f63,f177,f78])).

fof(f175,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v3_ordinal1(X0)
        | r2_hidden(k1_ordinal1(X0),sK0)
        | ~ v3_ordinal1(sK0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f64,f49])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ v4_ordinal1(X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | r2_hidden(k1_ordinal1(X2),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f64,plain,
    ( v4_ordinal1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f157,plain,
    ( ~ spl3_11
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f144,f120,f60,f126])).

fof(f126,plain,
    ( spl3_11
  <=> v3_ordinal1(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f60,plain,
    ( spl3_1
  <=> ! [X2] :
        ( k1_ordinal1(X2) != sK0
        | ~ v3_ordinal1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f120,plain,
    ( spl3_9
  <=> sK0 = k1_ordinal1(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f144,plain,
    ( ~ v3_ordinal1(sK2(sK0))
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(trivial_inequality_removal,[],[f137])).

fof(f137,plain,
    ( sK0 != sK0
    | ~ v3_ordinal1(sK2(sK0))
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(superposition,[],[f61,f121])).

fof(f121,plain,
    ( sK0 = k1_ordinal1(sK2(sK0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f61,plain,
    ( ! [X2] :
        ( k1_ordinal1(X2) != sK0
        | ~ v3_ordinal1(X2) )
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f131,plain,
    ( ~ spl3_5
    | spl3_2
    | spl3_11 ),
    inference(avatar_split_clause,[],[f130,f126,f63,f78])).

fof(f130,plain,
    ( v4_ordinal1(sK0)
    | ~ v3_ordinal1(sK0)
    | spl3_11 ),
    inference(resolution,[],[f127,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v3_ordinal1(sK2(X0))
      | v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f127,plain,
    ( ~ v3_ordinal1(sK2(sK0))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f128,plain,
    ( spl3_9
    | ~ spl3_5
    | spl3_10
    | ~ spl3_11
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f116,f90,f126,f123,f78,f120])).

fof(f90,plain,
    ( spl3_7
  <=> r2_hidden(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f116,plain,
    ( ~ v3_ordinal1(sK2(sK0))
    | r2_hidden(k1_ordinal1(sK2(sK0)),sK0)
    | ~ v3_ordinal1(sK0)
    | sK0 = k1_ordinal1(sK2(sK0))
    | ~ spl3_7 ),
    inference(resolution,[],[f114,f91])).

fof(f91,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(k1_ordinal1(X0),X1)
      | ~ v3_ordinal1(X1)
      | k1_ordinal1(X0) = X1 ) ),
    inference(duplicate_literal_removal,[],[f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k1_ordinal1(X0) = X1
      | ~ v3_ordinal1(X0)
      | r2_hidden(k1_ordinal1(X0),X1)
      | ~ v3_ordinal1(X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f112,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v3_ordinal1(k1_ordinal1(X0))
        & ~ v1_xboole_0(k1_ordinal1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_ordinal1)).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(k1_ordinal1(X0))
      | k1_ordinal1(X0) = X1
      | ~ v3_ordinal1(X0)
      | r2_hidden(k1_ordinal1(X0),X1)
      | ~ v3_ordinal1(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f111,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ v1_ordinal1(k1_ordinal1(X1))
      | ~ r2_hidden(X1,X0)
      | k1_ordinal1(X1) = X0
      | ~ v3_ordinal1(X1)
      | r2_hidden(k1_ordinal1(X1),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ r2_hidden(X1,X0)
      | k1_ordinal1(X1) = X0
      | ~ v3_ordinal1(X1)
      | r2_hidden(k1_ordinal1(X1),X0)
      | ~ v3_ordinal1(X0)
      | ~ v1_ordinal1(k1_ordinal1(X1)) ) ),
    inference(resolution,[],[f107,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

fof(f107,plain,(
    ! [X2,X3] :
      ( r2_xboole_0(k1_ordinal1(X2),X3)
      | ~ v3_ordinal1(X3)
      | ~ r2_hidden(X2,X3)
      | k1_ordinal1(X2) = X3
      | ~ v3_ordinal1(X2) ) ),
    inference(resolution,[],[f105,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_ordinal1(X1),X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(k1_ordinal1(X1),X0)
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f99,f48])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(k1_ordinal1(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(k1_ordinal1(X0),X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(resolution,[],[f53,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,X1)
              | ~ r1_ordinal1(k1_ordinal1(X0),X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f92,plain,
    ( ~ spl3_5
    | spl3_7
    | spl3_2 ),
    inference(avatar_split_clause,[],[f87,f63,f90,f78])).

fof(f87,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ v3_ordinal1(sK0)
    | spl3_2 ),
    inference(resolution,[],[f51,f70])).

fof(f70,plain,
    ( ~ v4_ordinal1(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f51,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | r2_hidden(sK2(X0),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f81,f67,f83])).

fof(f81,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl3_3 ),
    inference(superposition,[],[f45,f68])).

fof(f45,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f80,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f38,f78])).

fof(f38,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ( v4_ordinal1(sK0)
        & sK0 = k1_ordinal1(sK1)
        & v3_ordinal1(sK1) )
      | ( ! [X2] :
            ( k1_ordinal1(X2) != sK0
            | ~ v3_ordinal1(X2) )
        & ~ v4_ordinal1(sK0) ) )
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ( ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
          | ( ! [X2] :
                ( k1_ordinal1(X2) != X0
                | ~ v3_ordinal1(X2) )
            & ~ v4_ordinal1(X0) ) )
        & v3_ordinal1(X0) )
   => ( ( ( v4_ordinal1(sK0)
          & ? [X1] :
              ( k1_ordinal1(X1) = sK0
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != sK0
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(sK0) ) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( k1_ordinal1(X1) = sK0
        & v3_ordinal1(X1) )
   => ( sK0 = k1_ordinal1(sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ( ( v4_ordinal1(X0)
          & ? [X1] :
              ( k1_ordinal1(X1) = X0
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != X0
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(X0) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X2] :
                  ( v3_ordinal1(X2)
                 => k1_ordinal1(X2) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(rectify,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X1] :
                  ( v3_ordinal1(X1)
                 => k1_ordinal1(X1) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( ~ ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
        & ~ ( ! [X1] :
                ( v3_ordinal1(X1)
               => k1_ordinal1(X1) != X0 )
            & ~ v4_ordinal1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_ordinal1)).

fof(f76,plain,
    ( ~ spl3_2
    | spl3_4 ),
    inference(avatar_split_clause,[],[f39,f73,f63])).

fof(f39,plain,
    ( v3_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,
    ( spl3_1
    | spl3_4 ),
    inference(avatar_split_clause,[],[f40,f73,f60])).

fof(f40,plain,(
    ! [X2] :
      ( v3_ordinal1(sK1)
      | k1_ordinal1(X2) != sK0
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f41,f67,f63])).

fof(f41,plain,
    ( sK0 = k1_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f44,f63,f60])).

fof(f44,plain,(
    ! [X2] :
      ( v4_ordinal1(sK0)
      | k1_ordinal1(X2) != sK0
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

%------------------------------------------------------------------------------
