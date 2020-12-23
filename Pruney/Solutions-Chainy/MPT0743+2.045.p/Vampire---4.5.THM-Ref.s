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
% DateTime   : Thu Dec  3 12:55:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 218 expanded)
%              Number of leaves         :   20 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  322 ( 817 expanded)
%              Number of equality atoms :   10 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f391,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f65,f92,f94,f97,f107,f181,f183,f356,f389,f390])).

fof(f390,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | spl3_2 ),
    inference(avatar_split_clause,[],[f109,f61,f89,f85,f81])).

fof(f81,plain,
    ( spl3_3
  <=> v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f85,plain,
    ( spl3_4
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f89,plain,
    ( spl3_5
  <=> r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f61,plain,
    ( spl3_2
  <=> r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f109,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))
    | spl3_2 ),
    inference(resolution,[],[f63,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f63,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f389,plain,
    ( spl3_5
    | ~ spl3_12
    | ~ spl3_23 ),
    inference(avatar_contradiction_clause,[],[f386])).

fof(f386,plain,
    ( $false
    | spl3_5
    | ~ spl3_12
    | ~ spl3_23 ),
    inference(resolution,[],[f379,f90])).

fof(f90,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f379,plain,
    ( r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | ~ spl3_12
    | ~ spl3_23 ),
    inference(resolution,[],[f361,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f361,plain,
    ( r2_hidden(sK2(k2_xboole_0(sK0,k1_tarski(sK0)),sK1),sK1)
    | ~ spl3_12
    | ~ spl3_23 ),
    inference(resolution,[],[f355,f184])).

fof(f184,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(X0,sK1) )
    | ~ spl3_12 ),
    inference(resolution,[],[f180,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f180,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl3_12
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f355,plain,
    ( r2_hidden(sK2(k2_xboole_0(sK0,k1_tarski(sK0)),sK1),sK0)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl3_23
  <=> r2_hidden(sK2(k2_xboole_0(sK0,k1_tarski(sK0)),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f356,plain,
    ( spl3_23
    | ~ spl3_1
    | spl3_5 ),
    inference(avatar_split_clause,[],[f346,f89,f57,f353])).

fof(f57,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f346,plain,
    ( ~ r2_hidden(sK0,sK1)
    | r2_hidden(sK2(k2_xboole_0(sK0,k1_tarski(sK0)),sK1),sK0)
    | spl3_5 ),
    inference(resolution,[],[f213,f90])).

fof(f213,plain,(
    ! [X2,X3] :
      ( r1_tarski(k2_xboole_0(X2,k1_tarski(X2)),X3)
      | ~ r2_hidden(X2,X3)
      | r2_hidden(sK2(k2_xboole_0(X2,k1_tarski(X2)),X3),X2) ) ),
    inference(duplicate_literal_removal,[],[f210])).

fof(f210,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | r1_tarski(k2_xboole_0(X2,k1_tarski(X2)),X3)
      | r2_hidden(sK2(k2_xboole_0(X2,k1_tarski(X2)),X3),X2)
      | r1_tarski(k2_xboole_0(X2,k1_tarski(X2)),X3) ) ),
    inference(superposition,[],[f43,f125])).

fof(f125,plain,(
    ! [X4,X3] :
      ( sK2(k2_xboole_0(X3,k1_tarski(X3)),X4) = X3
      | r2_hidden(sK2(k2_xboole_0(X3,k1_tarski(X3)),X4),X3)
      | r1_tarski(k2_xboole_0(X3,k1_tarski(X3)),X4) ) ),
    inference(resolution,[],[f54,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f44,f36])).

fof(f36,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f183,plain,(
    spl3_11 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | spl3_11 ),
    inference(resolution,[],[f176,f31])).

fof(f31,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | r2_hidden(X0,X1) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
            | ~ r2_hidden(sK0,X1) )
          & ( r1_ordinal1(k1_ordinal1(sK0),X1)
            | r2_hidden(sK0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
          | ~ r2_hidden(sK0,X1) )
        & ( r1_ordinal1(k1_ordinal1(sK0),X1)
          | r2_hidden(sK0,X1) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
        | ~ r2_hidden(sK0,sK1) )
      & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
        | r2_hidden(sK0,sK1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f176,plain,
    ( ~ v3_ordinal1(sK0)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl3_11
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f181,plain,
    ( ~ spl3_11
    | spl3_12
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f169,f57,f178,f174])).

fof(f169,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f162,f108])).

fof(f108,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f58,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f58,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f162,plain,(
    ! [X1] :
      ( r1_tarski(sK1,X1)
      | r1_tarski(X1,sK1)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f159,f32])).

fof(f32,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X1,X0)
      | r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X1,X0)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f79,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f39,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f107,plain,
    ( spl3_1
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl3_1
    | ~ spl3_5 ),
    inference(resolution,[],[f100,f59])).

fof(f59,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f100,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_5 ),
    inference(resolution,[],[f99,f50])).

fof(f50,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f35,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f99,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_xboole_0(sK0,k1_tarski(sK0)))
        | r2_hidden(X0,sK1) )
    | ~ spl3_5 ),
    inference(resolution,[],[f91,f41])).

fof(f91,plain,
    ( r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f97,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f95,f31])).

% (14072)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f95,plain,
    ( ~ v3_ordinal1(sK0)
    | spl3_3 ),
    inference(resolution,[],[f83,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f37,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f83,plain,
    ( ~ v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f94,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f87,f32])).

fof(f87,plain,
    ( ~ v3_ordinal1(sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f92,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f77,f61,f89,f85,f81])).

% (14071)Termination reason: Refutation not found, incomplete strategy

% (14071)Memory used [KB]: 10746
fof(f77,plain,
    ( r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl3_2 ),
    inference(resolution,[],[f39,f62])).

% (14071)Time elapsed: 0.119 s
% (14071)------------------------------
% (14071)------------------------------
fof(f62,plain,
    ( r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f61])).

% (14072)Refutation not found, incomplete strategy% (14072)------------------------------
% (14072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14072)Termination reason: Refutation not found, incomplete strategy

% (14072)Memory used [KB]: 1663
% (14072)Time elapsed: 0.139 s
% (14072)------------------------------
% (14072)------------------------------
fof(f65,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f49,f61,f57])).

fof(f49,plain,
    ( r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f33,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f48,f61,f57])).

fof(f48,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f34,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:35:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (14064)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.51  % (14055)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (14063)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (14056)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (14063)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (14051)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (14080)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (14071)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (14071)Refutation not found, incomplete strategy% (14071)------------------------------
% 0.22/0.53  % (14071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f391,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f64,f65,f92,f94,f97,f107,f181,f183,f356,f389,f390])).
% 0.22/0.53  fof(f390,plain,(
% 0.22/0.53    ~spl3_3 | ~spl3_4 | ~spl3_5 | spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f109,f61,f89,f85,f81])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    spl3_3 <=> v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    spl3_4 <=> v3_ordinal1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    spl3_5 <=> r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    spl3_2 <=> r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    ~r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) | spl3_2),
% 0.22/0.53    inference(resolution,[],[f63,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ~r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | spl3_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f61])).
% 0.22/0.53  fof(f389,plain,(
% 0.22/0.53    spl3_5 | ~spl3_12 | ~spl3_23),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f386])).
% 0.22/0.53  fof(f386,plain,(
% 0.22/0.53    $false | (spl3_5 | ~spl3_12 | ~spl3_23)),
% 0.22/0.53    inference(resolution,[],[f379,f90])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ~r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | spl3_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f89])).
% 0.22/0.53  fof(f379,plain,(
% 0.22/0.53    r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | (~spl3_12 | ~spl3_23)),
% 0.22/0.53    inference(resolution,[],[f361,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(rectify,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.53  fof(f361,plain,(
% 0.22/0.53    r2_hidden(sK2(k2_xboole_0(sK0,k1_tarski(sK0)),sK1),sK1) | (~spl3_12 | ~spl3_23)),
% 0.22/0.53    inference(resolution,[],[f355,f184])).
% 0.22/0.53  fof(f184,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,sK1)) ) | ~spl3_12),
% 0.22/0.53    inference(resolution,[],[f180,f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f180,plain,(
% 0.22/0.53    r1_tarski(sK0,sK1) | ~spl3_12),
% 0.22/0.53    inference(avatar_component_clause,[],[f178])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    spl3_12 <=> r1_tarski(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.53  fof(f355,plain,(
% 0.22/0.53    r2_hidden(sK2(k2_xboole_0(sK0,k1_tarski(sK0)),sK1),sK0) | ~spl3_23),
% 0.22/0.53    inference(avatar_component_clause,[],[f353])).
% 0.22/0.53  fof(f353,plain,(
% 0.22/0.53    spl3_23 <=> r2_hidden(sK2(k2_xboole_0(sK0,k1_tarski(sK0)),sK1),sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.53  fof(f356,plain,(
% 0.22/0.53    spl3_23 | ~spl3_1 | spl3_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f346,f89,f57,f353])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    spl3_1 <=> r2_hidden(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.53  fof(f346,plain,(
% 0.22/0.53    ~r2_hidden(sK0,sK1) | r2_hidden(sK2(k2_xboole_0(sK0,k1_tarski(sK0)),sK1),sK0) | spl3_5),
% 0.22/0.53    inference(resolution,[],[f213,f90])).
% 0.22/0.53  fof(f213,plain,(
% 0.22/0.53    ( ! [X2,X3] : (r1_tarski(k2_xboole_0(X2,k1_tarski(X2)),X3) | ~r2_hidden(X2,X3) | r2_hidden(sK2(k2_xboole_0(X2,k1_tarski(X2)),X3),X2)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f210])).
% 0.22/0.53  fof(f210,plain,(
% 0.22/0.53    ( ! [X2,X3] : (~r2_hidden(X2,X3) | r1_tarski(k2_xboole_0(X2,k1_tarski(X2)),X3) | r2_hidden(sK2(k2_xboole_0(X2,k1_tarski(X2)),X3),X2) | r1_tarski(k2_xboole_0(X2,k1_tarski(X2)),X3)) )),
% 0.22/0.53    inference(superposition,[],[f43,f125])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    ( ! [X4,X3] : (sK2(k2_xboole_0(X3,k1_tarski(X3)),X4) = X3 | r2_hidden(sK2(k2_xboole_0(X3,k1_tarski(X3)),X4),X3) | r1_tarski(k2_xboole_0(X3,k1_tarski(X3)),X4)) )),
% 0.22/0.53    inference(resolution,[],[f54,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | r2_hidden(X0,X1) | X0 = X1) )),
% 0.22/0.53    inference(definition_unfolding,[],[f44,f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.22/0.53    inference(flattening,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.22/0.53    inference(nnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.22/0.53  fof(f183,plain,(
% 0.22/0.53    spl3_11),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f182])).
% 0.22/0.53  fof(f182,plain,(
% 0.22/0.53    $false | spl3_11),
% 0.22/0.53    inference(resolution,[],[f176,f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    v3_ordinal1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.53    inference(flattening,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.22/0.53    inference(negated_conjecture,[],[f9])).
% 0.22/0.53  fof(f9,conjecture,(
% 0.22/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.22/0.53  fof(f176,plain,(
% 0.22/0.53    ~v3_ordinal1(sK0) | spl3_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f174])).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    spl3_11 <=> v3_ordinal1(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    ~spl3_11 | spl3_12 | ~spl3_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f169,f57,f178,f174])).
% 0.22/0.53  fof(f169,plain,(
% 0.22/0.53    r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0) | ~spl3_1),
% 0.22/0.53    inference(resolution,[],[f162,f108])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    ~r1_tarski(sK1,sK0) | ~spl3_1),
% 0.22/0.53    inference(resolution,[],[f58,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    r2_hidden(sK0,sK1) | ~spl3_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f57])).
% 0.22/0.53  fof(f162,plain,(
% 0.22/0.53    ( ! [X1] : (r1_tarski(sK1,X1) | r1_tarski(X1,sK1) | ~v3_ordinal1(X1)) )),
% 0.22/0.53    inference(resolution,[],[f159,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    v3_ordinal1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_tarski(X1,X0) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f157])).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_tarski(X1,X0) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.53    inference(resolution,[],[f79,f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_ordinal1(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.22/0.53    inference(resolution,[],[f39,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.53    inference(flattening,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    spl3_1 | ~spl3_5),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f105])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    $false | (spl3_1 | ~spl3_5)),
% 0.22/0.53    inference(resolution,[],[f100,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ~r2_hidden(sK0,sK1) | spl3_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f57])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    r2_hidden(sK0,sK1) | ~spl3_5),
% 0.22/0.53    inference(resolution,[],[f99,f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f35,f36])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k2_xboole_0(sK0,k1_tarski(sK0))) | r2_hidden(X0,sK1)) ) | ~spl3_5),
% 0.22/0.53    inference(resolution,[],[f91,f41])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | ~spl3_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f89])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    spl3_3),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f96])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    $false | spl3_3),
% 0.22/0.53    inference(resolution,[],[f95,f31])).
% 0.22/0.53  % (14072)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    ~v3_ordinal1(sK0) | spl3_3),
% 0.22/0.53    inference(resolution,[],[f83,f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f37,f36])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    ~v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) | spl3_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f81])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    spl3_4),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f93])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    $false | spl3_4),
% 0.22/0.53    inference(resolution,[],[f87,f32])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    ~v3_ordinal1(sK1) | spl3_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f85])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    ~spl3_3 | ~spl3_4 | spl3_5 | ~spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f77,f61,f89,f85,f81])).
% 0.22/0.53  % (14071)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (14071)Memory used [KB]: 10746
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    r1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) | ~spl3_2),
% 0.22/0.53    inference(resolution,[],[f39,f62])).
% 0.22/0.53  % (14071)Time elapsed: 0.119 s
% 0.22/0.53  % (14071)------------------------------
% 0.22/0.53  % (14071)------------------------------
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | ~spl3_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f61])).
% 0.22/0.53  % (14072)Refutation not found, incomplete strategy% (14072)------------------------------
% 0.22/0.53  % (14072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (14072)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (14072)Memory used [KB]: 1663
% 0.22/0.53  % (14072)Time elapsed: 0.139 s
% 0.22/0.53  % (14072)------------------------------
% 0.22/0.53  % (14072)------------------------------
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    spl3_1 | spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f49,f61,f57])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | r2_hidden(sK0,sK1)),
% 0.22/0.53    inference(definition_unfolding,[],[f33,f36])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ~spl3_1 | ~spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f48,f61,f57])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ~r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | ~r2_hidden(sK0,sK1)),
% 0.22/0.53    inference(definition_unfolding,[],[f34,f36])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (14063)------------------------------
% 0.22/0.53  % (14063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (14063)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (14063)Memory used [KB]: 6396
% 0.22/0.53  % (14063)Time elapsed: 0.105 s
% 0.22/0.53  % (14063)------------------------------
% 0.22/0.53  % (14063)------------------------------
% 0.22/0.53  % (14050)Success in time 0.17 s
%------------------------------------------------------------------------------
