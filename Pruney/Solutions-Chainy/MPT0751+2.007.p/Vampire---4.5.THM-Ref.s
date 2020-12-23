%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 257 expanded)
%              Number of leaves         :   25 (  98 expanded)
%              Depth                    :   12
%              Number of atoms          :  427 ( 980 expanded)
%              Number of equality atoms :   40 ( 110 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f796,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f76,f82,f89,f137,f159,f166,f236,f304,f314,f351,f414,f486,f792])).

fof(f792,plain,
    ( ~ spl3_1
    | ~ spl3_17
    | ~ spl3_28 ),
    inference(avatar_contradiction_clause,[],[f791])).

fof(f791,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_17
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f783,f303])).

fof(f303,plain,
    ( r1_tarski(sK0,k1_ordinal1(sK0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl3_17
  <=> r1_tarski(sK0,k1_ordinal1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f783,plain,
    ( ~ r1_tarski(sK0,k1_ordinal1(sK0))
    | ~ spl3_1
    | ~ spl3_28 ),
    inference(unit_resulting_resolution,[],[f66,f66,f485,f42,f201])).

fof(f201,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | k1_ordinal1(X1) = X0 ) ),
    inference(resolution,[],[f114,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_ordinal1(X0),X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f113,f43])).

fof(f43,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v3_ordinal1(k1_ordinal1(X0))
        & ~ v1_xboole_0(k1_ordinal1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_ordinal1)).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(k1_ordinal1(X0),X1)
      | ~ v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(k1_ordinal1(X0),X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(resolution,[],[f48,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,X1)
              | ~ r1_ordinal1(k1_ordinal1(X0),X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f42,plain,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).

fof(f485,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f483])).

fof(f483,plain,
    ( spl3_28
  <=> r2_hidden(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f66,plain,
    ( v3_ordinal1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_1
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f486,plain,
    ( spl3_28
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f422,f411,f79,f73,f69,f64,f483])).

fof(f69,plain,
    ( spl3_2
  <=> v4_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f73,plain,
    ( spl3_3
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f79,plain,
    ( spl3_4
  <=> sK0 = k1_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f411,plain,
    ( spl3_25
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f422,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f418,f81])).

fof(f81,plain,
    ( sK0 = k1_ordinal1(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f418,plain,
    ( r2_hidden(k1_ordinal1(sK1),sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_25 ),
    inference(unit_resulting_resolution,[],[f66,f70,f75,f413,f44])).

fof(f44,plain,(
    ! [X2,X0] :
      ( ~ v4_ordinal1(X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | r2_hidden(k1_ordinal1(X2),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
        & r2_hidden(sK2(X0),X0)
        & v3_ordinal1(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).

fof(f413,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f411])).

fof(f75,plain,
    ( v3_ordinal1(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f70,plain,
    ( v4_ordinal1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f414,plain,
    ( spl3_25
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f372,f79,f411])).

fof(f372,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl3_4 ),
    inference(superposition,[],[f62,f81])).

fof(f62,plain,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f351,plain,
    ( ~ spl3_1
    | ~ spl3_7
    | ~ spl3_9
    | spl3_10
    | spl3_19 ),
    inference(avatar_contradiction_clause,[],[f350])).

fof(f350,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_9
    | spl3_10
    | spl3_19 ),
    inference(subsumption_resolution,[],[f349,f214])).

fof(f214,plain,
    ( r2_hidden(k1_ordinal1(sK2(sK0)),k1_ordinal1(sK0))
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f136,f158,f66,f132])).

fof(f132,plain,(
    ! [X2,X3] :
      ( r2_hidden(k1_ordinal1(X2),k1_ordinal1(X3))
      | ~ v3_ordinal1(X3)
      | ~ r2_hidden(X2,X3)
      | ~ v3_ordinal1(X2) ) ),
    inference(subsumption_resolution,[],[f130,f43])).

fof(f130,plain,(
    ! [X2,X3] :
      ( r2_hidden(k1_ordinal1(X2),k1_ordinal1(X3))
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(k1_ordinal1(X2))
      | ~ r2_hidden(X2,X3)
      | ~ v3_ordinal1(X2) ) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,(
    ! [X2,X3] :
      ( r2_hidden(k1_ordinal1(X2),k1_ordinal1(X3))
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(k1_ordinal1(X2))
      | ~ r2_hidden(X2,X3)
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(X2) ) ),
    inference(resolution,[],[f51,f48])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f158,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl3_9
  <=> r2_hidden(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f136,plain,
    ( v3_ordinal1(sK2(sK0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl3_7
  <=> v3_ordinal1(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f349,plain,
    ( ~ r2_hidden(k1_ordinal1(sK2(sK0)),k1_ordinal1(sK0))
    | spl3_10
    | spl3_19 ),
    inference(unit_resulting_resolution,[],[f165,f313,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_ordinal1(X1))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f313,plain,
    ( sK0 != k1_ordinal1(sK2(sK0))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl3_19
  <=> sK0 = k1_ordinal1(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f165,plain,
    ( ~ r2_hidden(k1_ordinal1(sK2(sK0)),sK0)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl3_10
  <=> r2_hidden(k1_ordinal1(sK2(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f314,plain,
    ( ~ spl3_19
    | spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f148,f134,f69,f311])).

fof(f148,plain,
    ( sK0 != k1_ordinal1(sK2(sK0))
    | spl3_2
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f136,f77])).

fof(f77,plain,
    ( ! [X2] :
        ( k1_ordinal1(X2) != sK0
        | ~ v3_ordinal1(X2) )
    | spl3_2 ),
    inference(subsumption_resolution,[],[f41,f71])).

fof(f71,plain,
    ( ~ v4_ordinal1(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f41,plain,(
    ! [X2] :
      ( v4_ordinal1(sK0)
      | k1_ordinal1(X2) != sK0
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ( v4_ordinal1(sK0)
        & sK0 = k1_ordinal1(sK1)
        & v3_ordinal1(sK1) )
      | ( ! [X2] :
            ( k1_ordinal1(X2) != sK0
            | ~ v3_ordinal1(X2) )
        & ~ v4_ordinal1(sK0) ) )
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f22,f21])).

fof(f21,plain,
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

fof(f22,plain,
    ( ? [X1] :
        ( k1_ordinal1(X1) = sK0
        & v3_ordinal1(X1) )
   => ( sK0 = k1_ordinal1(sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(rectify,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f304,plain,
    ( spl3_17
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f283,f233,f86,f64,f301])).

fof(f86,plain,
    ( spl3_5
  <=> v3_ordinal1(k1_ordinal1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f233,plain,
    ( spl3_13
  <=> r1_ordinal1(sK0,k1_ordinal1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f283,plain,
    ( r1_tarski(sK0,k1_ordinal1(sK0))
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f66,f88,f235,f52])).

fof(f235,plain,
    ( r1_ordinal1(sK0,k1_ordinal1(sK0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f233])).

fof(f88,plain,
    ( v3_ordinal1(k1_ordinal1(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f236,plain,
    ( spl3_13
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f168,f86,f64,f233])).

fof(f168,plain,
    ( r1_ordinal1(sK0,k1_ordinal1(sK0))
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f66,f88,f96,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_ordinal1(X1))
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f96,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(k1_ordinal1(X0))) ),
    inference(unit_resulting_resolution,[],[f62,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f166,plain,
    ( ~ spl3_10
    | ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f98,f69,f64,f163])).

fof(f98,plain,
    ( ~ r2_hidden(k1_ordinal1(sK2(sK0)),sK0)
    | ~ spl3_1
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f66,f71,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
      | v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f159,plain,
    ( spl3_9
    | ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f97,f69,f64,f156])).

fof(f97,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl3_1
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f66,f71,f46])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f137,plain,
    ( spl3_7
    | ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f95,f69,f64,f134])).

fof(f95,plain,
    ( v3_ordinal1(sK2(sK0))
    | ~ spl3_1
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f66,f71,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v3_ordinal1(sK2(X0))
      | v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f89,plain,
    ( spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f84,f64,f86])).

fof(f84,plain,
    ( v3_ordinal1(k1_ordinal1(sK0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f66,f43])).

fof(f82,plain,
    ( ~ spl3_2
    | spl3_4 ),
    inference(avatar_split_clause,[],[f38,f79,f69])).

fof(f38,plain,
    ( sK0 = k1_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f76,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f36,f73,f69])).

fof(f36,plain,
    ( v3_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f35,f64])).

fof(f35,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:25:15 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.49  % (638)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.49  % (641)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.49  % (635)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.49  % (648)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (670)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.49  % (644)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.49  % (667)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.49  % (636)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (639)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (642)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.50  % (675)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.50  % (635)Refutation not found, incomplete strategy% (635)------------------------------
% 0.22/0.50  % (635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (669)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.50  % (673)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.50  % (672)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.50  % (640)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  % (634)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.50  % (676)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.50  % (647)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (668)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.51  % (649)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (677)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (635)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (635)Memory used [KB]: 10746
% 0.22/0.52  % (635)Time elapsed: 0.087 s
% 0.22/0.52  % (635)------------------------------
% 0.22/0.52  % (635)------------------------------
% 0.22/0.52  % (640)Refutation not found, incomplete strategy% (640)------------------------------
% 0.22/0.52  % (640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (640)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (640)Memory used [KB]: 10618
% 0.22/0.52  % (640)Time elapsed: 0.107 s
% 0.22/0.52  % (640)------------------------------
% 0.22/0.52  % (640)------------------------------
% 0.22/0.52  % (674)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (637)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (675)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f796,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f67,f76,f82,f89,f137,f159,f166,f236,f304,f314,f351,f414,f486,f792])).
% 0.22/0.53  fof(f792,plain,(
% 0.22/0.53    ~spl3_1 | ~spl3_17 | ~spl3_28),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f791])).
% 0.22/0.53  fof(f791,plain,(
% 0.22/0.53    $false | (~spl3_1 | ~spl3_17 | ~spl3_28)),
% 0.22/0.53    inference(subsumption_resolution,[],[f783,f303])).
% 0.22/0.53  fof(f303,plain,(
% 0.22/0.53    r1_tarski(sK0,k1_ordinal1(sK0)) | ~spl3_17),
% 0.22/0.53    inference(avatar_component_clause,[],[f301])).
% 0.22/0.53  fof(f301,plain,(
% 0.22/0.53    spl3_17 <=> r1_tarski(sK0,k1_ordinal1(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.53  fof(f783,plain,(
% 0.22/0.53    ~r1_tarski(sK0,k1_ordinal1(sK0)) | (~spl3_1 | ~spl3_28)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f66,f66,f485,f42,f201])).
% 0.22/0.53  fof(f201,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | k1_ordinal1(X1) = X0) )),
% 0.22/0.53    inference(resolution,[],[f114,f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(flattening,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k1_ordinal1(X0),X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f113,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.22/0.53    inference(pure_predicate_removal,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : (v3_ordinal1(X0) => (v3_ordinal1(k1_ordinal1(X0)) & ~v1_xboole_0(k1_ordinal1(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_ordinal1)).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_tarski(k1_ordinal1(X0),X1) | ~v3_ordinal1(k1_ordinal1(X0))) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f112])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_tarski(k1_ordinal1(X0),X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(k1_ordinal1(X0))) )),
% 0.22/0.53    inference(resolution,[],[f48,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.53    inference(flattening,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (((r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0] : (k1_ordinal1(X0) != X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : k1_ordinal1(X0) != X0),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).
% 0.22/0.53  fof(f485,plain,(
% 0.22/0.53    r2_hidden(sK0,sK0) | ~spl3_28),
% 0.22/0.53    inference(avatar_component_clause,[],[f483])).
% 0.22/0.53  fof(f483,plain,(
% 0.22/0.53    spl3_28 <=> r2_hidden(sK0,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    v3_ordinal1(sK0) | ~spl3_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    spl3_1 <=> v3_ordinal1(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.53  fof(f486,plain,(
% 0.22/0.53    spl3_28 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_25),
% 0.22/0.53    inference(avatar_split_clause,[],[f422,f411,f79,f73,f69,f64,f483])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    spl3_2 <=> v4_ordinal1(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    spl3_3 <=> v3_ordinal1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    spl3_4 <=> sK0 = k1_ordinal1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.53  fof(f411,plain,(
% 0.22/0.53    spl3_25 <=> r2_hidden(sK1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.53  fof(f422,plain,(
% 0.22/0.53    r2_hidden(sK0,sK0) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_25)),
% 0.22/0.53    inference(forward_demodulation,[],[f418,f81])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    sK0 = k1_ordinal1(sK1) | ~spl3_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f79])).
% 0.22/0.53  fof(f418,plain,(
% 0.22/0.53    r2_hidden(k1_ordinal1(sK1),sK0) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_25)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f66,f70,f75,f413,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X2,X0] : (~v4_ordinal1(X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2) | r2_hidden(k1_ordinal1(X2),X0) | ~v3_ordinal1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0] : (((v4_ordinal1(X0) | (~r2_hidden(k1_ordinal1(sK2(X0)),X0) & r2_hidden(sK2(X0),X0) & v3_ordinal1(sK2(X0)))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK2(X0)),X0) & r2_hidden(sK2(X0),X0) & v3_ordinal1(sK2(X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 0.22/0.53    inference(rectify,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).
% 0.22/0.53  fof(f413,plain,(
% 0.22/0.53    r2_hidden(sK1,sK0) | ~spl3_25),
% 0.22/0.53    inference(avatar_component_clause,[],[f411])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    v3_ordinal1(sK1) | ~spl3_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f73])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    v4_ordinal1(sK0) | ~spl3_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f69])).
% 0.22/0.53  fof(f414,plain,(
% 0.22/0.53    spl3_25 | ~spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f372,f79,f411])).
% 0.22/0.53  fof(f372,plain,(
% 0.22/0.53    r2_hidden(sK1,sK0) | ~spl3_4),
% 0.22/0.53    inference(superposition,[],[f62,f81])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X1] : (r2_hidden(X1,k1_ordinal1(X1))) )),
% 0.22/0.53    inference(equality_resolution,[],[f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.22/0.53    inference(flattening,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.22/0.53    inference(nnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.22/0.53  fof(f351,plain,(
% 0.22/0.53    ~spl3_1 | ~spl3_7 | ~spl3_9 | spl3_10 | spl3_19),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f350])).
% 0.22/0.53  fof(f350,plain,(
% 0.22/0.53    $false | (~spl3_1 | ~spl3_7 | ~spl3_9 | spl3_10 | spl3_19)),
% 0.22/0.53    inference(subsumption_resolution,[],[f349,f214])).
% 0.22/0.53  fof(f214,plain,(
% 0.22/0.53    r2_hidden(k1_ordinal1(sK2(sK0)),k1_ordinal1(sK0)) | (~spl3_1 | ~spl3_7 | ~spl3_9)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f136,f158,f66,f132])).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    ( ! [X2,X3] : (r2_hidden(k1_ordinal1(X2),k1_ordinal1(X3)) | ~v3_ordinal1(X3) | ~r2_hidden(X2,X3) | ~v3_ordinal1(X2)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f130,f43])).
% 0.22/0.53  fof(f130,plain,(
% 0.22/0.53    ( ! [X2,X3] : (r2_hidden(k1_ordinal1(X2),k1_ordinal1(X3)) | ~v3_ordinal1(X3) | ~v3_ordinal1(k1_ordinal1(X2)) | ~r2_hidden(X2,X3) | ~v3_ordinal1(X2)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f129])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    ( ! [X2,X3] : (r2_hidden(k1_ordinal1(X2),k1_ordinal1(X3)) | ~v3_ordinal1(X3) | ~v3_ordinal1(k1_ordinal1(X2)) | ~r2_hidden(X2,X3) | ~v3_ordinal1(X3) | ~v3_ordinal1(X2)) )),
% 0.22/0.53    inference(resolution,[],[f51,f48])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.22/0.53  fof(f158,plain,(
% 0.22/0.53    r2_hidden(sK2(sK0),sK0) | ~spl3_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f156])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    spl3_9 <=> r2_hidden(sK2(sK0),sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    v3_ordinal1(sK2(sK0)) | ~spl3_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f134])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    spl3_7 <=> v3_ordinal1(sK2(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.53  fof(f349,plain,(
% 0.22/0.53    ~r2_hidden(k1_ordinal1(sK2(sK0)),k1_ordinal1(sK0)) | (spl3_10 | spl3_19)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f165,f313,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k1_ordinal1(X1)) | r2_hidden(X0,X1) | X0 = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f313,plain,(
% 0.22/0.53    sK0 != k1_ordinal1(sK2(sK0)) | spl3_19),
% 0.22/0.53    inference(avatar_component_clause,[],[f311])).
% 0.22/0.53  fof(f311,plain,(
% 0.22/0.53    spl3_19 <=> sK0 = k1_ordinal1(sK2(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    ~r2_hidden(k1_ordinal1(sK2(sK0)),sK0) | spl3_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f163])).
% 0.22/0.53  fof(f163,plain,(
% 0.22/0.53    spl3_10 <=> r2_hidden(k1_ordinal1(sK2(sK0)),sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.53  fof(f314,plain,(
% 0.22/0.53    ~spl3_19 | spl3_2 | ~spl3_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f148,f134,f69,f311])).
% 0.22/0.53  fof(f148,plain,(
% 0.22/0.53    sK0 != k1_ordinal1(sK2(sK0)) | (spl3_2 | ~spl3_7)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f136,f77])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X2] : (k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) ) | spl3_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f41,f71])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ~v4_ordinal1(sK0) | spl3_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f69])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X2] : (v4_ordinal1(sK0) | k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ((v4_ordinal1(sK0) & (sK0 = k1_ordinal1(sK1) & v3_ordinal1(sK1))) | (! [X2] : (k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(sK0))) & v3_ordinal1(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f22,f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0)) => (((v4_ordinal1(sK0) & ? [X1] : (k1_ordinal1(X1) = sK0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(sK0))) & v3_ordinal1(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ? [X1] : (k1_ordinal1(X1) = sK0 & v3_ordinal1(X1)) => (sK0 = k1_ordinal1(sK1) & v3_ordinal1(sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X2] : (v3_ordinal1(X2) => k1_ordinal1(X2) != X0) & ~v4_ordinal1(X0))))),
% 0.22/0.53    inference(rectify,[],[f10])).
% 0.22/0.53  fof(f10,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 0.22/0.53    inference(negated_conjecture,[],[f9])).
% 0.22/0.53  fof(f9,conjecture,(
% 0.22/0.53    ! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_ordinal1)).
% 0.22/0.53  fof(f304,plain,(
% 0.22/0.53    spl3_17 | ~spl3_1 | ~spl3_5 | ~spl3_13),
% 0.22/0.53    inference(avatar_split_clause,[],[f283,f233,f86,f64,f301])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    spl3_5 <=> v3_ordinal1(k1_ordinal1(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.53  fof(f233,plain,(
% 0.22/0.53    spl3_13 <=> r1_ordinal1(sK0,k1_ordinal1(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.53  fof(f283,plain,(
% 0.22/0.53    r1_tarski(sK0,k1_ordinal1(sK0)) | (~spl3_1 | ~spl3_5 | ~spl3_13)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f66,f88,f235,f52])).
% 0.22/0.53  fof(f235,plain,(
% 0.22/0.53    r1_ordinal1(sK0,k1_ordinal1(sK0)) | ~spl3_13),
% 0.22/0.53    inference(avatar_component_clause,[],[f233])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    v3_ordinal1(k1_ordinal1(sK0)) | ~spl3_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f86])).
% 0.22/0.53  fof(f236,plain,(
% 0.22/0.53    spl3_13 | ~spl3_1 | ~spl3_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f168,f86,f64,f233])).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    r1_ordinal1(sK0,k1_ordinal1(sK0)) | (~spl3_1 | ~spl3_5)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f66,f88,f96,f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k1_ordinal1(X1)) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(k1_ordinal1(X0)))) )),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f62,f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f166,plain,(
% 0.22/0.53    ~spl3_10 | ~spl3_1 | spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f98,f69,f64,f163])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    ~r2_hidden(k1_ordinal1(sK2(sK0)),sK0) | (~spl3_1 | spl3_2)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f66,f71,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(k1_ordinal1(sK2(X0)),X0) | v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    spl3_9 | ~spl3_1 | spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f97,f69,f64,f156])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    r2_hidden(sK2(sK0),sK0) | (~spl3_1 | spl3_2)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f66,f71,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    spl3_7 | ~spl3_1 | spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f95,f69,f64,f134])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    v3_ordinal1(sK2(sK0)) | (~spl3_1 | spl3_2)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f66,f71,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0] : (v3_ordinal1(sK2(X0)) | v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    spl3_5 | ~spl3_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f84,f64,f86])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    v3_ordinal1(k1_ordinal1(sK0)) | ~spl3_1),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f66,f43])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ~spl3_2 | spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f38,f79,f69])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    sK0 = k1_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ~spl3_2 | spl3_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f36,f73,f69])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    v3_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    spl3_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f35,f64])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    v3_ordinal1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (675)------------------------------
% 0.22/0.53  % (675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (675)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (675)Memory used [KB]: 11001
% 0.22/0.53  % (675)Time elapsed: 0.120 s
% 0.22/0.53  % (675)------------------------------
% 0.22/0.53  % (675)------------------------------
% 0.22/0.53  % (631)Success in time 0.155 s
%------------------------------------------------------------------------------
