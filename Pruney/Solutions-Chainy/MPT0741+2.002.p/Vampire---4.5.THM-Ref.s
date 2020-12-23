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
% DateTime   : Thu Dec  3 12:55:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 191 expanded)
%              Number of leaves         :   23 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :  364 ( 784 expanded)
%              Number of equality atoms :   27 (  69 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f247,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f71,f78,f82,f87,f103,f109,f120,f181,f218,f225,f232])).

fof(f232,plain,
    ( spl4_12
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f229,f175,f133])).

fof(f133,plain,
    ( spl4_12
  <=> v2_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f175,plain,
    ( spl4_19
  <=> r2_hidden(sK1(sK0),sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f229,plain,
    ( v2_ordinal1(sK0)
    | ~ spl4_19 ),
    inference(resolution,[],[f176,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(X0),sK2(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ( ~ r2_hidden(sK2(X0),sK1(X0))
          & sK1(X0) != sK2(X0)
          & ~ r2_hidden(sK1(X0),sK2(X0))
          & r2_hidden(sK2(X0),X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(X2,X1)
          & X1 != X2
          & ~ r2_hidden(X1,X2)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r2_hidden(sK2(X0),sK1(X0))
        & sK1(X0) != sK2(X0)
        & ~ r2_hidden(sK1(X0),sK2(X0))
        & r2_hidden(sK2(X0),X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1,X2] :
            ( r2_hidden(X2,X1)
            | X1 = X2
            | r2_hidden(X1,X2)
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ( r2_hidden(X2,X1)
          | X1 = X2
          | r2_hidden(X1,X2)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_ordinal1)).

fof(f176,plain,
    ( r2_hidden(sK1(sK0),sK2(sK0))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f175])).

fof(f225,plain,
    ( ~ spl4_2
    | spl4_1
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f223,f133,f58,f66])).

fof(f66,plain,
    ( spl4_2
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f58,plain,
    ( spl4_1
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f223,plain,
    ( v3_ordinal1(sK0)
    | ~ v1_ordinal1(sK0)
    | ~ spl4_12 ),
    inference(resolution,[],[f173,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v2_ordinal1(X0)
      | v3_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_ordinal1)).

fof(f173,plain,
    ( v2_ordinal1(sK0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f133])).

fof(f218,plain,
    ( spl4_12
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f213,f178,f133])).

fof(f178,plain,
    ( spl4_20
  <=> sK1(sK0) = sK2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f213,plain,
    ( v2_ordinal1(sK0)
    | ~ spl4_20 ),
    inference(trivial_inequality_removal,[],[f211])).

fof(f211,plain,
    ( sK1(sK0) != sK1(sK0)
    | v2_ordinal1(sK0)
    | ~ spl4_20 ),
    inference(superposition,[],[f49,f179])).

fof(f179,plain,
    ( sK1(sK0) = sK2(sK0)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f178])).

fof(f49,plain,(
    ! [X0] :
      ( sK1(X0) != sK2(X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f181,plain,
    ( spl4_12
    | spl4_19
    | spl4_20
    | ~ spl4_11
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f157,f101,f118,f178,f175,f133])).

fof(f118,plain,
    ( spl4_11
  <=> v3_ordinal1(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f101,plain,
    ( spl4_8
  <=> v3_ordinal1(sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f157,plain,
    ( ~ v3_ordinal1(sK2(sK0))
    | sK1(sK0) = sK2(sK0)
    | r2_hidden(sK1(sK0),sK2(sK0))
    | v2_ordinal1(sK0)
    | ~ spl4_8 ),
    inference(resolution,[],[f152,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(X0),sK1(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f152,plain,
    ( ! [X4] :
        ( r2_hidden(X4,sK1(sK0))
        | ~ v3_ordinal1(X4)
        | sK1(sK0) = X4
        | r2_hidden(sK1(sK0),X4) )
    | ~ spl4_8 ),
    inference(resolution,[],[f148,f102])).

fof(f102,plain,
    ( v3_ordinal1(sK1(sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f148,plain,(
    ! [X2,X3] :
      ( ~ v3_ordinal1(X3)
      | X2 = X3
      | ~ v3_ordinal1(X2)
      | r2_hidden(X2,X3)
      | r2_hidden(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,(
    ! [X2,X3] :
      ( X2 = X3
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(X2)
      | r2_hidden(X2,X3)
      | r2_hidden(X3,X2)
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(X2) ) ),
    inference(resolution,[],[f129,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | X0 = X1
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | X0 = X1
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f125,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f125,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X5,X4)
      | r2_hidden(X5,X4)
      | X4 = X5
      | ~ v3_ordinal1(X4)
      | ~ v3_ordinal1(X5) ) ),
    inference(resolution,[],[f122,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ v1_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f40,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

fof(f120,plain,
    ( spl4_11
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f111,f107,f118])).

fof(f107,plain,
    ( spl4_9
  <=> r2_hidden(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f111,plain,
    ( v3_ordinal1(sK2(sK0))
    | ~ spl4_9 ),
    inference(resolution,[],[f108,f37])).

fof(f37,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ v3_ordinal1(sK0)
    & ! [X1] :
        ( ( r1_tarski(X1,sK0)
          & v3_ordinal1(X1) )
        | ~ r2_hidden(X1,sK0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ~ v3_ordinal1(X0)
        & ! [X1] :
            ( ( r1_tarski(X1,X0)
              & v3_ordinal1(X1) )
            | ~ r2_hidden(X1,X0) ) )
   => ( ~ v3_ordinal1(sK0)
      & ! [X1] :
          ( ( r1_tarski(X1,sK0)
            & v3_ordinal1(X1) )
          | ~ r2_hidden(X1,sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(X0)
      & ! [X1] :
          ( ( r1_tarski(X1,X0)
            & v3_ordinal1(X1) )
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( r2_hidden(X1,X0)
           => ( r1_tarski(X1,X0)
              & v3_ordinal1(X1) ) )
       => v3_ordinal1(X0) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => ( r1_tarski(X1,X0)
            & v3_ordinal1(X1) ) )
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_ordinal1)).

fof(f108,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f109,plain,
    ( ~ spl4_2
    | spl4_9
    | spl4_1 ),
    inference(avatar_split_clause,[],[f105,f58,f107,f66])).

fof(f105,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ v1_ordinal1(sK0)
    | spl4_1 ),
    inference(resolution,[],[f63,f59])).

fof(f59,plain,
    ( ~ v3_ordinal1(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f63,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | r2_hidden(sK2(X0),X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(resolution,[],[f47,f44])).

fof(f47,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f103,plain,
    ( spl4_8
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f94,f69,f101])).

fof(f69,plain,
    ( spl4_3
  <=> r2_hidden(sK1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f94,plain,
    ( v3_ordinal1(sK1(sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f70,f37])).

fof(f70,plain,
    ( r2_hidden(sK1(sK0),sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f87,plain,
    ( spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f83,f80,f76])).

fof(f76,plain,
    ( spl4_4
  <=> r1_tarski(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f80,plain,
    ( spl4_5
  <=> r2_hidden(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f83,plain,
    ( r1_tarski(sK3(sK0),sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f81,f38])).

fof(f38,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | r1_tarski(X1,sK0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,
    ( r2_hidden(sK3(sK0),sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f82,plain,
    ( spl4_5
    | spl4_2 ),
    inference(avatar_split_clause,[],[f73,f66,f80])).

fof(f73,plain,
    ( r2_hidden(sK3(sK0),sK0)
    | spl4_2 ),
    inference(resolution,[],[f67,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK3(X0),X0)
          & r2_hidden(sK3(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK3(X0),X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f67,plain,
    ( ~ v1_ordinal1(sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f78,plain,
    ( ~ spl4_4
    | spl4_2 ),
    inference(avatar_split_clause,[],[f72,f66,f76])).

fof(f72,plain,
    ( ~ r1_tarski(sK3(sK0),sK0)
    | spl4_2 ),
    inference(resolution,[],[f67,f53])).

fof(f53,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ r1_tarski(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,
    ( ~ spl4_2
    | spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f64,f58,f69,f66])).

fof(f64,plain,
    ( r2_hidden(sK1(sK0),sK0)
    | ~ v1_ordinal1(sK0)
    | spl4_1 ),
    inference(resolution,[],[f62,f59])).

fof(f62,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | r2_hidden(sK1(X0),X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(resolution,[],[f46,f44])).

fof(f46,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f39,f58])).

fof(f39,plain,(
    ~ v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:05:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (12829)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (12836)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (12842)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (12842)Refutation not found, incomplete strategy% (12842)------------------------------
% 0.21/0.48  % (12842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (12842)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (12842)Memory used [KB]: 10618
% 0.21/0.48  % (12842)Time elapsed: 0.062 s
% 0.21/0.48  % (12842)------------------------------
% 0.21/0.48  % (12842)------------------------------
% 0.21/0.49  % (12828)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (12831)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (12828)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f247,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f60,f71,f78,f82,f87,f103,f109,f120,f181,f218,f225,f232])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    spl4_12 | ~spl4_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f229,f175,f133])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    spl4_12 <=> v2_ordinal1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    spl4_19 <=> r2_hidden(sK1(sK0),sK2(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.49  fof(f229,plain,(
% 0.21/0.49    v2_ordinal1(sK0) | ~spl4_19),
% 0.21/0.49    inference(resolution,[],[f176,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK1(X0),sK2(X0)) | v2_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0] : ((v2_ordinal1(X0) | (~r2_hidden(sK2(X0),sK1(X0)) & sK1(X0) != sK2(X0) & ~r2_hidden(sK1(X0),sK2(X0)) & r2_hidden(sK2(X0),X0) & r2_hidden(sK1(X0),X0))) & (! [X3,X4] : (r2_hidden(X4,X3) | X3 = X4 | r2_hidden(X3,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)) | ~v2_ordinal1(X0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0] : (? [X1,X2] : (~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0)) => (~r2_hidden(sK2(X0),sK1(X0)) & sK1(X0) != sK2(X0) & ~r2_hidden(sK1(X0),sK2(X0)) & r2_hidden(sK2(X0),X0) & r2_hidden(sK1(X0),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0] : ((v2_ordinal1(X0) | ? [X1,X2] : (~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0))) & (! [X3,X4] : (r2_hidden(X4,X3) | X3 = X4 | r2_hidden(X3,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)) | ~v2_ordinal1(X0)))),
% 0.21/0.49    inference(rectify,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : ((v2_ordinal1(X0) | ? [X1,X2] : (~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0))) & (! [X1,X2] : (r2_hidden(X2,X1) | X1 = X2 | r2_hidden(X1,X2) | ~r2_hidden(X2,X0) | ~r2_hidden(X1,X0)) | ~v2_ordinal1(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (v2_ordinal1(X0) <=> ! [X1,X2] : (r2_hidden(X2,X1) | X1 = X2 | r2_hidden(X1,X2) | ~r2_hidden(X2,X0) | ~r2_hidden(X1,X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (v2_ordinal1(X0) <=> ! [X1,X2] : ~(~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_ordinal1)).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    r2_hidden(sK1(sK0),sK2(sK0)) | ~spl4_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f175])).
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    ~spl4_2 | spl4_1 | ~spl4_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f223,f133,f58,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl4_2 <=> v1_ordinal1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    spl4_1 <=> v3_ordinal1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    v3_ordinal1(sK0) | ~v1_ordinal1(sK0) | ~spl4_12),
% 0.21/0.49    inference(resolution,[],[f173,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_ordinal1(X0) | v3_ordinal1(X0) | ~v1_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (v3_ordinal1(X0) | ~v2_ordinal1(X0) | ~v1_ordinal1(X0))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (v3_ordinal1(X0) | (~v2_ordinal1(X0) | ~v1_ordinal1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) => v3_ordinal1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_ordinal1)).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    v2_ordinal1(sK0) | ~spl4_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f133])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    spl4_12 | ~spl4_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f213,f178,f133])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    spl4_20 <=> sK1(sK0) = sK2(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    v2_ordinal1(sK0) | ~spl4_20),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f211])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    sK1(sK0) != sK1(sK0) | v2_ordinal1(sK0) | ~spl4_20),
% 0.21/0.49    inference(superposition,[],[f49,f179])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    sK1(sK0) = sK2(sK0) | ~spl4_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f178])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0] : (sK1(X0) != sK2(X0) | v2_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    spl4_12 | spl4_19 | spl4_20 | ~spl4_11 | ~spl4_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f157,f101,f118,f178,f175,f133])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    spl4_11 <=> v3_ordinal1(sK2(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl4_8 <=> v3_ordinal1(sK1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    ~v3_ordinal1(sK2(sK0)) | sK1(sK0) = sK2(sK0) | r2_hidden(sK1(sK0),sK2(sK0)) | v2_ordinal1(sK0) | ~spl4_8),
% 0.21/0.49    inference(resolution,[],[f152,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK2(X0),sK1(X0)) | v2_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    ( ! [X4] : (r2_hidden(X4,sK1(sK0)) | ~v3_ordinal1(X4) | sK1(sK0) = X4 | r2_hidden(sK1(sK0),X4)) ) | ~spl4_8),
% 0.21/0.49    inference(resolution,[],[f148,f102])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    v3_ordinal1(sK1(sK0)) | ~spl4_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f101])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~v3_ordinal1(X3) | X2 = X3 | ~v3_ordinal1(X2) | r2_hidden(X2,X3) | r2_hidden(X3,X2)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f147])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    ( ! [X2,X3] : (X2 = X3 | ~v3_ordinal1(X3) | ~v3_ordinal1(X2) | r2_hidden(X2,X3) | r2_hidden(X3,X2) | ~v3_ordinal1(X3) | ~v3_ordinal1(X2)) )),
% 0.21/0.49    inference(resolution,[],[f129,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | X0 = X1 | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f128])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | X0 = X1 | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.49    inference(resolution,[],[f125,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(flattening,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ( ! [X4,X5] : (~r1_tarski(X5,X4) | r2_hidden(X5,X4) | X4 = X5 | ~v3_ordinal1(X4) | ~v3_ordinal1(X5)) )),
% 0.21/0.49    inference(resolution,[],[f122,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_ordinal1(X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(resolution,[],[f40,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.21/0.49    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    spl4_11 | ~spl4_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f111,f107,f118])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    spl4_9 <=> r2_hidden(sK2(sK0),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    v3_ordinal1(sK2(sK0)) | ~spl4_9),
% 0.21/0.49    inference(resolution,[],[f108,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,sK0) | v3_ordinal1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ~v3_ordinal1(sK0) & ! [X1] : ((r1_tarski(X1,sK0) & v3_ordinal1(X1)) | ~r2_hidden(X1,sK0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ? [X0] : (~v3_ordinal1(X0) & ! [X1] : ((r1_tarski(X1,X0) & v3_ordinal1(X1)) | ~r2_hidden(X1,X0))) => (~v3_ordinal1(sK0) & ! [X1] : ((r1_tarski(X1,sK0) & v3_ordinal1(X1)) | ~r2_hidden(X1,sK0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0] : (~v3_ordinal1(X0) & ! [X1] : ((r1_tarski(X1,X0) & v3_ordinal1(X1)) | ~r2_hidden(X1,X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (! [X1] : (r2_hidden(X1,X0) => (r1_tarski(X1,X0) & v3_ordinal1(X1))) => v3_ordinal1(X0))),
% 0.21/0.49    inference(negated_conjecture,[],[f9])).
% 0.21/0.49  fof(f9,conjecture,(
% 0.21/0.49    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => (r1_tarski(X1,X0) & v3_ordinal1(X1))) => v3_ordinal1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_ordinal1)).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    r2_hidden(sK2(sK0),sK0) | ~spl4_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f107])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    ~spl4_2 | spl4_9 | spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f105,f58,f107,f66])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    r2_hidden(sK2(sK0),sK0) | ~v1_ordinal1(sK0) | spl4_1),
% 0.21/0.49    inference(resolution,[],[f63,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ~v3_ordinal1(sK0) | spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f58])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0] : (v3_ordinal1(X0) | r2_hidden(sK2(X0),X0) | ~v1_ordinal1(X0)) )),
% 0.21/0.49    inference(resolution,[],[f47,f44])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0] : (v2_ordinal1(X0) | r2_hidden(sK2(X0),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    spl4_8 | ~spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f94,f69,f101])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl4_3 <=> r2_hidden(sK1(sK0),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    v3_ordinal1(sK1(sK0)) | ~spl4_3),
% 0.21/0.49    inference(resolution,[],[f70,f37])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    r2_hidden(sK1(sK0),sK0) | ~spl4_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f69])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl4_4 | ~spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f83,f80,f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl4_4 <=> r1_tarski(sK3(sK0),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl4_5 <=> r2_hidden(sK3(sK0),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    r1_tarski(sK3(sK0),sK0) | ~spl4_5),
% 0.21/0.49    inference(resolution,[],[f81,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,sK0) | r1_tarski(X1,sK0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    r2_hidden(sK3(sK0),sK0) | ~spl4_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f80])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl4_5 | spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f73,f66,f80])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    r2_hidden(sK3(sK0),sK0) | spl4_2),
% 0.21/0.49    inference(resolution,[],[f67,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0] : (v1_ordinal1(X0) | r2_hidden(sK3(X0),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0] : ((v1_ordinal1(X0) | (~r1_tarski(sK3(X0),X0) & r2_hidden(sK3(X0),X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK3(X0),X0) & r2_hidden(sK3(X0),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 0.21/0.49    inference(rectify,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ~v1_ordinal1(sK0) | spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f66])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ~spl4_4 | spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f72,f66,f76])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ~r1_tarski(sK3(sK0),sK0) | spl4_2),
% 0.21/0.49    inference(resolution,[],[f67,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0] : (v1_ordinal1(X0) | ~r1_tarski(sK3(X0),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ~spl4_2 | spl4_3 | spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f64,f58,f69,f66])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    r2_hidden(sK1(sK0),sK0) | ~v1_ordinal1(sK0) | spl4_1),
% 0.21/0.49    inference(resolution,[],[f62,f59])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0] : (v3_ordinal1(X0) | r2_hidden(sK1(X0),X0) | ~v1_ordinal1(X0)) )),
% 0.21/0.49    inference(resolution,[],[f46,f44])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0] : (v2_ordinal1(X0) | r2_hidden(sK1(X0),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ~spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f39,f58])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ~v3_ordinal1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (12828)------------------------------
% 0.21/0.49  % (12828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (12828)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (12828)Memory used [KB]: 10746
% 0.21/0.49  % (12828)Time elapsed: 0.033 s
% 0.21/0.49  % (12828)------------------------------
% 0.21/0.49  % (12828)------------------------------
% 0.21/0.49  % (12819)Success in time 0.131 s
%------------------------------------------------------------------------------
