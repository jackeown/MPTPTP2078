%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 230 expanded)
%              Number of leaves         :   24 (  92 expanded)
%              Depth                    :    8
%              Number of atoms          :  346 ( 760 expanded)
%              Number of equality atoms :   19 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f267,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f69,f70,f87,f90,f100,f131,f137,f145,f151,f163,f170,f179,f200,f230,f233,f265,f266])).

fof(f266,plain,
    ( sK0 != sK1
    | r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f265,plain,
    ( ~ spl2_5
    | ~ spl2_2
    | spl2_7
    | spl2_15
    | spl2_4 ),
    inference(avatar_split_clause,[],[f261,f66,f197,f97,f57,f80])).

fof(f80,plain,
    ( spl2_5
  <=> v3_ordinal1(k1_ordinal1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f57,plain,
    ( spl2_2
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f97,plain,
    ( spl2_7
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f197,plain,
    ( spl2_15
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f66,plain,
    ( spl2_4
  <=> r1_ordinal1(k1_ordinal1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f261,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK0))
    | spl2_4 ),
    inference(resolution,[],[f154,f67])).

fof(f67,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f154,plain,(
    ! [X4,X3] :
      ( r1_ordinal1(k1_ordinal1(X4),X3)
      | X3 = X4
      | r2_hidden(X3,X4)
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(k1_ordinal1(X4)) ) ),
    inference(resolution,[],[f39,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_ordinal1(X1))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f233,plain,
    ( ~ spl2_1
    | ~ spl2_5
    | ~ spl2_18 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_18 ),
    inference(unit_resulting_resolution,[],[f54,f81,f71,f229,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f229,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK0)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl2_18
  <=> r1_ordinal1(k1_ordinal1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f71,plain,(
    ! [X0] : ~ r1_tarski(k1_ordinal1(X0),X0) ),
    inference(resolution,[],[f44,f48])).

fof(f48,plain,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f81,plain,
    ( v3_ordinal1(k1_ordinal1(sK0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f54,plain,
    ( v3_ordinal1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl2_1
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f230,plain,
    ( spl2_18
    | ~ spl2_4
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f203,f197,f66,f227])).

fof(f203,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK0)
    | ~ spl2_4
    | ~ spl2_15 ),
    inference(superposition,[],[f68,f199])).

fof(f199,plain,
    ( sK0 = sK1
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f197])).

fof(f68,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f200,plain,
    ( ~ spl2_13
    | spl2_15
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f183,f134,f197,f148])).

fof(f148,plain,
    ( spl2_13
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f134,plain,
    ( spl2_11
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f183,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK0,sK1)
    | ~ spl2_11 ),
    inference(resolution,[],[f135,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f135,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f179,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_10
    | spl2_12 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | spl2_10
    | spl2_12 ),
    inference(unit_resulting_resolution,[],[f59,f54,f129,f143,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f143,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl2_12 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl2_12
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f129,plain,
    ( ~ r1_ordinal1(sK1,sK0)
    | spl2_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl2_10
  <=> r1_ordinal1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f59,plain,
    ( v3_ordinal1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f170,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_12
    | spl2_13 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_12
    | spl2_13 ),
    inference(unit_resulting_resolution,[],[f54,f59,f150,f144,f35])).

fof(f144,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f142])).

fof(f150,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl2_13 ),
    inference(avatar_component_clause,[],[f148])).

fof(f163,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_10
    | spl2_11 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_10
    | spl2_11 ),
    inference(unit_resulting_resolution,[],[f59,f54,f136,f130,f35])).

fof(f130,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f136,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl2_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f151,plain,
    ( ~ spl2_13
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f146,f97,f148])).

fof(f146,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl2_7 ),
    inference(resolution,[],[f98,f44])).

fof(f98,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f145,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_12
    | spl2_7 ),
    inference(avatar_split_clause,[],[f125,f97,f142,f57,f52])).

fof(f125,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | spl2_7 ),
    inference(resolution,[],[f38,f99])).

fof(f99,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f137,plain,
    ( ~ spl2_11
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f132,f62,f134])).

fof(f62,plain,
    ( spl2_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f132,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f64,f44])).

fof(f64,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f131,plain,
    ( ~ spl2_2
    | ~ spl2_1
    | spl2_10
    | spl2_3 ),
    inference(avatar_split_clause,[],[f124,f62,f128,f52,f57])).

fof(f124,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | spl2_3 ),
    inference(resolution,[],[f38,f63])).

fof(f63,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f100,plain,
    ( ~ spl2_7
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f91,f84,f97])).

fof(f84,plain,
    ( spl2_6
  <=> r1_tarski(k1_ordinal1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f91,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl2_6 ),
    inference(resolution,[],[f86,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_ordinal1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f40,f44])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f90,plain,
    ( ~ spl2_1
    | spl2_5 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl2_1
    | spl2_5 ),
    inference(unit_resulting_resolution,[],[f54,f82,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f82,plain,
    ( ~ v3_ordinal1(k1_ordinal1(sK0))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f87,plain,
    ( ~ spl2_5
    | ~ spl2_2
    | spl2_6
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f78,f66,f84,f57,f80])).

fof(f78,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK0))
    | ~ spl2_4 ),
    inference(resolution,[],[f35,f68])).

fof(f70,plain,
    ( ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f34,f66,f62])).

fof(f34,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24,f23])).

fof(f23,plain,
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

fof(f24,plain,
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

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f69,plain,
    ( spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f33,f66,f62])).

fof(f33,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f32,f57])).

fof(f32,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f31,f52])).

fof(f31,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:33:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (18597)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.47  % (18615)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.49  % (18615)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f267,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f55,f60,f69,f70,f87,f90,f100,f131,f137,f145,f151,f163,f170,f179,f200,f230,f233,f265,f266])).
% 0.21/0.49  fof(f266,plain,(
% 0.21/0.49    sK0 != sK1 | r2_hidden(sK1,sK0) | ~r2_hidden(sK0,sK1)),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f265,plain,(
% 0.21/0.49    ~spl2_5 | ~spl2_2 | spl2_7 | spl2_15 | spl2_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f261,f66,f197,f97,f57,f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl2_5 <=> v3_ordinal1(k1_ordinal1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    spl2_2 <=> v3_ordinal1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl2_7 <=> r2_hidden(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    spl2_15 <=> sK0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl2_4 <=> r1_ordinal1(k1_ordinal1(sK0),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.49  fof(f261,plain,(
% 0.21/0.49    sK0 = sK1 | r2_hidden(sK1,sK0) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k1_ordinal1(sK0)) | spl2_4),
% 0.21/0.49    inference(resolution,[],[f154,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | spl2_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f66])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    ( ! [X4,X3] : (r1_ordinal1(k1_ordinal1(X4),X3) | X3 = X4 | r2_hidden(X3,X4) | ~v3_ordinal1(X3) | ~v3_ordinal1(k1_ordinal1(X4))) )),
% 0.21/0.49    inference(resolution,[],[f39,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k1_ordinal1(X1)) | r2_hidden(X0,X1) | X0 = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.21/0.49    inference(flattening,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    ~spl2_1 | ~spl2_5 | ~spl2_18),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f231])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    $false | (~spl2_1 | ~spl2_5 | ~spl2_18)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f54,f81,f71,f229,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.49  fof(f229,plain,(
% 0.21/0.49    r1_ordinal1(k1_ordinal1(sK0),sK0) | ~spl2_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f227])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    spl2_18 <=> r1_ordinal1(k1_ordinal1(sK0),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k1_ordinal1(X0),X0)) )),
% 0.21/0.49    inference(resolution,[],[f44,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X1] : (r2_hidden(X1,k1_ordinal1(X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    v3_ordinal1(k1_ordinal1(sK0)) | ~spl2_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f80])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    v3_ordinal1(sK0) | ~spl2_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    spl2_1 <=> v3_ordinal1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    spl2_18 | ~spl2_4 | ~spl2_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f203,f197,f66,f227])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    r1_ordinal1(k1_ordinal1(sK0),sK0) | (~spl2_4 | ~spl2_15)),
% 0.21/0.49    inference(superposition,[],[f68,f199])).
% 0.21/0.49  fof(f199,plain,(
% 0.21/0.49    sK0 = sK1 | ~spl2_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f197])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    r1_ordinal1(k1_ordinal1(sK0),sK1) | ~spl2_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f66])).
% 0.21/0.49  fof(f200,plain,(
% 0.21/0.49    ~spl2_13 | spl2_15 | ~spl2_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f183,f134,f197,f148])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    spl2_13 <=> r1_tarski(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    spl2_11 <=> r1_tarski(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    sK0 = sK1 | ~r1_tarski(sK0,sK1) | ~spl2_11),
% 0.21/0.49    inference(resolution,[],[f135,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.49    inference(flattening,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    r1_tarski(sK1,sK0) | ~spl2_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f134])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    ~spl2_1 | ~spl2_2 | spl2_10 | spl2_12),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f176])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    $false | (~spl2_1 | ~spl2_2 | spl2_10 | spl2_12)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f59,f54,f129,f143,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    ~r1_ordinal1(sK0,sK1) | spl2_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f142])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    spl2_12 <=> r1_ordinal1(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    ~r1_ordinal1(sK1,sK0) | spl2_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f128])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    spl2_10 <=> r1_ordinal1(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    v3_ordinal1(sK1) | ~spl2_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f57])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    ~spl2_1 | ~spl2_2 | ~spl2_12 | spl2_13),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f168])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    $false | (~spl2_1 | ~spl2_2 | ~spl2_12 | spl2_13)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f54,f59,f150,f144,f35])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    r1_ordinal1(sK0,sK1) | ~spl2_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f142])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    ~r1_tarski(sK0,sK1) | spl2_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f148])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    ~spl2_1 | ~spl2_2 | ~spl2_10 | spl2_11),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f161])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    $false | (~spl2_1 | ~spl2_2 | ~spl2_10 | spl2_11)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f59,f54,f136,f130,f35])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    r1_ordinal1(sK1,sK0) | ~spl2_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f128])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    ~r1_tarski(sK1,sK0) | spl2_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f134])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    ~spl2_13 | ~spl2_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f146,f97,f148])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    ~r1_tarski(sK0,sK1) | ~spl2_7),
% 0.21/0.49    inference(resolution,[],[f98,f44])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    r2_hidden(sK1,sK0) | ~spl2_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f97])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    ~spl2_1 | ~spl2_2 | spl2_12 | spl2_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f125,f97,f142,f57,f52])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | spl2_7),
% 0.21/0.49    inference(resolution,[],[f38,f99])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ~r2_hidden(sK1,sK0) | spl2_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f97])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    ~spl2_11 | ~spl2_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f132,f62,f134])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl2_3 <=> r2_hidden(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    ~r1_tarski(sK1,sK0) | ~spl2_3),
% 0.21/0.49    inference(resolution,[],[f64,f44])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    r2_hidden(sK0,sK1) | ~spl2_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ~spl2_2 | ~spl2_1 | spl2_10 | spl2_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f124,f62,f128,f52,f57])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | spl2_3),
% 0.21/0.49    inference(resolution,[],[f38,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ~r2_hidden(sK0,sK1) | spl2_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    ~spl2_7 | ~spl2_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f91,f84,f97])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    spl2_6 <=> r1_tarski(k1_ordinal1(sK0),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ~r2_hidden(sK1,sK0) | ~spl2_6),
% 0.21/0.49    inference(resolution,[],[f86,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(k1_ordinal1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(resolution,[],[f40,f44])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    r1_tarski(k1_ordinal1(sK0),sK1) | ~spl2_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f84])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ~spl2_1 | spl2_5),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    $false | (~spl2_1 | spl2_5)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f54,f82,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ~v3_ordinal1(k1_ordinal1(sK0)) | spl2_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f80])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ~spl2_5 | ~spl2_2 | spl2_6 | ~spl2_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f78,f66,f84,f57,f80])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    r1_tarski(k1_ordinal1(sK0),sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k1_ordinal1(sK0)) | ~spl2_4),
% 0.21/0.49    inference(resolution,[],[f35,f68])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ~spl2_3 | ~spl2_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f34,f66,f62])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.21/0.49    inference(negated_conjecture,[],[f10])).
% 0.21/0.49  fof(f10,conjecture,(
% 0.21/0.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl2_3 | spl2_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f33,f66,f62])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    spl2_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f32,f57])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    v3_ordinal1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    spl2_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f31,f52])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    v3_ordinal1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (18615)------------------------------
% 0.21/0.49  % (18615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (18615)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (18615)Memory used [KB]: 10874
% 0.21/0.49  % (18615)Time elapsed: 0.076 s
% 0.21/0.49  % (18615)------------------------------
% 0.21/0.49  % (18615)------------------------------
% 0.21/0.50  % (18587)Success in time 0.136 s
%------------------------------------------------------------------------------
