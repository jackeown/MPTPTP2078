%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:40 EST 2020

% Result     : Theorem 3.94s
% Output     : Refutation 4.18s
% Verified   : 
% Statistics : Number of formulae       :  225 ( 470 expanded)
%              Number of leaves         :   48 ( 158 expanded)
%              Depth                    :   14
%              Number of atoms          :  684 (1650 expanded)
%              Number of equality atoms :   50 ( 102 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (32538)Time limit reached!
% (32538)------------------------------
% (32538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (32538)Termination reason: Time limit

% (32538)Memory used [KB]: 8187
% (32538)Time elapsed: 0.502 s
% (32538)------------------------------
% (32538)------------------------------
% (32543)Time limit reached!
% (32543)------------------------------
% (32543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (32543)Termination reason: Time limit

% (32543)Memory used [KB]: 15095
% (32543)Time elapsed: 0.512 s
% (32543)------------------------------
% (32543)------------------------------
% (32526)Time limit reached!
% (32526)------------------------------
% (32526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (32526)Termination reason: Time limit

% (32526)Memory used [KB]: 4605
% (32526)Time elapsed: 0.508 s
% (32526)------------------------------
% (32526)------------------------------
fof(f3643,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f127,f132,f137,f141,f2972,f2990,f3021,f3178,f3243,f3349,f3385,f3473,f3482,f3497,f3504,f3510,f3611,f3613,f3617,f3638,f3642])).

fof(f3642,plain,(
    ~ spl11_6 ),
    inference(avatar_contradiction_clause,[],[f3641])).

fof(f3641,plain,
    ( $false
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f215,f1181])).

fof(f1181,plain,(
    ! [X1] : ~ r2_hidden(X1,X1) ),
    inference(resolution,[],[f1158,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f1158,plain,(
    ! [X3] : r1_tarski(X3,X3) ),
    inference(superposition,[],[f960,f115])).

fof(f115,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f74,f75])).

fof(f75,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f74,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f960,plain,(
    ! [X0] : r1_tarski(k3_tarski(X0),k3_tarski(X0)) ),
    inference(duplicate_literal_removal,[],[f953])).

fof(f953,plain,(
    ! [X0] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X0))
      | r1_tarski(k3_tarski(X0),k3_tarski(X0)) ) ),
    inference(resolution,[],[f207,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f30,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f207,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,k3_tarski(X1)),X1)
      | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(resolution,[],[f91,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK7(X0,X1),X1)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f215,plain,
    ( r2_hidden(sK4,sK4)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl11_6
  <=> r2_hidden(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f3638,plain,
    ( ~ spl11_1
    | ~ spl11_32 ),
    inference(avatar_contradiction_clause,[],[f3637])).

fof(f3637,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_32 ),
    inference(subsumption_resolution,[],[f3636,f121])).

fof(f121,plain,
    ( v4_ordinal1(sK4)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl11_1
  <=> v4_ordinal1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f3636,plain,
    ( ~ v4_ordinal1(sK4)
    | ~ spl11_32 ),
    inference(subsumption_resolution,[],[f3625,f1181])).

fof(f3625,plain,
    ( r2_hidden(sK4,sK4)
    | ~ v4_ordinal1(sK4)
    | ~ spl11_32 ),
    inference(superposition,[],[f2966,f82])).

fof(f82,plain,(
    ! [X0] :
      ( k3_tarski(X0) = X0
      | ~ v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
        | k3_tarski(X0) != X0 )
      & ( k3_tarski(X0) = X0
        | ~ v4_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v4_ordinal1(X0)
    <=> k3_tarski(X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_ordinal1)).

fof(f2966,plain,
    ( r2_hidden(k3_tarski(sK4),sK4)
    | ~ spl11_32 ),
    inference(avatar_component_clause,[],[f2965])).

fof(f2965,plain,
    ( spl11_32
  <=> r2_hidden(k3_tarski(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f3617,plain,
    ( spl11_46
    | spl11_2
    | ~ spl11_44
    | spl11_45 ),
    inference(avatar_split_clause,[],[f3401,f3294,f3290,f124,f3298])).

fof(f3298,plain,
    ( spl11_46
  <=> sK4 = k2_xboole_0(sK5,k2_tarski(sK5,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).

fof(f124,plain,
    ( spl11_2
  <=> r2_hidden(k2_xboole_0(sK5,k2_tarski(sK5,sK5)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f3290,plain,
    ( spl11_44
  <=> v3_ordinal1(k2_xboole_0(sK5,k2_tarski(sK5,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).

fof(f3294,plain,
    ( spl11_45
  <=> r2_hidden(sK4,k2_xboole_0(sK5,k2_tarski(sK5,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_45])])).

fof(f3401,plain,
    ( sK4 = k2_xboole_0(sK5,k2_tarski(sK5,sK5))
    | spl11_2
    | ~ spl11_44
    | spl11_45 ),
    inference(subsumption_resolution,[],[f3400,f3291])).

fof(f3291,plain,
    ( v3_ordinal1(k2_xboole_0(sK5,k2_tarski(sK5,sK5)))
    | ~ spl11_44 ),
    inference(avatar_component_clause,[],[f3290])).

fof(f3400,plain,
    ( sK4 = k2_xboole_0(sK5,k2_tarski(sK5,sK5))
    | ~ v3_ordinal1(k2_xboole_0(sK5,k2_tarski(sK5,sK5)))
    | spl11_2
    | spl11_45 ),
    inference(subsumption_resolution,[],[f3399,f68])).

fof(f68,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( ( ~ r2_hidden(k1_ordinal1(sK5),sK4)
        & r2_hidden(sK5,sK4)
        & v3_ordinal1(sK5) )
      | ~ v4_ordinal1(sK4) )
    & ( ! [X2] :
          ( r2_hidden(k1_ordinal1(X2),sK4)
          | ~ r2_hidden(X2,sK4)
          | ~ v3_ordinal1(X2) )
      | v4_ordinal1(sK4) )
    & v3_ordinal1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) )
          | ~ v4_ordinal1(X0) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | v4_ordinal1(X0) )
        & v3_ordinal1(X0) )
   => ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),sK4)
            & r2_hidden(X1,sK4)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(sK4) )
      & ( ! [X2] :
            ( r2_hidden(k1_ordinal1(X2),sK4)
            | ~ r2_hidden(X2,sK4)
            | ~ v3_ordinal1(X2) )
        | v4_ordinal1(sK4) )
      & v3_ordinal1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ~ r2_hidden(k1_ordinal1(X1),sK4)
        & r2_hidden(X1,sK4)
        & v3_ordinal1(X1) )
   => ( ~ r2_hidden(k1_ordinal1(sK5),sK4)
      & r2_hidden(sK5,sK4)
      & v3_ordinal1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X2] :
            ( r2_hidden(k1_ordinal1(X2),X0)
            | ~ r2_hidden(X2,X0)
            | ~ v3_ordinal1(X2) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( v4_ordinal1(X0)
        <=> ! [X1] :
              ( v3_ordinal1(X1)
             => ( r2_hidden(X1,X0)
               => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

fof(f3399,plain,
    ( sK4 = k2_xboole_0(sK5,k2_tarski(sK5,sK5))
    | ~ v3_ordinal1(sK4)
    | ~ v3_ordinal1(k2_xboole_0(sK5,k2_tarski(sK5,sK5)))
    | spl11_2
    | spl11_45 ),
    inference(subsumption_resolution,[],[f3395,f126])).

fof(f126,plain,
    ( ~ r2_hidden(k2_xboole_0(sK5,k2_tarski(sK5,sK5)),sK4)
    | spl11_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f3395,plain,
    ( sK4 = k2_xboole_0(sK5,k2_tarski(sK5,sK5))
    | r2_hidden(k2_xboole_0(sK5,k2_tarski(sK5,sK5)),sK4)
    | ~ v3_ordinal1(sK4)
    | ~ v3_ordinal1(k2_xboole_0(sK5,k2_tarski(sK5,sK5)))
    | spl11_45 ),
    inference(resolution,[],[f3295,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f3295,plain,
    ( ~ r2_hidden(sK4,k2_xboole_0(sK5,k2_tarski(sK5,sK5)))
    | spl11_45 ),
    inference(avatar_component_clause,[],[f3294])).

fof(f3613,plain,
    ( ~ spl11_33
    | spl11_32
    | spl11_35
    | spl11_34 ),
    inference(avatar_split_clause,[],[f3612,f2978,f2982,f2965,f2969])).

fof(f2969,plain,
    ( spl11_33
  <=> v3_ordinal1(k3_tarski(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).

fof(f2982,plain,
    ( spl11_35
  <=> sK4 = k3_tarski(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).

fof(f2978,plain,
    ( spl11_34
  <=> r2_hidden(sK4,k3_tarski(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f3612,plain,
    ( sK4 = k3_tarski(sK4)
    | r2_hidden(k3_tarski(sK4),sK4)
    | ~ v3_ordinal1(k3_tarski(sK4))
    | spl11_34 ),
    inference(subsumption_resolution,[],[f3185,f68])).

fof(f3185,plain,
    ( sK4 = k3_tarski(sK4)
    | r2_hidden(k3_tarski(sK4),sK4)
    | ~ v3_ordinal1(sK4)
    | ~ v3_ordinal1(k3_tarski(sK4))
    | spl11_34 ),
    inference(resolution,[],[f2979,f81])).

fof(f2979,plain,
    ( ~ r2_hidden(sK4,k3_tarski(sK4))
    | spl11_34 ),
    inference(avatar_component_clause,[],[f2978])).

fof(f3611,plain,
    ( ~ spl11_3
    | ~ spl11_50 ),
    inference(avatar_contradiction_clause,[],[f3610])).

fof(f3610,plain,
    ( $false
    | ~ spl11_3
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f3605,f131])).

fof(f131,plain,
    ( r2_hidden(sK5,sK4)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl11_3
  <=> r2_hidden(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f3605,plain,
    ( ~ r2_hidden(sK5,sK4)
    | ~ spl11_50 ),
    inference(resolution,[],[f3323,f169])).

fof(f169,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X6,k2_tarski(X5,X5))
      | ~ r2_hidden(X5,X6) ) ),
    inference(superposition,[],[f152,f115])).

fof(f152,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k3_tarski(X2),X1)
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f89,f101])).

fof(f3323,plain,
    ( r2_hidden(sK4,k2_tarski(sK5,sK5))
    | ~ spl11_50 ),
    inference(avatar_component_clause,[],[f3321])).

fof(f3321,plain,
    ( spl11_50
  <=> r2_hidden(sK4,k2_tarski(sK5,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).

fof(f3510,plain,
    ( ~ spl11_42
    | ~ spl11_3
    | ~ spl11_43 ),
    inference(avatar_split_clause,[],[f3509,f3259,f129,f3255])).

fof(f3255,plain,
    ( spl11_42
  <=> r2_hidden(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).

fof(f3259,plain,
    ( spl11_43
  <=> v1_ordinal1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_43])])).

fof(f3509,plain,
    ( ~ r2_hidden(sK4,sK5)
    | ~ spl11_3
    | ~ spl11_43 ),
    inference(subsumption_resolution,[],[f3506,f3260])).

fof(f3260,plain,
    ( v1_ordinal1(sK5)
    | ~ spl11_43 ),
    inference(avatar_component_clause,[],[f3259])).

fof(f3506,plain,
    ( ~ v1_ordinal1(sK5)
    | ~ r2_hidden(sK4,sK5)
    | ~ spl11_3 ),
    inference(resolution,[],[f131,f165])).

fof(f165,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ v1_ordinal1(X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f84,f101])).

fof(f84,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK6(X0),X0)
          & r2_hidden(sK6(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f46,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK6(X0),X0)
        & r2_hidden(sK6(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f3504,plain,
    ( spl11_50
    | spl11_42
    | ~ spl11_45 ),
    inference(avatar_split_clause,[],[f3379,f3294,f3255,f3321])).

fof(f3379,plain,
    ( r2_hidden(sK4,k2_tarski(sK5,sK5))
    | spl11_42
    | ~ spl11_45 ),
    inference(subsumption_resolution,[],[f3377,f3257])).

fof(f3257,plain,
    ( ~ r2_hidden(sK4,sK5)
    | spl11_42 ),
    inference(avatar_component_clause,[],[f3255])).

fof(f3377,plain,
    ( r2_hidden(sK4,sK5)
    | r2_hidden(sK4,k2_tarski(sK5,sK5))
    | ~ spl11_45 ),
    inference(resolution,[],[f3371,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ~ r2_hidden(X1,X0)
          & ~ r2_hidden(X1,X2) ) )
      & ( r2_hidden(X1,X0)
        | r2_hidden(X1,X2)
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X1,X3,X0] :
      ( ( sP2(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP2(X1,X3,X0) ) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X1,X3,X0] :
      ( ( sP2(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP2(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X1,X3,X0] :
      ( sP2(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f3371,plain,
    ( sP2(k2_tarski(sK5,sK5),sK4,sK5)
    | ~ spl11_45 ),
    inference(resolution,[],[f3296,f365])).

fof(f365,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,X2))
      | sP2(X2,X0,X1) ) ),
    inference(resolution,[],[f102,f118])).

fof(f118,plain,(
    ! [X0,X1] : sP3(X0,X1,k2_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP3(X0,X1,X2) )
      & ( sP3(X0,X1,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP3(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f36,f35])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( sP3(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP2(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f102,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP2(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ( ~ sP2(X1,sK10(X0,X1,X2),X0)
            | ~ r2_hidden(sK10(X0,X1,X2),X2) )
          & ( sP2(X1,sK10(X0,X1,X2),X0)
            | r2_hidden(sK10(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP2(X1,X4,X0) )
            & ( sP2(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f61,f62])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP2(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP2(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP2(X1,sK10(X0,X1,X2),X0)
          | ~ r2_hidden(sK10(X0,X1,X2),X2) )
        & ( sP2(X1,sK10(X0,X1,X2),X0)
          | r2_hidden(sK10(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP2(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP2(X1,X4,X0) )
            & ( sP2(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f60])).

% (32527)Time limit reached!
% (32527)------------------------------
% (32527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (32527)Termination reason: Time limit

% (32527)Memory used [KB]: 9338
% (32527)Time elapsed: 0.509 s
% (32527)------------------------------
% (32527)------------------------------
fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP2(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP2(X1,X3,X0) )
            & ( sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f3296,plain,
    ( r2_hidden(sK4,k2_xboole_0(sK5,k2_tarski(sK5,sK5)))
    | ~ spl11_45 ),
    inference(avatar_component_clause,[],[f3294])).

fof(f3497,plain,
    ( ~ spl11_3
    | spl11_6
    | ~ spl11_56 ),
    inference(avatar_contradiction_clause,[],[f3496])).

fof(f3496,plain,
    ( $false
    | ~ spl11_3
    | spl11_6
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f3484,f216])).

fof(f216,plain,
    ( ~ r2_hidden(sK4,sK4)
    | spl11_6 ),
    inference(avatar_component_clause,[],[f214])).

fof(f3484,plain,
    ( r2_hidden(sK4,sK4)
    | ~ spl11_3
    | ~ spl11_56 ),
    inference(backward_demodulation,[],[f131,f3468])).

fof(f3468,plain,
    ( sK4 = sK5
    | ~ spl11_56 ),
    inference(avatar_component_clause,[],[f3466])).

fof(f3466,plain,
    ( spl11_56
  <=> sK4 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).

fof(f3482,plain,
    ( ~ spl11_43
    | spl11_57 ),
    inference(avatar_contradiction_clause,[],[f3481])).

fof(f3481,plain,
    ( $false
    | ~ spl11_43
    | spl11_57 ),
    inference(subsumption_resolution,[],[f3476,f3260])).

fof(f3476,plain,
    ( ~ v1_ordinal1(sK5)
    | spl11_57 ),
    inference(resolution,[],[f3472,f995])).

fof(f995,plain,(
    ! [X0] :
      ( r1_tarski(k3_tarski(X0),X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f991])).

fof(f991,plain,(
    ! [X0] :
      ( r1_tarski(k3_tarski(X0),X0)
      | ~ v1_ordinal1(X0)
      | r1_tarski(k3_tarski(X0),X0) ) ),
    inference(resolution,[],[f209,f90])).

fof(f209,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK7(X4,X5),X5)
      | r1_tarski(k3_tarski(X4),X5)
      | ~ v1_ordinal1(X5) ) ),
    inference(resolution,[],[f91,f84])).

fof(f3472,plain,
    ( ~ r1_tarski(k3_tarski(sK5),sK5)
    | spl11_57 ),
    inference(avatar_component_clause,[],[f3470])).

fof(f3470,plain,
    ( spl11_57
  <=> r1_tarski(k3_tarski(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_57])])).

fof(f3473,plain,
    ( spl11_56
    | ~ spl11_57
    | ~ spl11_35
    | ~ spl11_46 ),
    inference(avatar_split_clause,[],[f3464,f3298,f2982,f3470,f3466])).

fof(f3464,plain,
    ( ~ r1_tarski(k3_tarski(sK5),sK5)
    | sK4 = sK5
    | ~ spl11_35
    | ~ spl11_46 ),
    inference(forward_demodulation,[],[f3463,f115])).

fof(f3463,plain,
    ( sK4 = sK5
    | ~ r1_tarski(k3_tarski(sK5),k3_tarski(k2_tarski(sK5,sK5)))
    | ~ spl11_35
    | ~ spl11_46 ),
    inference(forward_demodulation,[],[f3462,f2984])).

fof(f2984,plain,
    ( sK4 = k3_tarski(sK4)
    | ~ spl11_35 ),
    inference(avatar_component_clause,[],[f2982])).

fof(f3462,plain,
    ( sK5 = k3_tarski(sK4)
    | ~ r1_tarski(k3_tarski(sK5),k3_tarski(k2_tarski(sK5,sK5)))
    | ~ spl11_46 ),
    inference(forward_demodulation,[],[f3443,f115])).

fof(f3443,plain,
    ( k3_tarski(sK4) = k3_tarski(k2_tarski(sK5,sK5))
    | ~ r1_tarski(k3_tarski(sK5),k3_tarski(k2_tarski(sK5,sK5)))
    | ~ spl11_46 ),
    inference(superposition,[],[f331,f3300])).

fof(f3300,plain,
    ( sK4 = k2_xboole_0(sK5,k2_tarski(sK5,sK5))
    | ~ spl11_46 ),
    inference(avatar_component_clause,[],[f3298])).

fof(f331,plain,(
    ! [X6,X5] :
      ( k3_tarski(X6) = k3_tarski(k2_xboole_0(X5,X6))
      | ~ r1_tarski(k3_tarski(X5),k3_tarski(X6)) ) ),
    inference(superposition,[],[f87,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f87,plain,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(f3385,plain,
    ( ~ spl11_4
    | spl11_43 ),
    inference(avatar_contradiction_clause,[],[f3384])).

fof(f3384,plain,
    ( $false
    | ~ spl11_4
    | spl11_43 ),
    inference(subsumption_resolution,[],[f3383,f136])).

fof(f136,plain,
    ( v3_ordinal1(sK5)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl11_4
  <=> v3_ordinal1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f3383,plain,
    ( ~ v3_ordinal1(sK5)
    | spl11_43 ),
    inference(resolution,[],[f3261,f79])).

fof(f79,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f3261,plain,
    ( ~ v1_ordinal1(sK5)
    | spl11_43 ),
    inference(avatar_component_clause,[],[f3259])).

fof(f3349,plain,
    ( ~ spl11_4
    | spl11_44 ),
    inference(avatar_contradiction_clause,[],[f3348])).

fof(f3348,plain,
    ( $false
    | ~ spl11_4
    | spl11_44 ),
    inference(subsumption_resolution,[],[f3344,f136])).

fof(f3344,plain,
    ( ~ v3_ordinal1(sK5)
    | spl11_44 ),
    inference(resolution,[],[f3292,f116])).

fof(f116,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f77,f111])).

fof(f111,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f76,f75])).

fof(f76,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f77,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f3292,plain,
    ( ~ v3_ordinal1(k2_xboole_0(sK5,k2_tarski(sK5,sK5)))
    | spl11_44 ),
    inference(avatar_component_clause,[],[f3290])).

fof(f3243,plain,
    ( spl11_1
    | ~ spl11_35 ),
    inference(avatar_split_clause,[],[f3230,f2982,f120])).

fof(f3230,plain,
    ( v4_ordinal1(sK4)
    | ~ spl11_35 ),
    inference(trivial_inequality_removal,[],[f3197])).

fof(f3197,plain,
    ( sK4 != sK4
    | v4_ordinal1(sK4)
    | ~ spl11_35 ),
    inference(superposition,[],[f83,f2984])).

fof(f83,plain,(
    ! [X0] :
      ( k3_tarski(X0) != X0
      | v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f3178,plain,(
    ~ spl11_15 ),
    inference(avatar_contradiction_clause,[],[f3177])).

fof(f3177,plain,
    ( $false
    | ~ spl11_15 ),
    inference(subsumption_resolution,[],[f3176,f68])).

fof(f3176,plain,
    ( ~ v3_ordinal1(sK4)
    | ~ spl11_15 ),
    inference(resolution,[],[f3175,f79])).

fof(f3175,plain,
    ( ~ v1_ordinal1(sK4)
    | ~ spl11_15 ),
    inference(resolution,[],[f3171,f937])).

fof(f937,plain,
    ( sP0(sK4,sK4)
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f936])).

fof(f936,plain,
    ( spl11_15
  <=> sP0(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f3171,plain,(
    ! [X0] :
      ( ~ sP0(X0,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f3167])).

fof(f3167,plain,(
    ! [X0] :
      ( ~ v1_ordinal1(X0)
      | ~ sP0(X0,X0)
      | ~ sP0(X0,X0) ) ),
    inference(resolution,[],[f202,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | ~ r2_hidden(X1,X2) ) )
      & ( ( r2_hidden(sK9(X0,X1),X0)
          & r2_hidden(X1,sK9(X0,X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f56,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X0)
          & r2_hidden(X1,X3) )
     => ( r2_hidden(sK9(X0,X1),X0)
        & r2_hidden(X1,sK9(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | ~ r2_hidden(X1,X2) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X0)
            & r2_hidden(X1,X3) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0,X2] :
      ( ( sP0(X0,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X3) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X0)
            & r2_hidden(X2,X3) )
        | ~ sP0(X0,X2) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X2] :
      ( sP0(X0,X2)
    <=> ? [X3] :
          ( r2_hidden(X3,X0)
          & r2_hidden(X2,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f202,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(sK9(X2,X1),X1)
      | ~ v1_ordinal1(X1)
      | ~ sP0(X2,X1) ) ),
    inference(resolution,[],[f165,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,sK9(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f3021,plain,
    ( spl11_15
    | ~ spl11_34 ),
    inference(avatar_split_clause,[],[f3007,f2978,f936])).

fof(f3007,plain,
    ( sP0(sK4,sK4)
    | ~ spl11_34 ),
    inference(resolution,[],[f2980,f238])).

fof(f238,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_tarski(X1))
      | sP0(X1,X0) ) ),
    inference(resolution,[],[f92,f117])).

fof(f117,plain,(
    ! [X0] : sP1(X0,k3_tarski(X0)) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ~ sP1(X0,X1) )
      & ( sP1(X0,X1)
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> sP1(X0,X1) ) ),
    inference(definition_folding,[],[f4,f33,f32])).

fof(f33,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP0(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( ~ sP1(X0,X1)
      | ~ r2_hidden(X3,X1)
      | sP0(X0,X3) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( ~ sP0(X0,sK8(X0,X1))
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( sP0(X0,sK8(X0,X1))
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X0,X3) )
            & ( sP0(X0,X3)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f52,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ sP0(X0,X2)
            | ~ r2_hidden(X2,X1) )
          & ( sP0(X0,X2)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ sP0(X0,sK8(X0,X1))
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( sP0(X0,sK8(X0,X1))
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X0,X2)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X0,X2)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X0,X3) )
            & ( sP0(X0,X3)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X0,X2)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X0,X2)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ sP0(X0,X2) )
            & ( sP0(X0,X2)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f2980,plain,
    ( r2_hidden(sK4,k3_tarski(sK4))
    | ~ spl11_34 ),
    inference(avatar_component_clause,[],[f2978])).

fof(f2990,plain,(
    spl11_33 ),
    inference(avatar_contradiction_clause,[],[f2989])).

fof(f2989,plain,
    ( $false
    | spl11_33 ),
    inference(subsumption_resolution,[],[f2986,f68])).

fof(f2986,plain,
    ( ~ v3_ordinal1(sK4)
    | spl11_33 ),
    inference(resolution,[],[f2971,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_ordinal1)).

fof(f2971,plain,
    ( ~ v3_ordinal1(k3_tarski(sK4))
    | spl11_33 ),
    inference(avatar_component_clause,[],[f2969])).

fof(f2972,plain,
    ( ~ spl11_32
    | ~ spl11_33
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f2946,f139,f2969,f2965])).

fof(f139,plain,
    ( spl11_5
  <=> ! [X2] :
        ( r2_hidden(k2_xboole_0(X2,k2_tarski(X2,X2)),sK4)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f2946,plain,
    ( ~ v3_ordinal1(k3_tarski(sK4))
    | ~ r2_hidden(k3_tarski(sK4),sK4)
    | ~ spl11_5 ),
    inference(resolution,[],[f166,f140])).

fof(f140,plain,
    ( ! [X2] :
        ( r2_hidden(k2_xboole_0(X2,k2_tarski(X2,X2)),sK4)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,sK4) )
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f139])).

fof(f166,plain,(
    ! [X0] : ~ r2_hidden(k2_xboole_0(k3_tarski(X0),k2_tarski(k3_tarski(X0),k3_tarski(X0))),X0) ),
    inference(resolution,[],[f152,f114])).

fof(f114,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f73,f111])).

fof(f73,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f141,plain,
    ( spl11_1
    | spl11_5 ),
    inference(avatar_split_clause,[],[f113,f139,f120])).

fof(f113,plain,(
    ! [X2] :
      ( r2_hidden(k2_xboole_0(X2,k2_tarski(X2,X2)),sK4)
      | ~ r2_hidden(X2,sK4)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK4) ) ),
    inference(definition_unfolding,[],[f69,f111])).

fof(f69,plain,(
    ! [X2] :
      ( r2_hidden(k1_ordinal1(X2),sK4)
      | ~ r2_hidden(X2,sK4)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f137,plain,
    ( ~ spl11_1
    | spl11_4 ),
    inference(avatar_split_clause,[],[f70,f134,f120])).

fof(f70,plain,
    ( v3_ordinal1(sK5)
    | ~ v4_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f132,plain,
    ( ~ spl11_1
    | spl11_3 ),
    inference(avatar_split_clause,[],[f71,f129,f120])).

fof(f71,plain,
    ( r2_hidden(sK5,sK4)
    | ~ v4_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f127,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f112,f124,f120])).

fof(f112,plain,
    ( ~ r2_hidden(k2_xboole_0(sK5,k2_tarski(sK5,sK5)),sK4)
    | ~ v4_ordinal1(sK4) ),
    inference(definition_unfolding,[],[f72,f111])).

fof(f72,plain,
    ( ~ r2_hidden(k1_ordinal1(sK5),sK4)
    | ~ v4_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (32544)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (32548)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (32540)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (32530)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (32531)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (32548)Refutation not found, incomplete strategy% (32548)------------------------------
% 0.20/0.51  % (32548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (32532)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (32548)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (32548)Memory used [KB]: 10746
% 0.20/0.51  % (32548)Time elapsed: 0.053 s
% 0.20/0.51  % (32548)------------------------------
% 0.20/0.51  % (32548)------------------------------
% 0.20/0.52  % (32526)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (32529)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (32534)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (32535)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (32536)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (32537)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (32538)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (32552)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (32527)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (32541)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (32528)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (32553)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (32528)Refutation not found, incomplete strategy% (32528)------------------------------
% 0.20/0.54  % (32528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (32528)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (32528)Memory used [KB]: 10746
% 0.20/0.54  % (32528)Time elapsed: 0.127 s
% 0.20/0.54  % (32528)------------------------------
% 0.20/0.54  % (32528)------------------------------
% 0.20/0.54  % (32554)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (32555)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (32549)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  % (32545)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (32551)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (32546)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (32542)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (32547)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (32546)Refutation not found, incomplete strategy% (32546)------------------------------
% 0.20/0.55  % (32546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (32546)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (32546)Memory used [KB]: 10746
% 0.20/0.55  % (32546)Time elapsed: 0.142 s
% 0.20/0.55  % (32546)------------------------------
% 0.20/0.55  % (32546)------------------------------
% 0.20/0.55  % (32547)Refutation not found, incomplete strategy% (32547)------------------------------
% 0.20/0.55  % (32547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (32547)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (32547)Memory used [KB]: 1663
% 0.20/0.55  % (32547)Time elapsed: 0.139 s
% 0.20/0.55  % (32547)------------------------------
% 0.20/0.55  % (32547)------------------------------
% 0.20/0.55  % (32539)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (32533)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (32550)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (32543)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 2.06/0.66  % (32573)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.06/0.68  % (32576)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.06/0.69  % (32574)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.06/0.70  % (32575)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.33/0.83  % (32531)Time limit reached!
% 3.33/0.83  % (32531)------------------------------
% 3.33/0.83  % (32531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.33/0.83  % (32531)Termination reason: Time limit
% 3.33/0.83  
% 3.33/0.83  % (32531)Memory used [KB]: 8699
% 3.33/0.83  % (32531)Time elapsed: 0.418 s
% 3.33/0.83  % (32531)------------------------------
% 3.33/0.83  % (32531)------------------------------
% 3.94/0.90  % (32553)Refutation found. Thanks to Tanya!
% 3.94/0.90  % SZS status Theorem for theBenchmark
% 3.94/0.90  % SZS output start Proof for theBenchmark
% 4.18/0.91  % (32538)Time limit reached!
% 4.18/0.91  % (32538)------------------------------
% 4.18/0.91  % (32538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.18/0.91  % (32538)Termination reason: Time limit
% 4.18/0.91  
% 4.18/0.91  % (32538)Memory used [KB]: 8187
% 4.18/0.91  % (32538)Time elapsed: 0.502 s
% 4.18/0.91  % (32538)------------------------------
% 4.18/0.91  % (32538)------------------------------
% 4.18/0.92  % (32543)Time limit reached!
% 4.18/0.92  % (32543)------------------------------
% 4.18/0.92  % (32543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.18/0.92  % (32543)Termination reason: Time limit
% 4.18/0.92  
% 4.18/0.92  % (32543)Memory used [KB]: 15095
% 4.18/0.92  % (32543)Time elapsed: 0.512 s
% 4.18/0.92  % (32543)------------------------------
% 4.18/0.92  % (32543)------------------------------
% 4.18/0.92  % (32526)Time limit reached!
% 4.18/0.92  % (32526)------------------------------
% 4.18/0.92  % (32526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.18/0.92  % (32526)Termination reason: Time limit
% 4.18/0.92  
% 4.18/0.92  % (32526)Memory used [KB]: 4605
% 4.18/0.92  % (32526)Time elapsed: 0.508 s
% 4.18/0.92  % (32526)------------------------------
% 4.18/0.92  % (32526)------------------------------
% 4.18/0.92  fof(f3643,plain,(
% 4.18/0.92    $false),
% 4.18/0.92    inference(avatar_sat_refutation,[],[f127,f132,f137,f141,f2972,f2990,f3021,f3178,f3243,f3349,f3385,f3473,f3482,f3497,f3504,f3510,f3611,f3613,f3617,f3638,f3642])).
% 4.18/0.92  fof(f3642,plain,(
% 4.18/0.92    ~spl11_6),
% 4.18/0.92    inference(avatar_contradiction_clause,[],[f3641])).
% 4.18/0.92  fof(f3641,plain,(
% 4.18/0.92    $false | ~spl11_6),
% 4.18/0.92    inference(subsumption_resolution,[],[f215,f1181])).
% 4.18/0.92  fof(f1181,plain,(
% 4.18/0.92    ( ! [X1] : (~r2_hidden(X1,X1)) )),
% 4.18/0.92    inference(resolution,[],[f1158,f101])).
% 4.18/0.92  fof(f101,plain,(
% 4.18/0.92    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 4.18/0.92    inference(cnf_transformation,[],[f31])).
% 4.18/0.92  fof(f31,plain,(
% 4.18/0.92    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 4.18/0.92    inference(ennf_transformation,[],[f17])).
% 4.18/0.92  fof(f17,axiom,(
% 4.18/0.92    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 4.18/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 4.18/0.92  fof(f1158,plain,(
% 4.18/0.92    ( ! [X3] : (r1_tarski(X3,X3)) )),
% 4.18/0.92    inference(superposition,[],[f960,f115])).
% 4.18/0.92  fof(f115,plain,(
% 4.18/0.92    ( ! [X0] : (k3_tarski(k2_tarski(X0,X0)) = X0) )),
% 4.18/0.92    inference(definition_unfolding,[],[f74,f75])).
% 4.18/0.92  fof(f75,plain,(
% 4.18/0.92    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 4.18/0.92    inference(cnf_transformation,[],[f3])).
% 4.18/0.92  fof(f3,axiom,(
% 4.18/0.92    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 4.18/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 4.18/0.92  fof(f74,plain,(
% 4.18/0.92    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 4.18/0.92    inference(cnf_transformation,[],[f6])).
% 4.18/0.92  fof(f6,axiom,(
% 4.18/0.92    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 4.18/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 4.18/0.92  fof(f960,plain,(
% 4.18/0.92    ( ! [X0] : (r1_tarski(k3_tarski(X0),k3_tarski(X0))) )),
% 4.18/0.92    inference(duplicate_literal_removal,[],[f953])).
% 4.18/0.92  fof(f953,plain,(
% 4.18/0.92    ( ! [X0] : (r1_tarski(k3_tarski(X0),k3_tarski(X0)) | r1_tarski(k3_tarski(X0),k3_tarski(X0))) )),
% 4.18/0.92    inference(resolution,[],[f207,f90])).
% 4.18/0.92  fof(f90,plain,(
% 4.18/0.92    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 4.18/0.92    inference(cnf_transformation,[],[f50])).
% 4.18/0.92  fof(f50,plain,(
% 4.18/0.92    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 4.18/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f30,f49])).
% 4.18/0.92  fof(f49,plain,(
% 4.18/0.92    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 4.18/0.92    introduced(choice_axiom,[])).
% 4.18/0.92  fof(f30,plain,(
% 4.18/0.92    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 4.18/0.92    inference(ennf_transformation,[],[f7])).
% 4.18/0.92  fof(f7,axiom,(
% 4.18/0.92    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 4.18/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 4.18/0.92  fof(f207,plain,(
% 4.18/0.92    ( ! [X0,X1] : (~r2_hidden(sK7(X0,k3_tarski(X1)),X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1))) )),
% 4.18/0.92    inference(resolution,[],[f91,f89])).
% 4.18/0.92  fof(f89,plain,(
% 4.18/0.92    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 4.18/0.92    inference(cnf_transformation,[],[f29])).
% 4.18/0.92  fof(f29,plain,(
% 4.18/0.92    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 4.18/0.92    inference(ennf_transformation,[],[f5])).
% 4.18/0.92  fof(f5,axiom,(
% 4.18/0.92    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 4.18/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 4.18/0.92  fof(f91,plain,(
% 4.18/0.92    ( ! [X0,X1] : (~r1_tarski(sK7(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1)) )),
% 4.18/0.92    inference(cnf_transformation,[],[f50])).
% 4.18/0.92  fof(f215,plain,(
% 4.18/0.92    r2_hidden(sK4,sK4) | ~spl11_6),
% 4.18/0.92    inference(avatar_component_clause,[],[f214])).
% 4.18/0.92  fof(f214,plain,(
% 4.18/0.92    spl11_6 <=> r2_hidden(sK4,sK4)),
% 4.18/0.92    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 4.18/0.92  fof(f3638,plain,(
% 4.18/0.92    ~spl11_1 | ~spl11_32),
% 4.18/0.92    inference(avatar_contradiction_clause,[],[f3637])).
% 4.18/0.92  fof(f3637,plain,(
% 4.18/0.92    $false | (~spl11_1 | ~spl11_32)),
% 4.18/0.92    inference(subsumption_resolution,[],[f3636,f121])).
% 4.18/0.92  fof(f121,plain,(
% 4.18/0.92    v4_ordinal1(sK4) | ~spl11_1),
% 4.18/0.92    inference(avatar_component_clause,[],[f120])).
% 4.18/0.92  fof(f120,plain,(
% 4.18/0.92    spl11_1 <=> v4_ordinal1(sK4)),
% 4.18/0.92    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 4.18/0.92  fof(f3636,plain,(
% 4.18/0.92    ~v4_ordinal1(sK4) | ~spl11_32),
% 4.18/0.92    inference(subsumption_resolution,[],[f3625,f1181])).
% 4.18/0.92  fof(f3625,plain,(
% 4.18/0.92    r2_hidden(sK4,sK4) | ~v4_ordinal1(sK4) | ~spl11_32),
% 4.18/0.92    inference(superposition,[],[f2966,f82])).
% 4.18/0.92  fof(f82,plain,(
% 4.18/0.92    ( ! [X0] : (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)) )),
% 4.18/0.92    inference(cnf_transformation,[],[f44])).
% 4.18/0.92  fof(f44,plain,(
% 4.18/0.92    ! [X0] : ((v4_ordinal1(X0) | k3_tarski(X0) != X0) & (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)))),
% 4.18/0.92    inference(nnf_transformation,[],[f12])).
% 4.18/0.92  fof(f12,axiom,(
% 4.18/0.92    ! [X0] : (v4_ordinal1(X0) <=> k3_tarski(X0) = X0)),
% 4.18/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_ordinal1)).
% 4.18/0.92  fof(f2966,plain,(
% 4.18/0.92    r2_hidden(k3_tarski(sK4),sK4) | ~spl11_32),
% 4.18/0.92    inference(avatar_component_clause,[],[f2965])).
% 4.18/0.92  fof(f2965,plain,(
% 4.18/0.92    spl11_32 <=> r2_hidden(k3_tarski(sK4),sK4)),
% 4.18/0.92    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).
% 4.18/0.92  fof(f3617,plain,(
% 4.18/0.92    spl11_46 | spl11_2 | ~spl11_44 | spl11_45),
% 4.18/0.92    inference(avatar_split_clause,[],[f3401,f3294,f3290,f124,f3298])).
% 4.18/0.92  fof(f3298,plain,(
% 4.18/0.92    spl11_46 <=> sK4 = k2_xboole_0(sK5,k2_tarski(sK5,sK5))),
% 4.18/0.92    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).
% 4.18/0.92  fof(f124,plain,(
% 4.18/0.92    spl11_2 <=> r2_hidden(k2_xboole_0(sK5,k2_tarski(sK5,sK5)),sK4)),
% 4.18/0.92    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 4.18/0.92  fof(f3290,plain,(
% 4.18/0.92    spl11_44 <=> v3_ordinal1(k2_xboole_0(sK5,k2_tarski(sK5,sK5)))),
% 4.18/0.92    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).
% 4.18/0.92  fof(f3294,plain,(
% 4.18/0.92    spl11_45 <=> r2_hidden(sK4,k2_xboole_0(sK5,k2_tarski(sK5,sK5)))),
% 4.18/0.92    introduced(avatar_definition,[new_symbols(naming,[spl11_45])])).
% 4.18/0.92  fof(f3401,plain,(
% 4.18/0.92    sK4 = k2_xboole_0(sK5,k2_tarski(sK5,sK5)) | (spl11_2 | ~spl11_44 | spl11_45)),
% 4.18/0.92    inference(subsumption_resolution,[],[f3400,f3291])).
% 4.18/0.92  fof(f3291,plain,(
% 4.18/0.92    v3_ordinal1(k2_xboole_0(sK5,k2_tarski(sK5,sK5))) | ~spl11_44),
% 4.18/0.92    inference(avatar_component_clause,[],[f3290])).
% 4.18/0.92  fof(f3400,plain,(
% 4.18/0.92    sK4 = k2_xboole_0(sK5,k2_tarski(sK5,sK5)) | ~v3_ordinal1(k2_xboole_0(sK5,k2_tarski(sK5,sK5))) | (spl11_2 | spl11_45)),
% 4.18/0.92    inference(subsumption_resolution,[],[f3399,f68])).
% 4.18/0.92  fof(f68,plain,(
% 4.18/0.92    v3_ordinal1(sK4)),
% 4.18/0.92    inference(cnf_transformation,[],[f43])).
% 4.18/0.92  fof(f43,plain,(
% 4.18/0.92    ((~r2_hidden(k1_ordinal1(sK5),sK4) & r2_hidden(sK5,sK4) & v3_ordinal1(sK5)) | ~v4_ordinal1(sK4)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK4) | ~r2_hidden(X2,sK4) | ~v3_ordinal1(X2)) | v4_ordinal1(sK4)) & v3_ordinal1(sK4)),
% 4.18/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f42,f41])).
% 4.18/0.92  fof(f41,plain,(
% 4.18/0.92    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0)) => ((? [X1] : (~r2_hidden(k1_ordinal1(X1),sK4) & r2_hidden(X1,sK4) & v3_ordinal1(X1)) | ~v4_ordinal1(sK4)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK4) | ~r2_hidden(X2,sK4) | ~v3_ordinal1(X2)) | v4_ordinal1(sK4)) & v3_ordinal1(sK4))),
% 4.18/0.92    introduced(choice_axiom,[])).
% 4.18/0.92  fof(f42,plain,(
% 4.18/0.92    ? [X1] : (~r2_hidden(k1_ordinal1(X1),sK4) & r2_hidden(X1,sK4) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK5),sK4) & r2_hidden(sK5,sK4) & v3_ordinal1(sK5))),
% 4.18/0.92    introduced(choice_axiom,[])).
% 4.18/0.92  fof(f40,plain,(
% 4.18/0.92    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 4.18/0.92    inference(rectify,[],[f39])).
% 4.18/0.92  fof(f39,plain,(
% 4.18/0.92    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 4.18/0.92    inference(flattening,[],[f38])).
% 4.18/0.92  fof(f38,plain,(
% 4.18/0.92    ? [X0] : (((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 4.18/0.92    inference(nnf_transformation,[],[f21])).
% 4.18/0.92  fof(f21,plain,(
% 4.18/0.92    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 4.18/0.92    inference(flattening,[],[f20])).
% 4.18/0.92  fof(f20,plain,(
% 4.18/0.92    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 4.18/0.92    inference(ennf_transformation,[],[f19])).
% 4.18/0.92  fof(f19,negated_conjecture,(
% 4.18/0.92    ~! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 4.18/0.92    inference(negated_conjecture,[],[f18])).
% 4.18/0.92  fof(f18,conjecture,(
% 4.18/0.92    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 4.18/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).
% 4.18/0.92  fof(f3399,plain,(
% 4.18/0.92    sK4 = k2_xboole_0(sK5,k2_tarski(sK5,sK5)) | ~v3_ordinal1(sK4) | ~v3_ordinal1(k2_xboole_0(sK5,k2_tarski(sK5,sK5))) | (spl11_2 | spl11_45)),
% 4.18/0.92    inference(subsumption_resolution,[],[f3395,f126])).
% 4.18/0.92  fof(f126,plain,(
% 4.18/0.92    ~r2_hidden(k2_xboole_0(sK5,k2_tarski(sK5,sK5)),sK4) | spl11_2),
% 4.18/0.92    inference(avatar_component_clause,[],[f124])).
% 4.18/0.92  fof(f3395,plain,(
% 4.18/0.92    sK4 = k2_xboole_0(sK5,k2_tarski(sK5,sK5)) | r2_hidden(k2_xboole_0(sK5,k2_tarski(sK5,sK5)),sK4) | ~v3_ordinal1(sK4) | ~v3_ordinal1(k2_xboole_0(sK5,k2_tarski(sK5,sK5))) | spl11_45),
% 4.18/0.92    inference(resolution,[],[f3295,f81])).
% 4.18/0.92  fof(f81,plain,(
% 4.18/0.92    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 4.18/0.92    inference(cnf_transformation,[],[f26])).
% 4.18/0.92  fof(f26,plain,(
% 4.18/0.92    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 4.18/0.92    inference(flattening,[],[f25])).
% 4.18/0.92  fof(f25,plain,(
% 4.18/0.92    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 4.18/0.92    inference(ennf_transformation,[],[f14])).
% 4.18/0.92  fof(f14,axiom,(
% 4.18/0.92    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 4.18/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 4.18/0.92  fof(f3295,plain,(
% 4.18/0.92    ~r2_hidden(sK4,k2_xboole_0(sK5,k2_tarski(sK5,sK5))) | spl11_45),
% 4.18/0.92    inference(avatar_component_clause,[],[f3294])).
% 4.18/0.92  fof(f3613,plain,(
% 4.18/0.92    ~spl11_33 | spl11_32 | spl11_35 | spl11_34),
% 4.18/0.92    inference(avatar_split_clause,[],[f3612,f2978,f2982,f2965,f2969])).
% 4.18/0.92  fof(f2969,plain,(
% 4.18/0.92    spl11_33 <=> v3_ordinal1(k3_tarski(sK4))),
% 4.18/0.92    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).
% 4.18/0.92  fof(f2982,plain,(
% 4.18/0.92    spl11_35 <=> sK4 = k3_tarski(sK4)),
% 4.18/0.92    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).
% 4.18/0.92  fof(f2978,plain,(
% 4.18/0.92    spl11_34 <=> r2_hidden(sK4,k3_tarski(sK4))),
% 4.18/0.92    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).
% 4.18/0.92  fof(f3612,plain,(
% 4.18/0.92    sK4 = k3_tarski(sK4) | r2_hidden(k3_tarski(sK4),sK4) | ~v3_ordinal1(k3_tarski(sK4)) | spl11_34),
% 4.18/0.92    inference(subsumption_resolution,[],[f3185,f68])).
% 4.18/0.92  fof(f3185,plain,(
% 4.18/0.92    sK4 = k3_tarski(sK4) | r2_hidden(k3_tarski(sK4),sK4) | ~v3_ordinal1(sK4) | ~v3_ordinal1(k3_tarski(sK4)) | spl11_34),
% 4.18/0.92    inference(resolution,[],[f2979,f81])).
% 4.18/0.92  fof(f2979,plain,(
% 4.18/0.92    ~r2_hidden(sK4,k3_tarski(sK4)) | spl11_34),
% 4.18/0.92    inference(avatar_component_clause,[],[f2978])).
% 4.18/0.92  fof(f3611,plain,(
% 4.18/0.92    ~spl11_3 | ~spl11_50),
% 4.18/0.92    inference(avatar_contradiction_clause,[],[f3610])).
% 4.18/0.92  fof(f3610,plain,(
% 4.18/0.92    $false | (~spl11_3 | ~spl11_50)),
% 4.18/0.92    inference(subsumption_resolution,[],[f3605,f131])).
% 4.18/0.92  fof(f131,plain,(
% 4.18/0.92    r2_hidden(sK5,sK4) | ~spl11_3),
% 4.18/0.92    inference(avatar_component_clause,[],[f129])).
% 4.18/0.92  fof(f129,plain,(
% 4.18/0.92    spl11_3 <=> r2_hidden(sK5,sK4)),
% 4.18/0.92    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 4.18/0.92  fof(f3605,plain,(
% 4.18/0.92    ~r2_hidden(sK5,sK4) | ~spl11_50),
% 4.18/0.92    inference(resolution,[],[f3323,f169])).
% 4.18/0.92  fof(f169,plain,(
% 4.18/0.92    ( ! [X6,X5] : (~r2_hidden(X6,k2_tarski(X5,X5)) | ~r2_hidden(X5,X6)) )),
% 4.18/0.92    inference(superposition,[],[f152,f115])).
% 4.18/0.92  fof(f152,plain,(
% 4.18/0.92    ( ! [X2,X1] : (~r2_hidden(k3_tarski(X2),X1) | ~r2_hidden(X1,X2)) )),
% 4.18/0.92    inference(resolution,[],[f89,f101])).
% 4.18/0.92  fof(f3323,plain,(
% 4.18/0.92    r2_hidden(sK4,k2_tarski(sK5,sK5)) | ~spl11_50),
% 4.18/0.92    inference(avatar_component_clause,[],[f3321])).
% 4.18/0.92  fof(f3321,plain,(
% 4.18/0.92    spl11_50 <=> r2_hidden(sK4,k2_tarski(sK5,sK5))),
% 4.18/0.92    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).
% 4.18/0.92  fof(f3510,plain,(
% 4.18/0.92    ~spl11_42 | ~spl11_3 | ~spl11_43),
% 4.18/0.92    inference(avatar_split_clause,[],[f3509,f3259,f129,f3255])).
% 4.18/0.92  fof(f3255,plain,(
% 4.18/0.92    spl11_42 <=> r2_hidden(sK4,sK5)),
% 4.18/0.92    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).
% 4.18/0.92  fof(f3259,plain,(
% 4.18/0.92    spl11_43 <=> v1_ordinal1(sK5)),
% 4.18/0.92    introduced(avatar_definition,[new_symbols(naming,[spl11_43])])).
% 4.18/0.92  fof(f3509,plain,(
% 4.18/0.92    ~r2_hidden(sK4,sK5) | (~spl11_3 | ~spl11_43)),
% 4.18/0.92    inference(subsumption_resolution,[],[f3506,f3260])).
% 4.18/0.92  fof(f3260,plain,(
% 4.18/0.92    v1_ordinal1(sK5) | ~spl11_43),
% 4.18/0.92    inference(avatar_component_clause,[],[f3259])).
% 4.18/0.92  fof(f3506,plain,(
% 4.18/0.92    ~v1_ordinal1(sK5) | ~r2_hidden(sK4,sK5) | ~spl11_3),
% 4.18/0.92    inference(resolution,[],[f131,f165])).
% 4.18/0.92  fof(f165,plain,(
% 4.18/0.92    ( ! [X2,X1] : (~r2_hidden(X2,X1) | ~v1_ordinal1(X2) | ~r2_hidden(X1,X2)) )),
% 4.18/0.92    inference(resolution,[],[f84,f101])).
% 4.18/0.92  fof(f84,plain,(
% 4.18/0.92    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0) | ~v1_ordinal1(X0)) )),
% 4.18/0.92    inference(cnf_transformation,[],[f48])).
% 4.18/0.92  fof(f48,plain,(
% 4.18/0.92    ! [X0] : ((v1_ordinal1(X0) | (~r1_tarski(sK6(X0),X0) & r2_hidden(sK6(X0),X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 4.18/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f46,f47])).
% 4.18/0.92  fof(f47,plain,(
% 4.18/0.92    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK6(X0),X0) & r2_hidden(sK6(X0),X0)))),
% 4.18/0.92    introduced(choice_axiom,[])).
% 4.18/0.92  fof(f46,plain,(
% 4.18/0.92    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 4.18/0.92    inference(rectify,[],[f45])).
% 4.18/0.92  fof(f45,plain,(
% 4.18/0.92    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0)))),
% 4.18/0.92    inference(nnf_transformation,[],[f27])).
% 4.18/0.92  fof(f27,plain,(
% 4.18/0.92    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 4.18/0.92    inference(ennf_transformation,[],[f11])).
% 4.18/0.92  fof(f11,axiom,(
% 4.18/0.92    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 4.18/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).
% 4.18/0.92  fof(f3504,plain,(
% 4.18/0.92    spl11_50 | spl11_42 | ~spl11_45),
% 4.18/0.92    inference(avatar_split_clause,[],[f3379,f3294,f3255,f3321])).
% 4.18/0.92  fof(f3379,plain,(
% 4.18/0.92    r2_hidden(sK4,k2_tarski(sK5,sK5)) | (spl11_42 | ~spl11_45)),
% 4.18/0.92    inference(subsumption_resolution,[],[f3377,f3257])).
% 4.18/0.92  fof(f3257,plain,(
% 4.18/0.92    ~r2_hidden(sK4,sK5) | spl11_42),
% 4.18/0.92    inference(avatar_component_clause,[],[f3255])).
% 4.18/0.92  fof(f3377,plain,(
% 4.18/0.92    r2_hidden(sK4,sK5) | r2_hidden(sK4,k2_tarski(sK5,sK5)) | ~spl11_45),
% 4.18/0.92    inference(resolution,[],[f3371,f106])).
% 4.18/0.92  fof(f106,plain,(
% 4.18/0.92    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | r2_hidden(X1,X2) | r2_hidden(X1,X0)) )),
% 4.18/0.92    inference(cnf_transformation,[],[f66])).
% 4.18/0.92  fof(f66,plain,(
% 4.18/0.92    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | (~r2_hidden(X1,X0) & ~r2_hidden(X1,X2))) & (r2_hidden(X1,X0) | r2_hidden(X1,X2) | ~sP2(X0,X1,X2)))),
% 4.18/0.92    inference(rectify,[],[f65])).
% 4.18/0.92  fof(f65,plain,(
% 4.18/0.92    ! [X1,X3,X0] : ((sP2(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~sP2(X1,X3,X0)))),
% 4.18/0.92    inference(flattening,[],[f64])).
% 4.18/0.92  fof(f64,plain,(
% 4.18/0.92    ! [X1,X3,X0] : ((sP2(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~sP2(X1,X3,X0)))),
% 4.18/0.92    inference(nnf_transformation,[],[f35])).
% 4.18/0.92  fof(f35,plain,(
% 4.18/0.92    ! [X1,X3,X0] : (sP2(X1,X3,X0) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0)))),
% 4.18/0.92    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 4.18/0.92  fof(f3371,plain,(
% 4.18/0.92    sP2(k2_tarski(sK5,sK5),sK4,sK5) | ~spl11_45),
% 4.18/0.92    inference(resolution,[],[f3296,f365])).
% 4.18/0.92  fof(f365,plain,(
% 4.18/0.92    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,X2)) | sP2(X2,X0,X1)) )),
% 4.18/0.92    inference(resolution,[],[f102,f118])).
% 4.18/0.92  fof(f118,plain,(
% 4.18/0.92    ( ! [X0,X1] : (sP3(X0,X1,k2_xboole_0(X0,X1))) )),
% 4.18/0.92    inference(equality_resolution,[],[f109])).
% 4.18/0.92  fof(f109,plain,(
% 4.18/0.92    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | k2_xboole_0(X0,X1) != X2) )),
% 4.18/0.92    inference(cnf_transformation,[],[f67])).
% 4.18/0.92  fof(f67,plain,(
% 4.18/0.92    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP3(X0,X1,X2)) & (sP3(X0,X1,X2) | k2_xboole_0(X0,X1) != X2))),
% 4.18/0.92    inference(nnf_transformation,[],[f37])).
% 4.18/0.92  fof(f37,plain,(
% 4.18/0.92    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP3(X0,X1,X2))),
% 4.18/0.92    inference(definition_folding,[],[f1,f36,f35])).
% 4.18/0.92  fof(f36,plain,(
% 4.18/0.92    ! [X0,X1,X2] : (sP3(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP2(X1,X3,X0)))),
% 4.18/0.92    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 4.18/0.92  fof(f1,axiom,(
% 4.18/0.92    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 4.18/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 4.18/0.92  fof(f102,plain,(
% 4.18/0.92    ( ! [X4,X2,X0,X1] : (~sP3(X0,X1,X2) | ~r2_hidden(X4,X2) | sP2(X1,X4,X0)) )),
% 4.18/0.92    inference(cnf_transformation,[],[f63])).
% 4.18/0.92  fof(f63,plain,(
% 4.18/0.92    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ((~sP2(X1,sK10(X0,X1,X2),X0) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sP2(X1,sK10(X0,X1,X2),X0) | r2_hidden(sK10(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP2(X1,X4,X0)) & (sP2(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP3(X0,X1,X2)))),
% 4.18/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f61,f62])).
% 4.18/0.92  fof(f62,plain,(
% 4.18/0.92    ! [X2,X1,X0] : (? [X3] : ((~sP2(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP2(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP2(X1,sK10(X0,X1,X2),X0) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sP2(X1,sK10(X0,X1,X2),X0) | r2_hidden(sK10(X0,X1,X2),X2))))),
% 4.18/0.92    introduced(choice_axiom,[])).
% 4.18/0.92  fof(f61,plain,(
% 4.18/0.92    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : ((~sP2(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP2(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP2(X1,X4,X0)) & (sP2(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP3(X0,X1,X2)))),
% 4.18/0.92    inference(rectify,[],[f60])).
% 4.18/0.92  % (32527)Time limit reached!
% 4.18/0.92  % (32527)------------------------------
% 4.18/0.92  % (32527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.18/0.92  % (32527)Termination reason: Time limit
% 4.18/0.92  
% 4.18/0.92  % (32527)Memory used [KB]: 9338
% 4.18/0.92  % (32527)Time elapsed: 0.509 s
% 4.18/0.92  % (32527)------------------------------
% 4.18/0.92  % (32527)------------------------------
% 4.18/0.92  fof(f60,plain,(
% 4.18/0.92    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : ((~sP2(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP2(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP2(X1,X3,X0)) & (sP2(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP3(X0,X1,X2)))),
% 4.18/0.92    inference(nnf_transformation,[],[f36])).
% 4.18/0.92  fof(f3296,plain,(
% 4.18/0.92    r2_hidden(sK4,k2_xboole_0(sK5,k2_tarski(sK5,sK5))) | ~spl11_45),
% 4.18/0.92    inference(avatar_component_clause,[],[f3294])).
% 4.18/0.92  fof(f3497,plain,(
% 4.18/0.92    ~spl11_3 | spl11_6 | ~spl11_56),
% 4.18/0.92    inference(avatar_contradiction_clause,[],[f3496])).
% 4.18/0.92  fof(f3496,plain,(
% 4.18/0.92    $false | (~spl11_3 | spl11_6 | ~spl11_56)),
% 4.18/0.92    inference(subsumption_resolution,[],[f3484,f216])).
% 4.18/0.92  fof(f216,plain,(
% 4.18/0.92    ~r2_hidden(sK4,sK4) | spl11_6),
% 4.18/0.92    inference(avatar_component_clause,[],[f214])).
% 4.18/0.92  fof(f3484,plain,(
% 4.18/0.92    r2_hidden(sK4,sK4) | (~spl11_3 | ~spl11_56)),
% 4.18/0.92    inference(backward_demodulation,[],[f131,f3468])).
% 4.18/0.92  fof(f3468,plain,(
% 4.18/0.92    sK4 = sK5 | ~spl11_56),
% 4.18/0.92    inference(avatar_component_clause,[],[f3466])).
% 4.18/0.92  fof(f3466,plain,(
% 4.18/0.92    spl11_56 <=> sK4 = sK5),
% 4.18/0.92    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).
% 4.18/0.92  fof(f3482,plain,(
% 4.18/0.92    ~spl11_43 | spl11_57),
% 4.18/0.92    inference(avatar_contradiction_clause,[],[f3481])).
% 4.18/0.92  fof(f3481,plain,(
% 4.18/0.92    $false | (~spl11_43 | spl11_57)),
% 4.18/0.92    inference(subsumption_resolution,[],[f3476,f3260])).
% 4.18/0.92  fof(f3476,plain,(
% 4.18/0.92    ~v1_ordinal1(sK5) | spl11_57),
% 4.18/0.92    inference(resolution,[],[f3472,f995])).
% 4.18/0.92  fof(f995,plain,(
% 4.18/0.92    ( ! [X0] : (r1_tarski(k3_tarski(X0),X0) | ~v1_ordinal1(X0)) )),
% 4.18/0.92    inference(duplicate_literal_removal,[],[f991])).
% 4.18/0.92  fof(f991,plain,(
% 4.18/0.92    ( ! [X0] : (r1_tarski(k3_tarski(X0),X0) | ~v1_ordinal1(X0) | r1_tarski(k3_tarski(X0),X0)) )),
% 4.18/0.92    inference(resolution,[],[f209,f90])).
% 4.18/0.92  fof(f209,plain,(
% 4.18/0.92    ( ! [X4,X5] : (~r2_hidden(sK7(X4,X5),X5) | r1_tarski(k3_tarski(X4),X5) | ~v1_ordinal1(X5)) )),
% 4.18/0.92    inference(resolution,[],[f91,f84])).
% 4.18/0.92  fof(f3472,plain,(
% 4.18/0.92    ~r1_tarski(k3_tarski(sK5),sK5) | spl11_57),
% 4.18/0.92    inference(avatar_component_clause,[],[f3470])).
% 4.18/0.92  fof(f3470,plain,(
% 4.18/0.92    spl11_57 <=> r1_tarski(k3_tarski(sK5),sK5)),
% 4.18/0.92    introduced(avatar_definition,[new_symbols(naming,[spl11_57])])).
% 4.18/0.92  fof(f3473,plain,(
% 4.18/0.92    spl11_56 | ~spl11_57 | ~spl11_35 | ~spl11_46),
% 4.18/0.92    inference(avatar_split_clause,[],[f3464,f3298,f2982,f3470,f3466])).
% 4.18/0.92  fof(f3464,plain,(
% 4.18/0.92    ~r1_tarski(k3_tarski(sK5),sK5) | sK4 = sK5 | (~spl11_35 | ~spl11_46)),
% 4.18/0.92    inference(forward_demodulation,[],[f3463,f115])).
% 4.18/0.92  fof(f3463,plain,(
% 4.18/0.92    sK4 = sK5 | ~r1_tarski(k3_tarski(sK5),k3_tarski(k2_tarski(sK5,sK5))) | (~spl11_35 | ~spl11_46)),
% 4.18/0.92    inference(forward_demodulation,[],[f3462,f2984])).
% 4.18/0.92  fof(f2984,plain,(
% 4.18/0.92    sK4 = k3_tarski(sK4) | ~spl11_35),
% 4.18/0.92    inference(avatar_component_clause,[],[f2982])).
% 4.18/0.92  fof(f3462,plain,(
% 4.18/0.92    sK5 = k3_tarski(sK4) | ~r1_tarski(k3_tarski(sK5),k3_tarski(k2_tarski(sK5,sK5))) | ~spl11_46),
% 4.18/0.92    inference(forward_demodulation,[],[f3443,f115])).
% 4.18/0.92  fof(f3443,plain,(
% 4.18/0.92    k3_tarski(sK4) = k3_tarski(k2_tarski(sK5,sK5)) | ~r1_tarski(k3_tarski(sK5),k3_tarski(k2_tarski(sK5,sK5))) | ~spl11_46),
% 4.18/0.92    inference(superposition,[],[f331,f3300])).
% 4.18/0.92  fof(f3300,plain,(
% 4.18/0.92    sK4 = k2_xboole_0(sK5,k2_tarski(sK5,sK5)) | ~spl11_46),
% 4.18/0.92    inference(avatar_component_clause,[],[f3298])).
% 4.18/0.92  fof(f331,plain,(
% 4.18/0.92    ( ! [X6,X5] : (k3_tarski(X6) = k3_tarski(k2_xboole_0(X5,X6)) | ~r1_tarski(k3_tarski(X5),k3_tarski(X6))) )),
% 4.18/0.92    inference(superposition,[],[f87,f88])).
% 4.18/0.92  fof(f88,plain,(
% 4.18/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 4.18/0.92    inference(cnf_transformation,[],[f28])).
% 4.18/0.92  fof(f28,plain,(
% 4.18/0.92    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.18/0.92    inference(ennf_transformation,[],[f2])).
% 4.18/0.92  fof(f2,axiom,(
% 4.18/0.92    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.18/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 4.18/0.92  fof(f87,plain,(
% 4.18/0.92    ( ! [X0,X1] : (k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))) )),
% 4.18/0.92    inference(cnf_transformation,[],[f8])).
% 4.18/0.92  fof(f8,axiom,(
% 4.18/0.92    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))),
% 4.18/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).
% 4.18/0.92  fof(f3385,plain,(
% 4.18/0.92    ~spl11_4 | spl11_43),
% 4.18/0.92    inference(avatar_contradiction_clause,[],[f3384])).
% 4.18/0.92  fof(f3384,plain,(
% 4.18/0.92    $false | (~spl11_4 | spl11_43)),
% 4.18/0.92    inference(subsumption_resolution,[],[f3383,f136])).
% 4.18/0.92  fof(f136,plain,(
% 4.18/0.92    v3_ordinal1(sK5) | ~spl11_4),
% 4.18/0.92    inference(avatar_component_clause,[],[f134])).
% 4.18/0.92  fof(f134,plain,(
% 4.18/0.92    spl11_4 <=> v3_ordinal1(sK5)),
% 4.18/0.92    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 4.18/0.92  fof(f3383,plain,(
% 4.18/0.92    ~v3_ordinal1(sK5) | spl11_43),
% 4.18/0.92    inference(resolution,[],[f3261,f79])).
% 4.18/0.92  fof(f79,plain,(
% 4.18/0.92    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 4.18/0.92    inference(cnf_transformation,[],[f24])).
% 4.18/0.92  fof(f24,plain,(
% 4.18/0.92    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 4.18/0.92    inference(ennf_transformation,[],[f9])).
% 4.18/0.92  fof(f9,axiom,(
% 4.18/0.92    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 4.18/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).
% 4.18/0.92  fof(f3261,plain,(
% 4.18/0.92    ~v1_ordinal1(sK5) | spl11_43),
% 4.18/0.92    inference(avatar_component_clause,[],[f3259])).
% 4.18/0.92  fof(f3349,plain,(
% 4.18/0.92    ~spl11_4 | spl11_44),
% 4.18/0.92    inference(avatar_contradiction_clause,[],[f3348])).
% 4.18/0.92  fof(f3348,plain,(
% 4.18/0.92    $false | (~spl11_4 | spl11_44)),
% 4.18/0.92    inference(subsumption_resolution,[],[f3344,f136])).
% 4.18/0.92  fof(f3344,plain,(
% 4.18/0.92    ~v3_ordinal1(sK5) | spl11_44),
% 4.18/0.92    inference(resolution,[],[f3292,f116])).
% 4.18/0.92  fof(f116,plain,(
% 4.18/0.92    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) | ~v3_ordinal1(X0)) )),
% 4.18/0.92    inference(definition_unfolding,[],[f77,f111])).
% 4.18/0.92  fof(f111,plain,(
% 4.18/0.92    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0))) )),
% 4.18/0.92    inference(definition_unfolding,[],[f76,f75])).
% 4.18/0.92  fof(f76,plain,(
% 4.18/0.92    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 4.18/0.92    inference(cnf_transformation,[],[f10])).
% 4.18/0.92  fof(f10,axiom,(
% 4.18/0.92    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 4.18/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 4.18/0.92  fof(f77,plain,(
% 4.18/0.92    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 4.18/0.92    inference(cnf_transformation,[],[f22])).
% 4.18/0.92  fof(f22,plain,(
% 4.18/0.92    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 4.18/0.92    inference(ennf_transformation,[],[f15])).
% 4.18/0.92  fof(f15,axiom,(
% 4.18/0.92    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 4.18/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 4.18/0.92  fof(f3292,plain,(
% 4.18/0.92    ~v3_ordinal1(k2_xboole_0(sK5,k2_tarski(sK5,sK5))) | spl11_44),
% 4.18/0.92    inference(avatar_component_clause,[],[f3290])).
% 4.18/0.92  fof(f3243,plain,(
% 4.18/0.92    spl11_1 | ~spl11_35),
% 4.18/0.92    inference(avatar_split_clause,[],[f3230,f2982,f120])).
% 4.18/0.92  fof(f3230,plain,(
% 4.18/0.92    v4_ordinal1(sK4) | ~spl11_35),
% 4.18/0.92    inference(trivial_inequality_removal,[],[f3197])).
% 4.18/0.92  fof(f3197,plain,(
% 4.18/0.92    sK4 != sK4 | v4_ordinal1(sK4) | ~spl11_35),
% 4.18/0.92    inference(superposition,[],[f83,f2984])).
% 4.18/0.92  fof(f83,plain,(
% 4.18/0.92    ( ! [X0] : (k3_tarski(X0) != X0 | v4_ordinal1(X0)) )),
% 4.18/0.92    inference(cnf_transformation,[],[f44])).
% 4.18/0.92  fof(f3178,plain,(
% 4.18/0.92    ~spl11_15),
% 4.18/0.92    inference(avatar_contradiction_clause,[],[f3177])).
% 4.18/0.92  fof(f3177,plain,(
% 4.18/0.92    $false | ~spl11_15),
% 4.18/0.92    inference(subsumption_resolution,[],[f3176,f68])).
% 4.18/0.92  fof(f3176,plain,(
% 4.18/0.92    ~v3_ordinal1(sK4) | ~spl11_15),
% 4.18/0.92    inference(resolution,[],[f3175,f79])).
% 4.18/0.92  fof(f3175,plain,(
% 4.18/0.92    ~v1_ordinal1(sK4) | ~spl11_15),
% 4.18/0.92    inference(resolution,[],[f3171,f937])).
% 4.18/0.92  fof(f937,plain,(
% 4.18/0.92    sP0(sK4,sK4) | ~spl11_15),
% 4.18/0.92    inference(avatar_component_clause,[],[f936])).
% 4.18/0.92  fof(f936,plain,(
% 4.18/0.92    spl11_15 <=> sP0(sK4,sK4)),
% 4.18/0.92    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).
% 4.18/0.92  fof(f3171,plain,(
% 4.18/0.92    ( ! [X0] : (~sP0(X0,X0) | ~v1_ordinal1(X0)) )),
% 4.18/0.92    inference(duplicate_literal_removal,[],[f3167])).
% 4.18/0.92  fof(f3167,plain,(
% 4.18/0.92    ( ! [X0] : (~v1_ordinal1(X0) | ~sP0(X0,X0) | ~sP0(X0,X0)) )),
% 4.18/0.92    inference(resolution,[],[f202,f97])).
% 4.18/0.92  fof(f97,plain,(
% 4.18/0.92    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X0) | ~sP0(X0,X1)) )),
% 4.18/0.92    inference(cnf_transformation,[],[f58])).
% 4.18/0.92  fof(f58,plain,(
% 4.18/0.92    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (~r2_hidden(X2,X0) | ~r2_hidden(X1,X2))) & ((r2_hidden(sK9(X0,X1),X0) & r2_hidden(X1,sK9(X0,X1))) | ~sP0(X0,X1)))),
% 4.18/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f56,f57])).
% 4.18/0.92  fof(f57,plain,(
% 4.18/0.92    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X1,X3)) => (r2_hidden(sK9(X0,X1),X0) & r2_hidden(X1,sK9(X0,X1))))),
% 4.18/0.92    introduced(choice_axiom,[])).
% 4.18/0.92  fof(f56,plain,(
% 4.18/0.92    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (~r2_hidden(X2,X0) | ~r2_hidden(X1,X2))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X1,X3)) | ~sP0(X0,X1)))),
% 4.18/0.92    inference(rectify,[],[f55])).
% 4.18/0.92  fof(f55,plain,(
% 4.18/0.92    ! [X0,X2] : ((sP0(X0,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~sP0(X0,X2)))),
% 4.18/0.92    inference(nnf_transformation,[],[f32])).
% 4.18/0.92  fof(f32,plain,(
% 4.18/0.92    ! [X0,X2] : (sP0(X0,X2) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)))),
% 4.18/0.92    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 4.18/0.92  fof(f202,plain,(
% 4.18/0.92    ( ! [X2,X1] : (~r2_hidden(sK9(X2,X1),X1) | ~v1_ordinal1(X1) | ~sP0(X2,X1)) )),
% 4.18/0.92    inference(resolution,[],[f165,f96])).
% 4.18/0.92  fof(f96,plain,(
% 4.18/0.92    ( ! [X0,X1] : (r2_hidden(X1,sK9(X0,X1)) | ~sP0(X0,X1)) )),
% 4.18/0.92    inference(cnf_transformation,[],[f58])).
% 4.18/0.92  fof(f3021,plain,(
% 4.18/0.92    spl11_15 | ~spl11_34),
% 4.18/0.92    inference(avatar_split_clause,[],[f3007,f2978,f936])).
% 4.18/0.92  fof(f3007,plain,(
% 4.18/0.92    sP0(sK4,sK4) | ~spl11_34),
% 4.18/0.92    inference(resolution,[],[f2980,f238])).
% 4.18/0.92  fof(f238,plain,(
% 4.18/0.92    ( ! [X0,X1] : (~r2_hidden(X0,k3_tarski(X1)) | sP0(X1,X0)) )),
% 4.18/0.92    inference(resolution,[],[f92,f117])).
% 4.18/0.92  fof(f117,plain,(
% 4.18/0.92    ( ! [X0] : (sP1(X0,k3_tarski(X0))) )),
% 4.18/0.92    inference(equality_resolution,[],[f99])).
% 4.18/0.92  fof(f99,plain,(
% 4.18/0.92    ( ! [X0,X1] : (sP1(X0,X1) | k3_tarski(X0) != X1) )),
% 4.18/0.92    inference(cnf_transformation,[],[f59])).
% 4.18/0.92  fof(f59,plain,(
% 4.18/0.92    ! [X0,X1] : ((k3_tarski(X0) = X1 | ~sP1(X0,X1)) & (sP1(X0,X1) | k3_tarski(X0) != X1))),
% 4.18/0.92    inference(nnf_transformation,[],[f34])).
% 4.18/0.92  fof(f34,plain,(
% 4.18/0.92    ! [X0,X1] : (k3_tarski(X0) = X1 <=> sP1(X0,X1))),
% 4.18/0.92    inference(definition_folding,[],[f4,f33,f32])).
% 4.18/0.92  fof(f33,plain,(
% 4.18/0.92    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> sP0(X0,X2)))),
% 4.18/0.92    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 4.18/0.92  fof(f4,axiom,(
% 4.18/0.92    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 4.18/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 4.18/0.92  fof(f92,plain,(
% 4.18/0.92    ( ! [X0,X3,X1] : (~sP1(X0,X1) | ~r2_hidden(X3,X1) | sP0(X0,X3)) )),
% 4.18/0.92    inference(cnf_transformation,[],[f54])).
% 4.18/0.92  fof(f54,plain,(
% 4.18/0.92    ! [X0,X1] : ((sP1(X0,X1) | ((~sP0(X0,sK8(X0,X1)) | ~r2_hidden(sK8(X0,X1),X1)) & (sP0(X0,sK8(X0,X1)) | r2_hidden(sK8(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X0,X3)) & (sP0(X0,X3) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 4.18/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f52,f53])).
% 4.18/0.92  fof(f53,plain,(
% 4.18/0.92    ! [X1,X0] : (? [X2] : ((~sP0(X0,X2) | ~r2_hidden(X2,X1)) & (sP0(X0,X2) | r2_hidden(X2,X1))) => ((~sP0(X0,sK8(X0,X1)) | ~r2_hidden(sK8(X0,X1),X1)) & (sP0(X0,sK8(X0,X1)) | r2_hidden(sK8(X0,X1),X1))))),
% 4.18/0.92    introduced(choice_axiom,[])).
% 4.18/0.92  fof(f52,plain,(
% 4.18/0.92    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X0,X2) | ~r2_hidden(X2,X1)) & (sP0(X0,X2) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X0,X3)) & (sP0(X0,X3) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 4.18/0.92    inference(rectify,[],[f51])).
% 4.18/0.92  fof(f51,plain,(
% 4.18/0.92    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X0,X2) | ~r2_hidden(X2,X1)) & (sP0(X0,X2) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~sP0(X0,X2)) & (sP0(X0,X2) | ~r2_hidden(X2,X1))) | ~sP1(X0,X1)))),
% 4.18/0.92    inference(nnf_transformation,[],[f33])).
% 4.18/0.92  fof(f2980,plain,(
% 4.18/0.92    r2_hidden(sK4,k3_tarski(sK4)) | ~spl11_34),
% 4.18/0.92    inference(avatar_component_clause,[],[f2978])).
% 4.18/0.92  fof(f2990,plain,(
% 4.18/0.92    spl11_33),
% 4.18/0.92    inference(avatar_contradiction_clause,[],[f2989])).
% 4.18/0.92  fof(f2989,plain,(
% 4.18/0.92    $false | spl11_33),
% 4.18/0.92    inference(subsumption_resolution,[],[f2986,f68])).
% 4.18/0.92  fof(f2986,plain,(
% 4.18/0.92    ~v3_ordinal1(sK4) | spl11_33),
% 4.18/0.92    inference(resolution,[],[f2971,f78])).
% 4.18/0.92  fof(f78,plain,(
% 4.18/0.92    ( ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ~v3_ordinal1(X0)) )),
% 4.18/0.92    inference(cnf_transformation,[],[f23])).
% 4.18/0.92  fof(f23,plain,(
% 4.18/0.92    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ~v3_ordinal1(X0))),
% 4.18/0.92    inference(ennf_transformation,[],[f16])).
% 4.18/0.92  fof(f16,axiom,(
% 4.18/0.92    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k3_tarski(X0)))),
% 4.18/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_ordinal1)).
% 4.18/0.92  fof(f2971,plain,(
% 4.18/0.92    ~v3_ordinal1(k3_tarski(sK4)) | spl11_33),
% 4.18/0.92    inference(avatar_component_clause,[],[f2969])).
% 4.18/0.92  fof(f2972,plain,(
% 4.18/0.92    ~spl11_32 | ~spl11_33 | ~spl11_5),
% 4.18/0.92    inference(avatar_split_clause,[],[f2946,f139,f2969,f2965])).
% 4.18/0.92  fof(f139,plain,(
% 4.18/0.92    spl11_5 <=> ! [X2] : (r2_hidden(k2_xboole_0(X2,k2_tarski(X2,X2)),sK4) | ~v3_ordinal1(X2) | ~r2_hidden(X2,sK4))),
% 4.18/0.92    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 4.18/0.92  fof(f2946,plain,(
% 4.18/0.92    ~v3_ordinal1(k3_tarski(sK4)) | ~r2_hidden(k3_tarski(sK4),sK4) | ~spl11_5),
% 4.18/0.92    inference(resolution,[],[f166,f140])).
% 4.18/0.92  fof(f140,plain,(
% 4.18/0.92    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k2_tarski(X2,X2)),sK4) | ~v3_ordinal1(X2) | ~r2_hidden(X2,sK4)) ) | ~spl11_5),
% 4.18/0.92    inference(avatar_component_clause,[],[f139])).
% 4.18/0.92  fof(f166,plain,(
% 4.18/0.92    ( ! [X0] : (~r2_hidden(k2_xboole_0(k3_tarski(X0),k2_tarski(k3_tarski(X0),k3_tarski(X0))),X0)) )),
% 4.18/0.92    inference(resolution,[],[f152,f114])).
% 4.18/0.92  fof(f114,plain,(
% 4.18/0.92    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k2_tarski(X0,X0)))) )),
% 4.18/0.92    inference(definition_unfolding,[],[f73,f111])).
% 4.18/0.92  fof(f73,plain,(
% 4.18/0.92    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 4.18/0.92    inference(cnf_transformation,[],[f13])).
% 4.18/0.92  fof(f13,axiom,(
% 4.18/0.92    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 4.18/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 4.18/0.92  fof(f141,plain,(
% 4.18/0.92    spl11_1 | spl11_5),
% 4.18/0.92    inference(avatar_split_clause,[],[f113,f139,f120])).
% 4.18/0.92  fof(f113,plain,(
% 4.18/0.92    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k2_tarski(X2,X2)),sK4) | ~r2_hidden(X2,sK4) | ~v3_ordinal1(X2) | v4_ordinal1(sK4)) )),
% 4.18/0.92    inference(definition_unfolding,[],[f69,f111])).
% 4.18/0.92  fof(f69,plain,(
% 4.18/0.92    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK4) | ~r2_hidden(X2,sK4) | ~v3_ordinal1(X2) | v4_ordinal1(sK4)) )),
% 4.18/0.92    inference(cnf_transformation,[],[f43])).
% 4.18/0.92  fof(f137,plain,(
% 4.18/0.92    ~spl11_1 | spl11_4),
% 4.18/0.92    inference(avatar_split_clause,[],[f70,f134,f120])).
% 4.18/0.92  fof(f70,plain,(
% 4.18/0.92    v3_ordinal1(sK5) | ~v4_ordinal1(sK4)),
% 4.18/0.92    inference(cnf_transformation,[],[f43])).
% 4.18/0.92  fof(f132,plain,(
% 4.18/0.92    ~spl11_1 | spl11_3),
% 4.18/0.92    inference(avatar_split_clause,[],[f71,f129,f120])).
% 4.18/0.92  fof(f71,plain,(
% 4.18/0.92    r2_hidden(sK5,sK4) | ~v4_ordinal1(sK4)),
% 4.18/0.92    inference(cnf_transformation,[],[f43])).
% 4.18/0.92  fof(f127,plain,(
% 4.18/0.92    ~spl11_1 | ~spl11_2),
% 4.18/0.92    inference(avatar_split_clause,[],[f112,f124,f120])).
% 4.18/0.92  fof(f112,plain,(
% 4.18/0.92    ~r2_hidden(k2_xboole_0(sK5,k2_tarski(sK5,sK5)),sK4) | ~v4_ordinal1(sK4)),
% 4.18/0.92    inference(definition_unfolding,[],[f72,f111])).
% 4.18/0.92  fof(f72,plain,(
% 4.18/0.92    ~r2_hidden(k1_ordinal1(sK5),sK4) | ~v4_ordinal1(sK4)),
% 4.18/0.92    inference(cnf_transformation,[],[f43])).
% 4.18/0.92  % SZS output end Proof for theBenchmark
% 4.18/0.92  % (32553)------------------------------
% 4.18/0.92  % (32553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.18/0.92  % (32553)Termination reason: Refutation
% 4.18/0.92  
% 4.18/0.92  % (32553)Memory used [KB]: 8059
% 4.18/0.92  % (32553)Time elapsed: 0.478 s
% 4.18/0.92  % (32553)------------------------------
% 4.18/0.92  % (32553)------------------------------
% 4.18/0.92  % (32522)Success in time 0.559 s
%------------------------------------------------------------------------------
