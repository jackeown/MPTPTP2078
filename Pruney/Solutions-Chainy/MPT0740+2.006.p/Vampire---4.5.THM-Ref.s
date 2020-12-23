%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 233 expanded)
%              Number of leaves         :   26 (  89 expanded)
%              Depth                    :   13
%              Number of atoms          :  320 ( 707 expanded)
%              Number of equality atoms :   21 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f200,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f54,f75,f89,f98,f112,f113,f121,f137,f147,f154,f158,f165,f198,f199])).

fof(f199,plain,
    ( sK0 != k3_tarski(sK0)
    | v3_ordinal1(k3_tarski(sK0))
    | ~ v3_ordinal1(sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f198,plain,
    ( ~ spl3_5
    | spl3_17
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f184,f156,f152,f84])).

fof(f84,plain,
    ( spl3_5
  <=> r1_tarski(k3_tarski(k3_tarski(sK0)),k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f152,plain,
    ( spl3_17
  <=> r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f156,plain,
    ( spl3_18
  <=> r2_hidden(sK1(k3_tarski(sK0)),k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f184,plain,
    ( ~ r1_tarski(k3_tarski(k3_tarski(sK0)),k3_tarski(sK0))
    | spl3_17
    | ~ spl3_18 ),
    inference(resolution,[],[f174,f153])).

fof(f153,plain,
    ( ~ r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f152])).

fof(f174,plain,
    ( ! [X0] :
        ( r1_tarski(sK1(k3_tarski(sK0)),X0)
        | ~ r1_tarski(k3_tarski(k3_tarski(sK0)),X0) )
    | ~ spl3_18 ),
    inference(resolution,[],[f157,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r1_tarski(X2,X1)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

fof(f157,plain,
    ( r2_hidden(sK1(k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f156])).

fof(f165,plain,
    ( ~ spl3_2
    | spl3_1
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f161,f145,f48,f52])).

fof(f52,plain,
    ( spl3_2
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f48,plain,
    ( spl3_1
  <=> v3_ordinal1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f145,plain,
    ( spl3_16
  <=> r2_hidden(k3_tarski(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f161,plain,
    ( v3_ordinal1(k3_tarski(sK0))
    | ~ v3_ordinal1(sK0)
    | ~ spl3_16 ),
    inference(resolution,[],[f146,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f146,plain,
    ( r2_hidden(k3_tarski(sK0),sK0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f145])).

fof(f158,plain,
    ( spl3_18
    | spl3_15 ),
    inference(avatar_split_clause,[],[f149,f142,f156])).

fof(f142,plain,
    ( spl3_15
  <=> v1_ordinal1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f149,plain,
    ( r2_hidden(sK1(k3_tarski(sK0)),k3_tarski(sK0))
    | spl3_15 ),
    inference(resolution,[],[f143,f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK1(X0),X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK1(X0),X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f143,plain,
    ( ~ v1_ordinal1(k3_tarski(sK0))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f142])).

fof(f154,plain,
    ( ~ spl3_17
    | spl3_15 ),
    inference(avatar_split_clause,[],[f148,f142,f152])).

fof(f148,plain,
    ( ~ r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0))
    | spl3_15 ),
    inference(resolution,[],[f143,f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ r1_tarski(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f147,plain,
    ( ~ spl3_15
    | spl3_16
    | spl3_6
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f139,f110,f52,f87,f145,f142])).

fof(f87,plain,
    ( spl3_6
  <=> sK0 = k3_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f110,plain,
    ( spl3_10
  <=> r1_tarski(sK2(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f139,plain,
    ( sK0 = k3_tarski(sK0)
    | r2_hidden(k3_tarski(sK0),sK0)
    | ~ v1_ordinal1(k3_tarski(sK0))
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(resolution,[],[f120,f57])).

fof(f57,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2(X0,sK0),sK0)
        | k3_tarski(X0) = sK0
        | r2_hidden(k3_tarski(X0),sK0)
        | ~ v1_ordinal1(k3_tarski(X0)) )
    | ~ spl3_2 ),
    inference(resolution,[],[f56,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f56,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | ~ v1_ordinal1(X0)
        | sK0 = X0
        | r2_hidden(X0,sK0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f55,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f55,plain,
    ( ! [X0] :
        ( ~ r2_xboole_0(X0,sK0)
        | r2_hidden(X0,sK0)
        | ~ v1_ordinal1(X0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f36,f53])).

fof(f53,plain,
    ( v3_ordinal1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r2_xboole_0(X0,X1)
      | r2_hidden(X0,X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    ( r1_tarski(sK2(sK0,sK0),sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f137,plain,
    ( ~ spl3_2
    | spl3_11 ),
    inference(avatar_split_clause,[],[f128,f118,f52])).

fof(f118,plain,
    ( spl3_11
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f128,plain,
    ( ~ v3_ordinal1(sK0)
    | spl3_11 ),
    inference(resolution,[],[f119,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f119,plain,
    ( ~ v1_ordinal1(sK0)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f118])).

fof(f121,plain,
    ( ~ spl3_11
    | spl3_10
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f115,f81,f110,f118])).

fof(f81,plain,
    ( spl3_4
  <=> r2_hidden(sK2(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f115,plain,
    ( r1_tarski(sK2(sK0,sK0),sK0)
    | ~ v1_ordinal1(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f82,f38])).

fof(f38,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | r1_tarski(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f82,plain,
    ( r2_hidden(sK2(sK0,sK0),sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f113,plain,
    ( spl3_4
    | spl3_7 ),
    inference(avatar_split_clause,[],[f108,f96,f81])).

fof(f96,plain,
    ( spl3_7
  <=> r1_tarski(k3_tarski(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f108,plain,
    ( r2_hidden(sK2(sK0,sK0),sK0)
    | spl3_7 ),
    inference(resolution,[],[f97,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f97,plain,
    ( ~ r1_tarski(k3_tarski(sK0),sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f112,plain,
    ( ~ spl3_10
    | spl3_7 ),
    inference(avatar_split_clause,[],[f107,f96,f110])).

fof(f107,plain,
    ( ~ r1_tarski(sK2(sK0,sK0),sK0)
    | spl3_7 ),
    inference(resolution,[],[f97,f44])).

fof(f98,plain,
    ( ~ spl3_7
    | spl3_5 ),
    inference(avatar_split_clause,[],[f92,f84,f96])).

fof(f92,plain,
    ( ~ r1_tarski(k3_tarski(sK0),sK0)
    | spl3_5 ),
    inference(resolution,[],[f85,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f85,plain,
    ( ~ r1_tarski(k3_tarski(k3_tarski(sK0)),k3_tarski(sK0))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f89,plain,
    ( spl3_4
    | ~ spl3_5
    | spl3_6
    | spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f76,f73,f48,f87,f84,f81])).

fof(f73,plain,
    ( spl3_3
  <=> ! [X3] :
        ( sK0 = k3_tarski(X3)
        | v3_ordinal1(k3_tarski(X3))
        | ~ r1_tarski(k3_tarski(k3_tarski(X3)),k3_tarski(X3))
        | r2_hidden(sK2(X3,sK0),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f76,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ r1_tarski(k3_tarski(k3_tarski(sK0)),k3_tarski(sK0))
    | r2_hidden(sK2(sK0,sK0),sK0)
    | spl3_1
    | ~ spl3_3 ),
    inference(resolution,[],[f74,f49])).

fof(f49,plain,
    ( ~ v3_ordinal1(k3_tarski(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f74,plain,
    ( ! [X3] :
        ( v3_ordinal1(k3_tarski(X3))
        | sK0 = k3_tarski(X3)
        | ~ r1_tarski(k3_tarski(k3_tarski(X3)),k3_tarski(X3))
        | r2_hidden(sK2(X3,sK0),X3) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f75,plain,
    ( ~ spl3_2
    | spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f70,f52,f73,f52])).

fof(f70,plain,
    ( ! [X3] :
        ( sK0 = k3_tarski(X3)
        | r2_hidden(sK2(X3,sK0),X3)
        | ~ r1_tarski(k3_tarski(k3_tarski(X3)),k3_tarski(X3))
        | v3_ordinal1(k3_tarski(X3))
        | ~ v3_ordinal1(sK0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f67,f41])).

fof(f67,plain,
    ( ! [X1] :
        ( r2_hidden(k3_tarski(X1),sK0)
        | k3_tarski(X1) = sK0
        | r2_hidden(sK2(X1,sK0),X1)
        | ~ r1_tarski(k3_tarski(k3_tarski(X1)),k3_tarski(X1)) )
    | ~ spl3_2 ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,
    ( ! [X1] :
        ( r2_hidden(sK2(X1,sK0),X1)
        | k3_tarski(X1) = sK0
        | r2_hidden(k3_tarski(X1),sK0)
        | ~ r1_tarski(k3_tarski(k3_tarski(X1)),k3_tarski(X1))
        | r2_hidden(k3_tarski(X1),sK0)
        | r2_hidden(sK2(X1,sK0),X1)
        | k3_tarski(X1) = sK0 )
    | ~ spl3_2 ),
    inference(resolution,[],[f62,f59])).

fof(f59,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1(k3_tarski(X0)),k3_tarski(X0))
        | r2_hidden(k3_tarski(X0),sK0)
        | r2_hidden(sK2(X0,sK0),X0)
        | k3_tarski(X0) = sK0 )
    | ~ spl3_2 ),
    inference(resolution,[],[f58,f40])).

fof(f58,plain,
    ( ! [X1] :
        ( ~ v1_ordinal1(k3_tarski(X1))
        | k3_tarski(X1) = sK0
        | r2_hidden(k3_tarski(X1),sK0)
        | r2_hidden(sK2(X1,sK0),X1) )
    | ~ spl3_2 ),
    inference(resolution,[],[f56,f43])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( r1_tarski(sK1(k3_tarski(X0)),X1)
        | r2_hidden(sK2(X0,sK0),X0)
        | k3_tarski(X0) = sK0
        | r2_hidden(k3_tarski(X0),sK0)
        | ~ r1_tarski(k3_tarski(k3_tarski(X0)),X1) )
    | ~ spl3_2 ),
    inference(resolution,[],[f60,f46])).

fof(f60,plain,
    ( ! [X1] :
        ( r2_hidden(sK1(k3_tarski(X1)),k3_tarski(X1))
        | r2_hidden(k3_tarski(X1),sK0)
        | r2_hidden(sK2(X1,sK0),X1)
        | k3_tarski(X1) = sK0 )
    | ~ spl3_2 ),
    inference(resolution,[],[f58,f39])).

fof(f54,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f34,f52])).

fof(f34,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ v3_ordinal1(k3_tarski(sK0))
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ~ v3_ordinal1(k3_tarski(X0))
        & v3_ordinal1(X0) )
   => ( ~ v3_ordinal1(k3_tarski(sK0))
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(k3_tarski(X0))
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => v3_ordinal1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_ordinal1)).

fof(f50,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f35,f48])).

fof(f35,plain,(
    ~ v3_ordinal1(k3_tarski(sK0)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (6935)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.46  % (6935)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f200,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f50,f54,f75,f89,f98,f112,f113,f121,f137,f147,f154,f158,f165,f198,f199])).
% 0.21/0.46  fof(f199,plain,(
% 0.21/0.46    sK0 != k3_tarski(sK0) | v3_ordinal1(k3_tarski(sK0)) | ~v3_ordinal1(sK0)),
% 0.21/0.46    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.46  fof(f198,plain,(
% 0.21/0.46    ~spl3_5 | spl3_17 | ~spl3_18),
% 0.21/0.46    inference(avatar_split_clause,[],[f184,f156,f152,f84])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    spl3_5 <=> r1_tarski(k3_tarski(k3_tarski(sK0)),k3_tarski(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.46  fof(f152,plain,(
% 0.21/0.46    spl3_17 <=> r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.46  fof(f156,plain,(
% 0.21/0.46    spl3_18 <=> r2_hidden(sK1(k3_tarski(sK0)),k3_tarski(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.46  fof(f184,plain,(
% 0.21/0.46    ~r1_tarski(k3_tarski(k3_tarski(sK0)),k3_tarski(sK0)) | (spl3_17 | ~spl3_18)),
% 0.21/0.46    inference(resolution,[],[f174,f153])).
% 0.21/0.46  fof(f153,plain,(
% 0.21/0.46    ~r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0)) | spl3_17),
% 0.21/0.46    inference(avatar_component_clause,[],[f152])).
% 0.21/0.46  fof(f174,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tarski(sK1(k3_tarski(sK0)),X0) | ~r1_tarski(k3_tarski(k3_tarski(sK0)),X0)) ) | ~spl3_18),
% 0.21/0.46    inference(resolution,[],[f157,f46])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r1_tarski(X2,X1) | ~r1_tarski(k3_tarski(X0),X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1))),
% 0.21/0.46    inference(flattening,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X2,X1) | (~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).
% 0.21/0.46  fof(f157,plain,(
% 0.21/0.46    r2_hidden(sK1(k3_tarski(sK0)),k3_tarski(sK0)) | ~spl3_18),
% 0.21/0.46    inference(avatar_component_clause,[],[f156])).
% 0.21/0.46  fof(f165,plain,(
% 0.21/0.46    ~spl3_2 | spl3_1 | ~spl3_16),
% 0.21/0.46    inference(avatar_split_clause,[],[f161,f145,f48,f52])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    spl3_2 <=> v3_ordinal1(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    spl3_1 <=> v3_ordinal1(k3_tarski(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f145,plain,(
% 0.21/0.46    spl3_16 <=> r2_hidden(k3_tarski(sK0),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.46  fof(f161,plain,(
% 0.21/0.46    v3_ordinal1(k3_tarski(sK0)) | ~v3_ordinal1(sK0) | ~spl3_16),
% 0.21/0.46    inference(resolution,[],[f146,f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(X0,X1) | v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 0.21/0.46    inference(flattening,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).
% 0.21/0.46  fof(f146,plain,(
% 0.21/0.46    r2_hidden(k3_tarski(sK0),sK0) | ~spl3_16),
% 0.21/0.46    inference(avatar_component_clause,[],[f145])).
% 0.21/0.46  fof(f158,plain,(
% 0.21/0.46    spl3_18 | spl3_15),
% 0.21/0.46    inference(avatar_split_clause,[],[f149,f142,f156])).
% 0.21/0.46  fof(f142,plain,(
% 0.21/0.46    spl3_15 <=> v1_ordinal1(k3_tarski(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.46  fof(f149,plain,(
% 0.21/0.46    r2_hidden(sK1(k3_tarski(sK0)),k3_tarski(sK0)) | spl3_15),
% 0.21/0.46    inference(resolution,[],[f143,f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X0] : (v1_ordinal1(X0) | r2_hidden(sK1(X0),X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ! [X0] : ((v1_ordinal1(X0) | (~r1_tarski(sK1(X0),X0) & r2_hidden(sK1(X0),X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK1(X0),X0) & r2_hidden(sK1(X0),X0)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 0.21/0.46    inference(rectify,[],[f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0)))),
% 0.21/0.46    inference(nnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).
% 0.21/0.46  fof(f143,plain,(
% 0.21/0.46    ~v1_ordinal1(k3_tarski(sK0)) | spl3_15),
% 0.21/0.46    inference(avatar_component_clause,[],[f142])).
% 0.21/0.46  fof(f154,plain,(
% 0.21/0.46    ~spl3_17 | spl3_15),
% 0.21/0.46    inference(avatar_split_clause,[],[f148,f142,f152])).
% 0.21/0.46  fof(f148,plain,(
% 0.21/0.46    ~r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0)) | spl3_15),
% 0.21/0.46    inference(resolution,[],[f143,f40])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X0] : (v1_ordinal1(X0) | ~r1_tarski(sK1(X0),X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f31])).
% 0.21/0.46  fof(f147,plain,(
% 0.21/0.46    ~spl3_15 | spl3_16 | spl3_6 | ~spl3_2 | ~spl3_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f139,f110,f52,f87,f145,f142])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    spl3_6 <=> sK0 = k3_tarski(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.46  fof(f110,plain,(
% 0.21/0.46    spl3_10 <=> r1_tarski(sK2(sK0,sK0),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.46  fof(f139,plain,(
% 0.21/0.46    sK0 = k3_tarski(sK0) | r2_hidden(k3_tarski(sK0),sK0) | ~v1_ordinal1(k3_tarski(sK0)) | (~spl3_2 | ~spl3_10)),
% 0.21/0.46    inference(resolution,[],[f120,f57])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(sK2(X0,sK0),sK0) | k3_tarski(X0) = sK0 | r2_hidden(k3_tarski(X0),sK0) | ~v1_ordinal1(k3_tarski(X0))) ) | ~spl3_2),
% 0.21/0.46    inference(resolution,[],[f56,f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ~r1_tarski(sK2(X0,X1),X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(X0,sK0) | ~v1_ordinal1(X0) | sK0 = X0 | r2_hidden(X0,sK0)) ) | ~spl3_2),
% 0.21/0.46    inference(resolution,[],[f55,f45])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.21/0.46    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_xboole_0(X0,sK0) | r2_hidden(X0,sK0) | ~v1_ordinal1(X0)) ) | ~spl3_2),
% 0.21/0.46    inference(resolution,[],[f36,f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    v3_ordinal1(sK0) | ~spl3_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f52])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r2_xboole_0(X0,X1) | r2_hidden(X0,X1) | ~v1_ordinal1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.21/0.46    inference(flattening,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).
% 0.21/0.46  fof(f120,plain,(
% 0.21/0.46    r1_tarski(sK2(sK0,sK0),sK0) | ~spl3_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f110])).
% 0.21/0.46  fof(f137,plain,(
% 0.21/0.46    ~spl3_2 | spl3_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f128,f118,f52])).
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    spl3_11 <=> v1_ordinal1(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.46  fof(f128,plain,(
% 0.21/0.46    ~v3_ordinal1(sK0) | spl3_11),
% 0.21/0.46    inference(resolution,[],[f119,f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 0.21/0.46    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.21/0.46  fof(f119,plain,(
% 0.21/0.46    ~v1_ordinal1(sK0) | spl3_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f118])).
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    ~spl3_11 | spl3_10 | ~spl3_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f115,f81,f110,f118])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    spl3_4 <=> r2_hidden(sK2(sK0,sK0),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    r1_tarski(sK2(sK0,sK0),sK0) | ~v1_ordinal1(sK0) | ~spl3_4),
% 0.21/0.46    inference(resolution,[],[f82,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X2,X0] : (~r2_hidden(X2,X0) | r1_tarski(X2,X0) | ~v1_ordinal1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    r2_hidden(sK2(sK0,sK0),sK0) | ~spl3_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f81])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    spl3_4 | spl3_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f108,f96,f81])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    spl3_7 <=> r1_tarski(k3_tarski(sK0),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    r2_hidden(sK2(sK0,sK0),sK0) | spl3_7),
% 0.21/0.47    inference(resolution,[],[f97,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    ~r1_tarski(k3_tarski(sK0),sK0) | spl3_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f96])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    ~spl3_10 | spl3_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f107,f96,f110])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    ~r1_tarski(sK2(sK0,sK0),sK0) | spl3_7),
% 0.21/0.47    inference(resolution,[],[f97,f44])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    ~spl3_7 | spl3_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f92,f84,f96])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    ~r1_tarski(k3_tarski(sK0),sK0) | spl3_5),
% 0.21/0.47    inference(resolution,[],[f85,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    ~r1_tarski(k3_tarski(k3_tarski(sK0)),k3_tarski(sK0)) | spl3_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f84])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    spl3_4 | ~spl3_5 | spl3_6 | spl3_1 | ~spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f76,f73,f48,f87,f84,f81])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl3_3 <=> ! [X3] : (sK0 = k3_tarski(X3) | v3_ordinal1(k3_tarski(X3)) | ~r1_tarski(k3_tarski(k3_tarski(X3)),k3_tarski(X3)) | r2_hidden(sK2(X3,sK0),X3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    sK0 = k3_tarski(sK0) | ~r1_tarski(k3_tarski(k3_tarski(sK0)),k3_tarski(sK0)) | r2_hidden(sK2(sK0,sK0),sK0) | (spl3_1 | ~spl3_3)),
% 0.21/0.47    inference(resolution,[],[f74,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ~v3_ordinal1(k3_tarski(sK0)) | spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f48])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ( ! [X3] : (v3_ordinal1(k3_tarski(X3)) | sK0 = k3_tarski(X3) | ~r1_tarski(k3_tarski(k3_tarski(X3)),k3_tarski(X3)) | r2_hidden(sK2(X3,sK0),X3)) ) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f73])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ~spl3_2 | spl3_3 | ~spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f70,f52,f73,f52])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    ( ! [X3] : (sK0 = k3_tarski(X3) | r2_hidden(sK2(X3,sK0),X3) | ~r1_tarski(k3_tarski(k3_tarski(X3)),k3_tarski(X3)) | v3_ordinal1(k3_tarski(X3)) | ~v3_ordinal1(sK0)) ) | ~spl3_2),
% 0.21/0.47    inference(resolution,[],[f67,f41])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ( ! [X1] : (r2_hidden(k3_tarski(X1),sK0) | k3_tarski(X1) = sK0 | r2_hidden(sK2(X1,sK0),X1) | ~r1_tarski(k3_tarski(k3_tarski(X1)),k3_tarski(X1))) ) | ~spl3_2),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X1] : (r2_hidden(sK2(X1,sK0),X1) | k3_tarski(X1) = sK0 | r2_hidden(k3_tarski(X1),sK0) | ~r1_tarski(k3_tarski(k3_tarski(X1)),k3_tarski(X1)) | r2_hidden(k3_tarski(X1),sK0) | r2_hidden(sK2(X1,sK0),X1) | k3_tarski(X1) = sK0) ) | ~spl3_2),
% 0.21/0.47    inference(resolution,[],[f62,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_tarski(sK1(k3_tarski(X0)),k3_tarski(X0)) | r2_hidden(k3_tarski(X0),sK0) | r2_hidden(sK2(X0,sK0),X0) | k3_tarski(X0) = sK0) ) | ~spl3_2),
% 0.21/0.47    inference(resolution,[],[f58,f40])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X1] : (~v1_ordinal1(k3_tarski(X1)) | k3_tarski(X1) = sK0 | r2_hidden(k3_tarski(X1),sK0) | r2_hidden(sK2(X1,sK0),X1)) ) | ~spl3_2),
% 0.21/0.47    inference(resolution,[],[f56,f43])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(sK1(k3_tarski(X0)),X1) | r2_hidden(sK2(X0,sK0),X0) | k3_tarski(X0) = sK0 | r2_hidden(k3_tarski(X0),sK0) | ~r1_tarski(k3_tarski(k3_tarski(X0)),X1)) ) | ~spl3_2),
% 0.21/0.47    inference(resolution,[],[f60,f46])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X1] : (r2_hidden(sK1(k3_tarski(X1)),k3_tarski(X1)) | r2_hidden(k3_tarski(X1),sK0) | r2_hidden(sK2(X1,sK0),X1) | k3_tarski(X1) = sK0) ) | ~spl3_2),
% 0.21/0.47    inference(resolution,[],[f58,f39])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f34,f52])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    v3_ordinal1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ~v3_ordinal1(k3_tarski(sK0)) & v3_ordinal1(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ? [X0] : (~v3_ordinal1(k3_tarski(X0)) & v3_ordinal1(X0)) => (~v3_ordinal1(k3_tarski(sK0)) & v3_ordinal1(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0] : (~v3_ordinal1(k3_tarski(X0)) & v3_ordinal1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k3_tarski(X0)))),
% 0.21/0.47    inference(negated_conjecture,[],[f9])).
% 0.21/0.47  fof(f9,conjecture,(
% 0.21/0.47    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k3_tarski(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_ordinal1)).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ~spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f35,f48])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ~v3_ordinal1(k3_tarski(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (6935)------------------------------
% 0.21/0.47  % (6935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (6935)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (6935)Memory used [KB]: 10746
% 0.21/0.47  % (6935)Time elapsed: 0.016 s
% 0.21/0.47  % (6935)------------------------------
% 0.21/0.47  % (6935)------------------------------
% 0.21/0.47  % (6925)Success in time 0.112 s
%------------------------------------------------------------------------------
