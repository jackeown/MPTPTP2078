%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 249 expanded)
%              Number of leaves         :   28 (  97 expanded)
%              Depth                    :   10
%              Number of atoms          :  388 ( 718 expanded)
%              Number of equality atoms :   40 ( 107 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f395,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f103,f112,f113,f120,f138,f156,f209,f212,f310,f330,f340,f364,f372,f386,f394])).

fof(f394,plain,
    ( ~ spl3_7
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f387])).

fof(f387,plain,
    ( $false
    | ~ spl3_7
    | ~ spl3_16 ),
    inference(unit_resulting_resolution,[],[f137,f385,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f385,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f383])).

fof(f383,plain,
    ( spl3_16
  <=> r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f137,plain,
    ( r2_hidden(sK1,k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl3_7
  <=> r2_hidden(sK1,k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f386,plain,
    ( ~ spl3_6
    | ~ spl3_2
    | spl3_16
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f374,f109,f383,f100,f131])).

fof(f131,plain,
    ( spl3_6
  <=> v3_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f100,plain,
    ( spl3_2
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f109,plain,
    ( spl3_4
  <=> r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f374,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))))
    | ~ spl3_4 ),
    inference(resolution,[],[f110,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f110,plain,
    ( r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f372,plain,(
    ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f365])).

fof(f365,plain,
    ( $false
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f88,f363,f64])).

fof(f363,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl3_15
  <=> r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f88,plain,(
    ! [X1] : r2_hidden(X1,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1)))) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1))))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f55,f75])).

fof(f75,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0))) ),
    inference(definition_unfolding,[],[f57,f73,f74])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f72,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f71,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f70,f72])).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f57,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f364,plain,
    ( ~ spl3_6
    | ~ spl3_1
    | spl3_15
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f341,f306,f361,f95,f131])).

fof(f95,plain,
    ( spl3_1
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f306,plain,
    ( spl3_13
  <=> r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f341,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))))
    | ~ spl3_13 ),
    inference(resolution,[],[f308,f50])).

fof(f308,plain,
    ( r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f306])).

fof(f340,plain,
    ( spl3_13
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f339,f206,f109,f306])).

fof(f206,plain,
    ( spl3_10
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f339,plain,
    ( r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK0)
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f110,f208])).

fof(f208,plain,
    ( sK0 = sK1
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f206])).

fof(f330,plain,
    ( spl3_5
    | ~ spl3_7
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | spl3_5
    | ~ spl3_7
    | spl3_10 ),
    inference(unit_resulting_resolution,[],[f207,f119,f137,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1))))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f53,f75])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f119,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl3_5
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f207,plain,
    ( sK0 != sK1
    | spl3_10 ),
    inference(avatar_component_clause,[],[f206])).

fof(f310,plain,
    ( sK0 != sK1
    | r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f212,plain,
    ( ~ spl3_5
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | ~ spl3_5
    | spl3_7 ),
    inference(unit_resulting_resolution,[],[f136,f118,f90])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k1_enumset1(X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f59,f73])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f118,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f136,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f135])).

fof(f209,plain,
    ( ~ spl3_2
    | ~ spl3_1
    | spl3_5
    | spl3_10
    | spl3_3 ),
    inference(avatar_split_clause,[],[f194,f105,f206,f117,f95,f100])).

fof(f105,plain,
    ( spl3_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f194,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | spl3_3 ),
    inference(resolution,[],[f107,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f107,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f156,plain,
    ( ~ spl3_1
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | ~ spl3_1
    | spl3_6 ),
    inference(unit_resulting_resolution,[],[f97,f133,f81])).

fof(f81,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0))))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f56,f75])).

fof(f56,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f133,plain,
    ( ~ v3_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f131])).

fof(f97,plain,
    ( v3_ordinal1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f138,plain,
    ( ~ spl3_6
    | ~ spl3_2
    | spl3_7
    | spl3_4 ),
    inference(avatar_split_clause,[],[f126,f109,f135,f100,f131])).

fof(f126,plain,
    ( r2_hidden(sK1,k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))))
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))))
    | spl3_4 ),
    inference(resolution,[],[f52,f111])).

fof(f111,plain,
    ( ~ r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f120,plain,
    ( ~ spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f115,f105,f117])).

fof(f115,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f65,f106])).

fof(f106,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f113,plain,
    ( spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f77,f109,f105])).

fof(f77,plain,
    ( r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f48,f75])).

fof(f48,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f33,plain,
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

fof(f34,plain,
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

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f112,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f76,f109,f105])).

fof(f76,plain,
    ( ~ r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f49,f75])).

fof(f49,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f103,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f47,f100])).

fof(f47,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f98,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f46,f95])).

fof(f46,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:09:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (11742)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.50  % (11726)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (11734)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (11742)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (11748)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (11740)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (11719)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (11747)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (11723)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.54  % (11724)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (11732)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.55  % (11735)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f395,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f98,f103,f112,f113,f120,f138,f156,f209,f212,f310,f330,f340,f364,f372,f386,f394])).
% 0.20/0.55  fof(f394,plain,(
% 0.20/0.55    ~spl3_7 | ~spl3_16),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f387])).
% 0.20/0.55  fof(f387,plain,(
% 0.20/0.55    $false | (~spl3_7 | ~spl3_16)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f137,f385,f64])).
% 0.20/0.55  fof(f64,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,axiom,(
% 0.20/0.55    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.55  fof(f385,plain,(
% 0.20/0.55    r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1) | ~spl3_16),
% 0.20/0.55    inference(avatar_component_clause,[],[f383])).
% 0.20/0.55  fof(f383,plain,(
% 0.20/0.55    spl3_16 <=> r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.55  fof(f137,plain,(
% 0.20/0.55    r2_hidden(sK1,k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0)))) | ~spl3_7),
% 0.20/0.55    inference(avatar_component_clause,[],[f135])).
% 0.20/0.55  fof(f135,plain,(
% 0.20/0.55    spl3_7 <=> r2_hidden(sK1,k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.55  fof(f386,plain,(
% 0.20/0.55    ~spl3_6 | ~spl3_2 | spl3_16 | ~spl3_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f374,f109,f383,f100,f131])).
% 0.20/0.55  fof(f131,plain,(
% 0.20/0.55    spl3_6 <=> v3_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.55  fof(f100,plain,(
% 0.20/0.55    spl3_2 <=> v3_ordinal1(sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.55  fof(f109,plain,(
% 0.20/0.55    spl3_4 <=> r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.55  fof(f374,plain,(
% 0.20/0.55    r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0)))) | ~spl3_4),
% 0.20/0.55    inference(resolution,[],[f110,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.55    inference(nnf_transformation,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.55    inference(flattening,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,axiom,(
% 0.20/0.55    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.20/0.55  fof(f110,plain,(
% 0.20/0.55    r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1) | ~spl3_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f109])).
% 0.20/0.55  fof(f372,plain,(
% 0.20/0.55    ~spl3_15),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f365])).
% 0.20/0.55  fof(f365,plain,(
% 0.20/0.55    $false | ~spl3_15),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f88,f363,f64])).
% 0.20/0.55  fof(f363,plain,(
% 0.20/0.55    r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK0) | ~spl3_15),
% 0.20/0.55    inference(avatar_component_clause,[],[f361])).
% 0.20/0.55  fof(f361,plain,(
% 0.20/0.55    spl3_15 <=> r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.55  fof(f88,plain,(
% 0.20/0.55    ( ! [X1] : (r2_hidden(X1,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1))))) )),
% 0.20/0.55    inference(equality_resolution,[],[f78])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1)))) | X0 != X1) )),
% 0.20/0.55    inference(definition_unfolding,[],[f55,f75])).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0)))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f57,f73,f74])).
% 0.20/0.55  fof(f74,plain,(
% 0.20/0.55    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f71,f72])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.55  fof(f73,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f70,f72])).
% 0.20/0.55  fof(f70,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,axiom,(
% 0.20/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f38])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.20/0.55    inference(flattening,[],[f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.20/0.55    inference(nnf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,axiom,(
% 0.20/0.55    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.20/0.55  fof(f364,plain,(
% 0.20/0.55    ~spl3_6 | ~spl3_1 | spl3_15 | ~spl3_13),
% 0.20/0.55    inference(avatar_split_clause,[],[f341,f306,f361,f95,f131])).
% 0.20/0.55  fof(f95,plain,(
% 0.20/0.55    spl3_1 <=> v3_ordinal1(sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.55  fof(f306,plain,(
% 0.20/0.55    spl3_13 <=> r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.55  fof(f341,plain,(
% 0.20/0.55    r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0)))) | ~spl3_13),
% 0.20/0.55    inference(resolution,[],[f308,f50])).
% 0.20/0.55  fof(f308,plain,(
% 0.20/0.55    r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK0) | ~spl3_13),
% 0.20/0.55    inference(avatar_component_clause,[],[f306])).
% 0.20/0.55  fof(f340,plain,(
% 0.20/0.55    spl3_13 | ~spl3_4 | ~spl3_10),
% 0.20/0.55    inference(avatar_split_clause,[],[f339,f206,f109,f306])).
% 0.20/0.55  fof(f206,plain,(
% 0.20/0.55    spl3_10 <=> sK0 = sK1),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.55  fof(f339,plain,(
% 0.20/0.55    r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK0) | (~spl3_4 | ~spl3_10)),
% 0.20/0.55    inference(forward_demodulation,[],[f110,f208])).
% 0.20/0.55  fof(f208,plain,(
% 0.20/0.55    sK0 = sK1 | ~spl3_10),
% 0.20/0.55    inference(avatar_component_clause,[],[f206])).
% 0.20/0.55  fof(f330,plain,(
% 0.20/0.55    spl3_5 | ~spl3_7 | spl3_10),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f323])).
% 0.20/0.55  fof(f323,plain,(
% 0.20/0.55    $false | (spl3_5 | ~spl3_7 | spl3_10)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f207,f119,f137,f80])).
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X1,X1,X1)))) | r2_hidden(X0,X1) | X0 = X1) )),
% 0.20/0.55    inference(definition_unfolding,[],[f53,f75])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f38])).
% 0.20/0.55  fof(f119,plain,(
% 0.20/0.55    ~r2_hidden(sK1,sK0) | spl3_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f117])).
% 0.20/0.55  fof(f117,plain,(
% 0.20/0.55    spl3_5 <=> r2_hidden(sK1,sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.55  fof(f207,plain,(
% 0.20/0.55    sK0 != sK1 | spl3_10),
% 0.20/0.55    inference(avatar_component_clause,[],[f206])).
% 0.20/0.55  fof(f310,plain,(
% 0.20/0.55    sK0 != sK1 | r2_hidden(sK1,sK0) | ~r2_hidden(sK0,sK1)),
% 0.20/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.55  fof(f212,plain,(
% 0.20/0.55    ~spl3_5 | spl3_7),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f210])).
% 0.20/0.55  fof(f210,plain,(
% 0.20/0.55    $false | (~spl3_5 | spl3_7)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f136,f118,f90])).
% 0.20/0.55  fof(f90,plain,(
% 0.20/0.55    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f86])).
% 0.20/0.55  fof(f86,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k1_enumset1(X0,X0,X1)) != X2) )),
% 0.20/0.55    inference(definition_unfolding,[],[f59,f73])).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.55    inference(cnf_transformation,[],[f43])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.55    inference(rectify,[],[f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.55    inference(flattening,[],[f39])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.55    inference(nnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.55  fof(f118,plain,(
% 0.20/0.55    r2_hidden(sK1,sK0) | ~spl3_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f117])).
% 0.20/0.55  fof(f136,plain,(
% 0.20/0.55    ~r2_hidden(sK1,k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0)))) | spl3_7),
% 0.20/0.55    inference(avatar_component_clause,[],[f135])).
% 0.20/0.55  fof(f209,plain,(
% 0.20/0.55    ~spl3_2 | ~spl3_1 | spl3_5 | spl3_10 | spl3_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f194,f105,f206,f117,f95,f100])).
% 0.20/0.55  fof(f105,plain,(
% 0.20/0.55    spl3_3 <=> r2_hidden(sK0,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.55  fof(f194,plain,(
% 0.20/0.55    sK0 = sK1 | r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | spl3_3),
% 0.20/0.55    inference(resolution,[],[f107,f66])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.55    inference(flattening,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,axiom,(
% 0.20/0.55    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.20/0.55  fof(f107,plain,(
% 0.20/0.55    ~r2_hidden(sK0,sK1) | spl3_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f105])).
% 0.20/0.55  fof(f156,plain,(
% 0.20/0.55    ~spl3_1 | spl3_6),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f154])).
% 0.20/0.55  fof(f154,plain,(
% 0.20/0.55    $false | (~spl3_1 | spl3_6)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f97,f133,f81])).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    ( ! [X0] : (v3_ordinal1(k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0)))) | ~v3_ordinal1(X0)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f56,f75])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f17])).
% 0.20/0.55  fof(f17,axiom,(
% 0.20/0.55    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.20/0.55  fof(f133,plain,(
% 0.20/0.55    ~v3_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0)))) | spl3_6),
% 0.20/0.55    inference(avatar_component_clause,[],[f131])).
% 0.20/0.55  fof(f97,plain,(
% 0.20/0.55    v3_ordinal1(sK0) | ~spl3_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f95])).
% 0.20/0.55  fof(f138,plain,(
% 0.20/0.55    ~spl3_6 | ~spl3_2 | spl3_7 | spl3_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f126,f109,f135,f100,f131])).
% 0.20/0.55  fof(f126,plain,(
% 0.20/0.55    r2_hidden(sK1,k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0)))) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0)))) | spl3_4),
% 0.20/0.55    inference(resolution,[],[f52,f111])).
% 0.20/0.55  fof(f111,plain,(
% 0.20/0.55    ~r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1) | spl3_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f109])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.55    inference(flattening,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,axiom,(
% 0.20/0.55    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.20/0.55  fof(f120,plain,(
% 0.20/0.55    ~spl3_5 | ~spl3_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f115,f105,f117])).
% 0.20/0.55  fof(f115,plain,(
% 0.20/0.55    ~r2_hidden(sK1,sK0) | ~spl3_3),
% 0.20/0.55    inference(resolution,[],[f65,f106])).
% 0.20/0.55  fof(f106,plain,(
% 0.20/0.55    r2_hidden(sK0,sK1) | ~spl3_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f105])).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.20/0.55  fof(f113,plain,(
% 0.20/0.55    spl3_3 | spl3_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f77,f109,f105])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1) | r2_hidden(sK0,sK1)),
% 0.20/0.55    inference(definition_unfolding,[],[f48,f75])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.55    inference(flattening,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.55    inference(nnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f20])).
% 0.20/0.55  fof(f20,negated_conjecture,(
% 0.20/0.55    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.20/0.55    inference(negated_conjecture,[],[f19])).
% 0.20/0.55  fof(f19,conjecture,(
% 0.20/0.55    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.20/0.55  fof(f112,plain,(
% 0.20/0.55    ~spl3_3 | ~spl3_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f76,f109,f105])).
% 0.20/0.55  fof(f76,plain,(
% 0.20/0.55    ~r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1) | ~r2_hidden(sK0,sK1)),
% 0.20/0.55    inference(definition_unfolding,[],[f49,f75])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f35])).
% 0.20/0.55  fof(f103,plain,(
% 0.20/0.55    spl3_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f47,f100])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    v3_ordinal1(sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f35])).
% 0.20/0.55  fof(f98,plain,(
% 0.20/0.55    spl3_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f46,f95])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    v3_ordinal1(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f35])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (11742)------------------------------
% 0.20/0.55  % (11742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (11742)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (11742)Memory used [KB]: 11001
% 0.20/0.55  % (11742)Time elapsed: 0.126 s
% 0.20/0.55  % (11742)------------------------------
% 0.20/0.55  % (11742)------------------------------
% 0.20/0.55  % (11739)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (11727)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  % (11718)Success in time 0.193 s
%------------------------------------------------------------------------------
