%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 174 expanded)
%              Number of leaves         :   29 (  76 expanded)
%              Depth                    :    9
%              Number of atoms          :  289 ( 592 expanded)
%              Number of equality atoms :   32 (  64 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f399,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f52,f161,f167,f171,f195,f232,f237,f279,f302,f317,f359,f376,f378,f379,f394])).

fof(f394,plain,
    ( spl6_16
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f387,f230,f215])).

fof(f215,plain,
    ( spl6_16
  <=> r2_hidden(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f230,plain,
    ( spl6_18
  <=> r2_hidden(sK1(sK2(sK0,sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f387,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl6_18 ),
    inference(resolution,[],[f231,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK5(X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK5(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK5(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f13,f24])).

fof(f24,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK5(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK5(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f231,plain,
    ( r2_hidden(sK1(sK2(sK0,sK0),sK0),sK0)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f230])).

fof(f379,plain,
    ( ~ spl6_13
    | spl6_14
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f181,f159,f200,f197])).

fof(f197,plain,
    ( spl6_13
  <=> r1_xboole_0(sK2(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f200,plain,
    ( spl6_14
  <=> sK0 = k3_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f159,plain,
    ( spl6_7
  <=> ! [X18] :
        ( r2_hidden(sK2(sK0,X18),X18)
        | k3_tarski(sK0) = X18 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f181,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ r1_xboole_0(sK2(sK0,sK0),sK0)
    | ~ spl6_7 ),
    inference(resolution,[],[f160,f27])).

fof(f27,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r1_xboole_0(X1,sK0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK0)
        | ~ r2_hidden(X1,sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ r1_xboole_0(X1,X0)
            | ~ r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 )
   => ( ! [X1] :
          ( ~ r1_xboole_0(X1,sK0)
          | ~ r2_hidden(X1,sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f160,plain,
    ( ! [X18] :
        ( r2_hidden(sK2(sK0,X18),X18)
        | k3_tarski(sK0) = X18 )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f159])).

fof(f378,plain,(
    spl6_32 ),
    inference(avatar_contradiction_clause,[],[f377])).

fof(f377,plain,
    ( $false
    | spl6_32 ),
    inference(resolution,[],[f375,f29])).

fof(f29,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f375,plain,
    ( ~ r1_tarski(k1_xboole_0,sK5(k1_xboole_0))
    | spl6_32 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl6_32
  <=> r1_tarski(k1_xboole_0,sK5(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f376,plain,
    ( ~ spl6_32
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f369,f357,f374])).

fof(f357,plain,
    ( spl6_30
  <=> r2_hidden(sK5(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f369,plain,
    ( ~ r1_tarski(k1_xboole_0,sK5(k1_xboole_0))
    | ~ spl6_30 ),
    inference(resolution,[],[f358,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f358,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f357])).

fof(f359,plain,
    ( spl6_30
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f345,f193,f357])).

fof(f193,plain,
    ( spl6_12
  <=> r2_hidden(sK4(k1_xboole_0,sK2(sK0,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f345,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0)
    | ~ spl6_12 ),
    inference(resolution,[],[f194,f40])).

fof(f194,plain,
    ( r2_hidden(sK4(k1_xboole_0,sK2(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f193])).

fof(f317,plain,
    ( ~ spl6_6
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f242,f215,f156])).

fof(f156,plain,
    ( spl6_6
  <=> r1_xboole_0(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f242,plain,
    ( ~ r1_xboole_0(sK5(sK0),sK0)
    | ~ spl6_16 ),
    inference(resolution,[],[f216,f27])).

fof(f216,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f215])).

fof(f302,plain,
    ( ~ spl6_8
    | ~ spl6_23 ),
    inference(avatar_contradiction_clause,[],[f298])).

fof(f298,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f166,f277])).

fof(f277,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl6_23
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f166,plain,
    ( r2_hidden(sK1(sK5(sK0),sK0),sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl6_8
  <=> r2_hidden(sK1(sK5(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f279,plain,
    ( spl6_23
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f270,f169,f165,f276])).

fof(f169,plain,
    ( spl6_9
  <=> r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f270,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1(sK5(sK0),sK0),sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_9 ),
    inference(resolution,[],[f170,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK5(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f170,plain,
    ( r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f169])).

fof(f237,plain,
    ( sK0 != k3_tarski(sK0)
    | k1_xboole_0 != k3_tarski(sK0)
    | k1_xboole_0 = sK0 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f232,plain,
    ( spl6_18
    | spl6_13 ),
    inference(avatar_split_clause,[],[f227,f197,f230])).

fof(f227,plain,
    ( r2_hidden(sK1(sK2(sK0,sK0),sK0),sK0)
    | spl6_13 ),
    inference(resolution,[],[f198,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f198,plain,
    ( ~ r1_xboole_0(sK2(sK0,sK0),sK0)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f197])).

fof(f195,plain,
    ( spl6_12
    | spl6_11
    | ~ spl6_2
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f178,f159,f50,f189,f193])).

fof(f189,plain,
    ( spl6_11
  <=> k1_xboole_0 = k3_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f50,plain,
    ( spl6_2
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f178,plain,
    ( k1_xboole_0 = k3_tarski(sK0)
    | r2_hidden(sK4(k1_xboole_0,sK2(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_7 ),
    inference(resolution,[],[f160,f53])).

fof(f53,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | r2_hidden(sK4(k1_xboole_0,X0),k1_xboole_0) )
    | ~ spl6_2 ),
    inference(superposition,[],[f43,f51])).

fof(f51,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f43,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k3_tarski(X0))
      | r2_hidden(sK4(X0,X5),X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK2(X0,X1),X3) )
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( ( r2_hidden(sK3(X0,X1),X0)
              & r2_hidden(sK2(X0,X1),sK3(X0,X1)) )
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK4(X0,X5),X0)
                & r2_hidden(X5,sK4(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f22,f21,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK2(X0,X1),X3) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK2(X0,X1),X4) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK2(X0,X1),X4) )
     => ( r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK4(X0,X5),X0)
        & r2_hidden(X5,sK4(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f171,plain,
    ( spl6_9
    | spl6_6 ),
    inference(avatar_split_clause,[],[f163,f156,f169])).

fof(f163,plain,
    ( r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0))
    | spl6_6 ),
    inference(resolution,[],[f157,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f157,plain,
    ( ~ r1_xboole_0(sK5(sK0),sK0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f156])).

fof(f167,plain,
    ( spl6_8
    | spl6_6 ),
    inference(avatar_split_clause,[],[f162,f156,f165])).

fof(f162,plain,
    ( r2_hidden(sK1(sK5(sK0),sK0),sK0)
    | spl6_6 ),
    inference(resolution,[],[f157,f31])).

fof(f161,plain,
    ( ~ spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f139,f159,f156])).

fof(f139,plain,(
    ! [X18] :
      ( r2_hidden(sK2(sK0,X18),X18)
      | k3_tarski(sK0) = X18
      | ~ r1_xboole_0(sK5(sK0),sK0) ) ),
    inference(resolution,[],[f57,f27])).

fof(f57,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK5(X6),X6)
      | r2_hidden(sK2(X6,X7),X7)
      | k3_tarski(X6) = X7 ) ),
    inference(resolution,[],[f37,f40])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | k3_tarski(X0) = X1
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f28,f50])).

fof(f28,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f48,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f26,f46])).

fof(f46,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f26,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:21:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (23884)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.47  % (23883)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (23891)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (23884)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (23892)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (23888)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f399,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f48,f52,f161,f167,f171,f195,f232,f237,f279,f302,f317,f359,f376,f378,f379,f394])).
% 0.22/0.49  fof(f394,plain,(
% 0.22/0.49    spl6_16 | ~spl6_18),
% 0.22/0.49    inference(avatar_split_clause,[],[f387,f230,f215])).
% 0.22/0.49  fof(f215,plain,(
% 0.22/0.49    spl6_16 <=> r2_hidden(sK5(sK0),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.49  fof(f230,plain,(
% 0.22/0.49    spl6_18 <=> r2_hidden(sK1(sK2(sK0,sK0),sK0),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.49  fof(f387,plain,(
% 0.22/0.49    r2_hidden(sK5(sK0),sK0) | ~spl6_18),
% 0.22/0.49    inference(resolution,[],[f231,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK5(X1),X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK5(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f13,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK5(X1),X1)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).
% 0.22/0.49  fof(f231,plain,(
% 0.22/0.49    r2_hidden(sK1(sK2(sK0,sK0),sK0),sK0) | ~spl6_18),
% 0.22/0.49    inference(avatar_component_clause,[],[f230])).
% 0.22/0.49  fof(f379,plain,(
% 0.22/0.49    ~spl6_13 | spl6_14 | ~spl6_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f181,f159,f200,f197])).
% 0.22/0.49  fof(f197,plain,(
% 0.22/0.49    spl6_13 <=> r1_xboole_0(sK2(sK0,sK0),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.49  fof(f200,plain,(
% 0.22/0.49    spl6_14 <=> sK0 = k3_tarski(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.49  fof(f159,plain,(
% 0.22/0.49    spl6_7 <=> ! [X18] : (r2_hidden(sK2(sK0,X18),X18) | k3_tarski(sK0) = X18)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.49  fof(f181,plain,(
% 0.22/0.49    sK0 = k3_tarski(sK0) | ~r1_xboole_0(sK2(sK0,sK0),sK0) | ~spl6_7),
% 0.22/0.49    inference(resolution,[],[f160,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r1_xboole_0(X1,sK0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0)),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.49    inference(negated_conjecture,[],[f7])).
% 0.22/0.49  fof(f7,conjecture,(
% 0.22/0.49    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.22/0.49  fof(f160,plain,(
% 0.22/0.49    ( ! [X18] : (r2_hidden(sK2(sK0,X18),X18) | k3_tarski(sK0) = X18) ) | ~spl6_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f159])).
% 0.22/0.49  fof(f378,plain,(
% 0.22/0.49    spl6_32),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f377])).
% 0.22/0.49  fof(f377,plain,(
% 0.22/0.49    $false | spl6_32),
% 0.22/0.49    inference(resolution,[],[f375,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.49  fof(f375,plain,(
% 0.22/0.49    ~r1_tarski(k1_xboole_0,sK5(k1_xboole_0)) | spl6_32),
% 0.22/0.49    inference(avatar_component_clause,[],[f374])).
% 0.22/0.49  fof(f374,plain,(
% 0.22/0.49    spl6_32 <=> r1_tarski(k1_xboole_0,sK5(k1_xboole_0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.22/0.49  fof(f376,plain,(
% 0.22/0.49    ~spl6_32 | ~spl6_30),
% 0.22/0.49    inference(avatar_split_clause,[],[f369,f357,f374])).
% 0.22/0.49  fof(f357,plain,(
% 0.22/0.49    spl6_30 <=> r2_hidden(sK5(k1_xboole_0),k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.22/0.49  fof(f369,plain,(
% 0.22/0.49    ~r1_tarski(k1_xboole_0,sK5(k1_xboole_0)) | ~spl6_30),
% 0.22/0.49    inference(resolution,[],[f358,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.49  fof(f358,plain,(
% 0.22/0.49    r2_hidden(sK5(k1_xboole_0),k1_xboole_0) | ~spl6_30),
% 0.22/0.49    inference(avatar_component_clause,[],[f357])).
% 0.22/0.49  fof(f359,plain,(
% 0.22/0.49    spl6_30 | ~spl6_12),
% 0.22/0.49    inference(avatar_split_clause,[],[f345,f193,f357])).
% 0.22/0.49  fof(f193,plain,(
% 0.22/0.49    spl6_12 <=> r2_hidden(sK4(k1_xboole_0,sK2(sK0,k1_xboole_0)),k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.49  fof(f345,plain,(
% 0.22/0.49    r2_hidden(sK5(k1_xboole_0),k1_xboole_0) | ~spl6_12),
% 0.22/0.49    inference(resolution,[],[f194,f40])).
% 0.22/0.49  fof(f194,plain,(
% 0.22/0.49    r2_hidden(sK4(k1_xboole_0,sK2(sK0,k1_xboole_0)),k1_xboole_0) | ~spl6_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f193])).
% 0.22/0.49  fof(f317,plain,(
% 0.22/0.49    ~spl6_6 | ~spl6_16),
% 0.22/0.49    inference(avatar_split_clause,[],[f242,f215,f156])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    spl6_6 <=> r1_xboole_0(sK5(sK0),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.49  fof(f242,plain,(
% 0.22/0.49    ~r1_xboole_0(sK5(sK0),sK0) | ~spl6_16),
% 0.22/0.49    inference(resolution,[],[f216,f27])).
% 0.22/0.49  fof(f216,plain,(
% 0.22/0.49    r2_hidden(sK5(sK0),sK0) | ~spl6_16),
% 0.22/0.49    inference(avatar_component_clause,[],[f215])).
% 0.22/0.49  fof(f302,plain,(
% 0.22/0.49    ~spl6_8 | ~spl6_23),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f298])).
% 0.22/0.49  fof(f298,plain,(
% 0.22/0.49    $false | (~spl6_8 | ~spl6_23)),
% 0.22/0.49    inference(subsumption_resolution,[],[f166,f277])).
% 0.22/0.49  fof(f277,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl6_23),
% 0.22/0.49    inference(avatar_component_clause,[],[f276])).
% 0.22/0.49  fof(f276,plain,(
% 0.22/0.49    spl6_23 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.22/0.49  fof(f166,plain,(
% 0.22/0.49    r2_hidden(sK1(sK5(sK0),sK0),sK0) | ~spl6_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f165])).
% 0.22/0.49  fof(f165,plain,(
% 0.22/0.49    spl6_8 <=> r2_hidden(sK1(sK5(sK0),sK0),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.49  fof(f279,plain,(
% 0.22/0.49    spl6_23 | ~spl6_8 | ~spl6_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f270,f169,f165,f276])).
% 0.22/0.49  fof(f169,plain,(
% 0.22/0.49    spl6_9 <=> r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.49  fof(f270,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(sK1(sK5(sK0),sK0),sK0) | ~r2_hidden(X0,sK0)) ) | ~spl6_9),
% 0.22/0.49    inference(resolution,[],[f170,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f170,plain,(
% 0.22/0.49    r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0)) | ~spl6_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f169])).
% 0.22/0.49  fof(f237,plain,(
% 0.22/0.49    sK0 != k3_tarski(sK0) | k1_xboole_0 != k3_tarski(sK0) | k1_xboole_0 = sK0),
% 0.22/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.49  fof(f232,plain,(
% 0.22/0.49    spl6_18 | spl6_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f227,f197,f230])).
% 0.22/0.49  fof(f227,plain,(
% 0.22/0.49    r2_hidden(sK1(sK2(sK0,sK0),sK0),sK0) | spl6_13),
% 0.22/0.49    inference(resolution,[],[f198,f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.49    inference(rectify,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.49  fof(f198,plain,(
% 0.22/0.49    ~r1_xboole_0(sK2(sK0,sK0),sK0) | spl6_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f197])).
% 0.22/0.49  fof(f195,plain,(
% 0.22/0.49    spl6_12 | spl6_11 | ~spl6_2 | ~spl6_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f178,f159,f50,f189,f193])).
% 0.22/0.49  fof(f189,plain,(
% 0.22/0.49    spl6_11 <=> k1_xboole_0 = k3_tarski(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    spl6_2 <=> k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.49  fof(f178,plain,(
% 0.22/0.49    k1_xboole_0 = k3_tarski(sK0) | r2_hidden(sK4(k1_xboole_0,sK2(sK0,k1_xboole_0)),k1_xboole_0) | (~spl6_2 | ~spl6_7)),
% 0.22/0.49    inference(resolution,[],[f160,f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(sK4(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl6_2),
% 0.22/0.49    inference(superposition,[],[f43,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    k1_xboole_0 = k3_tarski(k1_xboole_0) | ~spl6_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f50])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0,X5] : (~r2_hidden(X5,k3_tarski(X0)) | r2_hidden(sK4(X0,X5),X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & ((r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),sK3(X0,X1))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f22,f21,f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK2(X0,X1),X4)) | r2_hidden(sK2(X0,X1),X1))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK2(X0,X1),X4)) => (r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),sK3(X0,X1))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 0.22/0.49    inference(rectify,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 0.22/0.49  fof(f171,plain,(
% 0.22/0.49    spl6_9 | spl6_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f163,f156,f169])).
% 0.22/0.49  fof(f163,plain,(
% 0.22/0.49    r2_hidden(sK1(sK5(sK0),sK0),sK5(sK0)) | spl6_6),
% 0.22/0.49    inference(resolution,[],[f157,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f157,plain,(
% 0.22/0.49    ~r1_xboole_0(sK5(sK0),sK0) | spl6_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f156])).
% 0.22/0.49  fof(f167,plain,(
% 0.22/0.49    spl6_8 | spl6_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f162,f156,f165])).
% 0.22/0.49  fof(f162,plain,(
% 0.22/0.49    r2_hidden(sK1(sK5(sK0),sK0),sK0) | spl6_6),
% 0.22/0.49    inference(resolution,[],[f157,f31])).
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    ~spl6_6 | spl6_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f139,f159,f156])).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    ( ! [X18] : (r2_hidden(sK2(sK0,X18),X18) | k3_tarski(sK0) = X18 | ~r1_xboole_0(sK5(sK0),sK0)) )),
% 0.22/0.49    inference(resolution,[],[f57,f27])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X6,X7] : (r2_hidden(sK5(X6),X6) | r2_hidden(sK2(X6,X7),X7) | k3_tarski(X6) = X7) )),
% 0.22/0.49    inference(resolution,[],[f37,f40])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | k3_tarski(X0) = X1 | r2_hidden(sK2(X0,X1),X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    spl6_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f28,f50])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ~spl6_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f26,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    spl6_1 <=> k1_xboole_0 = sK0),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    k1_xboole_0 != sK0),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (23884)------------------------------
% 0.22/0.49  % (23884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (23884)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (23884)Memory used [KB]: 10874
% 0.22/0.49  % (23884)Time elapsed: 0.060 s
% 0.22/0.49  % (23884)------------------------------
% 0.22/0.49  % (23884)------------------------------
% 0.22/0.49  % (23877)Success in time 0.133 s
%------------------------------------------------------------------------------
