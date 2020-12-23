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
% DateTime   : Thu Dec  3 12:58:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 200 expanded)
%              Number of leaves         :   24 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          :  295 ( 736 expanded)
%              Number of equality atoms :   35 (  79 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f479,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f56,f61,f163,f181,f192,f199,f206,f210,f310,f389,f404,f478])).

fof(f478,plain,
    ( ~ spl6_11
    | spl6_1
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f476,f161,f50,f197])).

fof(f197,plain,
    ( spl6_11
  <=> r1_xboole_0(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f50,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f161,plain,
    ( spl6_7
  <=> ! [X0] :
        ( r2_hidden(sK1(k1_xboole_0,sK0,X0),X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f476,plain,
    ( k1_xboole_0 = sK0
    | ~ r1_xboole_0(sK5(sK0),sK0)
    | ~ spl6_7 ),
    inference(resolution,[],[f338,f30])).

fof(f30,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r1_xboole_0(X1,sK0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK0)
        | ~ r2_hidden(X1,sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f17])).

fof(f17,plain,
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

fof(f12,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f338,plain,
    ( ! [X4] :
        ( r2_hidden(sK5(X4),X4)
        | k1_xboole_0 = X4 )
    | ~ spl6_7 ),
    inference(resolution,[],[f162,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK5(X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK5(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK5(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f27])).

fof(f27,plain,(
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

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f162,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(k1_xboole_0,sK0,X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f161])).

fof(f404,plain,
    ( ~ spl6_10
    | ~ spl6_30 ),
    inference(avatar_contradiction_clause,[],[f400])).

fof(f400,plain,
    ( $false
    | ~ spl6_10
    | ~ spl6_30 ),
    inference(resolution,[],[f191,f308])).

fof(f308,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl6_30
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f191,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl6_10
  <=> r2_hidden(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f389,plain,
    ( spl6_10
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f243,f204,f190])).

fof(f204,plain,
    ( spl6_12
  <=> r2_hidden(sK4(sK5(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f243,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f205,f44])).

fof(f205,plain,
    ( r2_hidden(sK4(sK5(sK0),sK0),sK0)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f204])).

fof(f310,plain,
    ( spl6_30
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f303,f208,f204,f307])).

fof(f208,plain,
    ( spl6_13
  <=> r2_hidden(sK4(sK5(sK0),sK0),sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f303,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK5(sK0),sK0),sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_13 ),
    inference(resolution,[],[f209,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK5(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f209,plain,
    ( r2_hidden(sK4(sK5(sK0),sK0),sK5(sK0))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f208])).

fof(f210,plain,
    ( spl6_13
    | spl6_11 ),
    inference(avatar_split_clause,[],[f201,f197,f208])).

fof(f201,plain,
    ( r2_hidden(sK4(sK5(sK0),sK0),sK5(sK0))
    | spl6_11 ),
    inference(resolution,[],[f198,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f198,plain,
    ( ~ r1_xboole_0(sK5(sK0),sK0)
    | spl6_11 ),
    inference(avatar_component_clause,[],[f197])).

fof(f206,plain,
    ( spl6_12
    | spl6_11 ),
    inference(avatar_split_clause,[],[f200,f197,f204])).

fof(f200,plain,
    ( r2_hidden(sK4(sK5(sK0),sK0),sK0)
    | spl6_11 ),
    inference(resolution,[],[f198,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f199,plain,
    ( ~ spl6_11
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f193,f190,f197])).

fof(f193,plain,
    ( ~ r1_xboole_0(sK5(sK0),sK0)
    | ~ spl6_10 ),
    inference(resolution,[],[f191,f30])).

fof(f192,plain,
    ( spl6_10
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f184,f178,f190])).

fof(f178,plain,
    ( spl6_8
  <=> r2_hidden(sK4(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f184,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl6_8 ),
    inference(resolution,[],[f179,f44])).

fof(f179,plain,
    ( r2_hidden(sK4(sK0,sK0),sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f178])).

fof(f181,plain,
    ( spl6_8
    | spl6_6 ),
    inference(avatar_split_clause,[],[f175,f158,f178])).

fof(f158,plain,
    ( spl6_6
  <=> r1_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f175,plain,
    ( r2_hidden(sK4(sK0,sK0),sK0)
    | spl6_6 ),
    inference(resolution,[],[f159,f40])).

fof(f159,plain,
    ( ~ r1_xboole_0(sK0,sK0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f158])).

fof(f163,plain,
    ( ~ spl6_6
    | spl6_7
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f156,f59,f161,f158])).

fof(f59,plain,
    ( spl6_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f156,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(k1_xboole_0,sK0,X0),X0)
        | ~ r1_xboole_0(sK0,sK0)
        | k1_xboole_0 = X0 )
    | ~ spl6_3 ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(k1_xboole_0,sK0,X0),X0)
        | ~ r1_xboole_0(sK0,sK0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = X0
        | r2_hidden(sK1(k1_xboole_0,sK0,X0),X0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f91,f84])).

fof(f84,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2(k1_xboole_0,sK0,X0),sK0),sK0)
        | k1_xboole_0 = X0
        | r2_hidden(sK1(k1_xboole_0,sK0,X0),X0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f82,f41])).

fof(f82,plain,
    ( ! [X15] :
        ( ~ r1_xboole_0(sK2(k1_xboole_0,sK0,X15),sK0)
        | r2_hidden(sK1(k1_xboole_0,sK0,X15),X15)
        | k1_xboole_0 = X15 )
    | ~ spl6_3 ),
    inference(resolution,[],[f75,f30])).

fof(f75,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK2(k1_xboole_0,X3,X4),X3)
        | k1_xboole_0 = X4
        | r2_hidden(sK1(k1_xboole_0,X3,X4),X4) )
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f74,f32])).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

fof(f74,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK2(k1_xboole_0,X3,X4),X3)
        | r2_hidden(sK1(k1_xboole_0,X3,X4),X4)
        | k10_relat_1(k1_xboole_0,X3) = X4 )
    | ~ spl6_3 ),
    inference(resolution,[],[f38,f60])).

fof(f60,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK2(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK3(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f23,f22,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

% (923)Refutation not found, incomplete strategy% (923)------------------------------
% (923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (923)Termination reason: Refutation not found, incomplete strategy

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f19])).

% (923)Memory used [KB]: 1663
% (923)Time elapsed: 0.079 s
% (923)------------------------------
% (923)------------------------------
fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f91,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(sK4(sK2(k1_xboole_0,sK0,X1),sK0),X2)
        | r2_hidden(sK1(k1_xboole_0,sK0,X1),X1)
        | ~ r1_xboole_0(X2,sK0)
        | k1_xboole_0 = X1 )
    | ~ spl6_3 ),
    inference(resolution,[],[f84,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,
    ( spl6_3
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f57,f54,f59])).

fof(f54,plain,
    ( spl6_2
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f57,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_2 ),
    inference(superposition,[],[f33,f55])).

fof(f55,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f56,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f31,f54])).

fof(f31,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f52,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f29,f50])).

fof(f29,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:28:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (916)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.47  % (925)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.47  % (925)Refutation not found, incomplete strategy% (925)------------------------------
% 0.22/0.47  % (925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (917)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.47  % (925)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (925)Memory used [KB]: 6140
% 0.22/0.47  % (925)Time elapsed: 0.005 s
% 0.22/0.47  % (925)------------------------------
% 0.22/0.47  % (925)------------------------------
% 0.22/0.48  % (924)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (915)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (919)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (923)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (916)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f479,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f52,f56,f61,f163,f181,f192,f199,f206,f210,f310,f389,f404,f478])).
% 0.22/0.50  fof(f478,plain,(
% 0.22/0.50    ~spl6_11 | spl6_1 | ~spl6_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f476,f161,f50,f197])).
% 0.22/0.50  fof(f197,plain,(
% 0.22/0.50    spl6_11 <=> r1_xboole_0(sK5(sK0),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    spl6_1 <=> k1_xboole_0 = sK0),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    spl6_7 <=> ! [X0] : (r2_hidden(sK1(k1_xboole_0,sK0,X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.50  fof(f476,plain,(
% 0.22/0.50    k1_xboole_0 = sK0 | ~r1_xboole_0(sK5(sK0),sK0) | ~spl6_7),
% 0.22/0.50    inference(resolution,[],[f338,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r1_xboole_0(X1,sK0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0)),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.50    inference(negated_conjecture,[],[f8])).
% 0.22/0.50  fof(f8,conjecture,(
% 0.22/0.50    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.22/0.50  fof(f338,plain,(
% 0.22/0.50    ( ! [X4] : (r2_hidden(sK5(X4),X4) | k1_xboole_0 = X4) ) | ~spl6_7),
% 0.22/0.50    inference(resolution,[],[f162,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK5(X1),X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK5(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK5(X1),X1)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(sK1(k1_xboole_0,sK0,X0),X0) | k1_xboole_0 = X0) ) | ~spl6_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f161])).
% 0.22/0.50  fof(f404,plain,(
% 0.22/0.50    ~spl6_10 | ~spl6_30),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f400])).
% 0.22/0.50  fof(f400,plain,(
% 0.22/0.50    $false | (~spl6_10 | ~spl6_30)),
% 0.22/0.50    inference(resolution,[],[f191,f308])).
% 0.22/0.50  fof(f308,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl6_30),
% 0.22/0.50    inference(avatar_component_clause,[],[f307])).
% 0.22/0.50  fof(f307,plain,(
% 0.22/0.50    spl6_30 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.22/0.50  fof(f191,plain,(
% 0.22/0.50    r2_hidden(sK5(sK0),sK0) | ~spl6_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f190])).
% 0.22/0.50  fof(f190,plain,(
% 0.22/0.50    spl6_10 <=> r2_hidden(sK5(sK0),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.50  fof(f389,plain,(
% 0.22/0.50    spl6_10 | ~spl6_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f243,f204,f190])).
% 0.22/0.50  fof(f204,plain,(
% 0.22/0.50    spl6_12 <=> r2_hidden(sK4(sK5(sK0),sK0),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.50  fof(f243,plain,(
% 0.22/0.50    r2_hidden(sK5(sK0),sK0) | ~spl6_12),
% 0.22/0.50    inference(resolution,[],[f205,f44])).
% 0.22/0.50  fof(f205,plain,(
% 0.22/0.50    r2_hidden(sK4(sK5(sK0),sK0),sK0) | ~spl6_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f204])).
% 0.22/0.50  fof(f310,plain,(
% 0.22/0.50    spl6_30 | ~spl6_12 | ~spl6_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f303,f208,f204,f307])).
% 0.22/0.50  fof(f208,plain,(
% 0.22/0.50    spl6_13 <=> r2_hidden(sK4(sK5(sK0),sK0),sK5(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.50  fof(f303,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(sK4(sK5(sK0),sK0),sK0) | ~r2_hidden(X0,sK0)) ) | ~spl6_13),
% 0.22/0.50    inference(resolution,[],[f209,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK5(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f209,plain,(
% 0.22/0.50    r2_hidden(sK4(sK5(sK0),sK0),sK5(sK0)) | ~spl6_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f208])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    spl6_13 | spl6_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f201,f197,f208])).
% 0.22/0.50  fof(f201,plain,(
% 0.22/0.50    r2_hidden(sK4(sK5(sK0),sK0),sK5(sK0)) | spl6_11),
% 0.22/0.50    inference(resolution,[],[f198,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(rectify,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.50  fof(f198,plain,(
% 0.22/0.50    ~r1_xboole_0(sK5(sK0),sK0) | spl6_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f197])).
% 0.22/0.50  fof(f206,plain,(
% 0.22/0.50    spl6_12 | spl6_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f200,f197,f204])).
% 0.22/0.50  fof(f200,plain,(
% 0.22/0.50    r2_hidden(sK4(sK5(sK0),sK0),sK0) | spl6_11),
% 0.22/0.50    inference(resolution,[],[f198,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f199,plain,(
% 0.22/0.50    ~spl6_11 | ~spl6_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f193,f190,f197])).
% 0.22/0.50  fof(f193,plain,(
% 0.22/0.50    ~r1_xboole_0(sK5(sK0),sK0) | ~spl6_10),
% 0.22/0.50    inference(resolution,[],[f191,f30])).
% 0.22/0.50  fof(f192,plain,(
% 0.22/0.50    spl6_10 | ~spl6_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f184,f178,f190])).
% 0.22/0.50  fof(f178,plain,(
% 0.22/0.50    spl6_8 <=> r2_hidden(sK4(sK0,sK0),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.50  fof(f184,plain,(
% 0.22/0.50    r2_hidden(sK5(sK0),sK0) | ~spl6_8),
% 0.22/0.50    inference(resolution,[],[f179,f44])).
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    r2_hidden(sK4(sK0,sK0),sK0) | ~spl6_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f178])).
% 0.22/0.50  fof(f181,plain,(
% 0.22/0.50    spl6_8 | spl6_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f175,f158,f178])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    spl6_6 <=> r1_xboole_0(sK0,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    r2_hidden(sK4(sK0,sK0),sK0) | spl6_6),
% 0.22/0.50    inference(resolution,[],[f159,f40])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    ~r1_xboole_0(sK0,sK0) | spl6_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f158])).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    ~spl6_6 | spl6_7 | ~spl6_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f156,f59,f161,f158])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    spl6_3 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(sK1(k1_xboole_0,sK0,X0),X0) | ~r1_xboole_0(sK0,sK0) | k1_xboole_0 = X0) ) | ~spl6_3),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f153])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(sK1(k1_xboole_0,sK0,X0),X0) | ~r1_xboole_0(sK0,sK0) | k1_xboole_0 = X0 | k1_xboole_0 = X0 | r2_hidden(sK1(k1_xboole_0,sK0,X0),X0)) ) | ~spl6_3),
% 0.22/0.50    inference(resolution,[],[f91,f84])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(sK4(sK2(k1_xboole_0,sK0,X0),sK0),sK0) | k1_xboole_0 = X0 | r2_hidden(sK1(k1_xboole_0,sK0,X0),X0)) ) | ~spl6_3),
% 0.22/0.50    inference(resolution,[],[f82,f41])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ( ! [X15] : (~r1_xboole_0(sK2(k1_xboole_0,sK0,X15),sK0) | r2_hidden(sK1(k1_xboole_0,sK0,X15),X15) | k1_xboole_0 = X15) ) | ~spl6_3),
% 0.22/0.50    inference(resolution,[],[f75,f30])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X4,X3] : (r2_hidden(sK2(k1_xboole_0,X3,X4),X3) | k1_xboole_0 = X4 | r2_hidden(sK1(k1_xboole_0,X3,X4),X4)) ) | ~spl6_3),
% 0.22/0.50    inference(forward_demodulation,[],[f74,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X4,X3] : (r2_hidden(sK2(k1_xboole_0,X3,X4),X3) | r2_hidden(sK1(k1_xboole_0,X3,X4),X4) | k10_relat_1(k1_xboole_0,X3) = X4) ) | ~spl6_3),
% 0.22/0.50    inference(resolution,[],[f38,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    v1_relat_1(k1_xboole_0) | ~spl6_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f59])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2) | k10_relat_1(X0,X1) = X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f23,f22,f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  % (923)Refutation not found, incomplete strategy% (923)------------------------------
% 0.22/0.50  % (923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (923)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(rectify,[],[f19])).
% 0.22/0.50  % (923)Memory used [KB]: 1663
% 0.22/0.50  % (923)Time elapsed: 0.079 s
% 0.22/0.50  % (923)------------------------------
% 0.22/0.50  % (923)------------------------------
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    ( ! [X2,X1] : (~r2_hidden(sK4(sK2(k1_xboole_0,sK0,X1),sK0),X2) | r2_hidden(sK1(k1_xboole_0,sK0,X1),X1) | ~r1_xboole_0(X2,sK0) | k1_xboole_0 = X1) ) | ~spl6_3),
% 0.22/0.50    inference(resolution,[],[f84,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    spl6_3 | ~spl6_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f57,f54,f59])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    spl6_2 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    v1_relat_1(k1_xboole_0) | ~spl6_2),
% 0.22/0.50    inference(superposition,[],[f33,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl6_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f54])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    spl6_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f31,f54])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ~spl6_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f29,f50])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    k1_xboole_0 != sK0),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (916)------------------------------
% 0.22/0.50  % (916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (916)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (916)Memory used [KB]: 11001
% 0.22/0.50  % (916)Time elapsed: 0.063 s
% 0.22/0.50  % (916)------------------------------
% 0.22/0.50  % (916)------------------------------
% 0.22/0.50  % (909)Success in time 0.137 s
%------------------------------------------------------------------------------
