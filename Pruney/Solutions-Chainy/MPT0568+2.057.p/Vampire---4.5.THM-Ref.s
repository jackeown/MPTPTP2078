%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 167 expanded)
%              Number of leaves         :   16 (  56 expanded)
%              Depth                    :   18
%              Number of atoms          :  221 ( 626 expanded)
%              Number of equality atoms :   53 ( 120 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f251,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f123,f250])).

fof(f250,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(trivial_inequality_removal,[],[f246])).

fof(f246,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(superposition,[],[f27,f185])).

fof(f185,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(resolution,[],[f180,f126])).

fof(f126,plain,
    ( ! [X2,X3] :
        ( ~ sP0(X2,k1_xboole_0,X3)
        | k10_relat_1(k1_xboole_0,X2) = X3 )
    | ~ spl6_3 ),
    inference(resolution,[],[f115,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0)
      | ~ sP0(X1,X0,X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ~ sP0(X1,X0,X2) )
          & ( sP0(X1,X0,X2)
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> sP0(X1,X0,X2) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f115,plain,
    ( sP1(k1_xboole_0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl6_3
  <=> sP1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f180,plain,
    ( ! [X8] : sP0(X8,k1_xboole_0,k1_xboole_0)
    | ~ spl6_4 ),
    inference(resolution,[],[f170,f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),X1)
      | sP0(X0,X1,k1_xboole_0) ) ),
    inference(trivial_inequality_removal,[],[f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | sP0(X0,X1,k1_xboole_0)
      | r2_hidden(k4_tarski(sK3(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),X1) ) ),
    inference(superposition,[],[f63,f28])).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k1_enumset1(sK3(X0,X1,X2),sK3(X0,X1,X2),sK3(X0,X1,X2))) != X2
      | sP0(X0,X1,X2)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1) ) ),
    inference(resolution,[],[f35,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f44,f46])).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f40])).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X1) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X0)
              & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r2_hidden(X7,X0)
                  | ~ r2_hidden(k4_tarski(X6,X7),X1) ) )
            & ( ( r2_hidden(sK5(X0,X1,X6),X0)
                & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X1) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f19,f22,f21,f20])).

% (6568)Refutation not found, incomplete strategy% (6568)------------------------------
% (6568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6568)Termination reason: Refutation not found, incomplete strategy

% (6568)Memory used [KB]: 1791
% (6568)Time elapsed: 0.108 s
% (6568)------------------------------
% (6568)------------------------------
fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(X3,X4),X1) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X0)
                & r2_hidden(k4_tarski(X3,X5),X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X0)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X1) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X0)
              & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X1) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X0)
          & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X1) )
     => ( r2_hidden(sK4(X0,X1,X2),X0)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X0)
          & r2_hidden(k4_tarski(X6,X8),X1) )
     => ( r2_hidden(sK5(X0,X1,X6),X0)
        & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(X4,X0)
                  | ~ r2_hidden(k4_tarski(X3,X4),X1) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r2_hidden(X5,X0)
                  & r2_hidden(k4_tarski(X3,X5),X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r2_hidden(X7,X0)
                  | ~ r2_hidden(k4_tarski(X6,X7),X1) ) )
            & ( ? [X8] :
                  ( r2_hidden(X8,X0)
                  & r2_hidden(k4_tarski(X6,X8),X1) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f170,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_4 ),
    inference(resolution,[],[f168,f78])).

fof(f78,plain,(
    ! [X6,X7,X5] :
      ( ~ sP0(X7,k10_relat_1(k1_xboole_0,k1_xboole_0),X6)
      | ~ r2_hidden(X5,X6) ) ),
    inference(resolution,[],[f74,f32])).

fof(f32,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X1)
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    ! [X3] : ~ r2_hidden(X3,k10_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f72,f52])).

fof(f52,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f39,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

% (6547)Refutation not found, incomplete strategy% (6547)------------------------------
% (6547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6547)Termination reason: Refutation not found, incomplete strategy

% (6547)Memory used [KB]: 10618
% (6547)Time elapsed: 0.078 s
% (6547)------------------------------
% (6547)------------------------------
fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k10_relat_1(X1,k1_xboole_0)) ) ),
    inference(resolution,[],[f69,f38])).

fof(f38,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f11,f13,f12])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ sP1(X1)
      | ~ r2_hidden(X0,k10_relat_1(X1,k1_xboole_0)) ) ),
    inference(resolution,[],[f68,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0,k10_relat_1(X0,X1))
      | ~ sP1(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

% (6545)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(k1_xboole_0,X0,X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(trivial_inequality_removal,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ sP0(k1_xboole_0,X0,X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(superposition,[],[f59,f28])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_xboole_0(X2,k1_enumset1(sK5(X2,X3,X0),sK5(X2,X3,X0),sK5(X2,X3,X0))) != X2
      | ~ sP0(X2,X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f33,f48])).

fof(f33,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X0)
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f168,plain,
    ( ! [X6,X7] : sP0(X6,k10_relat_1(k1_xboole_0,X7),k1_xboole_0)
    | ~ spl6_4 ),
    inference(resolution,[],[f140,f119])).

fof(f119,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl6_4
  <=> ! [X1,X0] : ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f27,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f15])).

fof(f15,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

fof(f123,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl6_3 ),
    inference(resolution,[],[f121,f52])).

fof(f121,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl6_3 ),
    inference(resolution,[],[f116,f38])).

fof(f116,plain,
    ( ~ sP1(k1_xboole_0)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f120,plain,
    ( ~ spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f110,f118,f114])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))
      | ~ sP1(k1_xboole_0) ) ),
    inference(resolution,[],[f109,f49])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,k1_xboole_0,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(trivial_inequality_removal,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ sP0(X1,k1_xboole_0,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(superposition,[],[f60,f28])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_xboole_0(X3,k1_enumset1(k4_tarski(X0,sK5(X2,X3,X0)),k4_tarski(X0,sK5(X2,X3,X0)),k4_tarski(X0,sK5(X2,X3,X0)))) != X3
      | ~ sP0(X2,X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f32,f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:33:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (6548)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.49  % (6549)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (6568)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.50  % (6563)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.50  % (6557)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (6555)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.50  % (6553)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.50  % (6553)Refutation not found, incomplete strategy% (6553)------------------------------
% 0.22/0.50  % (6553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (6553)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (6553)Memory used [KB]: 10618
% 0.22/0.50  % (6553)Time elapsed: 0.101 s
% 0.22/0.50  % (6553)------------------------------
% 0.22/0.50  % (6553)------------------------------
% 0.22/0.50  % (6547)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (6555)Refutation not found, incomplete strategy% (6555)------------------------------
% 0.22/0.50  % (6555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (6555)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (6555)Memory used [KB]: 10618
% 0.22/0.50  % (6555)Time elapsed: 0.064 s
% 0.22/0.50  % (6555)------------------------------
% 0.22/0.50  % (6555)------------------------------
% 0.22/0.50  % (6551)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (6554)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (6550)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (6559)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (6569)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.51  % (6557)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f251,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f120,f123,f250])).
% 0.22/0.51  fof(f250,plain,(
% 0.22/0.51    ~spl6_3 | ~spl6_4),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f249])).
% 0.22/0.51  fof(f249,plain,(
% 0.22/0.51    $false | (~spl6_3 | ~spl6_4)),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f246])).
% 0.22/0.51  fof(f246,plain,(
% 0.22/0.51    k1_xboole_0 != k1_xboole_0 | (~spl6_3 | ~spl6_4)),
% 0.22/0.51    inference(superposition,[],[f27,f185])).
% 0.22/0.51  fof(f185,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | (~spl6_3 | ~spl6_4)),
% 0.22/0.51    inference(resolution,[],[f180,f126])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~sP0(X2,k1_xboole_0,X3) | k10_relat_1(k1_xboole_0,X2) = X3) ) | ~spl6_3),
% 0.22/0.51    inference(resolution,[],[f115,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~sP1(X0) | ~sP0(X1,X0,X2) | k10_relat_1(X0,X1) = X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k10_relat_1(X0,X1) != X2)) | ~sP1(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> sP0(X1,X0,X2)) | ~sP1(X0))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    sP1(k1_xboole_0) | ~spl6_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f114])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    spl6_3 <=> sP1(k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.51  fof(f180,plain,(
% 0.22/0.51    ( ! [X8] : (sP0(X8,k1_xboole_0,k1_xboole_0)) ) | ~spl6_4),
% 0.22/0.51    inference(resolution,[],[f170,f140])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),X1) | sP0(X0,X1,k1_xboole_0)) )),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f139])).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | sP0(X0,X1,k1_xboole_0) | r2_hidden(k4_tarski(sK3(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),X1)) )),
% 0.22/0.51    inference(superposition,[],[f63,f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k1_enumset1(sK3(X0,X1,X2),sK3(X0,X1,X2),sK3(X0,X1,X2))) != X2 | sP0(X0,X1,X2) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1)) )),
% 0.22/0.51    inference(resolution,[],[f35,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) != X0) )),
% 0.22/0.51    inference(definition_unfolding,[],[f44,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f29,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1) | sP0(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X1)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X0) | ~r2_hidden(k4_tarski(X6,X7),X1))) & ((r2_hidden(sK5(X0,X1,X6),X0) & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X1)) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f19,f22,f21,f20])).
% 0.22/0.51  % (6568)Refutation not found, incomplete strategy% (6568)------------------------------
% 0.22/0.51  % (6568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (6568)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (6568)Memory used [KB]: 1791
% 0.22/0.51  % (6568)Time elapsed: 0.108 s
% 0.22/0.51  % (6568)------------------------------
% 0.22/0.51  % (6568)------------------------------
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X1)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X0) & r2_hidden(k4_tarski(X3,X5),X1)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X1)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X0) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X1)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X0) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X1)) => (r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X1)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X0) & r2_hidden(k4_tarski(X6,X8),X1)) => (r2_hidden(sK5(X0,X1,X6),X0) & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X1)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X1)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X0) & r2_hidden(k4_tarski(X3,X5),X1)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X0) | ~r2_hidden(k4_tarski(X6,X7),X1))) & (? [X8] : (r2_hidden(X8,X0) & r2_hidden(k4_tarski(X6,X8),X1)) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.51    inference(rectify,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.51    inference(nnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0))))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl6_4),
% 0.22/0.51    inference(resolution,[],[f168,f78])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X6,X7,X5] : (~sP0(X7,k10_relat_1(k1_xboole_0,k1_xboole_0),X6) | ~r2_hidden(X5,X6)) )),
% 0.22/0.51    inference(resolution,[],[f74,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X6,X2,X0,X1] : (r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X1) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X3] : (~r2_hidden(X3,k10_relat_1(k1_xboole_0,k1_xboole_0))) )),
% 0.22/0.51    inference(resolution,[],[f72,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    v1_relat_1(k1_xboole_0)),
% 0.22/0.51    inference(superposition,[],[f39,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.51    inference(flattening,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.51  % (6547)Refutation not found, incomplete strategy% (6547)------------------------------
% 0.22/0.51  % (6547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (6547)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (6547)Memory used [KB]: 10618
% 0.22/0.51  % (6547)Time elapsed: 0.078 s
% 0.22/0.51  % (6547)------------------------------
% 0.22/0.51  % (6547)------------------------------
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,k10_relat_1(X1,k1_xboole_0))) )),
% 0.22/0.51    inference(resolution,[],[f69,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0] : (sP1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : (sP1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(definition_folding,[],[f11,f13,f12])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~sP1(X1) | ~r2_hidden(X0,k10_relat_1(X1,k1_xboole_0))) )),
% 0.22/0.52    inference(resolution,[],[f68,f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X0,X1] : (sP0(X1,X0,k10_relat_1(X0,X1)) | ~sP1(X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k10_relat_1(X0,X1) != X2 | ~sP1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  % (6545)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~sP0(k1_xboole_0,X0,X2) | ~r2_hidden(X1,X2)) )),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 != k1_xboole_0 | ~sP0(k1_xboole_0,X0,X2) | ~r2_hidden(X1,X2)) )),
% 0.22/0.52    inference(superposition,[],[f59,f28])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k4_xboole_0(X2,k1_enumset1(sK5(X2,X3,X0),sK5(X2,X3,X0),sK5(X2,X3,X0))) != X2 | ~sP0(X2,X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(resolution,[],[f33,f48])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X6,X2,X0,X1] : (r2_hidden(sK5(X0,X1,X6),X0) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f168,plain,(
% 0.22/0.52    ( ! [X6,X7] : (sP0(X6,k10_relat_1(k1_xboole_0,X7),k1_xboole_0)) ) | ~spl6_4),
% 0.22/0.52    inference(resolution,[],[f140,f119])).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))) ) | ~spl6_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f118])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    spl6_4 <=> ! [X1,X0] : ~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2)),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,negated_conjecture,(
% 0.22/0.52    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.52    inference(negated_conjecture,[],[f8])).
% 0.22/0.52  fof(f8,conjecture,(
% 0.22/0.52    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    spl6_3),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f122])).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    $false | spl6_3),
% 0.22/0.52    inference(resolution,[],[f121,f52])).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    ~v1_relat_1(k1_xboole_0) | spl6_3),
% 0.22/0.52    inference(resolution,[],[f116,f38])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    ~sP1(k1_xboole_0) | spl6_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f114])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    ~spl6_3 | spl6_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f110,f118,f114])).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) | ~sP1(k1_xboole_0)) )),
% 0.22/0.52    inference(resolution,[],[f109,f49])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~sP0(X1,k1_xboole_0,X2) | ~r2_hidden(X0,X2)) )),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f108])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 != k1_xboole_0 | ~sP0(X1,k1_xboole_0,X2) | ~r2_hidden(X0,X2)) )),
% 0.22/0.52    inference(superposition,[],[f60,f28])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k4_xboole_0(X3,k1_enumset1(k4_tarski(X0,sK5(X2,X3,X0)),k4_tarski(X0,sK5(X2,X3,X0)),k4_tarski(X0,sK5(X2,X3,X0)))) != X3 | ~sP0(X2,X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(resolution,[],[f32,f48])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (6557)------------------------------
% 0.22/0.52  % (6557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6545)Refutation not found, incomplete strategy% (6545)------------------------------
% 0.22/0.52  % (6545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6545)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (6545)Memory used [KB]: 1663
% 0.22/0.52  % (6545)Time elapsed: 0.100 s
% 0.22/0.52  % (6545)------------------------------
% 0.22/0.52  % (6545)------------------------------
% 0.22/0.52  % (6557)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (6557)Memory used [KB]: 6396
% 0.22/0.52  % (6557)Time elapsed: 0.095 s
% 0.22/0.52  % (6557)------------------------------
% 0.22/0.52  % (6557)------------------------------
% 0.22/0.52  % (6552)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (6558)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (6544)Success in time 0.149 s
%------------------------------------------------------------------------------
