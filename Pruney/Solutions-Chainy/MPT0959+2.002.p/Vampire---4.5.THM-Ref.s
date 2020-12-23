%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:05 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 280 expanded)
%              Number of leaves         :   26 (  85 expanded)
%              Depth                    :   17
%              Number of atoms          :  554 (1030 expanded)
%              Number of equality atoms :  153 ( 288 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f430,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f190,f419,f429])).

fof(f429,plain,(
    spl15_2 ),
    inference(avatar_contradiction_clause,[],[f428])).

fof(f428,plain,
    ( $false
    | spl15_2 ),
    inference(subsumption_resolution,[],[f427,f118])).

fof(f118,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f427,plain,
    ( ~ r1_tarski(sK4,sK4)
    | spl15_2 ),
    inference(subsumption_resolution,[],[f426,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(resolution,[],[f125,f124])).

fof(f124,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP3(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ( ( ( sK14(X0,X1,X2,X3) != X0
              & sK14(X0,X1,X2,X3) != X1
              & sK14(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK14(X0,X1,X2,X3),X3) )
          & ( sK14(X0,X1,X2,X3) = X0
            | sK14(X0,X1,X2,X3) = X1
            | sK14(X0,X1,X2,X3) = X2
            | r2_hidden(sK14(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f53,f54])).

fof(f54,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK14(X0,X1,X2,X3) != X0
            & sK14(X0,X1,X2,X3) != X1
            & sK14(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK14(X0,X1,X2,X3),X3) )
        & ( sK14(X0,X1,X2,X3) = X0
          | sK14(X0,X1,X2,X3) = X1
          | sK14(X0,X1,X2,X3) = X2
          | r2_hidden(sK14(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP3(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP3(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP3(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP3(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X2,X1,X0,X3] :
      ( sP3(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f125,plain,(
    ! [X2,X0,X1] : sP3(X2,X1,X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X2,X1,X0,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f102,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP3(X2,X1,X0,X3) )
      & ( sP3(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP3(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f21,f27])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f426,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | ~ r1_tarski(sK4,sK4)
    | spl15_2 ),
    inference(duplicate_literal_removal,[],[f425])).

fof(f425,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | ~ r1_tarski(sK4,sK4)
    | spl15_2 ),
    inference(resolution,[],[f424,f196])).

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f68,f130])).

fof(f130,plain,(
    ! [X0] : sP0(k1_wellord2(X0),X0) ),
    inference(subsumption_resolution,[],[f129,f58])).

fof(f58,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f129,plain,(
    ! [X0] :
      ( sP0(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f113,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f18,f23,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
            <=> r1_tarski(X2,X3) )
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        & k3_relat_1(X1) = X0 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(f113,plain,(
    ! [X0] :
      ( ~ sP1(X0,k1_wellord2(X0))
      | sP0(k1_wellord2(X0),X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | k1_wellord2(X0) != X1
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | k1_wellord2(X0) != X1 ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f68,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ sP0(X0,X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(k4_tarski(X4,X5),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ~ r1_tarski(sK7(X0,X1),sK8(X0,X1))
            | ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) )
          & ( r1_tarski(sK7(X0,X1),sK8(X0,X1))
            | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) )
          & r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X1) )
        | k3_relat_1(X0) != X1 )
      & ( ( ! [X4,X5] :
              ( ( ( r2_hidden(k4_tarski(X4,X5),X0)
                  | ~ r1_tarski(X4,X5) )
                & ( r1_tarski(X4,X5)
                  | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1) )
          & k3_relat_1(X0) = X1 )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X0) )
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ( ~ r1_tarski(sK7(X0,X1),sK8(X0,X1))
          | ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) )
        & ( r1_tarski(sK7(X0,X1),sK8(X0,X1))
          | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) )
        & r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( r1_tarski(X2,X3)
              | r2_hidden(k4_tarski(X2,X3),X0) )
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) )
        | k3_relat_1(X0) != X1 )
      & ( ( ! [X4,X5] :
              ( ( ( r2_hidden(k4_tarski(X4,X5),X0)
                  | ~ r1_tarski(X4,X5) )
                & ( r1_tarski(X4,X5)
                  | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1) )
          & k3_relat_1(X0) = X1 )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2,X3] :
            ( ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( r1_tarski(X2,X3)
              | r2_hidden(k4_tarski(X2,X3),X1) )
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | k3_relat_1(X1) != X0 )
      & ( ( ! [X2,X3] :
              ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                  | ~ r1_tarski(X2,X3) )
                & ( r1_tarski(X2,X3)
                  | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2,X3] :
            ( ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( r1_tarski(X2,X3)
              | r2_hidden(k4_tarski(X2,X3),X1) )
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | k3_relat_1(X1) != X0 )
      & ( ( ! [X2,X3] :
              ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                  | ~ r1_tarski(X2,X3) )
                & ( r1_tarski(X2,X3)
                  | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f424,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK4),k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)))
    | spl15_2 ),
    inference(resolution,[],[f422,f301])).

fof(f301,plain,(
    ! [X43,X44,X42] :
      ( r1_tarski(k2_zfmisc_1(k2_enumset1(X42,X42,X42,X42),k2_enumset1(X43,X43,X43,X43)),X44)
      | ~ r2_hidden(k4_tarski(X42,X43),X44) ) ),
    inference(superposition,[],[f107,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f81,f104,f105,f104])).

fof(f105,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f104])).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f104,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f63,f79])).

fof(f63,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f81,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f78,f105])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

% (31963)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f422,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)),k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)))
    | spl15_2 ),
    inference(forward_demodulation,[],[f188,f109])).

fof(f188,plain,
    ( ~ r1_tarski(k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4)),k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)))
    | spl15_2 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl15_2
  <=> r1_tarski(k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4)),k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f419,plain,(
    spl15_1 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | spl15_1 ),
    inference(resolution,[],[f411,f286])).

fof(f286,plain,
    ( ~ r1_tarski(k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)),k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)))
    | spl15_1 ),
    inference(backward_demodulation,[],[f184,f109])).

fof(f184,plain,
    ( ~ r1_tarski(k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4)))
    | spl15_1 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl15_1
  <=> r1_tarski(k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f411,plain,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(duplicate_literal_removal,[],[f404])).

fof(f404,plain,(
    ! [X0] :
      ( r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))
      | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ) ),
    inference(resolution,[],[f403,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(k1_wellord2(X0),X1),X0)
      | r1_tarski(k1_wellord2(X0),X1) ) ),
    inference(subsumption_resolution,[],[f157,f58])).

fof(f157,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(k1_wellord2(X0),X1),X0)
      | ~ v1_relat_1(k1_wellord2(X0))
      | r1_tarski(k1_wellord2(X0),X1) ) ),
    inference(superposition,[],[f155,f131])).

fof(f131,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(resolution,[],[f130,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k3_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f155,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK5(X2,X3),k3_relat_1(X2))
      | ~ v1_relat_1(X2)
      | r1_tarski(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f154])).

fof(f154,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,X3)
      | ~ v1_relat_1(X2)
      | r2_hidden(sK5(X2,X3),k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f61,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(f403,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(k1_wellord2(X0),k2_zfmisc_1(X1,X0)),X1)
      | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X0)) ) ),
    inference(subsumption_resolution,[],[f402,f58])).

fof(f402,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(k1_wellord2(X0),k2_zfmisc_1(X1,X0)),X1)
      | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f395])).

fof(f395,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(k1_wellord2(X0),k2_zfmisc_1(X1,X0)),X1)
      | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X0))
      | ~ v1_relat_1(k1_wellord2(X0))
      | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X0)) ) ),
    inference(resolution,[],[f172,f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(k1_wellord2(X0),X1),X0)
      | r1_tarski(k1_wellord2(X0),X1) ) ),
    inference(subsumption_resolution,[],[f161,f58])).

fof(f161,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(k1_wellord2(X0),X1),X0)
      | ~ v1_relat_1(k1_wellord2(X0))
      | r1_tarski(k1_wellord2(X0),X1) ) ),
    inference(superposition,[],[f156,f131])).

fof(f156,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK6(X0,X1),k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f61,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f172,plain,(
    ! [X14,X15,X13] :
      ( ~ r2_hidden(sK6(X13,k2_zfmisc_1(X14,X15)),X15)
      | ~ r2_hidden(sK5(X13,k2_zfmisc_1(X14,X15)),X14)
      | r1_tarski(X13,k2_zfmisc_1(X14,X15))
      | ~ v1_relat_1(X13) ) ),
    inference(resolution,[],[f168,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f168,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1))
      | ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f120,f121])).

fof(f121,plain,(
    ! [X0,X1] : sP2(X1,X0,k2_zfmisc_1(X0,X1)) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,X0,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ~ sP2(X1,X0,X2) )
      & ( sP2(X1,X0,X2)
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> sP2(X1,X0,X2) ) ),
    inference(definition_folding,[],[f6,f25])).

fof(f25,plain,(
    ! [X1,X0,X2] :
      ( sP2(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f120,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X10,X0)
      | ~ r2_hidden(X9,X1)
      | r2_hidden(k4_tarski(X9,X10),X2) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X0)
      | ~ r2_hidden(X9,X1)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK9(X0,X1,X2)
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X1) )
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( ( sK9(X0,X1,X2) = k4_tarski(sK10(X0,X1,X2),sK11(X0,X1,X2))
              & r2_hidden(sK11(X0,X1,X2),X0)
              & r2_hidden(sK10(X0,X1,X2),X1) )
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X0)
                  | ~ r2_hidden(X9,X1) ) )
            & ( ( k4_tarski(sK12(X0,X1,X8),sK13(X0,X1,X8)) = X8
                & r2_hidden(sK13(X0,X1,X8),X0)
                & r2_hidden(sK12(X0,X1,X8),X1) )
              | ~ r2_hidden(X8,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12,sK13])],[f45,f48,f47,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X0)
                & r2_hidden(X6,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK9(X0,X1,X2)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X1) )
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK9(X0,X1,X2)
              & r2_hidden(X7,X0)
              & r2_hidden(X6,X1) )
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK9(X0,X1,X2)
          & r2_hidden(X7,X0)
          & r2_hidden(X6,X1) )
     => ( sK9(X0,X1,X2) = k4_tarski(sK10(X0,X1,X2),sK11(X0,X1,X2))
        & r2_hidden(sK11(X0,X1,X2),X0)
        & r2_hidden(sK10(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X0)
          & r2_hidden(X11,X1) )
     => ( k4_tarski(sK12(X0,X1,X8),sK13(X0,X1,X8)) = X8
        & r2_hidden(sK13(X0,X1,X8),X0)
        & r2_hidden(sK12(X0,X1,X8),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X0)
                  | ~ r2_hidden(X4,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X0)
                  & r2_hidden(X6,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X0)
                  | ~ r2_hidden(X9,X1) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X0)
                  & r2_hidden(X11,X1) )
              | ~ r2_hidden(X8,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f190,plain,
    ( ~ spl15_2
    | ~ spl15_1 ),
    inference(avatar_split_clause,[],[f180,f182,f186])).

fof(f180,plain,
    ( ~ r1_tarski(k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4)))
    | ~ r1_tarski(k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4)),k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(extensionality_resolution,[],[f76,f106])).

fof(f106,plain,(
    k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)) != k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4)) ),
    inference(definition_unfolding,[],[f57,f105,f105])).

% (31961)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f57,plain,(
    k1_wellord2(k1_tarski(sK4)) != k1_tarski(k4_tarski(sK4,sK4)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    k1_wellord2(k1_tarski(sK4)) != k1_tarski(k4_tarski(sK4,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f29])).

fof(f29,plain,
    ( ? [X0] : k1_wellord2(k1_tarski(X0)) != k1_tarski(k4_tarski(X0,X0))
   => k1_wellord2(k1_tarski(sK4)) != k1_tarski(k4_tarski(sK4,sK4)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] : k1_wellord2(k1_tarski(X0)) != k1_tarski(k4_tarski(X0,X0)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] : k1_wellord2(k1_tarski(X0)) = k1_tarski(k4_tarski(X0,X0)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] : k1_wellord2(k1_tarski(X0)) = k1_tarski(k4_tarski(X0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_wellord2)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:19:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (31953)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.49  % (31969)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (31969)Refutation not found, incomplete strategy% (31969)------------------------------
% 0.21/0.49  % (31969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (31969)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (31969)Memory used [KB]: 1663
% 0.21/0.49  % (31969)Time elapsed: 0.070 s
% 0.21/0.49  % (31969)------------------------------
% 0.21/0.49  % (31969)------------------------------
% 0.21/0.53  % (31942)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (31943)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.31/0.53  % (31962)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.31/0.54  % (31940)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.31/0.54  % (31958)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.31/0.54  % (31958)Refutation not found, incomplete strategy% (31958)------------------------------
% 1.31/0.54  % (31958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (31958)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (31958)Memory used [KB]: 1791
% 1.31/0.54  % (31958)Time elapsed: 0.119 s
% 1.31/0.54  % (31958)------------------------------
% 1.31/0.54  % (31958)------------------------------
% 1.31/0.54  % (31944)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.31/0.55  % (31954)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.31/0.55  % (31945)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.31/0.55  % (31954)Refutation not found, incomplete strategy% (31954)------------------------------
% 1.31/0.55  % (31954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (31954)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (31954)Memory used [KB]: 1791
% 1.31/0.55  % (31954)Time elapsed: 0.086 s
% 1.31/0.55  % (31954)------------------------------
% 1.31/0.55  % (31954)------------------------------
% 1.31/0.55  % (31965)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.31/0.55  % (31946)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.55  % (31964)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.42/0.55  % (31950)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.42/0.55  % (31957)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.42/0.55  % (31950)Refutation not found, incomplete strategy% (31950)------------------------------
% 1.42/0.55  % (31950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (31950)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (31950)Memory used [KB]: 10746
% 1.42/0.55  % (31950)Time elapsed: 0.130 s
% 1.42/0.55  % (31950)------------------------------
% 1.42/0.55  % (31950)------------------------------
% 1.42/0.56  % (31941)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.42/0.56  % (31941)Refutation not found, incomplete strategy% (31941)------------------------------
% 1.42/0.56  % (31941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (31941)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (31941)Memory used [KB]: 1663
% 1.42/0.56  % (31941)Time elapsed: 0.141 s
% 1.42/0.56  % (31941)------------------------------
% 1.42/0.56  % (31941)------------------------------
% 1.42/0.56  % (31951)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.42/0.56  % (31949)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.42/0.56  % (31966)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.42/0.56  % (31956)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.42/0.56  % (31956)Refutation not found, incomplete strategy% (31956)------------------------------
% 1.42/0.56  % (31956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (31948)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.42/0.57  % (31955)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.42/0.57  % (31952)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.42/0.57  % (31964)Refutation not found, incomplete strategy% (31964)------------------------------
% 1.42/0.57  % (31964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (31964)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (31964)Memory used [KB]: 10746
% 1.42/0.57  % (31964)Time elapsed: 0.159 s
% 1.42/0.57  % (31964)------------------------------
% 1.42/0.57  % (31964)------------------------------
% 1.42/0.57  % (31959)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.42/0.57  % (31966)Refutation not found, incomplete strategy% (31966)------------------------------
% 1.42/0.57  % (31966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (31966)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (31966)Memory used [KB]: 6268
% 1.42/0.57  % (31966)Time elapsed: 0.150 s
% 1.42/0.57  % (31966)------------------------------
% 1.42/0.57  % (31966)------------------------------
% 1.42/0.57  % (31952)Refutation not found, incomplete strategy% (31952)------------------------------
% 1.42/0.57  % (31952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (31952)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (31952)Memory used [KB]: 10618
% 1.42/0.57  % (31952)Time elapsed: 0.161 s
% 1.42/0.57  % (31952)------------------------------
% 1.42/0.57  % (31952)------------------------------
% 1.42/0.57  % (31956)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (31956)Memory used [KB]: 10746
% 1.42/0.57  % (31956)Time elapsed: 0.150 s
% 1.42/0.57  % (31956)------------------------------
% 1.42/0.57  % (31956)------------------------------
% 1.42/0.57  % (31968)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.42/0.57  % (31960)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.42/0.58  % (31957)Refutation not found, incomplete strategy% (31957)------------------------------
% 1.42/0.58  % (31957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.58  % (31957)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.58  
% 1.42/0.58  % (31957)Memory used [KB]: 1791
% 1.42/0.58  % (31957)Time elapsed: 0.169 s
% 1.42/0.58  % (31957)------------------------------
% 1.42/0.58  % (31957)------------------------------
% 1.42/0.58  % (31968)Refutation not found, incomplete strategy% (31968)------------------------------
% 1.42/0.58  % (31968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.58  % (31967)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.42/0.58  % (31947)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.42/0.58  % (31968)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.58  
% 1.42/0.58  % (31968)Memory used [KB]: 10746
% 1.42/0.58  % (31968)Time elapsed: 0.169 s
% 1.42/0.58  % (31968)------------------------------
% 1.42/0.58  % (31968)------------------------------
% 1.42/0.59  % (31967)Refutation not found, incomplete strategy% (31967)------------------------------
% 1.42/0.59  % (31967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.59  % (31967)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.59  
% 1.42/0.59  % (31967)Memory used [KB]: 6268
% 1.42/0.59  % (31967)Time elapsed: 0.180 s
% 1.42/0.59  % (31967)------------------------------
% 1.42/0.59  % (31967)------------------------------
% 1.42/0.59  % (31946)Refutation found. Thanks to Tanya!
% 1.42/0.59  % SZS status Theorem for theBenchmark
% 1.42/0.59  % SZS output start Proof for theBenchmark
% 1.42/0.59  fof(f430,plain,(
% 1.42/0.59    $false),
% 1.42/0.59    inference(avatar_sat_refutation,[],[f190,f419,f429])).
% 1.42/0.59  fof(f429,plain,(
% 1.42/0.59    spl15_2),
% 1.42/0.59    inference(avatar_contradiction_clause,[],[f428])).
% 1.42/0.59  fof(f428,plain,(
% 1.42/0.59    $false | spl15_2),
% 1.42/0.59    inference(subsumption_resolution,[],[f427,f118])).
% 1.42/0.59  fof(f118,plain,(
% 1.42/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.42/0.59    inference(equality_resolution,[],[f75])).
% 1.42/0.59  fof(f75,plain,(
% 1.42/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.42/0.59    inference(cnf_transformation,[],[f42])).
% 1.42/0.59  fof(f42,plain,(
% 1.42/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.42/0.59    inference(flattening,[],[f41])).
% 1.42/0.59  fof(f41,plain,(
% 1.42/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.42/0.59    inference(nnf_transformation,[],[f1])).
% 1.42/0.59  fof(f1,axiom,(
% 1.42/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.42/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.42/0.59  fof(f427,plain,(
% 1.42/0.59    ~r1_tarski(sK4,sK4) | spl15_2),
% 1.42/0.59    inference(subsumption_resolution,[],[f426,f134])).
% 1.42/0.59  fof(f134,plain,(
% 1.42/0.59    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_enumset1(X0,X0,X1,X2))) )),
% 1.42/0.59    inference(resolution,[],[f125,f124])).
% 1.42/0.59  fof(f124,plain,(
% 1.42/0.59    ( ! [X0,X5,X3,X1] : (~sP3(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 1.42/0.59    inference(equality_resolution,[],[f95])).
% 1.42/0.59  fof(f95,plain,(
% 1.42/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP3(X0,X1,X2,X3)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f55])).
% 1.42/0.59  fof(f55,plain,(
% 1.42/0.59    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | (((sK14(X0,X1,X2,X3) != X0 & sK14(X0,X1,X2,X3) != X1 & sK14(X0,X1,X2,X3) != X2) | ~r2_hidden(sK14(X0,X1,X2,X3),X3)) & (sK14(X0,X1,X2,X3) = X0 | sK14(X0,X1,X2,X3) = X1 | sK14(X0,X1,X2,X3) = X2 | r2_hidden(sK14(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP3(X0,X1,X2,X3)))),
% 1.42/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f53,f54])).
% 1.42/0.59  fof(f54,plain,(
% 1.42/0.59    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK14(X0,X1,X2,X3) != X0 & sK14(X0,X1,X2,X3) != X1 & sK14(X0,X1,X2,X3) != X2) | ~r2_hidden(sK14(X0,X1,X2,X3),X3)) & (sK14(X0,X1,X2,X3) = X0 | sK14(X0,X1,X2,X3) = X1 | sK14(X0,X1,X2,X3) = X2 | r2_hidden(sK14(X0,X1,X2,X3),X3))))),
% 1.42/0.59    introduced(choice_axiom,[])).
% 1.42/0.59  fof(f53,plain,(
% 1.42/0.59    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP3(X0,X1,X2,X3)))),
% 1.42/0.59    inference(rectify,[],[f52])).
% 1.42/0.59  fof(f52,plain,(
% 1.42/0.59    ! [X2,X1,X0,X3] : ((sP3(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP3(X2,X1,X0,X3)))),
% 1.42/0.59    inference(flattening,[],[f51])).
% 1.42/0.59  fof(f51,plain,(
% 1.42/0.59    ! [X2,X1,X0,X3] : ((sP3(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP3(X2,X1,X0,X3)))),
% 1.42/0.59    inference(nnf_transformation,[],[f27])).
% 1.42/0.59  fof(f27,plain,(
% 1.42/0.59    ! [X2,X1,X0,X3] : (sP3(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.42/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.42/0.59  fof(f125,plain,(
% 1.42/0.59    ( ! [X2,X0,X1] : (sP3(X2,X1,X0,k2_enumset1(X0,X0,X1,X2))) )),
% 1.42/0.59    inference(equality_resolution,[],[f112])).
% 1.42/0.59  fof(f112,plain,(
% 1.42/0.59    ( ! [X2,X0,X3,X1] : (sP3(X2,X1,X0,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.42/0.59    inference(definition_unfolding,[],[f102,f79])).
% 1.42/0.59  fof(f79,plain,(
% 1.42/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f5])).
% 1.42/0.59  fof(f5,axiom,(
% 1.42/0.59    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.42/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.42/0.59  fof(f102,plain,(
% 1.42/0.59    ( ! [X2,X0,X3,X1] : (sP3(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.42/0.59    inference(cnf_transformation,[],[f56])).
% 1.42/0.59  fof(f56,plain,(
% 1.42/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP3(X2,X1,X0,X3)) & (sP3(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.42/0.59    inference(nnf_transformation,[],[f28])).
% 1.42/0.59  fof(f28,plain,(
% 1.42/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP3(X2,X1,X0,X3))),
% 1.42/0.59    inference(definition_folding,[],[f21,f27])).
% 1.42/0.59  fof(f21,plain,(
% 1.42/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.42/0.59    inference(ennf_transformation,[],[f2])).
% 1.42/0.59  fof(f2,axiom,(
% 1.42/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.42/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.42/0.59  fof(f426,plain,(
% 1.42/0.59    ~r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) | ~r1_tarski(sK4,sK4) | spl15_2),
% 1.42/0.59    inference(duplicate_literal_removal,[],[f425])).
% 1.42/0.59  fof(f425,plain,(
% 1.42/0.59    ~r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) | ~r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) | ~r1_tarski(sK4,sK4) | spl15_2),
% 1.42/0.59    inference(resolution,[],[f424,f196])).
% 1.42/0.59  fof(f196,plain,(
% 1.42/0.59    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.42/0.59    inference(resolution,[],[f68,f130])).
% 1.42/0.59  fof(f130,plain,(
% 1.42/0.59    ( ! [X0] : (sP0(k1_wellord2(X0),X0)) )),
% 1.42/0.59    inference(subsumption_resolution,[],[f129,f58])).
% 1.42/0.59  fof(f58,plain,(
% 1.42/0.59    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 1.42/0.59    inference(cnf_transformation,[],[f12])).
% 1.42/0.59  fof(f12,axiom,(
% 1.42/0.59    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 1.42/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 1.42/0.59  fof(f129,plain,(
% 1.42/0.59    ( ! [X0] : (sP0(k1_wellord2(X0),X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 1.42/0.59    inference(resolution,[],[f113,f73])).
% 1.42/0.59  fof(f73,plain,(
% 1.42/0.59    ( ! [X0,X1] : (sP1(X0,X1) | ~v1_relat_1(X1)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f24])).
% 1.42/0.59  fof(f24,plain,(
% 1.42/0.59    ! [X0,X1] : (sP1(X0,X1) | ~v1_relat_1(X1))),
% 1.42/0.59    inference(definition_folding,[],[f18,f23,f22])).
% 1.42/0.59  fof(f22,plain,(
% 1.42/0.59    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0))),
% 1.42/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.42/0.59  fof(f23,plain,(
% 1.42/0.59    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 1.42/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.42/0.59  fof(f18,plain,(
% 1.42/0.59    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 1.42/0.59    inference(flattening,[],[f17])).
% 1.42/0.59  fof(f17,plain,(
% 1.42/0.59    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 1.42/0.59    inference(ennf_transformation,[],[f11])).
% 1.42/0.59  fof(f11,axiom,(
% 1.42/0.59    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 1.42/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 1.42/0.59  fof(f113,plain,(
% 1.42/0.59    ( ! [X0] : (~sP1(X0,k1_wellord2(X0)) | sP0(k1_wellord2(X0),X0)) )),
% 1.42/0.59    inference(equality_resolution,[],[f64])).
% 1.42/0.59  fof(f64,plain,(
% 1.42/0.59    ( ! [X0,X1] : (sP0(X1,X0) | k1_wellord2(X0) != X1 | ~sP1(X0,X1)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f35])).
% 1.42/0.59  fof(f35,plain,(
% 1.42/0.59    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ~sP0(X1,X0)) & (sP0(X1,X0) | k1_wellord2(X0) != X1)) | ~sP1(X0,X1))),
% 1.42/0.59    inference(nnf_transformation,[],[f23])).
% 1.42/0.59  fof(f68,plain,(
% 1.42/0.59    ( ! [X4,X0,X5,X1] : (~sP0(X0,X1) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | r2_hidden(k4_tarski(X4,X5),X0)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f40])).
% 1.42/0.59  fof(f40,plain,(
% 1.42/0.59    ! [X0,X1] : ((sP0(X0,X1) | ((~r1_tarski(sK7(X0,X1),sK8(X0,X1)) | ~r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)) & (r1_tarski(sK7(X0,X1),sK8(X0,X1)) | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)) & r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK7(X0,X1),X1)) | k3_relat_1(X0) != X1) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X0))) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) & k3_relat_1(X0) = X1) | ~sP0(X0,X1)))),
% 1.42/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f38,f39])).
% 1.42/0.59  fof(f39,plain,(
% 1.42/0.59    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X0)) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => ((~r1_tarski(sK7(X0,X1),sK8(X0,X1)) | ~r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)) & (r1_tarski(sK7(X0,X1),sK8(X0,X1)) | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)) & r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK7(X0,X1),X1)))),
% 1.42/0.59    introduced(choice_axiom,[])).
% 1.42/0.59  fof(f38,plain,(
% 1.42/0.59    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X0)) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) | k3_relat_1(X0) != X1) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X0))) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) & k3_relat_1(X0) = X1) | ~sP0(X0,X1)))),
% 1.42/0.59    inference(rectify,[],[f37])).
% 1.42/0.59  fof(f37,plain,(
% 1.42/0.59    ! [X1,X0] : ((sP0(X1,X0) | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | ~sP0(X1,X0)))),
% 1.42/0.59    inference(flattening,[],[f36])).
% 1.42/0.59  fof(f36,plain,(
% 1.42/0.59    ! [X1,X0] : ((sP0(X1,X0) | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | ~sP0(X1,X0)))),
% 1.42/0.59    inference(nnf_transformation,[],[f22])).
% 1.42/0.59  fof(f424,plain,(
% 1.42/0.59    ~r2_hidden(k4_tarski(sK4,sK4),k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4))) | spl15_2),
% 1.42/0.59    inference(resolution,[],[f422,f301])).
% 1.42/0.59  fof(f301,plain,(
% 1.42/0.59    ( ! [X43,X44,X42] : (r1_tarski(k2_zfmisc_1(k2_enumset1(X42,X42,X42,X42),k2_enumset1(X43,X43,X43,X43)),X44) | ~r2_hidden(k4_tarski(X42,X43),X44)) )),
% 1.42/0.59    inference(superposition,[],[f107,f109])).
% 1.42/0.59  fof(f109,plain,(
% 1.42/0.59    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 1.42/0.59    inference(definition_unfolding,[],[f81,f104,f105,f104])).
% 1.42/0.59  fof(f105,plain,(
% 1.42/0.59    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.42/0.59    inference(definition_unfolding,[],[f59,f104])).
% 1.42/0.59  fof(f59,plain,(
% 1.42/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f3])).
% 1.42/0.59  fof(f3,axiom,(
% 1.42/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.42/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.42/0.59  fof(f104,plain,(
% 1.42/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.42/0.59    inference(definition_unfolding,[],[f63,f79])).
% 1.42/0.59  fof(f63,plain,(
% 1.42/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f4])).
% 1.42/0.59  fof(f4,axiom,(
% 1.42/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.42/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.42/0.59  fof(f81,plain,(
% 1.42/0.59    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 1.42/0.59    inference(cnf_transformation,[],[f8])).
% 1.42/0.59  fof(f8,axiom,(
% 1.42/0.59    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 1.42/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 1.42/0.59  fof(f107,plain,(
% 1.42/0.59    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.42/0.59    inference(definition_unfolding,[],[f78,f105])).
% 1.42/0.59  fof(f78,plain,(
% 1.42/0.59    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f43])).
% 1.42/0.59  fof(f43,plain,(
% 1.42/0.59    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.42/0.59    inference(nnf_transformation,[],[f7])).
% 1.42/0.59  % (31963)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.42/0.59  fof(f7,axiom,(
% 1.42/0.59    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.42/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.42/0.59  fof(f422,plain,(
% 1.42/0.59    ~r1_tarski(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)),k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4))) | spl15_2),
% 1.42/0.59    inference(forward_demodulation,[],[f188,f109])).
% 1.42/0.59  fof(f188,plain,(
% 1.42/0.59    ~r1_tarski(k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4)),k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4))) | spl15_2),
% 1.42/0.59    inference(avatar_component_clause,[],[f186])).
% 1.42/0.59  fof(f186,plain,(
% 1.42/0.59    spl15_2 <=> r1_tarski(k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4)),k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)))),
% 1.42/0.59    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).
% 1.42/0.59  fof(f419,plain,(
% 1.42/0.59    spl15_1),
% 1.42/0.59    inference(avatar_contradiction_clause,[],[f416])).
% 1.42/0.59  fof(f416,plain,(
% 1.42/0.59    $false | spl15_1),
% 1.42/0.59    inference(resolution,[],[f411,f286])).
% 1.42/0.59  fof(f286,plain,(
% 1.42/0.59    ~r1_tarski(k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)),k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4))) | spl15_1),
% 1.42/0.59    inference(backward_demodulation,[],[f184,f109])).
% 1.42/0.59  fof(f184,plain,(
% 1.42/0.59    ~r1_tarski(k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4))) | spl15_1),
% 1.42/0.59    inference(avatar_component_clause,[],[f182])).
% 1.42/0.59  fof(f182,plain,(
% 1.42/0.59    spl15_1 <=> r1_tarski(k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4)))),
% 1.42/0.59    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).
% 1.42/0.59  fof(f411,plain,(
% 1.42/0.59    ( ! [X0] : (r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))) )),
% 1.42/0.59    inference(duplicate_literal_removal,[],[f404])).
% 1.42/0.59  fof(f404,plain,(
% 1.42/0.59    ( ! [X0] : (r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))) )),
% 1.42/0.59    inference(resolution,[],[f403,f158])).
% 1.42/0.59  fof(f158,plain,(
% 1.42/0.59    ( ! [X0,X1] : (r2_hidden(sK5(k1_wellord2(X0),X1),X0) | r1_tarski(k1_wellord2(X0),X1)) )),
% 1.42/0.59    inference(subsumption_resolution,[],[f157,f58])).
% 1.42/0.59  fof(f157,plain,(
% 1.42/0.59    ( ! [X0,X1] : (r2_hidden(sK5(k1_wellord2(X0),X1),X0) | ~v1_relat_1(k1_wellord2(X0)) | r1_tarski(k1_wellord2(X0),X1)) )),
% 1.42/0.59    inference(superposition,[],[f155,f131])).
% 1.42/0.59  fof(f131,plain,(
% 1.42/0.59    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 1.42/0.59    inference(resolution,[],[f130,f66])).
% 1.42/0.59  fof(f66,plain,(
% 1.42/0.59    ( ! [X0,X1] : (~sP0(X0,X1) | k3_relat_1(X0) = X1) )),
% 1.42/0.59    inference(cnf_transformation,[],[f40])).
% 1.42/0.59  fof(f155,plain,(
% 1.42/0.59    ( ! [X2,X3] : (r2_hidden(sK5(X2,X3),k3_relat_1(X2)) | ~v1_relat_1(X2) | r1_tarski(X2,X3)) )),
% 1.42/0.59    inference(duplicate_literal_removal,[],[f154])).
% 1.42/0.59  fof(f154,plain,(
% 1.42/0.59    ( ! [X2,X3] : (r1_tarski(X2,X3) | ~v1_relat_1(X2) | r2_hidden(sK5(X2,X3),k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.42/0.59    inference(resolution,[],[f61,f82])).
% 1.42/0.59  fof(f82,plain,(
% 1.42/0.59    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f20])).
% 1.42/0.59  fof(f20,plain,(
% 1.42/0.59    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 1.42/0.59    inference(flattening,[],[f19])).
% 1.42/0.59  fof(f19,plain,(
% 1.42/0.59    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 1.42/0.59    inference(ennf_transformation,[],[f10])).
% 1.42/0.59  fof(f10,axiom,(
% 1.42/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 1.42/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).
% 1.42/0.59  fof(f61,plain,(
% 1.42/0.59    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f34])).
% 1.42/0.59  fof(f34,plain,(
% 1.42/0.59    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 1.42/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f32,f33])).
% 1.42/0.59  fof(f33,plain,(
% 1.42/0.59    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)))),
% 1.42/0.59    introduced(choice_axiom,[])).
% 1.42/0.59  fof(f32,plain,(
% 1.42/0.59    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 1.42/0.59    inference(rectify,[],[f31])).
% 1.42/0.59  fof(f31,plain,(
% 1.42/0.59    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 1.42/0.59    inference(nnf_transformation,[],[f16])).
% 1.42/0.59  fof(f16,plain,(
% 1.42/0.59    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 1.42/0.59    inference(ennf_transformation,[],[f9])).
% 1.42/0.59  fof(f9,axiom,(
% 1.42/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 1.42/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).
% 1.42/0.59  fof(f403,plain,(
% 1.42/0.59    ( ! [X0,X1] : (~r2_hidden(sK5(k1_wellord2(X0),k2_zfmisc_1(X1,X0)),X1) | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X0))) )),
% 1.42/0.59    inference(subsumption_resolution,[],[f402,f58])).
% 1.42/0.59  fof(f402,plain,(
% 1.42/0.59    ( ! [X0,X1] : (~r2_hidden(sK5(k1_wellord2(X0),k2_zfmisc_1(X1,X0)),X1) | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 1.42/0.59    inference(duplicate_literal_removal,[],[f395])).
% 1.42/0.59  fof(f395,plain,(
% 1.42/0.59    ( ! [X0,X1] : (~r2_hidden(sK5(k1_wellord2(X0),k2_zfmisc_1(X1,X0)),X1) | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X0)) | ~v1_relat_1(k1_wellord2(X0)) | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X0))) )),
% 1.42/0.59    inference(resolution,[],[f172,f162])).
% 1.42/0.59  fof(f162,plain,(
% 1.42/0.59    ( ! [X0,X1] : (r2_hidden(sK6(k1_wellord2(X0),X1),X0) | r1_tarski(k1_wellord2(X0),X1)) )),
% 1.42/0.59    inference(subsumption_resolution,[],[f161,f58])).
% 1.42/0.59  fof(f161,plain,(
% 1.42/0.59    ( ! [X0,X1] : (r2_hidden(sK6(k1_wellord2(X0),X1),X0) | ~v1_relat_1(k1_wellord2(X0)) | r1_tarski(k1_wellord2(X0),X1)) )),
% 1.42/0.59    inference(superposition,[],[f156,f131])).
% 1.42/0.59  fof(f156,plain,(
% 1.42/0.59    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),k3_relat_1(X0)) | ~v1_relat_1(X0) | r1_tarski(X0,X1)) )),
% 1.42/0.59    inference(duplicate_literal_removal,[],[f153])).
% 1.42/0.59  fof(f153,plain,(
% 1.42/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_relat_1(X0) | r2_hidden(sK6(X0,X1),k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.42/0.59    inference(resolution,[],[f61,f83])).
% 1.42/0.59  fof(f83,plain,(
% 1.42/0.59    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f20])).
% 1.42/0.59  fof(f172,plain,(
% 1.42/0.59    ( ! [X14,X15,X13] : (~r2_hidden(sK6(X13,k2_zfmisc_1(X14,X15)),X15) | ~r2_hidden(sK5(X13,k2_zfmisc_1(X14,X15)),X14) | r1_tarski(X13,k2_zfmisc_1(X14,X15)) | ~v1_relat_1(X13)) )),
% 1.42/0.59    inference(resolution,[],[f168,f62])).
% 1.42/0.59  fof(f62,plain,(
% 1.42/0.59    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f34])).
% 1.42/0.59  fof(f168,plain,(
% 1.42/0.59    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) | ~r2_hidden(X2,X3) | ~r2_hidden(X0,X1)) )),
% 1.42/0.59    inference(resolution,[],[f120,f121])).
% 1.42/0.59  fof(f121,plain,(
% 1.42/0.59    ( ! [X0,X1] : (sP2(X1,X0,k2_zfmisc_1(X0,X1))) )),
% 1.42/0.59    inference(equality_resolution,[],[f92])).
% 1.42/0.59  fof(f92,plain,(
% 1.42/0.59    ( ! [X2,X0,X1] : (sP2(X1,X0,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.42/0.59    inference(cnf_transformation,[],[f50])).
% 1.42/0.59  fof(f50,plain,(
% 1.42/0.59    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ~sP2(X1,X0,X2)) & (sP2(X1,X0,X2) | k2_zfmisc_1(X0,X1) != X2))),
% 1.42/0.59    inference(nnf_transformation,[],[f26])).
% 1.42/0.59  fof(f26,plain,(
% 1.42/0.59    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> sP2(X1,X0,X2))),
% 1.42/0.59    inference(definition_folding,[],[f6,f25])).
% 1.42/0.59  fof(f25,plain,(
% 1.42/0.59    ! [X1,X0,X2] : (sP2(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.42/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.42/0.59  fof(f6,axiom,(
% 1.42/0.59    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.42/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.42/0.59  fof(f120,plain,(
% 1.42/0.59    ( ! [X2,X0,X10,X1,X9] : (~sP2(X0,X1,X2) | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1) | r2_hidden(k4_tarski(X9,X10),X2)) )),
% 1.42/0.59    inference(equality_resolution,[],[f87])).
% 1.42/0.59  fof(f87,plain,(
% 1.42/0.59    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1) | ~sP2(X0,X1,X2)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f49])).
% 1.42/0.59  fof(f49,plain,(
% 1.42/0.59    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((! [X4,X5] : (k4_tarski(X4,X5) != sK9(X0,X1,X2) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(sK9(X0,X1,X2),X2)) & ((sK9(X0,X1,X2) = k4_tarski(sK10(X0,X1,X2),sK11(X0,X1,X2)) & r2_hidden(sK11(X0,X1,X2),X0) & r2_hidden(sK10(X0,X1,X2),X1)) | r2_hidden(sK9(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1))) & ((k4_tarski(sK12(X0,X1,X8),sK13(X0,X1,X8)) = X8 & r2_hidden(sK13(X0,X1,X8),X0) & r2_hidden(sK12(X0,X1,X8),X1)) | ~r2_hidden(X8,X2))) | ~sP2(X0,X1,X2)))),
% 1.42/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12,sK13])],[f45,f48,f47,f46])).
% 1.42/0.59  fof(f46,plain,(
% 1.42/0.59    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK9(X0,X1,X2) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK9(X0,X1,X2) & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(sK9(X0,X1,X2),X2))))),
% 1.42/0.59    introduced(choice_axiom,[])).
% 1.42/0.59  fof(f47,plain,(
% 1.42/0.59    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK9(X0,X1,X2) & r2_hidden(X7,X0) & r2_hidden(X6,X1)) => (sK9(X0,X1,X2) = k4_tarski(sK10(X0,X1,X2),sK11(X0,X1,X2)) & r2_hidden(sK11(X0,X1,X2),X0) & r2_hidden(sK10(X0,X1,X2),X1)))),
% 1.42/0.59    introduced(choice_axiom,[])).
% 1.42/0.59  fof(f48,plain,(
% 1.42/0.59    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X0) & r2_hidden(X11,X1)) => (k4_tarski(sK12(X0,X1,X8),sK13(X0,X1,X8)) = X8 & r2_hidden(sK13(X0,X1,X8),X0) & r2_hidden(sK12(X0,X1,X8),X1)))),
% 1.42/0.59    introduced(choice_axiom,[])).
% 1.42/0.59  fof(f45,plain,(
% 1.42/0.59    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X0) & r2_hidden(X11,X1)) | ~r2_hidden(X8,X2))) | ~sP2(X0,X1,X2)))),
% 1.42/0.59    inference(rectify,[],[f44])).
% 1.42/0.59  fof(f44,plain,(
% 1.42/0.59    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 1.42/0.59    inference(nnf_transformation,[],[f25])).
% 1.42/0.59  fof(f190,plain,(
% 1.42/0.59    ~spl15_2 | ~spl15_1),
% 1.42/0.59    inference(avatar_split_clause,[],[f180,f182,f186])).
% 1.42/0.59  fof(f180,plain,(
% 1.42/0.59    ~r1_tarski(k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4))) | ~r1_tarski(k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4)),k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)))),
% 1.42/0.59    inference(extensionality_resolution,[],[f76,f106])).
% 1.42/0.59  fof(f106,plain,(
% 1.42/0.59    k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)) != k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4))),
% 1.42/0.59    inference(definition_unfolding,[],[f57,f105,f105])).
% 1.42/0.59  % (31961)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.42/0.59  fof(f57,plain,(
% 1.42/0.59    k1_wellord2(k1_tarski(sK4)) != k1_tarski(k4_tarski(sK4,sK4))),
% 1.42/0.59    inference(cnf_transformation,[],[f30])).
% 1.42/0.59  fof(f30,plain,(
% 1.42/0.59    k1_wellord2(k1_tarski(sK4)) != k1_tarski(k4_tarski(sK4,sK4))),
% 1.42/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f29])).
% 1.42/0.59  fof(f29,plain,(
% 1.42/0.59    ? [X0] : k1_wellord2(k1_tarski(X0)) != k1_tarski(k4_tarski(X0,X0)) => k1_wellord2(k1_tarski(sK4)) != k1_tarski(k4_tarski(sK4,sK4))),
% 1.42/0.59    introduced(choice_axiom,[])).
% 1.42/0.59  fof(f15,plain,(
% 1.42/0.59    ? [X0] : k1_wellord2(k1_tarski(X0)) != k1_tarski(k4_tarski(X0,X0))),
% 1.42/0.59    inference(ennf_transformation,[],[f14])).
% 1.42/0.59  fof(f14,negated_conjecture,(
% 1.42/0.59    ~! [X0] : k1_wellord2(k1_tarski(X0)) = k1_tarski(k4_tarski(X0,X0))),
% 1.42/0.59    inference(negated_conjecture,[],[f13])).
% 1.42/0.59  fof(f13,conjecture,(
% 1.42/0.59    ! [X0] : k1_wellord2(k1_tarski(X0)) = k1_tarski(k4_tarski(X0,X0))),
% 1.42/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_wellord2)).
% 1.42/0.59  fof(f76,plain,(
% 1.42/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.42/0.59    inference(cnf_transformation,[],[f42])).
% 1.42/0.59  % SZS output end Proof for theBenchmark
% 1.42/0.59  % (31946)------------------------------
% 1.42/0.59  % (31946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.59  % (31946)Termination reason: Refutation
% 1.42/0.59  
% 1.42/0.59  % (31946)Memory used [KB]: 11257
% 1.42/0.59  % (31946)Time elapsed: 0.136 s
% 1.42/0.59  % (31946)------------------------------
% 1.42/0.59  % (31946)------------------------------
% 1.42/0.59  % (31939)Success in time 0.223 s
%------------------------------------------------------------------------------
