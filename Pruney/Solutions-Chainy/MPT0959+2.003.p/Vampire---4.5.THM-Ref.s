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
% DateTime   : Thu Dec  3 13:00:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 279 expanded)
%              Number of leaves         :   26 (  84 expanded)
%              Depth                    :   17
%              Number of atoms          :  569 (1042 expanded)
%              Number of equality atoms :  153 ( 285 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f585,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f195,f437,f584])).

fof(f584,plain,(
    spl15_2 ),
    inference(avatar_contradiction_clause,[],[f583])).

fof(f583,plain,
    ( $false
    | spl15_2 ),
    inference(subsumption_resolution,[],[f582,f121])).

fof(f121,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f582,plain,
    ( ~ r1_tarski(sK4,sK4)
    | spl15_2 ),
    inference(subsumption_resolution,[],[f581,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(resolution,[],[f128,f127])).

fof(f127,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP3(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f54,f55])).

fof(f55,plain,(
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

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

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

fof(f128,plain,(
    ! [X2,X0,X1] : sP3(X2,X1,X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X2,X1,X0,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f104,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f581,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | ~ r1_tarski(sK4,sK4)
    | spl15_2 ),
    inference(duplicate_literal_removal,[],[f580])).

fof(f580,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | ~ r1_tarski(sK4,sK4)
    | spl15_2 ),
    inference(resolution,[],[f577,f201])).

fof(f201,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f69,f133])).

fof(f133,plain,(
    ! [X0] : sP0(k1_wellord2(X0),X0) ),
    inference(subsumption_resolution,[],[f132,f59])).

fof(f59,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f132,plain,(
    ! [X0] :
      ( sP0(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f116,f74])).

fof(f74,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f116,plain,(
    ! [X0] :
      ( ~ sP1(X0,k1_wellord2(X0))
      | sP0(k1_wellord2(X0),X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
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

fof(f69,plain,(
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

fof(f577,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK4),k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)))
    | spl15_2 ),
    inference(duplicate_literal_removal,[],[f566])).

fof(f566,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK4),k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)))
    | ~ r2_hidden(k4_tarski(sK4,sK4),k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)))
    | spl15_2 ),
    inference(resolution,[],[f307,f440])).

fof(f440,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)),k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)))
    | spl15_2 ),
    inference(forward_demodulation,[],[f193,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f80,f106,f107,f106])).

fof(f107,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f60,f106])).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f106,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f64,f78])).

fof(f64,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f80,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f193,plain,
    ( ~ r1_tarski(k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4)),k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)))
    | spl15_2 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl15_2
  <=> r1_tarski(k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4)),k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f307,plain,(
    ! [X47,X45,X46,X44] :
      ( r1_tarski(k2_zfmisc_1(k2_enumset1(X44,X44,X44,X46),k2_enumset1(X45,X45,X45,X45)),X47)
      | ~ r2_hidden(k4_tarski(X46,X45),X47)
      | ~ r2_hidden(k4_tarski(X44,X45),X47) ) ),
    inference(superposition,[],[f111,f109])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f95,f106])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f437,plain,(
    spl15_1 ),
    inference(avatar_contradiction_clause,[],[f434])).

fof(f434,plain,
    ( $false
    | spl15_1 ),
    inference(resolution,[],[f429,f292])).

fof(f292,plain,
    ( ~ r1_tarski(k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)),k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)))
    | spl15_1 ),
    inference(backward_demodulation,[],[f189,f109])).

fof(f189,plain,
    ( ~ r1_tarski(k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4)))
    | spl15_1 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl15_1
  <=> r1_tarski(k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f429,plain,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(duplicate_literal_removal,[],[f422])).

fof(f422,plain,(
    ! [X0] :
      ( r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))
      | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ) ),
    inference(resolution,[],[f421,f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(k1_wellord2(X0),X1),X0)
      | r1_tarski(k1_wellord2(X0),X1) ) ),
    inference(subsumption_resolution,[],[f164,f59])).

fof(f164,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(k1_wellord2(X0),X1),X0)
      | ~ v1_relat_1(k1_wellord2(X0))
      | r1_tarski(k1_wellord2(X0),X1) ) ),
    inference(superposition,[],[f160,f134])).

fof(f134,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(resolution,[],[f133,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k3_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f160,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK5(X2,X3),k3_relat_1(X2))
      | ~ v1_relat_1(X2)
      | r1_tarski(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,X3)
      | ~ v1_relat_1(X2)
      | r2_hidden(sK5(X2,X3),k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f62,f81])).

fof(f81,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(f62,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f421,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(k1_wellord2(X0),k2_zfmisc_1(X1,X0)),X1)
      | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X0)) ) ),
    inference(subsumption_resolution,[],[f420,f59])).

fof(f420,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(k1_wellord2(X0),k2_zfmisc_1(X1,X0)),X1)
      | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f413])).

fof(f413,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(k1_wellord2(X0),k2_zfmisc_1(X1,X0)),X1)
      | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X0))
      | ~ v1_relat_1(k1_wellord2(X0))
      | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X0)) ) ),
    inference(resolution,[],[f177,f167])).

fof(f167,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(k1_wellord2(X0),X1),X0)
      | r1_tarski(k1_wellord2(X0),X1) ) ),
    inference(subsumption_resolution,[],[f166,f59])).

fof(f166,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(k1_wellord2(X0),X1),X0)
      | ~ v1_relat_1(k1_wellord2(X0))
      | r1_tarski(k1_wellord2(X0),X1) ) ),
    inference(superposition,[],[f161,f134])).

fof(f161,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK6(X0,X1),k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f62,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f177,plain,(
    ! [X14,X15,X13] :
      ( ~ r2_hidden(sK6(X13,k2_zfmisc_1(X14,X15)),X15)
      | ~ r2_hidden(sK5(X13,k2_zfmisc_1(X14,X15)),X14)
      | r1_tarski(X13,k2_zfmisc_1(X14,X15))
      | ~ v1_relat_1(X13) ) ),
    inference(resolution,[],[f173,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f173,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1))
      | ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f123,f124])).

fof(f124,plain,(
    ! [X0,X1] : sP2(X1,X0,k2_zfmisc_1(X0,X1)) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,X0,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f123,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X10,X0)
      | ~ r2_hidden(X9,X1)
      | r2_hidden(k4_tarski(X9,X10),X2) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X0)
      | ~ r2_hidden(X9,X1)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12,sK13])],[f44,f47,f46,f45])).

fof(f45,plain,(
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

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK9(X0,X1,X2)
          & r2_hidden(X7,X0)
          & r2_hidden(X6,X1) )
     => ( sK9(X0,X1,X2) = k4_tarski(sK10(X0,X1,X2),sK11(X0,X1,X2))
        & r2_hidden(sK11(X0,X1,X2),X0)
        & r2_hidden(sK10(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X0)
          & r2_hidden(X11,X1) )
     => ( k4_tarski(sK12(X0,X1,X8),sK13(X0,X1,X8)) = X8
        & r2_hidden(sK13(X0,X1,X8),X0)
        & r2_hidden(sK12(X0,X1,X8),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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

fof(f195,plain,
    ( ~ spl15_2
    | ~ spl15_1 ),
    inference(avatar_split_clause,[],[f185,f187,f191])).

fof(f185,plain,
    ( ~ r1_tarski(k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4)))
    | ~ r1_tarski(k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4)),k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(extensionality_resolution,[],[f77,f108])).

fof(f108,plain,(
    k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)) != k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4)) ),
    inference(definition_unfolding,[],[f58,f107,f107])).

fof(f58,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord2)).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:56:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (8220)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (8204)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (8199)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (8212)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.52  % (8212)Refutation not found, incomplete strategy% (8212)------------------------------
% 0.20/0.52  % (8212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8206)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (8212)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (8212)Memory used [KB]: 1791
% 0.20/0.52  % (8212)Time elapsed: 0.115 s
% 0.20/0.52  % (8212)------------------------------
% 0.20/0.52  % (8212)------------------------------
% 0.20/0.52  % (8220)Refutation not found, incomplete strategy% (8220)------------------------------
% 0.20/0.52  % (8220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8220)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (8220)Memory used [KB]: 6268
% 0.20/0.53  % (8220)Time elapsed: 0.115 s
% 0.20/0.53  % (8220)------------------------------
% 0.20/0.53  % (8220)------------------------------
% 0.20/0.53  % (8204)Refutation not found, incomplete strategy% (8204)------------------------------
% 0.20/0.53  % (8204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (8204)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (8204)Memory used [KB]: 10746
% 0.20/0.53  % (8204)Time elapsed: 0.117 s
% 0.20/0.53  % (8204)------------------------------
% 0.20/0.53  % (8204)------------------------------
% 0.20/0.53  % (8196)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (8195)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (8195)Refutation not found, incomplete strategy% (8195)------------------------------
% 0.20/0.53  % (8195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (8195)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (8195)Memory used [KB]: 1663
% 0.20/0.53  % (8195)Time elapsed: 0.123 s
% 0.20/0.53  % (8195)------------------------------
% 0.20/0.53  % (8195)------------------------------
% 0.20/0.53  % (8194)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (8197)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.54  % (8217)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (8198)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.54  % (8203)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (8218)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (8221)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (8206)Refutation not found, incomplete strategy% (8206)------------------------------
% 0.20/0.54  % (8206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (8206)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (8206)Memory used [KB]: 10618
% 0.20/0.54  % (8206)Time elapsed: 0.136 s
% 0.20/0.54  % (8206)------------------------------
% 0.20/0.54  % (8206)------------------------------
% 0.20/0.55  % (8221)Refutation not found, incomplete strategy% (8221)------------------------------
% 0.20/0.55  % (8221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (8221)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (8221)Memory used [KB]: 6268
% 0.20/0.55  % (8221)Time elapsed: 0.136 s
% 0.20/0.55  % (8221)------------------------------
% 0.20/0.55  % (8221)------------------------------
% 0.20/0.55  % (8209)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.55  % (8222)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (8200)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (8211)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (8215)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (8210)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (8213)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (8222)Refutation not found, incomplete strategy% (8222)------------------------------
% 0.20/0.55  % (8222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (8222)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (8222)Memory used [KB]: 10746
% 0.20/0.55  % (8222)Time elapsed: 0.140 s
% 0.20/0.55  % (8222)------------------------------
% 0.20/0.55  % (8222)------------------------------
% 0.20/0.55  % (8211)Refutation not found, incomplete strategy% (8211)------------------------------
% 0.20/0.55  % (8211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (8211)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (8211)Memory used [KB]: 1791
% 0.20/0.55  % (8211)Time elapsed: 0.147 s
% 0.20/0.55  % (8211)------------------------------
% 0.20/0.55  % (8211)------------------------------
% 0.20/0.55  % (8201)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.55  % (8210)Refutation not found, incomplete strategy% (8210)------------------------------
% 0.20/0.55  % (8210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (8210)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (8210)Memory used [KB]: 10746
% 0.20/0.55  % (8210)Time elapsed: 0.147 s
% 0.20/0.55  % (8210)------------------------------
% 0.20/0.55  % (8210)------------------------------
% 0.20/0.55  % (8214)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (8202)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.56  % (8205)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.56  % (8207)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.56  % (8219)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.56  % (8223)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.56  % (8223)Refutation not found, incomplete strategy% (8223)------------------------------
% 0.20/0.56  % (8223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (8223)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (8223)Memory used [KB]: 1663
% 0.20/0.56  % (8223)Time elapsed: 0.157 s
% 0.20/0.56  % (8223)------------------------------
% 0.20/0.56  % (8223)------------------------------
% 0.20/0.57  % (8218)Refutation not found, incomplete strategy% (8218)------------------------------
% 0.20/0.57  % (8218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (8218)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (8218)Memory used [KB]: 10746
% 0.20/0.57  % (8218)Time elapsed: 0.138 s
% 0.20/0.57  % (8218)------------------------------
% 0.20/0.57  % (8218)------------------------------
% 0.20/0.58  % (8216)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.58  % (8208)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.59  % (8208)Refutation not found, incomplete strategy% (8208)------------------------------
% 0.20/0.59  % (8208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (8208)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.59  
% 0.20/0.59  % (8208)Memory used [KB]: 1791
% 0.20/0.59  % (8208)Time elapsed: 0.151 s
% 0.20/0.59  % (8208)------------------------------
% 0.20/0.59  % (8208)------------------------------
% 0.20/0.60  % (8200)Refutation found. Thanks to Tanya!
% 0.20/0.60  % SZS status Theorem for theBenchmark
% 0.20/0.60  % SZS output start Proof for theBenchmark
% 0.20/0.60  fof(f585,plain,(
% 0.20/0.60    $false),
% 0.20/0.60    inference(avatar_sat_refutation,[],[f195,f437,f584])).
% 0.20/0.60  fof(f584,plain,(
% 0.20/0.60    spl15_2),
% 0.20/0.60    inference(avatar_contradiction_clause,[],[f583])).
% 0.20/0.60  fof(f583,plain,(
% 0.20/0.60    $false | spl15_2),
% 0.20/0.60    inference(subsumption_resolution,[],[f582,f121])).
% 0.20/0.60  fof(f121,plain,(
% 0.20/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.60    inference(equality_resolution,[],[f76])).
% 0.20/0.60  fof(f76,plain,(
% 0.20/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.60    inference(cnf_transformation,[],[f42])).
% 0.20/0.60  fof(f42,plain,(
% 0.20/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.60    inference(flattening,[],[f41])).
% 0.20/0.60  fof(f41,plain,(
% 0.20/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.60    inference(nnf_transformation,[],[f1])).
% 0.20/0.60  fof(f1,axiom,(
% 0.20/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.60  fof(f582,plain,(
% 0.20/0.60    ~r1_tarski(sK4,sK4) | spl15_2),
% 0.20/0.60    inference(subsumption_resolution,[],[f581,f137])).
% 0.20/0.60  fof(f137,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_enumset1(X0,X0,X1,X2))) )),
% 0.20/0.60    inference(resolution,[],[f128,f127])).
% 0.20/0.60  fof(f127,plain,(
% 0.20/0.60    ( ! [X0,X5,X3,X1] : (~sP3(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 0.20/0.60    inference(equality_resolution,[],[f97])).
% 0.20/0.60  fof(f97,plain,(
% 0.20/0.60    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP3(X0,X1,X2,X3)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f56])).
% 0.20/0.60  fof(f56,plain,(
% 0.20/0.60    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | (((sK14(X0,X1,X2,X3) != X0 & sK14(X0,X1,X2,X3) != X1 & sK14(X0,X1,X2,X3) != X2) | ~r2_hidden(sK14(X0,X1,X2,X3),X3)) & (sK14(X0,X1,X2,X3) = X0 | sK14(X0,X1,X2,X3) = X1 | sK14(X0,X1,X2,X3) = X2 | r2_hidden(sK14(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP3(X0,X1,X2,X3)))),
% 0.20/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f54,f55])).
% 0.20/0.60  fof(f55,plain,(
% 0.20/0.60    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK14(X0,X1,X2,X3) != X0 & sK14(X0,X1,X2,X3) != X1 & sK14(X0,X1,X2,X3) != X2) | ~r2_hidden(sK14(X0,X1,X2,X3),X3)) & (sK14(X0,X1,X2,X3) = X0 | sK14(X0,X1,X2,X3) = X1 | sK14(X0,X1,X2,X3) = X2 | r2_hidden(sK14(X0,X1,X2,X3),X3))))),
% 0.20/0.60    introduced(choice_axiom,[])).
% 0.20/0.60  fof(f54,plain,(
% 0.20/0.60    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP3(X0,X1,X2,X3)))),
% 0.20/0.60    inference(rectify,[],[f53])).
% 0.20/0.60  fof(f53,plain,(
% 0.20/0.60    ! [X2,X1,X0,X3] : ((sP3(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP3(X2,X1,X0,X3)))),
% 0.20/0.60    inference(flattening,[],[f52])).
% 0.20/0.60  fof(f52,plain,(
% 0.20/0.60    ! [X2,X1,X0,X3] : ((sP3(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP3(X2,X1,X0,X3)))),
% 0.20/0.60    inference(nnf_transformation,[],[f27])).
% 0.20/0.60  fof(f27,plain,(
% 0.20/0.60    ! [X2,X1,X0,X3] : (sP3(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.20/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.60  fof(f128,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (sP3(X2,X1,X0,k2_enumset1(X0,X0,X1,X2))) )),
% 0.20/0.60    inference(equality_resolution,[],[f115])).
% 0.20/0.60  fof(f115,plain,(
% 0.20/0.60    ( ! [X2,X0,X3,X1] : (sP3(X2,X1,X0,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.20/0.60    inference(definition_unfolding,[],[f104,f78])).
% 0.20/0.60  fof(f78,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f5])).
% 0.20/0.60  fof(f5,axiom,(
% 0.20/0.60    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.60  fof(f104,plain,(
% 0.20/0.60    ( ! [X2,X0,X3,X1] : (sP3(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.60    inference(cnf_transformation,[],[f57])).
% 0.20/0.60  fof(f57,plain,(
% 0.20/0.60    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP3(X2,X1,X0,X3)) & (sP3(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.60    inference(nnf_transformation,[],[f28])).
% 0.20/0.60  fof(f28,plain,(
% 0.20/0.60    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP3(X2,X1,X0,X3))),
% 0.20/0.60    inference(definition_folding,[],[f21,f27])).
% 0.20/0.60  fof(f21,plain,(
% 0.20/0.60    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.20/0.60    inference(ennf_transformation,[],[f2])).
% 0.20/0.60  fof(f2,axiom,(
% 0.20/0.60    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.20/0.60  fof(f581,plain,(
% 0.20/0.60    ~r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) | ~r1_tarski(sK4,sK4) | spl15_2),
% 0.20/0.60    inference(duplicate_literal_removal,[],[f580])).
% 0.20/0.60  fof(f580,plain,(
% 0.20/0.60    ~r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) | ~r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) | ~r1_tarski(sK4,sK4) | spl15_2),
% 0.20/0.60    inference(resolution,[],[f577,f201])).
% 0.20/0.60  fof(f201,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.60    inference(resolution,[],[f69,f133])).
% 0.20/0.60  fof(f133,plain,(
% 0.20/0.60    ( ! [X0] : (sP0(k1_wellord2(X0),X0)) )),
% 0.20/0.60    inference(subsumption_resolution,[],[f132,f59])).
% 0.20/0.60  fof(f59,plain,(
% 0.20/0.60    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.60    inference(cnf_transformation,[],[f12])).
% 0.20/0.60  fof(f12,axiom,(
% 0.20/0.60    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.20/0.60  fof(f132,plain,(
% 0.20/0.60    ( ! [X0] : (sP0(k1_wellord2(X0),X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.60    inference(resolution,[],[f116,f74])).
% 0.20/0.60  fof(f74,plain,(
% 0.20/0.60    ( ! [X0,X1] : (sP1(X0,X1) | ~v1_relat_1(X1)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f24])).
% 0.20/0.60  fof(f24,plain,(
% 0.20/0.60    ! [X0,X1] : (sP1(X0,X1) | ~v1_relat_1(X1))),
% 0.20/0.60    inference(definition_folding,[],[f18,f23,f22])).
% 0.20/0.60  fof(f22,plain,(
% 0.20/0.60    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0))),
% 0.20/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.60  fof(f23,plain,(
% 0.20/0.60    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.20/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.60  fof(f18,plain,(
% 0.20/0.60    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.20/0.60    inference(flattening,[],[f17])).
% 0.20/0.60  fof(f17,plain,(
% 0.20/0.60    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.20/0.60    inference(ennf_transformation,[],[f11])).
% 0.20/0.60  fof(f11,axiom,(
% 0.20/0.60    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 0.20/0.60  fof(f116,plain,(
% 0.20/0.60    ( ! [X0] : (~sP1(X0,k1_wellord2(X0)) | sP0(k1_wellord2(X0),X0)) )),
% 0.20/0.60    inference(equality_resolution,[],[f65])).
% 0.20/0.60  fof(f65,plain,(
% 0.20/0.60    ( ! [X0,X1] : (sP0(X1,X0) | k1_wellord2(X0) != X1 | ~sP1(X0,X1)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f35])).
% 0.20/0.60  fof(f35,plain,(
% 0.20/0.60    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ~sP0(X1,X0)) & (sP0(X1,X0) | k1_wellord2(X0) != X1)) | ~sP1(X0,X1))),
% 0.20/0.60    inference(nnf_transformation,[],[f23])).
% 0.20/0.60  fof(f69,plain,(
% 0.20/0.60    ( ! [X4,X0,X5,X1] : (~sP0(X0,X1) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | r2_hidden(k4_tarski(X4,X5),X0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f40])).
% 0.20/0.60  fof(f40,plain,(
% 0.20/0.60    ! [X0,X1] : ((sP0(X0,X1) | ((~r1_tarski(sK7(X0,X1),sK8(X0,X1)) | ~r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)) & (r1_tarski(sK7(X0,X1),sK8(X0,X1)) | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)) & r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK7(X0,X1),X1)) | k3_relat_1(X0) != X1) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X0))) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) & k3_relat_1(X0) = X1) | ~sP0(X0,X1)))),
% 0.20/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f38,f39])).
% 0.20/0.60  fof(f39,plain,(
% 0.20/0.60    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X0)) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => ((~r1_tarski(sK7(X0,X1),sK8(X0,X1)) | ~r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)) & (r1_tarski(sK7(X0,X1),sK8(X0,X1)) | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)) & r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK7(X0,X1),X1)))),
% 0.20/0.60    introduced(choice_axiom,[])).
% 0.20/0.60  fof(f38,plain,(
% 0.20/0.60    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X0)) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) | k3_relat_1(X0) != X1) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X0))) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) & k3_relat_1(X0) = X1) | ~sP0(X0,X1)))),
% 0.20/0.60    inference(rectify,[],[f37])).
% 0.20/0.60  fof(f37,plain,(
% 0.20/0.60    ! [X1,X0] : ((sP0(X1,X0) | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | ~sP0(X1,X0)))),
% 0.20/0.60    inference(flattening,[],[f36])).
% 0.20/0.60  fof(f36,plain,(
% 0.20/0.60    ! [X1,X0] : ((sP0(X1,X0) | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | ~sP0(X1,X0)))),
% 0.20/0.60    inference(nnf_transformation,[],[f22])).
% 0.20/0.60  fof(f577,plain,(
% 0.20/0.60    ~r2_hidden(k4_tarski(sK4,sK4),k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4))) | spl15_2),
% 0.20/0.60    inference(duplicate_literal_removal,[],[f566])).
% 0.20/0.60  fof(f566,plain,(
% 0.20/0.60    ~r2_hidden(k4_tarski(sK4,sK4),k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4))) | ~r2_hidden(k4_tarski(sK4,sK4),k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4))) | spl15_2),
% 0.20/0.60    inference(resolution,[],[f307,f440])).
% 0.20/0.60  fof(f440,plain,(
% 0.20/0.60    ~r1_tarski(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)),k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4))) | spl15_2),
% 0.20/0.60    inference(forward_demodulation,[],[f193,f109])).
% 0.20/0.60  fof(f109,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.20/0.60    inference(definition_unfolding,[],[f80,f106,f107,f106])).
% 0.20/0.60  fof(f107,plain,(
% 0.20/0.60    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.60    inference(definition_unfolding,[],[f60,f106])).
% 0.20/0.60  fof(f60,plain,(
% 0.20/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f3])).
% 0.20/0.60  fof(f3,axiom,(
% 0.20/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.60  fof(f106,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.60    inference(definition_unfolding,[],[f64,f78])).
% 0.20/0.60  fof(f64,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f4])).
% 0.20/0.60  fof(f4,axiom,(
% 0.20/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.60  fof(f80,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.20/0.60    inference(cnf_transformation,[],[f7])).
% 0.20/0.60  fof(f7,axiom,(
% 0.20/0.60    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.20/0.60  fof(f193,plain,(
% 0.20/0.60    ~r1_tarski(k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4)),k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4))) | spl15_2),
% 0.20/0.60    inference(avatar_component_clause,[],[f191])).
% 0.20/0.60  fof(f191,plain,(
% 0.20/0.60    spl15_2 <=> r1_tarski(k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4)),k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).
% 0.20/0.60  fof(f307,plain,(
% 0.20/0.60    ( ! [X47,X45,X46,X44] : (r1_tarski(k2_zfmisc_1(k2_enumset1(X44,X44,X44,X46),k2_enumset1(X45,X45,X45,X45)),X47) | ~r2_hidden(k4_tarski(X46,X45),X47) | ~r2_hidden(k4_tarski(X44,X45),X47)) )),
% 0.20/0.60    inference(superposition,[],[f111,f109])).
% 0.20/0.60  fof(f111,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.60    inference(definition_unfolding,[],[f95,f106])).
% 0.20/0.60  fof(f95,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f51])).
% 0.20/0.60  fof(f51,plain,(
% 0.20/0.60    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.60    inference(flattening,[],[f50])).
% 0.20/0.60  fof(f50,plain,(
% 0.20/0.60    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.60    inference(nnf_transformation,[],[f8])).
% 0.20/0.60  fof(f8,axiom,(
% 0.20/0.60    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.20/0.60  fof(f437,plain,(
% 0.20/0.60    spl15_1),
% 0.20/0.60    inference(avatar_contradiction_clause,[],[f434])).
% 0.20/0.60  fof(f434,plain,(
% 0.20/0.60    $false | spl15_1),
% 0.20/0.60    inference(resolution,[],[f429,f292])).
% 0.20/0.60  fof(f292,plain,(
% 0.20/0.60    ~r1_tarski(k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)),k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4))) | spl15_1),
% 0.20/0.60    inference(backward_demodulation,[],[f189,f109])).
% 0.20/0.60  fof(f189,plain,(
% 0.20/0.60    ~r1_tarski(k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4))) | spl15_1),
% 0.20/0.60    inference(avatar_component_clause,[],[f187])).
% 0.20/0.60  fof(f187,plain,(
% 0.20/0.60    spl15_1 <=> r1_tarski(k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4)))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).
% 0.20/0.60  fof(f429,plain,(
% 0.20/0.60    ( ! [X0] : (r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))) )),
% 0.20/0.60    inference(duplicate_literal_removal,[],[f422])).
% 0.20/0.60  fof(f422,plain,(
% 0.20/0.60    ( ! [X0] : (r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))) )),
% 0.20/0.60    inference(resolution,[],[f421,f165])).
% 0.20/0.60  fof(f165,plain,(
% 0.20/0.60    ( ! [X0,X1] : (r2_hidden(sK5(k1_wellord2(X0),X1),X0) | r1_tarski(k1_wellord2(X0),X1)) )),
% 0.20/0.60    inference(subsumption_resolution,[],[f164,f59])).
% 0.20/0.60  fof(f164,plain,(
% 0.20/0.60    ( ! [X0,X1] : (r2_hidden(sK5(k1_wellord2(X0),X1),X0) | ~v1_relat_1(k1_wellord2(X0)) | r1_tarski(k1_wellord2(X0),X1)) )),
% 0.20/0.60    inference(superposition,[],[f160,f134])).
% 0.20/0.60  fof(f134,plain,(
% 0.20/0.60    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.20/0.60    inference(resolution,[],[f133,f67])).
% 0.20/0.60  fof(f67,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~sP0(X0,X1) | k3_relat_1(X0) = X1) )),
% 0.20/0.60    inference(cnf_transformation,[],[f40])).
% 0.20/0.60  fof(f160,plain,(
% 0.20/0.60    ( ! [X2,X3] : (r2_hidden(sK5(X2,X3),k3_relat_1(X2)) | ~v1_relat_1(X2) | r1_tarski(X2,X3)) )),
% 0.20/0.60    inference(duplicate_literal_removal,[],[f159])).
% 0.20/0.60  fof(f159,plain,(
% 0.20/0.60    ( ! [X2,X3] : (r1_tarski(X2,X3) | ~v1_relat_1(X2) | r2_hidden(sK5(X2,X3),k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.20/0.60    inference(resolution,[],[f62,f81])).
% 0.20/0.60  fof(f81,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f20])).
% 0.20/0.60  fof(f20,plain,(
% 0.20/0.60    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.20/0.60    inference(flattening,[],[f19])).
% 0.20/0.60  fof(f19,plain,(
% 0.20/0.60    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.20/0.60    inference(ennf_transformation,[],[f10])).
% 0.20/0.60  fof(f10,axiom,(
% 0.20/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).
% 0.20/0.60  fof(f62,plain,(
% 0.20/0.60    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f34])).
% 0.20/0.60  fof(f34,plain,(
% 0.20/0.60    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.20/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f32,f33])).
% 0.20/0.60  fof(f33,plain,(
% 0.20/0.60    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)))),
% 0.20/0.60    introduced(choice_axiom,[])).
% 0.20/0.60  fof(f32,plain,(
% 0.20/0.60    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.20/0.60    inference(rectify,[],[f31])).
% 0.20/0.60  fof(f31,plain,(
% 0.20/0.60    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.20/0.60    inference(nnf_transformation,[],[f16])).
% 0.20/0.60  fof(f16,plain,(
% 0.20/0.60    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.20/0.60    inference(ennf_transformation,[],[f9])).
% 0.20/0.60  fof(f9,axiom,(
% 0.20/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 0.20/0.60  fof(f421,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~r2_hidden(sK5(k1_wellord2(X0),k2_zfmisc_1(X1,X0)),X1) | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X0))) )),
% 0.20/0.60    inference(subsumption_resolution,[],[f420,f59])).
% 0.20/0.60  fof(f420,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~r2_hidden(sK5(k1_wellord2(X0),k2_zfmisc_1(X1,X0)),X1) | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.60    inference(duplicate_literal_removal,[],[f413])).
% 0.20/0.60  fof(f413,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~r2_hidden(sK5(k1_wellord2(X0),k2_zfmisc_1(X1,X0)),X1) | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X0)) | ~v1_relat_1(k1_wellord2(X0)) | r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X1,X0))) )),
% 0.20/0.60    inference(resolution,[],[f177,f167])).
% 0.20/0.60  fof(f167,plain,(
% 0.20/0.60    ( ! [X0,X1] : (r2_hidden(sK6(k1_wellord2(X0),X1),X0) | r1_tarski(k1_wellord2(X0),X1)) )),
% 0.20/0.60    inference(subsumption_resolution,[],[f166,f59])).
% 0.20/0.60  fof(f166,plain,(
% 0.20/0.60    ( ! [X0,X1] : (r2_hidden(sK6(k1_wellord2(X0),X1),X0) | ~v1_relat_1(k1_wellord2(X0)) | r1_tarski(k1_wellord2(X0),X1)) )),
% 0.20/0.60    inference(superposition,[],[f161,f134])).
% 0.20/0.60  fof(f161,plain,(
% 0.20/0.60    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),k3_relat_1(X0)) | ~v1_relat_1(X0) | r1_tarski(X0,X1)) )),
% 0.20/0.60    inference(duplicate_literal_removal,[],[f158])).
% 0.20/0.60  fof(f158,plain,(
% 0.20/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_relat_1(X0) | r2_hidden(sK6(X0,X1),k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.60    inference(resolution,[],[f62,f82])).
% 0.20/0.60  fof(f82,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f20])).
% 0.20/0.60  fof(f177,plain,(
% 0.20/0.60    ( ! [X14,X15,X13] : (~r2_hidden(sK6(X13,k2_zfmisc_1(X14,X15)),X15) | ~r2_hidden(sK5(X13,k2_zfmisc_1(X14,X15)),X14) | r1_tarski(X13,k2_zfmisc_1(X14,X15)) | ~v1_relat_1(X13)) )),
% 0.20/0.60    inference(resolution,[],[f173,f63])).
% 0.20/0.60  fof(f63,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f34])).
% 0.20/0.60  fof(f173,plain,(
% 0.20/0.60    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) | ~r2_hidden(X2,X3) | ~r2_hidden(X0,X1)) )),
% 0.20/0.60    inference(resolution,[],[f123,f124])).
% 0.20/0.60  fof(f124,plain,(
% 0.20/0.60    ( ! [X0,X1] : (sP2(X1,X0,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.60    inference(equality_resolution,[],[f91])).
% 0.20/0.60  fof(f91,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (sP2(X1,X0,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.60    inference(cnf_transformation,[],[f49])).
% 0.20/0.60  fof(f49,plain,(
% 0.20/0.60    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ~sP2(X1,X0,X2)) & (sP2(X1,X0,X2) | k2_zfmisc_1(X0,X1) != X2))),
% 0.20/0.60    inference(nnf_transformation,[],[f26])).
% 0.20/0.60  fof(f26,plain,(
% 0.20/0.60    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> sP2(X1,X0,X2))),
% 0.20/0.60    inference(definition_folding,[],[f6,f25])).
% 0.20/0.60  fof(f25,plain,(
% 0.20/0.60    ! [X1,X0,X2] : (sP2(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.20/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.60  fof(f6,axiom,(
% 0.20/0.60    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.20/0.60  fof(f123,plain,(
% 0.20/0.60    ( ! [X2,X0,X10,X1,X9] : (~sP2(X0,X1,X2) | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1) | r2_hidden(k4_tarski(X9,X10),X2)) )),
% 0.20/0.60    inference(equality_resolution,[],[f86])).
% 0.20/0.60  fof(f86,plain,(
% 0.20/0.60    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1) | ~sP2(X0,X1,X2)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f48])).
% 0.20/0.60  fof(f48,plain,(
% 0.20/0.60    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((! [X4,X5] : (k4_tarski(X4,X5) != sK9(X0,X1,X2) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(sK9(X0,X1,X2),X2)) & ((sK9(X0,X1,X2) = k4_tarski(sK10(X0,X1,X2),sK11(X0,X1,X2)) & r2_hidden(sK11(X0,X1,X2),X0) & r2_hidden(sK10(X0,X1,X2),X1)) | r2_hidden(sK9(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1))) & ((k4_tarski(sK12(X0,X1,X8),sK13(X0,X1,X8)) = X8 & r2_hidden(sK13(X0,X1,X8),X0) & r2_hidden(sK12(X0,X1,X8),X1)) | ~r2_hidden(X8,X2))) | ~sP2(X0,X1,X2)))),
% 0.20/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12,sK13])],[f44,f47,f46,f45])).
% 0.20/0.60  fof(f45,plain,(
% 0.20/0.60    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK9(X0,X1,X2) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK9(X0,X1,X2) & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(sK9(X0,X1,X2),X2))))),
% 0.20/0.60    introduced(choice_axiom,[])).
% 0.20/0.60  fof(f46,plain,(
% 0.20/0.60    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK9(X0,X1,X2) & r2_hidden(X7,X0) & r2_hidden(X6,X1)) => (sK9(X0,X1,X2) = k4_tarski(sK10(X0,X1,X2),sK11(X0,X1,X2)) & r2_hidden(sK11(X0,X1,X2),X0) & r2_hidden(sK10(X0,X1,X2),X1)))),
% 0.20/0.60    introduced(choice_axiom,[])).
% 0.20/0.60  fof(f47,plain,(
% 0.20/0.60    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X0) & r2_hidden(X11,X1)) => (k4_tarski(sK12(X0,X1,X8),sK13(X0,X1,X8)) = X8 & r2_hidden(sK13(X0,X1,X8),X0) & r2_hidden(sK12(X0,X1,X8),X1)))),
% 0.20/0.60    introduced(choice_axiom,[])).
% 0.20/0.60  fof(f44,plain,(
% 0.20/0.60    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X0) & r2_hidden(X11,X1)) | ~r2_hidden(X8,X2))) | ~sP2(X0,X1,X2)))),
% 0.20/0.60    inference(rectify,[],[f43])).
% 0.20/0.60  fof(f43,plain,(
% 0.20/0.60    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 0.20/0.60    inference(nnf_transformation,[],[f25])).
% 0.20/0.60  fof(f195,plain,(
% 0.20/0.60    ~spl15_2 | ~spl15_1),
% 0.20/0.60    inference(avatar_split_clause,[],[f185,f187,f191])).
% 0.20/0.60  fof(f185,plain,(
% 0.20/0.60    ~r1_tarski(k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4))) | ~r1_tarski(k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4)),k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)))),
% 0.20/0.60    inference(extensionality_resolution,[],[f77,f108])).
% 0.20/0.60  fof(f108,plain,(
% 0.20/0.60    k1_wellord2(k2_enumset1(sK4,sK4,sK4,sK4)) != k2_enumset1(k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4),k4_tarski(sK4,sK4))),
% 0.20/0.60    inference(definition_unfolding,[],[f58,f107,f107])).
% 0.20/0.60  fof(f58,plain,(
% 0.20/0.60    k1_wellord2(k1_tarski(sK4)) != k1_tarski(k4_tarski(sK4,sK4))),
% 0.20/0.60    inference(cnf_transformation,[],[f30])).
% 0.20/0.60  fof(f30,plain,(
% 0.20/0.60    k1_wellord2(k1_tarski(sK4)) != k1_tarski(k4_tarski(sK4,sK4))),
% 0.20/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f29])).
% 0.20/0.60  fof(f29,plain,(
% 0.20/0.60    ? [X0] : k1_wellord2(k1_tarski(X0)) != k1_tarski(k4_tarski(X0,X0)) => k1_wellord2(k1_tarski(sK4)) != k1_tarski(k4_tarski(sK4,sK4))),
% 0.20/0.60    introduced(choice_axiom,[])).
% 0.20/0.60  fof(f15,plain,(
% 0.20/0.60    ? [X0] : k1_wellord2(k1_tarski(X0)) != k1_tarski(k4_tarski(X0,X0))),
% 0.20/0.60    inference(ennf_transformation,[],[f14])).
% 0.20/0.60  fof(f14,negated_conjecture,(
% 0.20/0.60    ~! [X0] : k1_wellord2(k1_tarski(X0)) = k1_tarski(k4_tarski(X0,X0))),
% 0.20/0.60    inference(negated_conjecture,[],[f13])).
% 0.20/0.60  fof(f13,conjecture,(
% 0.20/0.60    ! [X0] : k1_wellord2(k1_tarski(X0)) = k1_tarski(k4_tarski(X0,X0))),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord2)).
% 0.20/0.60  fof(f77,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f42])).
% 0.20/0.60  % SZS output end Proof for theBenchmark
% 0.20/0.60  % (8200)------------------------------
% 0.20/0.60  % (8200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.60  % (8200)Termination reason: Refutation
% 0.20/0.60  
% 0.20/0.60  % (8200)Memory used [KB]: 11513
% 0.20/0.60  % (8200)Time elapsed: 0.154 s
% 0.20/0.60  % (8200)------------------------------
% 0.20/0.60  % (8200)------------------------------
% 0.20/0.61  % (8193)Success in time 0.236 s
%------------------------------------------------------------------------------
