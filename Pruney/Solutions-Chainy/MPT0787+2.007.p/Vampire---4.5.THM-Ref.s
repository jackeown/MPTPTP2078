%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:04 EST 2020

% Result     : Theorem 2.23s
% Output     : Refutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :  175 (2438 expanded)
%              Number of leaves         :   26 ( 615 expanded)
%              Depth                    :   36
%              Number of atoms          :  766 (14498 expanded)
%              Number of equality atoms :   99 (1594 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f893,plain,(
    $false ),
    inference(subsumption_resolution,[],[f892,f79])).

fof(f79,plain,(
    r2_hidden(sK8,k3_relat_1(sK10)) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9))
      | ~ r2_hidden(k4_tarski(sK8,sK9),sK10) )
    & ( r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9))
      | r2_hidden(k4_tarski(sK8,sK9),sK10) )
    & r2_hidden(sK9,k3_relat_1(sK10))
    & r2_hidden(sK8,k3_relat_1(sK10))
    & v2_wellord1(sK10)
    & v1_relat_1(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f38,f39])).

fof(f39,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) )
        & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | r2_hidden(k4_tarski(X0,X1),X2) )
        & r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9))
        | ~ r2_hidden(k4_tarski(sK8,sK9),sK10) )
      & ( r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9))
        | r2_hidden(k4_tarski(sK8,sK9),sK10) )
      & r2_hidden(sK9,k3_relat_1(sK10))
      & r2_hidden(sK8,k3_relat_1(sK10))
      & v2_wellord1(sK10)
      & v1_relat_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => ( r2_hidden(k4_tarski(X0,X1),X2)
          <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).

fof(f892,plain,(
    ~ r2_hidden(sK8,k3_relat_1(sK10)) ),
    inference(resolution,[],[f839,f176])).

fof(f176,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,X0),sK10)
      | ~ r2_hidden(X0,k3_relat_1(sK10)) ) ),
    inference(subsumption_resolution,[],[f175,f77])).

fof(f77,plain,(
    v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f40])).

fof(f175,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_relat_1(sK10))
      | r2_hidden(k4_tarski(X0,X0),sK10)
      | ~ v1_relat_1(sK10) ) ),
    inference(resolution,[],[f83,f141])).

fof(f141,plain,(
    v1_relat_2(sK10) ),
    inference(resolution,[],[f138,f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ sP2(X0)
      | v1_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( sP2(X0)
        | ~ v1_wellord1(X0)
        | ~ v6_relat_2(X0)
        | ~ v4_relat_2(X0)
        | ~ v8_relat_2(X0)
        | ~ v1_relat_2(X0) )
      & ( ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) )
        | ~ sP2(X0) ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( sP2(X0)
        | ~ v1_wellord1(X0)
        | ~ v6_relat_2(X0)
        | ~ v4_relat_2(X0)
        | ~ v8_relat_2(X0)
        | ~ v1_relat_2(X0) )
      & ( ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) )
        | ~ sP2(X0) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( sP2(X0)
    <=> ( v1_wellord1(X0)
        & v6_relat_2(X0)
        & v4_relat_2(X0)
        & v8_relat_2(X0)
        & v1_relat_2(X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f138,plain,(
    sP2(sK10) ),
    inference(subsumption_resolution,[],[f137,f77])).

fof(f137,plain,
    ( sP2(sK10)
    | ~ v1_relat_1(sK10) ),
    inference(resolution,[],[f136,f78])).

fof(f78,plain,(
    v2_wellord1(sK10) ),
    inference(cnf_transformation,[],[f40])).

fof(f136,plain,(
    ! [X0] :
      ( ~ v2_wellord1(X0)
      | sP2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f99,f107])).

fof(f107,plain,(
    ! [X0] :
      ( sP3(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( sP3(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f18,f29,f28])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> sP2(X0) )
      | ~ sP3(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

fof(f99,plain,(
    ! [X0] :
      ( ~ sP3(X0)
      | ~ v2_wellord1(X0)
      | sP2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ sP2(X0) )
        & ( sP2(X0)
          | ~ v2_wellord1(X0) ) )
      | ~ sP3(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f83,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_2(X0)
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | r2_hidden(k4_tarski(X2,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK11(X0),sK11(X0)),X0)
            & r2_hidden(sK11(X0),k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f42,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_tarski(X1,X1),X0)
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK11(X0),sK11(X0)),X0)
        & r2_hidden(sK11(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ? [X1] :
              ( ~ r2_hidden(k4_tarski(X1,X1),X0)
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ? [X1] :
              ( ~ r2_hidden(k4_tarski(X1,X1),X0)
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1] :
              ( r2_hidden(k4_tarski(X1,X1),X0)
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).

fof(f839,plain,(
    ~ r2_hidden(k4_tarski(sK8,sK8),sK10) ),
    inference(forward_demodulation,[],[f838,f791])).

fof(f791,plain,(
    sK8 = sK9 ),
    inference(subsumption_resolution,[],[f790,f149])).

fof(f149,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_wellord1(sK10,X0)) ),
    inference(resolution,[],[f148,f132])).

fof(f132,plain,(
    ! [X4,X2,X0] :
      ( ~ sP4(X0,X4,X2)
      | ~ r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f110])).

fof(f110,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ( ( ~ r2_hidden(k4_tarski(sK17(X0,X1,X2),X1),X0)
            | sK17(X0,X1,X2) = X1
            | ~ r2_hidden(sK17(X0,X1,X2),X2) )
          & ( ( r2_hidden(k4_tarski(sK17(X0,X1,X2),X1),X0)
              & sK17(X0,X1,X2) != X1 )
            | r2_hidden(sK17(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(k4_tarski(X4,X1),X0)
              | X1 = X4 )
            & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                & X1 != X4 )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f60,f61])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK17(X0,X1,X2),X1),X0)
          | sK17(X0,X1,X2) = X1
          | ~ r2_hidden(sK17(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK17(X0,X1,X2),X1),X0)
            & sK17(X0,X1,X2) != X1 )
          | r2_hidden(sK17(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              | X1 = X3
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(k4_tarski(X4,X1),X0)
              | X1 = X4 )
            & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                & X1 != X4 )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              | X1 = X3
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(k4_tarski(X3,X1),X0)
              | X1 = X3 )
            & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              | X1 = X3
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(k4_tarski(X3,X1),X0)
              | X1 = X3 )
            & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( sP4(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(k4_tarski(X3,X1),X0)
            & X1 != X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f148,plain,(
    ! [X0] : sP4(sK10,X0,k1_wellord1(sK10,X0)) ),
    inference(resolution,[],[f147,f77])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | sP4(X0,X1,k1_wellord1(X0,X1)) ) ),
    inference(resolution,[],[f131,f116])).

fof(f116,plain,(
    ! [X0] :
      ( sP5(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( sP5(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f19,f32,f31])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> sP4(X0,X1,X2) )
      | ~ sP5(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ sP5(X0)
      | sP4(X0,X1,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X1,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ sP5(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ~ sP4(X0,X1,X2) )
          & ( sP4(X0,X1,X2)
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ sP5(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f790,plain,
    ( sK8 = sK9
    | r2_hidden(sK9,k1_wellord1(sK10,sK9)) ),
    inference(duplicate_literal_removal,[],[f778])).

fof(f778,plain,
    ( sK8 = sK9
    | r2_hidden(sK9,k1_wellord1(sK10,sK9))
    | sK8 = sK9 ),
    inference(resolution,[],[f719,f753])).

fof(f753,plain,
    ( r2_hidden(k4_tarski(sK9,sK8),sK10)
    | sK8 = sK9 ),
    inference(subsumption_resolution,[],[f745,f732])).

fof(f732,plain,
    ( ~ r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9))
    | sK8 = sK9 ),
    inference(resolution,[],[f716,f82])).

fof(f82,plain,
    ( ~ r2_hidden(k4_tarski(sK8,sK9),sK10)
    | ~ r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) ),
    inference(cnf_transformation,[],[f40])).

fof(f716,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),sK10)
    | sK8 = sK9 ),
    inference(resolution,[],[f715,f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_wellord1(sK10,X1))
      | r2_hidden(k4_tarski(X0,X1),sK10) ) ),
    inference(resolution,[],[f111,f148])).

fof(f111,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(k4_tarski(X4,X1),X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f715,plain,
    ( r2_hidden(sK8,k1_wellord1(sK10,sK9))
    | sK8 = sK9 ),
    inference(subsumption_resolution,[],[f714,f181])).

fof(f181,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK10)
      | X0 = X1
      | r2_hidden(X0,k1_wellord1(sK10,X1)) ) ),
    inference(resolution,[],[f112,f148])).

fof(f112,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f714,plain,
    ( sK8 = sK9
    | r2_hidden(sK8,k1_wellord1(sK10,sK9))
    | r2_hidden(k4_tarski(sK8,sK9),sK10) ),
    inference(subsumption_resolution,[],[f705,f149])).

fof(f705,plain,
    ( sK8 = sK9
    | r2_hidden(sK8,k1_wellord1(sK10,sK9))
    | r2_hidden(k4_tarski(sK8,sK9),sK10)
    | r2_hidden(sK9,k1_wellord1(sK10,sK9)) ),
    inference(resolution,[],[f703,f164])).

fof(f164,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_wellord1(sK10,sK8))
      | r2_hidden(k4_tarski(sK8,sK9),sK10)
      | r2_hidden(X0,k1_wellord1(sK10,sK9)) ) ),
    inference(resolution,[],[f81,f126])).

fof(f126,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK21(X0,X1),X1)
          & r2_hidden(sK21(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21])],[f74,f75])).

fof(f75,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK21(X0,X1),X1)
        & r2_hidden(sK21(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f81,plain,
    ( r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9))
    | r2_hidden(k4_tarski(sK8,sK9),sK10) ),
    inference(cnf_transformation,[],[f40])).

fof(f703,plain,
    ( r2_hidden(sK9,k1_wellord1(sK10,sK8))
    | sK8 = sK9
    | r2_hidden(sK8,k1_wellord1(sK10,sK9)) ),
    inference(duplicate_literal_removal,[],[f700])).

fof(f700,plain,
    ( sK8 = sK9
    | r2_hidden(sK9,k1_wellord1(sK10,sK8))
    | sK8 = sK9
    | r2_hidden(sK8,k1_wellord1(sK10,sK9)) ),
    inference(resolution,[],[f697,f181])).

fof(f697,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),sK10)
    | sK8 = sK9
    | r2_hidden(sK9,k1_wellord1(sK10,sK8)) ),
    inference(duplicate_literal_removal,[],[f694])).

fof(f694,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),sK10)
    | sK8 = sK9
    | sK8 = sK9
    | r2_hidden(sK9,k1_wellord1(sK10,sK8)) ),
    inference(resolution,[],[f663,f181])).

fof(f663,plain,
    ( r2_hidden(k4_tarski(sK9,sK8),sK10)
    | r2_hidden(k4_tarski(sK8,sK9),sK10)
    | sK8 = sK9 ),
    inference(resolution,[],[f626,f80])).

fof(f80,plain,(
    r2_hidden(sK9,k3_relat_1(sK10)) ),
    inference(cnf_transformation,[],[f40])).

fof(f626,plain,(
    ! [X22] :
      ( ~ r2_hidden(X22,k3_relat_1(sK10))
      | sK8 = X22
      | r2_hidden(k4_tarski(sK8,X22),sK10)
      | r2_hidden(k4_tarski(X22,sK8),sK10) ) ),
    inference(resolution,[],[f359,f79])).

fof(f359,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(sK10))
      | X0 = X1
      | ~ r2_hidden(X1,k3_relat_1(sK10))
      | r2_hidden(k4_tarski(X0,X1),sK10)
      | r2_hidden(k4_tarski(X1,X0),sK10) ) ),
    inference(resolution,[],[f88,f144])).

fof(f144,plain,(
    sP0(sK10) ),
    inference(subsumption_resolution,[],[f143,f77])).

fof(f143,plain,
    ( sP0(sK10)
    | ~ v1_relat_1(sK10) ),
    inference(resolution,[],[f142,f94])).

fof(f94,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f15,f26,f25])).

fof(f25,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1,X2] :
          ( r2_hidden(k4_tarski(X2,X1),X0)
          | r2_hidden(k4_tarski(X1,X2),X0)
          | X1 = X2
          | ~ r2_hidden(X2,k3_relat_1(X0))
          | ~ r2_hidden(X1,k3_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f26,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f15,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).

fof(f142,plain,
    ( ~ sP1(sK10)
    | sP0(sK10) ),
    inference(resolution,[],[f139,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v6_relat_2(X0)
      | sP0(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v6_relat_2(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f139,plain,(
    v6_relat_2(sK10) ),
    inference(resolution,[],[f138,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ~ sP2(X0)
      | v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f88,plain,(
    ! [X4,X0,X3] :
      ( ~ sP0(X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | r2_hidden(k4_tarski(X4,X3),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ~ r2_hidden(k4_tarski(sK13(X0),sK12(X0)),X0)
          & ~ r2_hidden(k4_tarski(sK12(X0),sK13(X0)),X0)
          & sK12(X0) != sK13(X0)
          & r2_hidden(sK13(X0),k3_relat_1(X0))
          & r2_hidden(sK12(X0),k3_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(k4_tarski(X4,X3),X0)
            | r2_hidden(k4_tarski(X3,X4),X0)
            | X3 = X4
            | ~ r2_hidden(X4,k3_relat_1(X0))
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f47,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0))
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK13(X0),sK12(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK12(X0),sK13(X0)),X0)
        & sK12(X0) != sK13(X0)
        & r2_hidden(sK13(X0),k3_relat_1(X0))
        & r2_hidden(sK12(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(k4_tarski(X2,X1),X0)
            & ~ r2_hidden(k4_tarski(X1,X2),X0)
            & X1 != X2
            & r2_hidden(X2,k3_relat_1(X0))
            & r2_hidden(X1,k3_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(k4_tarski(X4,X3),X0)
            | r2_hidden(k4_tarski(X3,X4),X0)
            | X3 = X4
            | ~ r2_hidden(X4,k3_relat_1(X0))
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(k4_tarski(X2,X1),X0)
            & ~ r2_hidden(k4_tarski(X1,X2),X0)
            & X1 != X2
            & r2_hidden(X2,k3_relat_1(X0))
            & r2_hidden(X1,k3_relat_1(X0)) ) )
      & ( ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f745,plain,
    ( r2_hidden(k4_tarski(sK9,sK8),sK10)
    | r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9))
    | sK8 = sK9 ),
    inference(superposition,[],[f167,f738])).

fof(f738,plain,
    ( sK9 = sK21(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9))
    | sK8 = sK9 ),
    inference(resolution,[],[f732,f605])).

fof(f605,plain,
    ( r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9))
    | sK9 = sK21(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) ),
    inference(duplicate_literal_removal,[],[f597])).

fof(f597,plain,
    ( sK9 = sK21(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9))
    | r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9))
    | r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) ),
    inference(resolution,[],[f310,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK21(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f310,plain,(
    ! [X2] :
      ( r2_hidden(sK21(k1_wellord1(sK10,sK8),X2),k1_wellord1(sK10,sK9))
      | sK9 = sK21(k1_wellord1(sK10,sK8),X2)
      | r1_tarski(k1_wellord1(sK10,sK8),X2) ) ),
    inference(resolution,[],[f308,f181])).

fof(f308,plain,(
    ! [X5] :
      ( r2_hidden(k4_tarski(sK21(k1_wellord1(sK10,sK8),X5),sK9),sK10)
      | r1_tarski(k1_wellord1(sK10,sK8),X5) ) ),
    inference(subsumption_resolution,[],[f306,f283])).

fof(f283,plain,(
    ! [X6,X7,X5] :
      ( r2_hidden(k4_tarski(sK21(k1_wellord1(sK10,X5),X7),X6),sK10)
      | ~ r2_hidden(k4_tarski(X5,X6),sK10)
      | r1_tarski(k1_wellord1(sK10,X5),X7) ) ),
    inference(resolution,[],[f280,f167])).

fof(f280,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X0),sK10)
      | ~ r2_hidden(k4_tarski(X0,X1),sK10)
      | r2_hidden(k4_tarski(X2,X1),sK10) ) ),
    inference(subsumption_resolution,[],[f279,f77])).

fof(f279,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK10)
      | ~ r2_hidden(k4_tarski(X2,X0),sK10)
      | r2_hidden(k4_tarski(X2,X1),sK10)
      | ~ v1_relat_1(sK10) ) ),
    inference(resolution,[],[f95,f140])).

fof(f140,plain,(
    v8_relat_2(sK10) ),
    inference(resolution,[],[f138,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ sP2(X0)
      | v8_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f95,plain,(
    ! [X6,X4,X0,X5] :
      ( ~ v8_relat_2(X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | r2_hidden(k4_tarski(X4,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK14(X0),sK16(X0)),X0)
            & r2_hidden(k4_tarski(sK15(X0),sK16(X0)),X0)
            & r2_hidden(k4_tarski(sK14(X0),sK15(X0)),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15,sK16])],[f51,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( ~ r2_hidden(k4_tarski(sK14(X0),sK16(X0)),X0)
        & r2_hidden(k4_tarski(sK15(X0),sK16(X0)),X0)
        & r2_hidden(k4_tarski(sK14(X0),sK15(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2,X3] :
              ( r2_hidden(k4_tarski(X1,X3),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => r2_hidden(k4_tarski(X1,X3),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_wellord1)).

fof(f306,plain,(
    ! [X5] :
      ( r2_hidden(k4_tarski(sK8,sK9),sK10)
      | r1_tarski(k1_wellord1(sK10,sK8),X5)
      | r2_hidden(k4_tarski(sK21(k1_wellord1(sK10,sK8),X5),sK9),sK10) ) ),
    inference(resolution,[],[f214,f165])).

fof(f214,plain,(
    ! [X1] :
      ( r2_hidden(sK21(k1_wellord1(sK10,sK8),X1),k1_wellord1(sK10,sK9))
      | r2_hidden(k4_tarski(sK8,sK9),sK10)
      | r1_tarski(k1_wellord1(sK10,sK8),X1) ) ),
    inference(resolution,[],[f164,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK21(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f167,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(sK21(k1_wellord1(sK10,X2),X3),X2),sK10)
      | r1_tarski(k1_wellord1(sK10,X2),X3) ) ),
    inference(resolution,[],[f165,f127])).

fof(f719,plain,(
    ! [X1] :
      ( ~ r2_hidden(k4_tarski(X1,sK8),sK10)
      | sK8 = sK9
      | r2_hidden(X1,k1_wellord1(sK10,sK9)) ) ),
    inference(resolution,[],[f715,f207])).

fof(f207,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_wellord1(sK10,X2))
      | ~ r2_hidden(k4_tarski(X0,X1),sK10)
      | r2_hidden(X0,k1_wellord1(sK10,X2)) ) ),
    inference(resolution,[],[f206,f121])).

fof(f121,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ sP6(X0,X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(X5,X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( sP6(X0,X1)
        | ( ~ r2_hidden(sK20(X0,X1),X0)
          & r2_hidden(k4_tarski(sK20(X0,X1),sK19(X0,X1)),X1)
          & r2_hidden(sK19(X0,X1),X0) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r2_hidden(k4_tarski(X5,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ sP6(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19,sK20])],[f69,f71,f70])).

fof(f70,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X0)
              & r2_hidden(k4_tarski(X3,X2),X1) )
          & r2_hidden(X2,X0) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X0)
            & r2_hidden(k4_tarski(X3,sK19(X0,X1)),X1) )
        & r2_hidden(sK19(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X0)
          & r2_hidden(k4_tarski(X3,sK19(X0,X1)),X1) )
     => ( ~ r2_hidden(sK20(X0,X1),X0)
        & r2_hidden(k4_tarski(sK20(X0,X1),sK19(X0,X1)),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( sP6(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,X0)
                & r2_hidden(k4_tarski(X3,X2),X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r2_hidden(k4_tarski(X5,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ sP6(X0,X1) ) ) ),
    inference(rectify,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( sP6(X0,X1)
        | ? [X3] :
            ( ? [X4] :
                ( ~ r2_hidden(X4,X0)
                & r2_hidden(k4_tarski(X4,X3),X1) )
            & r2_hidden(X3,X0) ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(X4,X3),X1) )
            | ~ r2_hidden(X3,X0) )
        | ~ sP6(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( sP6(X0,X1)
    <=> ! [X3] :
          ( ! [X4] :
              ( r2_hidden(X4,X0)
              | ~ r2_hidden(k4_tarski(X4,X3),X1) )
          | ~ r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f206,plain,(
    ! [X0] : sP6(k1_wellord1(sK10,X0),sK10) ),
    inference(subsumption_resolution,[],[f205,f187])).

fof(f187,plain,(
    ! [X2,X3] :
      ( sP6(k1_wellord1(sK10,X2),X3)
      | r2_hidden(X2,k3_relat_1(sK10)) ) ),
    inference(resolution,[],[f166,f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK10)
      | r2_hidden(X1,k3_relat_1(sK10)) ) ),
    inference(resolution,[],[f130,f77])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(f166,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK19(k1_wellord1(sK10,X0),X1),X0),sK10)
      | sP6(k1_wellord1(sK10,X0),X1) ) ),
    inference(resolution,[],[f165,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK19(X0,X1),X0)
      | sP6(X0,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f205,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_relat_1(sK10))
      | sP6(k1_wellord1(sK10,X0),sK10) ) ),
    inference(resolution,[],[f203,f133])).

fof(f133,plain,(
    ! [X0,X3] :
      ( ~ sP7(X0,k1_wellord1(X0,X3))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | sP6(k1_wellord1(X0,X3),X0) ) ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,(
    ! [X0,X3,X1] :
      ( sP6(X1,X0)
      | k1_wellord1(X0,X3) != X1
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ sP7(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_wellord1(X0,sK18(X0,X1)) = X1
            & r2_hidden(sK18(X0,X1),k3_relat_1(X0)) )
          | k3_relat_1(X0) = X1
          | ~ sP6(X1,X0) )
        & ( sP6(X1,X0)
          | ( ! [X3] :
                ( k1_wellord1(X0,X3) != X1
                | ~ r2_hidden(X3,k3_relat_1(X0)) )
            & k3_relat_1(X0) != X1 ) ) )
      | ~ sP7(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f65,f66])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_wellord1(X0,X2) = X1
          & r2_hidden(X2,k3_relat_1(X0)) )
     => ( k1_wellord1(X0,sK18(X0,X1)) = X1
        & r2_hidden(sK18(X0,X1),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X0,X2) = X1
              & r2_hidden(X2,k3_relat_1(X0)) )
          | k3_relat_1(X0) = X1
          | ~ sP6(X1,X0) )
        & ( sP6(X1,X0)
          | ( ! [X3] :
                ( k1_wellord1(X0,X3) != X1
                | ~ r2_hidden(X3,k3_relat_1(X0)) )
            & k3_relat_1(X0) != X1 ) ) )
      | ~ sP7(X0,X1) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0
          | ~ sP6(X0,X1) )
        & ( sP6(X0,X1)
          | ( ! [X2] :
                ( k1_wellord1(X1,X2) != X0
                | ~ r2_hidden(X2,k3_relat_1(X1)) )
            & k3_relat_1(X1) != X0 ) ) )
      | ~ sP7(X1,X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0
          | ~ sP6(X0,X1) )
        & ( sP6(X0,X1)
          | ( ! [X2] :
                ( k1_wellord1(X1,X2) != X0
                | ~ r2_hidden(X2,k3_relat_1(X1)) )
            & k3_relat_1(X1) != X0 ) ) )
      | ~ sP7(X1,X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0 )
      <=> sP6(X0,X1) )
      | ~ sP7(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f203,plain,(
    ! [X0] : sP7(sK10,k1_wellord1(sK10,X0)) ),
    inference(resolution,[],[f202,f153])).

fof(f153,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_relat_1(sK10))
      | sP7(sK10,X0) ) ),
    inference(subsumption_resolution,[],[f152,f77])).

fof(f152,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_relat_1(sK10))
      | sP7(sK10,X0)
      | ~ v1_relat_1(sK10) ) ),
    inference(resolution,[],[f125,f78])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | sP7(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( sP7(X1,X0)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f21,f35,f34])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0 )
      <=> ! [X3] :
            ( ! [X4] :
                ( r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(X4,X3),X1) )
            | ~ r2_hidden(X3,X0) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( ? [X2] :
              ( k1_wellord1(X1,X2) = X0
              & r2_hidden(X2,k3_relat_1(X1)) )
          | k3_relat_1(X1) = X0 )
      <=> ! [X3] :
            ( ! [X4] :
                ( r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(X4,X3),X1) )
            | ~ r2_hidden(X3,X0) ) )
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ( r1_tarski(X0,k3_relat_1(X1))
          & v2_wellord1(X1) )
       => ( ~ ( ! [X2] :
                  ~ ( k1_wellord1(X1,X2) = X0
                    & r2_hidden(X2,k3_relat_1(X1)) )
              & k3_relat_1(X1) != X0 )
        <=> ! [X3] :
              ( r2_hidden(X3,X0)
             => ! [X4] :
                  ( r2_hidden(k4_tarski(X4,X3),X1)
                 => r2_hidden(X4,X0) ) ) ) ) ) ),
    inference(rectify,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ( r1_tarski(X0,k3_relat_1(X1))
          & v2_wellord1(X1) )
       => ( ~ ( ! [X2] :
                  ~ ( k1_wellord1(X1,X2) = X0
                    & r2_hidden(X2,k3_relat_1(X1)) )
              & k3_relat_1(X1) != X0 )
        <=> ! [X2] :
              ( r2_hidden(X2,X0)
             => ! [X3] :
                  ( r2_hidden(k4_tarski(X3,X2),X1)
                 => r2_hidden(X3,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_wellord1)).

fof(f202,plain,(
    ! [X0] : r1_tarski(k1_wellord1(sK10,X0),k3_relat_1(sK10)) ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,(
    ! [X0] :
      ( r1_tarski(k1_wellord1(sK10,X0),k3_relat_1(sK10))
      | r1_tarski(k1_wellord1(sK10,X0),k3_relat_1(sK10)) ) ),
    inference(resolution,[],[f192,f128])).

fof(f192,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK21(k1_wellord1(sK10,X4),X5),k3_relat_1(sK10))
      | r1_tarski(k1_wellord1(sK10,X4),X5) ) ),
    inference(resolution,[],[f167,f154])).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK10)
      | r2_hidden(X0,k3_relat_1(sK10)) ) ),
    inference(resolution,[],[f129,f77])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f838,plain,(
    ~ r2_hidden(k4_tarski(sK8,sK9),sK10) ),
    inference(subsumption_resolution,[],[f794,f146])).

fof(f146,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f128,f127])).

fof(f794,plain,
    ( ~ r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK8))
    | ~ r2_hidden(k4_tarski(sK8,sK9),sK10) ),
    inference(backward_demodulation,[],[f82,f791])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n001.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 15:30:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.48  % (31505)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.18/0.48  % (31513)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.18/0.50  % (31491)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.18/0.50  % (31497)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.18/0.51  % (31510)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.18/0.51  % (31502)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.18/0.51  % (31500)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.52  % (31489)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.18/0.52  % (31492)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.18/0.52  % (31501)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.18/0.52  % (31507)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.18/0.52  % (31494)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.18/0.52  % (31490)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.18/0.52  % (31503)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.18/0.52  % (31493)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.18/0.52  % (31515)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.18/0.52  % (31488)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.38/0.52  % (31490)Refutation not found, incomplete strategy% (31490)------------------------------
% 1.38/0.52  % (31490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.52  % (31490)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.52  
% 1.38/0.52  % (31490)Memory used [KB]: 10874
% 1.38/0.52  % (31490)Time elapsed: 0.125 s
% 1.38/0.52  % (31490)------------------------------
% 1.38/0.52  % (31490)------------------------------
% 1.38/0.52  % (31504)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.53  % (31499)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.38/0.53  % (31511)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.38/0.53  % (31516)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.53  % (31506)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.53  % (31517)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.38/0.53  % (31510)Refutation not found, incomplete strategy% (31510)------------------------------
% 1.38/0.53  % (31510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (31510)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.53  
% 1.38/0.53  % (31510)Memory used [KB]: 10874
% 1.38/0.53  % (31510)Time elapsed: 0.108 s
% 1.38/0.53  % (31510)------------------------------
% 1.38/0.53  % (31510)------------------------------
% 1.38/0.53  % (31496)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.38/0.53  % (31495)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.53  % (31498)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.38/0.53  % (31509)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.53  % (31508)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.38/0.54  % (31512)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.54  % (31514)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.23/0.64  % (31495)Refutation found. Thanks to Tanya!
% 2.23/0.64  % SZS status Theorem for theBenchmark
% 2.23/0.64  % SZS output start Proof for theBenchmark
% 2.23/0.64  fof(f893,plain,(
% 2.23/0.64    $false),
% 2.23/0.64    inference(subsumption_resolution,[],[f892,f79])).
% 2.23/0.64  fof(f79,plain,(
% 2.23/0.64    r2_hidden(sK8,k3_relat_1(sK10))),
% 2.23/0.64    inference(cnf_transformation,[],[f40])).
% 2.23/0.64  fof(f40,plain,(
% 2.23/0.64    (~r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) | ~r2_hidden(k4_tarski(sK8,sK9),sK10)) & (r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) | r2_hidden(k4_tarski(sK8,sK9),sK10)) & r2_hidden(sK9,k3_relat_1(sK10)) & r2_hidden(sK8,k3_relat_1(sK10)) & v2_wellord1(sK10) & v1_relat_1(sK10)),
% 2.23/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f38,f39])).
% 2.23/0.64  fof(f39,plain,(
% 2.23/0.64    ? [X0,X1,X2] : ((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2)) => ((~r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) | ~r2_hidden(k4_tarski(sK8,sK9),sK10)) & (r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) | r2_hidden(k4_tarski(sK8,sK9),sK10)) & r2_hidden(sK9,k3_relat_1(sK10)) & r2_hidden(sK8,k3_relat_1(sK10)) & v2_wellord1(sK10) & v1_relat_1(sK10))),
% 2.23/0.64    introduced(choice_axiom,[])).
% 2.23/0.64  fof(f38,plain,(
% 2.23/0.64    ? [X0,X1,X2] : ((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 2.23/0.64    inference(flattening,[],[f37])).
% 2.23/0.64  fof(f37,plain,(
% 2.23/0.64    ? [X0,X1,X2] : (((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 2.23/0.64    inference(nnf_transformation,[],[f13])).
% 2.23/0.64  fof(f13,plain,(
% 2.23/0.64    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 2.23/0.64    inference(flattening,[],[f12])).
% 2.23/0.64  fof(f12,plain,(
% 2.23/0.64    ? [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2))) & v1_relat_1(X2))),
% 2.23/0.64    inference(ennf_transformation,[],[f10])).
% 2.23/0.64  fof(f10,negated_conjecture,(
% 2.23/0.64    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 2.23/0.64    inference(negated_conjecture,[],[f9])).
% 2.23/0.64  fof(f9,conjecture,(
% 2.23/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 2.23/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).
% 2.23/0.64  fof(f892,plain,(
% 2.23/0.64    ~r2_hidden(sK8,k3_relat_1(sK10))),
% 2.23/0.64    inference(resolution,[],[f839,f176])).
% 2.23/0.64  fof(f176,plain,(
% 2.23/0.64    ( ! [X0] : (r2_hidden(k4_tarski(X0,X0),sK10) | ~r2_hidden(X0,k3_relat_1(sK10))) )),
% 2.23/0.64    inference(subsumption_resolution,[],[f175,f77])).
% 2.23/0.64  fof(f77,plain,(
% 2.23/0.64    v1_relat_1(sK10)),
% 2.23/0.64    inference(cnf_transformation,[],[f40])).
% 2.23/0.64  fof(f175,plain,(
% 2.23/0.64    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(sK10)) | r2_hidden(k4_tarski(X0,X0),sK10) | ~v1_relat_1(sK10)) )),
% 2.23/0.64    inference(resolution,[],[f83,f141])).
% 2.23/0.64  fof(f141,plain,(
% 2.23/0.64    v1_relat_2(sK10)),
% 2.23/0.64    inference(resolution,[],[f138,f101])).
% 2.23/0.64  fof(f101,plain,(
% 2.23/0.64    ( ! [X0] : (~sP2(X0) | v1_relat_2(X0)) )),
% 2.23/0.64    inference(cnf_transformation,[],[f56])).
% 2.23/0.64  fof(f56,plain,(
% 2.23/0.64    ! [X0] : ((sP2(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~sP2(X0)))),
% 2.23/0.64    inference(flattening,[],[f55])).
% 2.23/0.64  fof(f55,plain,(
% 2.23/0.64    ! [X0] : ((sP2(X0) | (~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0))) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~sP2(X0)))),
% 2.23/0.64    inference(nnf_transformation,[],[f28])).
% 2.23/0.64  fof(f28,plain,(
% 2.23/0.64    ! [X0] : (sP2(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)))),
% 2.23/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.23/0.64  fof(f138,plain,(
% 2.23/0.64    sP2(sK10)),
% 2.23/0.64    inference(subsumption_resolution,[],[f137,f77])).
% 2.23/0.64  fof(f137,plain,(
% 2.23/0.64    sP2(sK10) | ~v1_relat_1(sK10)),
% 2.23/0.64    inference(resolution,[],[f136,f78])).
% 2.23/0.64  fof(f78,plain,(
% 2.23/0.64    v2_wellord1(sK10)),
% 2.23/0.64    inference(cnf_transformation,[],[f40])).
% 2.23/0.64  fof(f136,plain,(
% 2.23/0.64    ( ! [X0] : (~v2_wellord1(X0) | sP2(X0) | ~v1_relat_1(X0)) )),
% 2.23/0.64    inference(resolution,[],[f99,f107])).
% 2.23/0.64  fof(f107,plain,(
% 2.23/0.64    ( ! [X0] : (sP3(X0) | ~v1_relat_1(X0)) )),
% 2.23/0.64    inference(cnf_transformation,[],[f30])).
% 2.23/0.64  fof(f30,plain,(
% 2.23/0.64    ! [X0] : (sP3(X0) | ~v1_relat_1(X0))),
% 2.23/0.64    inference(definition_folding,[],[f18,f29,f28])).
% 2.23/0.64  fof(f29,plain,(
% 2.23/0.64    ! [X0] : ((v2_wellord1(X0) <=> sP2(X0)) | ~sP3(X0))),
% 2.23/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.23/0.66  fof(f18,plain,(
% 2.23/0.66    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 2.23/0.66    inference(ennf_transformation,[],[f4])).
% 2.23/0.66  fof(f4,axiom,(
% 2.23/0.66    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 2.23/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).
% 2.23/0.66  fof(f99,plain,(
% 2.23/0.66    ( ! [X0] : (~sP3(X0) | ~v2_wellord1(X0) | sP2(X0)) )),
% 2.23/0.66    inference(cnf_transformation,[],[f54])).
% 2.23/0.66  fof(f54,plain,(
% 2.23/0.66    ! [X0] : (((v2_wellord1(X0) | ~sP2(X0)) & (sP2(X0) | ~v2_wellord1(X0))) | ~sP3(X0))),
% 2.23/0.66    inference(nnf_transformation,[],[f29])).
% 2.23/0.66  fof(f83,plain,(
% 2.23/0.66    ( ! [X2,X0] : (~v1_relat_2(X0) | ~r2_hidden(X2,k3_relat_1(X0)) | r2_hidden(k4_tarski(X2,X2),X0) | ~v1_relat_1(X0)) )),
% 2.23/0.66    inference(cnf_transformation,[],[f44])).
% 2.23/0.66  fof(f44,plain,(
% 2.23/0.66    ! [X0] : (((v1_relat_2(X0) | (~r2_hidden(k4_tarski(sK11(X0),sK11(X0)),X0) & r2_hidden(sK11(X0),k3_relat_1(X0)))) & (! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0))) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 2.23/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f42,f43])).
% 2.23/0.66  fof(f43,plain,(
% 2.23/0.66    ! [X0] : (? [X1] : (~r2_hidden(k4_tarski(X1,X1),X0) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK11(X0),sK11(X0)),X0) & r2_hidden(sK11(X0),k3_relat_1(X0))))),
% 2.23/0.66    introduced(choice_axiom,[])).
% 2.23/0.66  fof(f42,plain,(
% 2.23/0.66    ! [X0] : (((v1_relat_2(X0) | ? [X1] : (~r2_hidden(k4_tarski(X1,X1),X0) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0))) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 2.23/0.66    inference(rectify,[],[f41])).
% 2.23/0.66  fof(f41,plain,(
% 2.23/0.66    ! [X0] : (((v1_relat_2(X0) | ? [X1] : (~r2_hidden(k4_tarski(X1,X1),X0) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1] : (r2_hidden(k4_tarski(X1,X1),X0) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 2.23/0.66    inference(nnf_transformation,[],[f14])).
% 2.23/0.66  fof(f14,plain,(
% 2.23/0.66    ! [X0] : ((v1_relat_2(X0) <=> ! [X1] : (r2_hidden(k4_tarski(X1,X1),X0) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 2.23/0.66    inference(ennf_transformation,[],[f5])).
% 2.23/0.66  fof(f5,axiom,(
% 2.23/0.66    ! [X0] : (v1_relat_1(X0) => (v1_relat_2(X0) <=> ! [X1] : (r2_hidden(X1,k3_relat_1(X0)) => r2_hidden(k4_tarski(X1,X1),X0))))),
% 2.23/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).
% 2.23/0.66  fof(f839,plain,(
% 2.23/0.66    ~r2_hidden(k4_tarski(sK8,sK8),sK10)),
% 2.23/0.66    inference(forward_demodulation,[],[f838,f791])).
% 2.23/0.66  fof(f791,plain,(
% 2.23/0.66    sK8 = sK9),
% 2.23/0.66    inference(subsumption_resolution,[],[f790,f149])).
% 2.23/0.66  fof(f149,plain,(
% 2.23/0.66    ( ! [X0] : (~r2_hidden(X0,k1_wellord1(sK10,X0))) )),
% 2.23/0.66    inference(resolution,[],[f148,f132])).
% 2.23/0.66  fof(f132,plain,(
% 2.23/0.66    ( ! [X4,X2,X0] : (~sP4(X0,X4,X2) | ~r2_hidden(X4,X2)) )),
% 2.23/0.66    inference(equality_resolution,[],[f110])).
% 2.23/0.66  fof(f110,plain,(
% 2.23/0.66    ( ! [X4,X2,X0,X1] : (X1 != X4 | ~r2_hidden(X4,X2) | ~sP4(X0,X1,X2)) )),
% 2.23/0.66    inference(cnf_transformation,[],[f62])).
% 2.23/0.66  fof(f62,plain,(
% 2.23/0.66    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ((~r2_hidden(k4_tarski(sK17(X0,X1,X2),X1),X0) | sK17(X0,X1,X2) = X1 | ~r2_hidden(sK17(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK17(X0,X1,X2),X1),X0) & sK17(X0,X1,X2) != X1) | r2_hidden(sK17(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | ~sP4(X0,X1,X2)))),
% 2.23/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f60,f61])).
% 2.23/0.66  fof(f61,plain,(
% 2.23/0.66    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK17(X0,X1,X2),X1),X0) | sK17(X0,X1,X2) = X1 | ~r2_hidden(sK17(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK17(X0,X1,X2),X1),X0) & sK17(X0,X1,X2) != X1) | r2_hidden(sK17(X0,X1,X2),X2))))),
% 2.23/0.66    introduced(choice_axiom,[])).
% 2.23/0.66  fof(f60,plain,(
% 2.23/0.66    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | ~sP4(X0,X1,X2)))),
% 2.23/0.66    inference(rectify,[],[f59])).
% 2.23/0.66  fof(f59,plain,(
% 2.23/0.66    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | ~sP4(X0,X1,X2)))),
% 2.23/0.66    inference(flattening,[],[f58])).
% 2.23/0.66  fof(f58,plain,(
% 2.23/0.66    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | ~sP4(X0,X1,X2)))),
% 2.23/0.66    inference(nnf_transformation,[],[f31])).
% 2.23/0.66  fof(f31,plain,(
% 2.23/0.66    ! [X0,X1,X2] : (sP4(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3)))),
% 2.23/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 2.23/0.66  fof(f148,plain,(
% 2.23/0.66    ( ! [X0] : (sP4(sK10,X0,k1_wellord1(sK10,X0))) )),
% 2.23/0.66    inference(resolution,[],[f147,f77])).
% 2.23/0.66  fof(f147,plain,(
% 2.23/0.66    ( ! [X0,X1] : (~v1_relat_1(X0) | sP4(X0,X1,k1_wellord1(X0,X1))) )),
% 2.23/0.66    inference(resolution,[],[f131,f116])).
% 2.23/0.66  fof(f116,plain,(
% 2.23/0.66    ( ! [X0] : (sP5(X0) | ~v1_relat_1(X0)) )),
% 2.23/0.66    inference(cnf_transformation,[],[f33])).
% 2.23/0.66  fof(f33,plain,(
% 2.23/0.66    ! [X0] : (sP5(X0) | ~v1_relat_1(X0))),
% 2.23/0.66    inference(definition_folding,[],[f19,f32,f31])).
% 2.23/0.66  fof(f32,plain,(
% 2.23/0.66    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> sP4(X0,X1,X2)) | ~sP5(X0))),
% 2.23/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 2.23/0.66  fof(f19,plain,(
% 2.23/0.66    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 2.23/0.66    inference(ennf_transformation,[],[f3])).
% 2.23/0.66  fof(f3,axiom,(
% 2.23/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 2.23/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).
% 2.23/0.66  fof(f131,plain,(
% 2.23/0.66    ( ! [X0,X1] : (~sP5(X0) | sP4(X0,X1,k1_wellord1(X0,X1))) )),
% 2.23/0.66    inference(equality_resolution,[],[f108])).
% 2.23/0.66  fof(f108,plain,(
% 2.23/0.66    ( ! [X2,X0,X1] : (sP4(X0,X1,X2) | k1_wellord1(X0,X1) != X2 | ~sP5(X0)) )),
% 2.23/0.66    inference(cnf_transformation,[],[f57])).
% 2.23/0.66  fof(f57,plain,(
% 2.23/0.66    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ~sP4(X0,X1,X2)) & (sP4(X0,X1,X2) | k1_wellord1(X0,X1) != X2)) | ~sP5(X0))),
% 2.23/0.66    inference(nnf_transformation,[],[f32])).
% 2.23/0.66  fof(f790,plain,(
% 2.23/0.66    sK8 = sK9 | r2_hidden(sK9,k1_wellord1(sK10,sK9))),
% 2.23/0.66    inference(duplicate_literal_removal,[],[f778])).
% 2.23/0.66  fof(f778,plain,(
% 2.23/0.66    sK8 = sK9 | r2_hidden(sK9,k1_wellord1(sK10,sK9)) | sK8 = sK9),
% 2.23/0.66    inference(resolution,[],[f719,f753])).
% 2.23/0.66  fof(f753,plain,(
% 2.23/0.66    r2_hidden(k4_tarski(sK9,sK8),sK10) | sK8 = sK9),
% 2.23/0.66    inference(subsumption_resolution,[],[f745,f732])).
% 2.23/0.66  fof(f732,plain,(
% 2.23/0.66    ~r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) | sK8 = sK9),
% 2.23/0.66    inference(resolution,[],[f716,f82])).
% 2.23/0.66  fof(f82,plain,(
% 2.23/0.66    ~r2_hidden(k4_tarski(sK8,sK9),sK10) | ~r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9))),
% 2.23/0.66    inference(cnf_transformation,[],[f40])).
% 2.23/0.66  fof(f716,plain,(
% 2.23/0.66    r2_hidden(k4_tarski(sK8,sK9),sK10) | sK8 = sK9),
% 2.23/0.66    inference(resolution,[],[f715,f165])).
% 2.23/0.66  fof(f165,plain,(
% 2.23/0.66    ( ! [X0,X1] : (~r2_hidden(X0,k1_wellord1(sK10,X1)) | r2_hidden(k4_tarski(X0,X1),sK10)) )),
% 2.23/0.66    inference(resolution,[],[f111,f148])).
% 2.23/0.66  fof(f111,plain,(
% 2.23/0.66    ( ! [X4,X2,X0,X1] : (~sP4(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(k4_tarski(X4,X1),X0)) )),
% 2.23/0.66    inference(cnf_transformation,[],[f62])).
% 2.23/0.66  fof(f715,plain,(
% 2.23/0.66    r2_hidden(sK8,k1_wellord1(sK10,sK9)) | sK8 = sK9),
% 2.23/0.66    inference(subsumption_resolution,[],[f714,f181])).
% 2.23/0.66  fof(f181,plain,(
% 2.23/0.66    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK10) | X0 = X1 | r2_hidden(X0,k1_wellord1(sK10,X1))) )),
% 2.23/0.66    inference(resolution,[],[f112,f148])).
% 2.23/0.66  fof(f112,plain,(
% 2.23/0.66    ( ! [X4,X2,X0,X1] : (~sP4(X0,X1,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | r2_hidden(X4,X2)) )),
% 2.23/0.66    inference(cnf_transformation,[],[f62])).
% 2.23/0.66  fof(f714,plain,(
% 2.23/0.66    sK8 = sK9 | r2_hidden(sK8,k1_wellord1(sK10,sK9)) | r2_hidden(k4_tarski(sK8,sK9),sK10)),
% 2.23/0.66    inference(subsumption_resolution,[],[f705,f149])).
% 2.23/0.66  fof(f705,plain,(
% 2.23/0.66    sK8 = sK9 | r2_hidden(sK8,k1_wellord1(sK10,sK9)) | r2_hidden(k4_tarski(sK8,sK9),sK10) | r2_hidden(sK9,k1_wellord1(sK10,sK9))),
% 2.23/0.66    inference(resolution,[],[f703,f164])).
% 2.23/0.66  fof(f164,plain,(
% 2.23/0.66    ( ! [X0] : (~r2_hidden(X0,k1_wellord1(sK10,sK8)) | r2_hidden(k4_tarski(sK8,sK9),sK10) | r2_hidden(X0,k1_wellord1(sK10,sK9))) )),
% 2.23/0.66    inference(resolution,[],[f81,f126])).
% 2.23/0.66  fof(f126,plain,(
% 2.23/0.66    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 2.23/0.66    inference(cnf_transformation,[],[f76])).
% 2.23/0.66  fof(f76,plain,(
% 2.23/0.66    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK21(X0,X1),X1) & r2_hidden(sK21(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.23/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21])],[f74,f75])).
% 2.23/0.66  fof(f75,plain,(
% 2.23/0.66    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK21(X0,X1),X1) & r2_hidden(sK21(X0,X1),X0)))),
% 2.23/0.66    introduced(choice_axiom,[])).
% 2.23/0.66  fof(f74,plain,(
% 2.23/0.66    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.23/0.66    inference(rectify,[],[f73])).
% 2.23/0.66  fof(f73,plain,(
% 2.23/0.66    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.23/0.66    inference(nnf_transformation,[],[f22])).
% 2.23/0.66  fof(f22,plain,(
% 2.23/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.23/0.66    inference(ennf_transformation,[],[f1])).
% 2.23/0.66  fof(f1,axiom,(
% 2.23/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.23/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.23/0.66  fof(f81,plain,(
% 2.23/0.66    r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) | r2_hidden(k4_tarski(sK8,sK9),sK10)),
% 2.23/0.66    inference(cnf_transformation,[],[f40])).
% 2.23/0.66  fof(f703,plain,(
% 2.23/0.66    r2_hidden(sK9,k1_wellord1(sK10,sK8)) | sK8 = sK9 | r2_hidden(sK8,k1_wellord1(sK10,sK9))),
% 2.23/0.66    inference(duplicate_literal_removal,[],[f700])).
% 2.23/0.66  fof(f700,plain,(
% 2.23/0.66    sK8 = sK9 | r2_hidden(sK9,k1_wellord1(sK10,sK8)) | sK8 = sK9 | r2_hidden(sK8,k1_wellord1(sK10,sK9))),
% 2.23/0.66    inference(resolution,[],[f697,f181])).
% 2.23/0.66  fof(f697,plain,(
% 2.23/0.66    r2_hidden(k4_tarski(sK8,sK9),sK10) | sK8 = sK9 | r2_hidden(sK9,k1_wellord1(sK10,sK8))),
% 2.23/0.66    inference(duplicate_literal_removal,[],[f694])).
% 2.23/0.66  fof(f694,plain,(
% 2.23/0.66    r2_hidden(k4_tarski(sK8,sK9),sK10) | sK8 = sK9 | sK8 = sK9 | r2_hidden(sK9,k1_wellord1(sK10,sK8))),
% 2.23/0.66    inference(resolution,[],[f663,f181])).
% 2.23/0.66  fof(f663,plain,(
% 2.23/0.66    r2_hidden(k4_tarski(sK9,sK8),sK10) | r2_hidden(k4_tarski(sK8,sK9),sK10) | sK8 = sK9),
% 2.23/0.66    inference(resolution,[],[f626,f80])).
% 2.23/0.66  fof(f80,plain,(
% 2.23/0.66    r2_hidden(sK9,k3_relat_1(sK10))),
% 2.23/0.66    inference(cnf_transformation,[],[f40])).
% 2.23/0.66  fof(f626,plain,(
% 2.23/0.66    ( ! [X22] : (~r2_hidden(X22,k3_relat_1(sK10)) | sK8 = X22 | r2_hidden(k4_tarski(sK8,X22),sK10) | r2_hidden(k4_tarski(X22,sK8),sK10)) )),
% 2.23/0.66    inference(resolution,[],[f359,f79])).
% 2.23/0.66  fof(f359,plain,(
% 2.23/0.66    ( ! [X0,X1] : (~r2_hidden(X0,k3_relat_1(sK10)) | X0 = X1 | ~r2_hidden(X1,k3_relat_1(sK10)) | r2_hidden(k4_tarski(X0,X1),sK10) | r2_hidden(k4_tarski(X1,X0),sK10)) )),
% 2.23/0.66    inference(resolution,[],[f88,f144])).
% 2.23/0.66  fof(f144,plain,(
% 2.23/0.66    sP0(sK10)),
% 2.23/0.66    inference(subsumption_resolution,[],[f143,f77])).
% 2.23/0.66  fof(f143,plain,(
% 2.23/0.66    sP0(sK10) | ~v1_relat_1(sK10)),
% 2.23/0.66    inference(resolution,[],[f142,f94])).
% 2.23/0.66  fof(f94,plain,(
% 2.23/0.66    ( ! [X0] : (sP1(X0) | ~v1_relat_1(X0)) )),
% 2.23/0.66    inference(cnf_transformation,[],[f27])).
% 2.23/0.66  fof(f27,plain,(
% 2.23/0.66    ! [X0] : (sP1(X0) | ~v1_relat_1(X0))),
% 2.23/0.66    inference(definition_folding,[],[f15,f26,f25])).
% 2.23/0.66  fof(f25,plain,(
% 2.23/0.66    ! [X0] : (sP0(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0))))),
% 2.23/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.23/0.66  fof(f26,plain,(
% 2.23/0.66    ! [X0] : ((v6_relat_2(X0) <=> sP0(X0)) | ~sP1(X0))),
% 2.23/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.23/0.66  fof(f15,plain,(
% 2.23/0.66    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 2.23/0.66    inference(ennf_transformation,[],[f7])).
% 2.23/0.66  fof(f7,axiom,(
% 2.23/0.66    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 2.23/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).
% 2.23/0.66  fof(f142,plain,(
% 2.23/0.66    ~sP1(sK10) | sP0(sK10)),
% 2.23/0.66    inference(resolution,[],[f139,f86])).
% 2.23/0.66  fof(f86,plain,(
% 2.23/0.66    ( ! [X0] : (~v6_relat_2(X0) | sP0(X0) | ~sP1(X0)) )),
% 2.23/0.66    inference(cnf_transformation,[],[f45])).
% 2.23/0.66  fof(f45,plain,(
% 2.23/0.66    ! [X0] : (((v6_relat_2(X0) | ~sP0(X0)) & (sP0(X0) | ~v6_relat_2(X0))) | ~sP1(X0))),
% 2.23/0.66    inference(nnf_transformation,[],[f26])).
% 2.23/0.66  fof(f139,plain,(
% 2.23/0.66    v6_relat_2(sK10)),
% 2.23/0.66    inference(resolution,[],[f138,f104])).
% 2.23/0.66  fof(f104,plain,(
% 2.23/0.66    ( ! [X0] : (~sP2(X0) | v6_relat_2(X0)) )),
% 2.23/0.66    inference(cnf_transformation,[],[f56])).
% 2.23/0.66  fof(f88,plain,(
% 2.23/0.66    ( ! [X4,X0,X3] : (~sP0(X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | r2_hidden(k4_tarski(X4,X3),X0)) )),
% 2.23/0.66    inference(cnf_transformation,[],[f49])).
% 2.23/0.66  fof(f49,plain,(
% 2.23/0.66    ! [X0] : ((sP0(X0) | (~r2_hidden(k4_tarski(sK13(X0),sK12(X0)),X0) & ~r2_hidden(k4_tarski(sK12(X0),sK13(X0)),X0) & sK12(X0) != sK13(X0) & r2_hidden(sK13(X0),k3_relat_1(X0)) & r2_hidden(sK12(X0),k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~sP0(X0)))),
% 2.23/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f47,f48])).
% 2.23/0.66  fof(f48,plain,(
% 2.23/0.66    ! [X0] : (? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK13(X0),sK12(X0)),X0) & ~r2_hidden(k4_tarski(sK12(X0),sK13(X0)),X0) & sK12(X0) != sK13(X0) & r2_hidden(sK13(X0),k3_relat_1(X0)) & r2_hidden(sK12(X0),k3_relat_1(X0))))),
% 2.23/0.66    introduced(choice_axiom,[])).
% 2.23/0.66  fof(f47,plain,(
% 2.23/0.66    ! [X0] : ((sP0(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~sP0(X0)))),
% 2.23/0.66    inference(rectify,[],[f46])).
% 2.23/0.66  fof(f46,plain,(
% 2.23/0.66    ! [X0] : ((sP0(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0))) | ~sP0(X0)))),
% 2.23/0.66    inference(nnf_transformation,[],[f25])).
% 2.23/0.66  fof(f745,plain,(
% 2.23/0.66    r2_hidden(k4_tarski(sK9,sK8),sK10) | r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) | sK8 = sK9),
% 2.23/0.66    inference(superposition,[],[f167,f738])).
% 2.23/0.66  fof(f738,plain,(
% 2.23/0.66    sK9 = sK21(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) | sK8 = sK9),
% 2.23/0.66    inference(resolution,[],[f732,f605])).
% 2.23/0.66  fof(f605,plain,(
% 2.23/0.66    r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) | sK9 = sK21(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9))),
% 2.23/0.66    inference(duplicate_literal_removal,[],[f597])).
% 2.23/0.66  fof(f597,plain,(
% 2.23/0.66    sK9 = sK21(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) | r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9)) | r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK9))),
% 2.23/0.66    inference(resolution,[],[f310,f128])).
% 2.23/0.66  fof(f128,plain,(
% 2.23/0.66    ( ! [X0,X1] : (~r2_hidden(sK21(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.23/0.66    inference(cnf_transformation,[],[f76])).
% 2.23/0.66  fof(f310,plain,(
% 2.23/0.66    ( ! [X2] : (r2_hidden(sK21(k1_wellord1(sK10,sK8),X2),k1_wellord1(sK10,sK9)) | sK9 = sK21(k1_wellord1(sK10,sK8),X2) | r1_tarski(k1_wellord1(sK10,sK8),X2)) )),
% 2.23/0.66    inference(resolution,[],[f308,f181])).
% 2.23/0.66  fof(f308,plain,(
% 2.23/0.66    ( ! [X5] : (r2_hidden(k4_tarski(sK21(k1_wellord1(sK10,sK8),X5),sK9),sK10) | r1_tarski(k1_wellord1(sK10,sK8),X5)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f306,f283])).
% 2.23/0.66  fof(f283,plain,(
% 2.23/0.66    ( ! [X6,X7,X5] : (r2_hidden(k4_tarski(sK21(k1_wellord1(sK10,X5),X7),X6),sK10) | ~r2_hidden(k4_tarski(X5,X6),sK10) | r1_tarski(k1_wellord1(sK10,X5),X7)) )),
% 2.23/0.66    inference(resolution,[],[f280,f167])).
% 2.23/0.66  fof(f280,plain,(
% 2.23/0.66    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X2,X0),sK10) | ~r2_hidden(k4_tarski(X0,X1),sK10) | r2_hidden(k4_tarski(X2,X1),sK10)) )),
% 2.23/0.66    inference(subsumption_resolution,[],[f279,f77])).
% 2.23/0.66  fof(f279,plain,(
% 2.23/0.66    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK10) | ~r2_hidden(k4_tarski(X2,X0),sK10) | r2_hidden(k4_tarski(X2,X1),sK10) | ~v1_relat_1(sK10)) )),
% 2.23/0.66    inference(resolution,[],[f95,f140])).
% 2.23/0.66  fof(f140,plain,(
% 2.23/0.66    v8_relat_2(sK10)),
% 2.23/0.66    inference(resolution,[],[f138,f102])).
% 2.23/0.66  fof(f102,plain,(
% 2.23/0.66    ( ! [X0] : (~sP2(X0) | v8_relat_2(X0)) )),
% 2.23/0.66    inference(cnf_transformation,[],[f56])).
% 2.23/0.66  fof(f95,plain,(
% 2.23/0.66    ( ! [X6,X4,X0,X5] : (~v8_relat_2(X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | r2_hidden(k4_tarski(X4,X6),X0) | ~v1_relat_1(X0)) )),
% 2.23/0.66    inference(cnf_transformation,[],[f53])).
% 2.23/0.66  fof(f53,plain,(
% 2.23/0.66    ! [X0] : (((v8_relat_2(X0) | (~r2_hidden(k4_tarski(sK14(X0),sK16(X0)),X0) & r2_hidden(k4_tarski(sK15(X0),sK16(X0)),X0) & r2_hidden(k4_tarski(sK14(X0),sK15(X0)),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 2.23/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15,sK16])],[f51,f52])).
% 2.23/0.66  fof(f52,plain,(
% 2.23/0.66    ! [X0] : (? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (~r2_hidden(k4_tarski(sK14(X0),sK16(X0)),X0) & r2_hidden(k4_tarski(sK15(X0),sK16(X0)),X0) & r2_hidden(k4_tarski(sK14(X0),sK15(X0)),X0)))),
% 2.23/0.67    introduced(choice_axiom,[])).
% 2.23/0.67  fof(f51,plain,(
% 2.23/0.67    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 2.23/0.67    inference(rectify,[],[f50])).
% 2.23/0.67  fof(f50,plain,(
% 2.23/0.67    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 2.23/0.67    inference(nnf_transformation,[],[f17])).
% 2.23/0.67  fof(f17,plain,(
% 2.23/0.67    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 2.23/0.67    inference(flattening,[],[f16])).
% 2.23/0.67  fof(f16,plain,(
% 2.23/0.67    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | (~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 2.23/0.67    inference(ennf_transformation,[],[f6])).
% 2.23/0.67  fof(f6,axiom,(
% 2.23/0.67    ! [X0] : (v1_relat_1(X0) => (v8_relat_2(X0) <=> ! [X1,X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => r2_hidden(k4_tarski(X1,X3),X0))))),
% 2.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_wellord1)).
% 2.23/0.67  fof(f306,plain,(
% 2.23/0.67    ( ! [X5] : (r2_hidden(k4_tarski(sK8,sK9),sK10) | r1_tarski(k1_wellord1(sK10,sK8),X5) | r2_hidden(k4_tarski(sK21(k1_wellord1(sK10,sK8),X5),sK9),sK10)) )),
% 2.23/0.67    inference(resolution,[],[f214,f165])).
% 2.23/0.67  fof(f214,plain,(
% 2.23/0.67    ( ! [X1] : (r2_hidden(sK21(k1_wellord1(sK10,sK8),X1),k1_wellord1(sK10,sK9)) | r2_hidden(k4_tarski(sK8,sK9),sK10) | r1_tarski(k1_wellord1(sK10,sK8),X1)) )),
% 2.23/0.67    inference(resolution,[],[f164,f127])).
% 2.23/0.67  fof(f127,plain,(
% 2.23/0.67    ( ! [X0,X1] : (r2_hidden(sK21(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.23/0.67    inference(cnf_transformation,[],[f76])).
% 2.23/0.67  fof(f167,plain,(
% 2.23/0.67    ( ! [X2,X3] : (r2_hidden(k4_tarski(sK21(k1_wellord1(sK10,X2),X3),X2),sK10) | r1_tarski(k1_wellord1(sK10,X2),X3)) )),
% 2.23/0.67    inference(resolution,[],[f165,f127])).
% 2.23/0.67  fof(f719,plain,(
% 2.23/0.67    ( ! [X1] : (~r2_hidden(k4_tarski(X1,sK8),sK10) | sK8 = sK9 | r2_hidden(X1,k1_wellord1(sK10,sK9))) )),
% 2.23/0.67    inference(resolution,[],[f715,f207])).
% 2.23/0.67  fof(f207,plain,(
% 2.23/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_wellord1(sK10,X2)) | ~r2_hidden(k4_tarski(X0,X1),sK10) | r2_hidden(X0,k1_wellord1(sK10,X2))) )),
% 2.23/0.67    inference(resolution,[],[f206,f121])).
% 2.23/0.67  fof(f121,plain,(
% 2.23/0.67    ( ! [X4,X0,X5,X1] : (~sP6(X0,X1) | ~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(X4,X0) | r2_hidden(X5,X0)) )),
% 2.23/0.67    inference(cnf_transformation,[],[f72])).
% 2.23/0.67  fof(f72,plain,(
% 2.23/0.67    ! [X0,X1] : ((sP6(X0,X1) | ((~r2_hidden(sK20(X0,X1),X0) & r2_hidden(k4_tarski(sK20(X0,X1),sK19(X0,X1)),X1)) & r2_hidden(sK19(X0,X1),X0))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r2_hidden(k4_tarski(X5,X4),X1)) | ~r2_hidden(X4,X0)) | ~sP6(X0,X1)))),
% 2.23/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19,sK20])],[f69,f71,f70])).
% 2.23/0.67  fof(f70,plain,(
% 2.23/0.67    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r2_hidden(k4_tarski(X3,X2),X1)) & r2_hidden(X2,X0)) => (? [X3] : (~r2_hidden(X3,X0) & r2_hidden(k4_tarski(X3,sK19(X0,X1)),X1)) & r2_hidden(sK19(X0,X1),X0)))),
% 2.23/0.67    introduced(choice_axiom,[])).
% 2.23/0.67  fof(f71,plain,(
% 2.23/0.67    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X0) & r2_hidden(k4_tarski(X3,sK19(X0,X1)),X1)) => (~r2_hidden(sK20(X0,X1),X0) & r2_hidden(k4_tarski(sK20(X0,X1),sK19(X0,X1)),X1)))),
% 2.23/0.67    introduced(choice_axiom,[])).
% 2.23/0.67  fof(f69,plain,(
% 2.23/0.67    ! [X0,X1] : ((sP6(X0,X1) | ? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r2_hidden(k4_tarski(X3,X2),X1)) & r2_hidden(X2,X0))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r2_hidden(k4_tarski(X5,X4),X1)) | ~r2_hidden(X4,X0)) | ~sP6(X0,X1)))),
% 2.23/0.67    inference(rectify,[],[f68])).
% 2.23/0.67  fof(f68,plain,(
% 2.23/0.67    ! [X0,X1] : ((sP6(X0,X1) | ? [X3] : (? [X4] : (~r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X3),X1)) & r2_hidden(X3,X0))) & (! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0)) | ~sP6(X0,X1)))),
% 2.23/0.67    inference(nnf_transformation,[],[f34])).
% 2.23/0.67  fof(f34,plain,(
% 2.23/0.67    ! [X0,X1] : (sP6(X0,X1) <=> ! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0)))),
% 2.23/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 2.23/0.67  fof(f206,plain,(
% 2.23/0.67    ( ! [X0] : (sP6(k1_wellord1(sK10,X0),sK10)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f205,f187])).
% 2.23/0.67  fof(f187,plain,(
% 2.23/0.67    ( ! [X2,X3] : (sP6(k1_wellord1(sK10,X2),X3) | r2_hidden(X2,k3_relat_1(sK10))) )),
% 2.23/0.67    inference(resolution,[],[f166,f159])).
% 2.23/0.67  fof(f159,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK10) | r2_hidden(X1,k3_relat_1(sK10))) )),
% 2.23/0.67    inference(resolution,[],[f130,f77])).
% 2.23/0.67  fof(f130,plain,(
% 2.23/0.67    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k3_relat_1(X2))) )),
% 2.23/0.67    inference(cnf_transformation,[],[f24])).
% 2.23/0.67  fof(f24,plain,(
% 2.23/0.67    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 2.23/0.67    inference(flattening,[],[f23])).
% 2.23/0.67  fof(f23,plain,(
% 2.23/0.67    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 2.23/0.67    inference(ennf_transformation,[],[f2])).
% 2.23/0.67  fof(f2,axiom,(
% 2.23/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 2.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).
% 2.23/0.67  fof(f166,plain,(
% 2.23/0.67    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK19(k1_wellord1(sK10,X0),X1),X0),sK10) | sP6(k1_wellord1(sK10,X0),X1)) )),
% 2.23/0.67    inference(resolution,[],[f165,f122])).
% 2.23/0.67  fof(f122,plain,(
% 2.23/0.67    ( ! [X0,X1] : (r2_hidden(sK19(X0,X1),X0) | sP6(X0,X1)) )),
% 2.23/0.67    inference(cnf_transformation,[],[f72])).
% 2.23/0.67  fof(f205,plain,(
% 2.23/0.67    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(sK10)) | sP6(k1_wellord1(sK10,X0),sK10)) )),
% 2.23/0.67    inference(resolution,[],[f203,f133])).
% 2.23/0.67  fof(f133,plain,(
% 2.23/0.67    ( ! [X0,X3] : (~sP7(X0,k1_wellord1(X0,X3)) | ~r2_hidden(X3,k3_relat_1(X0)) | sP6(k1_wellord1(X0,X3),X0)) )),
% 2.23/0.67    inference(equality_resolution,[],[f118])).
% 2.23/0.67  fof(f118,plain,(
% 2.23/0.67    ( ! [X0,X3,X1] : (sP6(X1,X0) | k1_wellord1(X0,X3) != X1 | ~r2_hidden(X3,k3_relat_1(X0)) | ~sP7(X0,X1)) )),
% 2.23/0.67    inference(cnf_transformation,[],[f67])).
% 2.23/0.67  fof(f67,plain,(
% 2.23/0.67    ! [X0,X1] : ((((k1_wellord1(X0,sK18(X0,X1)) = X1 & r2_hidden(sK18(X0,X1),k3_relat_1(X0))) | k3_relat_1(X0) = X1 | ~sP6(X1,X0)) & (sP6(X1,X0) | (! [X3] : (k1_wellord1(X0,X3) != X1 | ~r2_hidden(X3,k3_relat_1(X0))) & k3_relat_1(X0) != X1))) | ~sP7(X0,X1))),
% 2.23/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f65,f66])).
% 2.23/0.67  fof(f66,plain,(
% 2.23/0.67    ! [X1,X0] : (? [X2] : (k1_wellord1(X0,X2) = X1 & r2_hidden(X2,k3_relat_1(X0))) => (k1_wellord1(X0,sK18(X0,X1)) = X1 & r2_hidden(sK18(X0,X1),k3_relat_1(X0))))),
% 2.23/0.67    introduced(choice_axiom,[])).
% 2.23/0.67  fof(f65,plain,(
% 2.23/0.67    ! [X0,X1] : (((? [X2] : (k1_wellord1(X0,X2) = X1 & r2_hidden(X2,k3_relat_1(X0))) | k3_relat_1(X0) = X1 | ~sP6(X1,X0)) & (sP6(X1,X0) | (! [X3] : (k1_wellord1(X0,X3) != X1 | ~r2_hidden(X3,k3_relat_1(X0))) & k3_relat_1(X0) != X1))) | ~sP7(X0,X1))),
% 2.23/0.67    inference(rectify,[],[f64])).
% 2.23/0.67  fof(f64,plain,(
% 2.23/0.67    ! [X1,X0] : (((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0 | ~sP6(X0,X1)) & (sP6(X0,X1) | (! [X2] : (k1_wellord1(X1,X2) != X0 | ~r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0))) | ~sP7(X1,X0))),
% 2.23/0.67    inference(flattening,[],[f63])).
% 2.23/0.67  fof(f63,plain,(
% 2.23/0.67    ! [X1,X0] : ((((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) | ~sP6(X0,X1)) & (sP6(X0,X1) | (! [X2] : (k1_wellord1(X1,X2) != X0 | ~r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0))) | ~sP7(X1,X0))),
% 2.23/0.67    inference(nnf_transformation,[],[f35])).
% 2.23/0.67  fof(f35,plain,(
% 2.23/0.67    ! [X1,X0] : (((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) <=> sP6(X0,X1)) | ~sP7(X1,X0))),
% 2.23/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).
% 2.23/0.67  fof(f203,plain,(
% 2.23/0.67    ( ! [X0] : (sP7(sK10,k1_wellord1(sK10,X0))) )),
% 2.23/0.67    inference(resolution,[],[f202,f153])).
% 2.23/0.67  fof(f153,plain,(
% 2.23/0.67    ( ! [X0] : (~r1_tarski(X0,k3_relat_1(sK10)) | sP7(sK10,X0)) )),
% 2.23/0.67    inference(subsumption_resolution,[],[f152,f77])).
% 2.23/0.67  fof(f152,plain,(
% 2.23/0.67    ( ! [X0] : (~r1_tarski(X0,k3_relat_1(sK10)) | sP7(sK10,X0) | ~v1_relat_1(sK10)) )),
% 2.23/0.67    inference(resolution,[],[f125,f78])).
% 2.23/0.67  fof(f125,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~v2_wellord1(X1) | ~r1_tarski(X0,k3_relat_1(X1)) | sP7(X1,X0) | ~v1_relat_1(X1)) )),
% 2.23/0.67    inference(cnf_transformation,[],[f36])).
% 2.23/0.67  fof(f36,plain,(
% 2.23/0.67    ! [X0,X1] : (sP7(X1,X0) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 2.23/0.67    inference(definition_folding,[],[f21,f35,f34])).
% 2.23/0.67  fof(f21,plain,(
% 2.23/0.67    ! [X0,X1] : (((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) <=> ! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0))) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 2.23/0.67    inference(flattening,[],[f20])).
% 2.23/0.67  fof(f20,plain,(
% 2.23/0.67    ! [X0,X1] : ((((? [X2] : (k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) | k3_relat_1(X1) = X0) <=> ! [X3] : (! [X4] : (r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X3),X1)) | ~r2_hidden(X3,X0))) | (~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1))) | ~v1_relat_1(X1))),
% 2.23/0.67    inference(ennf_transformation,[],[f11])).
% 2.23/0.67  fof(f11,plain,(
% 2.23/0.67    ! [X0,X1] : (v1_relat_1(X1) => ((r1_tarski(X0,k3_relat_1(X1)) & v2_wellord1(X1)) => (~(! [X2] : ~(k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0) <=> ! [X3] : (r2_hidden(X3,X0) => ! [X4] : (r2_hidden(k4_tarski(X4,X3),X1) => r2_hidden(X4,X0))))))),
% 2.23/0.67    inference(rectify,[],[f8])).
% 2.23/0.67  fof(f8,axiom,(
% 2.23/0.67    ! [X0,X1] : (v1_relat_1(X1) => ((r1_tarski(X0,k3_relat_1(X1)) & v2_wellord1(X1)) => (~(! [X2] : ~(k1_wellord1(X1,X2) = X0 & r2_hidden(X2,k3_relat_1(X1))) & k3_relat_1(X1) != X0) <=> ! [X2] : (r2_hidden(X2,X0) => ! [X3] : (r2_hidden(k4_tarski(X3,X2),X1) => r2_hidden(X3,X0))))))),
% 2.23/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_wellord1)).
% 2.23/0.67  fof(f202,plain,(
% 2.23/0.67    ( ! [X0] : (r1_tarski(k1_wellord1(sK10,X0),k3_relat_1(sK10))) )),
% 2.23/0.67    inference(duplicate_literal_removal,[],[f201])).
% 2.23/0.67  fof(f201,plain,(
% 2.23/0.67    ( ! [X0] : (r1_tarski(k1_wellord1(sK10,X0),k3_relat_1(sK10)) | r1_tarski(k1_wellord1(sK10,X0),k3_relat_1(sK10))) )),
% 2.23/0.67    inference(resolution,[],[f192,f128])).
% 2.23/0.67  fof(f192,plain,(
% 2.23/0.67    ( ! [X4,X5] : (r2_hidden(sK21(k1_wellord1(sK10,X4),X5),k3_relat_1(sK10)) | r1_tarski(k1_wellord1(sK10,X4),X5)) )),
% 2.23/0.67    inference(resolution,[],[f167,f154])).
% 2.23/0.67  fof(f154,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK10) | r2_hidden(X0,k3_relat_1(sK10))) )),
% 2.23/0.67    inference(resolution,[],[f129,f77])).
% 2.23/0.67  fof(f129,plain,(
% 2.23/0.67    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k3_relat_1(X2))) )),
% 2.23/0.67    inference(cnf_transformation,[],[f24])).
% 2.23/0.67  fof(f838,plain,(
% 2.23/0.67    ~r2_hidden(k4_tarski(sK8,sK9),sK10)),
% 2.23/0.67    inference(subsumption_resolution,[],[f794,f146])).
% 2.23/0.67  fof(f146,plain,(
% 2.23/0.67    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.23/0.67    inference(duplicate_literal_removal,[],[f145])).
% 2.23/0.67  fof(f145,plain,(
% 2.23/0.67    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 2.23/0.67    inference(resolution,[],[f128,f127])).
% 2.23/0.67  fof(f794,plain,(
% 2.23/0.67    ~r1_tarski(k1_wellord1(sK10,sK8),k1_wellord1(sK10,sK8)) | ~r2_hidden(k4_tarski(sK8,sK9),sK10)),
% 2.23/0.67    inference(backward_demodulation,[],[f82,f791])).
% 2.23/0.67  % SZS output end Proof for theBenchmark
% 2.23/0.67  % (31495)------------------------------
% 2.23/0.67  % (31495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.23/0.67  % (31495)Termination reason: Refutation
% 2.23/0.67  
% 2.23/0.67  % (31495)Memory used [KB]: 7291
% 2.23/0.67  % (31495)Time elapsed: 0.257 s
% 2.23/0.67  % (31495)------------------------------
% 2.23/0.67  % (31495)------------------------------
% 2.23/0.67  % (31487)Success in time 0.326 s
%------------------------------------------------------------------------------
