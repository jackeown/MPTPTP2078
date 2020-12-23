%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 364 expanded)
%              Number of leaves         :   15 ( 111 expanded)
%              Depth                    :   29
%              Number of atoms          :  308 (1212 expanded)
%              Number of equality atoms :   39 ( 184 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f312,plain,(
    $false ),
    inference(subsumption_resolution,[],[f309,f43])).

fof(f43,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f309,plain,(
    ~ v1_relat_1(k1_wellord2(sK6)) ),
    inference(resolution,[],[f305,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( sP5(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( sP5(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f12,f21,f20,f19,f18])).

fof(f18,plain,(
    ! [X3,X2,X1] :
      ( sP2(X3,X2,X1)
    <=> ( r2_hidden(k4_tarski(X2,X3),X1)
      <=> r1_tarski(X2,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f19,plain,(
    ! [X1,X0] :
      ( sP3(X1,X0)
    <=> ! [X2,X3] :
          ( sP2(X3,X2,X1)
          | ~ r2_hidden(X3,X0)
          | ~ r2_hidden(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f20,plain,(
    ! [X0,X1] :
      ( sP4(X0,X1)
    <=> ( sP3(X1,X0)
        & k3_relat_1(X1) = X0 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ( k1_wellord2(X0) = X1
      <=> sP4(X0,X1) )
      | ~ sP5(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f305,plain,(
    ~ sP5(k1_wellord2(sK6),sK6) ),
    inference(resolution,[],[f304,f70])).

fof(f70,plain,(
    ! [X1] :
      ( sP4(X1,k1_wellord2(X1))
      | ~ sP5(k1_wellord2(X1),X1) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( sP4(X1,X0)
      | k1_wellord2(X1) != X0
      | ~ sP5(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X1) = X0
          | ~ sP4(X1,X0) )
        & ( sP4(X1,X0)
          | k1_wellord2(X1) != X0 ) )
      | ~ sP5(X0,X1) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ( ( k1_wellord2(X0) = X1
          | ~ sP4(X0,X1) )
        & ( sP4(X0,X1)
          | k1_wellord2(X0) != X1 ) )
      | ~ sP5(X1,X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f304,plain,(
    ! [X0] : ~ sP4(X0,k1_wellord2(sK6)) ),
    inference(subsumption_resolution,[],[f303,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ~ sP3(X1,X0)
        | k3_relat_1(X1) != X0 )
      & ( ( sP3(X1,X0)
          & k3_relat_1(X1) = X0 )
        | ~ sP4(X0,X1) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ~ sP3(X1,X0)
        | k3_relat_1(X1) != X0 )
      & ( ( sP3(X1,X0)
          & k3_relat_1(X1) = X0 )
        | ~ sP4(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f303,plain,(
    ! [X0] :
      ( ~ sP3(k1_wellord2(sK6),X0)
      | ~ sP4(X0,k1_wellord2(sK6)) ) ),
    inference(superposition,[],[f297,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f297,plain,(
    ~ sP3(k1_wellord2(sK6),k3_relat_1(k1_wellord2(sK6))) ),
    inference(subsumption_resolution,[],[f296,f257])).

fof(f257,plain,(
    ~ r1_tarski(sK8(k1_wellord2(sK6)),sK7(k1_wellord2(sK6))) ),
    inference(subsumption_resolution,[],[f252,f81])).

fof(f81,plain,(
    sK7(k1_wellord2(sK6)) != sK8(k1_wellord2(sK6)) ),
    inference(resolution,[],[f78,f49])).

fof(f49,plain,(
    ! [X0] :
      ( sP0(X0)
      | sK7(X0) != sK8(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( sK7(X0) != sK8(X0)
          & r2_hidden(k4_tarski(sK8(X0),sK7(X0)),X0)
          & r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | ~ r2_hidden(k4_tarski(X4,X3),X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X0) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f27,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & r2_hidden(k4_tarski(X2,X1),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( sK7(X0) != sK8(X0)
        & r2_hidden(k4_tarski(sK8(X0),sK7(X0)),X0)
        & r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & r2_hidden(k4_tarski(X2,X1),X0)
            & r2_hidden(k4_tarski(X1,X2),X0) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | ~ r2_hidden(k4_tarski(X4,X3),X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X0) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & r2_hidden(k4_tarski(X2,X1),X0)
            & r2_hidden(k4_tarski(X1,X2),X0) ) )
      & ( ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1,X2] :
          ( X1 = X2
          | ~ r2_hidden(k4_tarski(X2,X1),X0)
          | ~ r2_hidden(k4_tarski(X1,X2),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f78,plain,(
    ~ sP0(k1_wellord2(sK6)) ),
    inference(subsumption_resolution,[],[f76,f43])).

fof(f76,plain,
    ( ~ sP0(k1_wellord2(sK6))
    | ~ v1_relat_1(k1_wellord2(sK6)) ),
    inference(resolution,[],[f74,f50])).

fof(f50,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f10,f16,f15])).

fof(f16,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f10,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( ( r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).

fof(f74,plain,
    ( ~ sP1(k1_wellord2(sK6))
    | ~ sP0(k1_wellord2(sK6)) ),
    inference(resolution,[],[f42,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ sP0(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v4_relat_2(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f42,plain,(
    ~ v4_relat_2(k1_wellord2(sK6)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ~ v4_relat_2(k1_wellord2(sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f8,f23])).

fof(f23,plain,
    ( ? [X0] : ~ v4_relat_2(k1_wellord2(X0))
   => ~ v4_relat_2(k1_wellord2(sK6)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] : ~ v4_relat_2(k1_wellord2(X0)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : v4_relat_2(k1_wellord2(X0)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : v4_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_wellord2)).

fof(f252,plain,
    ( sK7(k1_wellord2(sK6)) = sK8(k1_wellord2(sK6))
    | ~ r1_tarski(sK8(k1_wellord2(sK6)),sK7(k1_wellord2(sK6))) ),
    inference(resolution,[],[f250,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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

fof(f250,plain,(
    r1_tarski(sK7(k1_wellord2(sK6)),sK8(k1_wellord2(sK6))) ),
    inference(subsumption_resolution,[],[f248,f135])).

fof(f135,plain,(
    r2_hidden(sK8(k1_wellord2(sK6)),sK6) ),
    inference(subsumption_resolution,[],[f132,f43])).

fof(f132,plain,
    ( r2_hidden(sK8(k1_wellord2(sK6)),sK6)
    | ~ v1_relat_1(k1_wellord2(sK6)) ),
    inference(resolution,[],[f121,f64])).

fof(f121,plain,
    ( ~ sP5(k1_wellord2(sK6),sK6)
    | r2_hidden(sK8(k1_wellord2(sK6)),sK6) ),
    inference(resolution,[],[f108,f70])).

fof(f108,plain,(
    ! [X0] :
      ( ~ sP4(X0,k1_wellord2(sK6))
      | r2_hidden(sK8(k1_wellord2(sK6)),X0) ) ),
    inference(superposition,[],[f100,f53])).

fof(f100,plain,(
    r2_hidden(sK8(k1_wellord2(sK6)),k3_relat_1(k1_wellord2(sK6))) ),
    inference(subsumption_resolution,[],[f91,f43])).

fof(f91,plain,
    ( r2_hidden(sK8(k1_wellord2(sK6)),k3_relat_1(k1_wellord2(sK6)))
    | ~ v1_relat_1(k1_wellord2(sK6)) ),
    inference(resolution,[],[f79,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f79,plain,(
    r2_hidden(k4_tarski(sK7(k1_wellord2(sK6)),sK8(k1_wellord2(sK6))),k1_wellord2(sK6)) ),
    inference(resolution,[],[f78,f47])).

fof(f47,plain,(
    ! [X0] :
      ( sP0(X0)
      | r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f248,plain,
    ( ~ r2_hidden(sK8(k1_wellord2(sK6)),sK6)
    | r1_tarski(sK7(k1_wellord2(sK6)),sK8(k1_wellord2(sK6))) ),
    inference(resolution,[],[f245,f92])).

fof(f92,plain,
    ( ~ sP2(sK8(k1_wellord2(sK6)),sK7(k1_wellord2(sK6)),k1_wellord2(sK6))
    | r1_tarski(sK7(k1_wellord2(sK6)),sK8(k1_wellord2(sK6))) ),
    inference(resolution,[],[f79,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(k4_tarski(X1,X0),X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ~ r1_tarski(X1,X0)
            | ~ r2_hidden(k4_tarski(X1,X0),X2) )
          & ( r1_tarski(X1,X0)
            | r2_hidden(k4_tarski(X1,X0),X2) ) ) )
      & ( ( ( r2_hidden(k4_tarski(X1,X0),X2)
            | ~ r1_tarski(X1,X0) )
          & ( r1_tarski(X1,X0)
            | ~ r2_hidden(k4_tarski(X1,X0),X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X3,X2,X1] :
      ( ( sP2(X3,X2,X1)
        | ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
      & ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r1_tarski(X2,X3) )
          & ( r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
        | ~ sP2(X3,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f245,plain,(
    ! [X0] :
      ( sP2(X0,sK7(k1_wellord2(sK6)),k1_wellord2(sK6))
      | ~ r2_hidden(X0,sK6) ) ),
    inference(subsumption_resolution,[],[f242,f43])).

fof(f242,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK6)
      | sP2(X0,sK7(k1_wellord2(sK6)),k1_wellord2(sK6))
      | ~ v1_relat_1(k1_wellord2(sK6)) ) ),
    inference(resolution,[],[f183,f64])).

fof(f183,plain,(
    ! [X0] :
      ( ~ sP5(k1_wellord2(sK6),sK6)
      | ~ r2_hidden(X0,sK6)
      | sP2(X0,sK7(k1_wellord2(sK6)),k1_wellord2(sK6)) ) ),
    inference(resolution,[],[f165,f70])).

fof(f165,plain,(
    ! [X6,X7] :
      ( ~ sP4(sK6,X7)
      | sP2(X6,sK7(k1_wellord2(sK6)),X7)
      | ~ r2_hidden(X6,sK6) ) ),
    inference(resolution,[],[f128,f54])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ sP3(X1,sK6)
      | ~ r2_hidden(X0,sK6)
      | sP2(X0,sK7(k1_wellord2(sK6)),X1) ) ),
    inference(resolution,[],[f127,f56])).

fof(f56,plain,(
    ! [X4,X0,X5,X1] :
      ( sP2(X5,X4,X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ( ~ sP2(sK10(X0,X1),sK9(X0,X1),X0)
          & r2_hidden(sK10(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X1) ) )
      & ( ! [X4,X5] :
            ( sP2(X5,X4,X0)
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X1) )
        | ~ sP3(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ sP2(X3,X2,X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ sP2(sK10(X0,X1),sK9(X0,X1),X0)
        & r2_hidden(sK10(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ? [X2,X3] :
            ( ~ sP2(X3,X2,X0)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) ) )
      & ( ! [X4,X5] :
            ( sP2(X5,X4,X0)
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X1) )
        | ~ sP3(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ( sP3(X1,X0)
        | ? [X2,X3] :
            ( ~ sP2(X3,X2,X1)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2,X3] :
            ( sP2(X3,X2,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ sP3(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f127,plain,(
    r2_hidden(sK7(k1_wellord2(sK6)),sK6) ),
    inference(subsumption_resolution,[],[f124,f43])).

fof(f124,plain,
    ( r2_hidden(sK7(k1_wellord2(sK6)),sK6)
    | ~ v1_relat_1(k1_wellord2(sK6)) ),
    inference(resolution,[],[f118,f64])).

fof(f118,plain,
    ( ~ sP5(k1_wellord2(sK6),sK6)
    | r2_hidden(sK7(k1_wellord2(sK6)),sK6) ),
    inference(resolution,[],[f104,f70])).

fof(f104,plain,(
    ! [X0] :
      ( ~ sP4(X0,k1_wellord2(sK6))
      | r2_hidden(sK7(k1_wellord2(sK6)),X0) ) ),
    inference(superposition,[],[f99,f53])).

fof(f99,plain,(
    r2_hidden(sK7(k1_wellord2(sK6)),k3_relat_1(k1_wellord2(sK6))) ),
    inference(subsumption_resolution,[],[f90,f43])).

fof(f90,plain,
    ( r2_hidden(sK7(k1_wellord2(sK6)),k3_relat_1(k1_wellord2(sK6)))
    | ~ v1_relat_1(k1_wellord2(sK6)) ),
    inference(resolution,[],[f79,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f296,plain,
    ( ~ sP3(k1_wellord2(sK6),k3_relat_1(k1_wellord2(sK6)))
    | r1_tarski(sK8(k1_wellord2(sK6)),sK7(k1_wellord2(sK6))) ),
    inference(subsumption_resolution,[],[f292,f100])).

fof(f292,plain,
    ( ~ r2_hidden(sK8(k1_wellord2(sK6)),k3_relat_1(k1_wellord2(sK6)))
    | ~ sP3(k1_wellord2(sK6),k3_relat_1(k1_wellord2(sK6)))
    | r1_tarski(sK8(k1_wellord2(sK6)),sK7(k1_wellord2(sK6))) ),
    inference(resolution,[],[f102,f111])).

fof(f111,plain,
    ( ~ sP2(sK7(k1_wellord2(sK6)),sK8(k1_wellord2(sK6)),k1_wellord2(sK6))
    | r1_tarski(sK8(k1_wellord2(sK6)),sK7(k1_wellord2(sK6))) ),
    inference(resolution,[],[f80,f60])).

fof(f80,plain,(
    r2_hidden(k4_tarski(sK8(k1_wellord2(sK6)),sK7(k1_wellord2(sK6))),k1_wellord2(sK6)) ),
    inference(resolution,[],[f78,f48])).

fof(f48,plain,(
    ! [X0] :
      ( sP0(X0)
      | r2_hidden(k4_tarski(sK8(X0),sK7(X0)),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f102,plain,(
    ! [X2,X3] :
      ( sP2(sK7(k1_wellord2(sK6)),X2,X3)
      | ~ r2_hidden(X2,k3_relat_1(k1_wellord2(sK6)))
      | ~ sP3(X3,k3_relat_1(k1_wellord2(sK6))) ) ),
    inference(resolution,[],[f99,f56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:56:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.47  % (32217)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.48  % (32217)Refutation not found, incomplete strategy% (32217)------------------------------
% 0.20/0.48  % (32217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (32217)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (32217)Memory used [KB]: 10618
% 0.20/0.48  % (32217)Time elapsed: 0.060 s
% 0.20/0.48  % (32217)------------------------------
% 0.20/0.48  % (32217)------------------------------
% 0.20/0.48  % (32225)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.49  % (32225)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f312,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f309,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.20/0.49  fof(f309,plain,(
% 0.20/0.49    ~v1_relat_1(k1_wellord2(sK6))),
% 0.20/0.49    inference(resolution,[],[f305,f64])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sP5(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1] : (sP5(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(definition_folding,[],[f12,f21,f20,f19,f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X3,X2,X1] : (sP2(X3,X2,X1) <=> (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X1,X0] : (sP3(X1,X0) <=> ! [X2,X3] : (sP2(X3,X2,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1] : (sP4(X0,X1) <=> (sP3(X1,X0) & k3_relat_1(X1) = X0))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X1,X0] : ((k1_wellord2(X0) = X1 <=> sP4(X0,X1)) | ~sP5(X1,X0))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.20/0.49  fof(f305,plain,(
% 0.20/0.49    ~sP5(k1_wellord2(sK6),sK6)),
% 0.20/0.49    inference(resolution,[],[f304,f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X1] : (sP4(X1,k1_wellord2(X1)) | ~sP5(k1_wellord2(X1),X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sP4(X1,X0) | k1_wellord2(X1) != X0 | ~sP5(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0,X1] : (((k1_wellord2(X1) = X0 | ~sP4(X1,X0)) & (sP4(X1,X0) | k1_wellord2(X1) != X0)) | ~sP5(X0,X1))),
% 0.20/0.49    inference(rectify,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X1,X0] : (((k1_wellord2(X0) = X1 | ~sP4(X0,X1)) & (sP4(X0,X1) | k1_wellord2(X0) != X1)) | ~sP5(X1,X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f21])).
% 0.20/0.49  fof(f304,plain,(
% 0.20/0.49    ( ! [X0] : (~sP4(X0,k1_wellord2(sK6))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f303,f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sP3(X1,X0) | ~sP4(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0,X1] : ((sP4(X0,X1) | ~sP3(X1,X0) | k3_relat_1(X1) != X0) & ((sP3(X1,X0) & k3_relat_1(X1) = X0) | ~sP4(X0,X1)))),
% 0.20/0.49    inference(flattening,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X0,X1] : ((sP4(X0,X1) | (~sP3(X1,X0) | k3_relat_1(X1) != X0)) & ((sP3(X1,X0) & k3_relat_1(X1) = X0) | ~sP4(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f20])).
% 0.20/0.49  fof(f303,plain,(
% 0.20/0.49    ( ! [X0] : (~sP3(k1_wellord2(sK6),X0) | ~sP4(X0,k1_wellord2(sK6))) )),
% 0.20/0.49    inference(superposition,[],[f297,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | ~sP4(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f33])).
% 0.20/0.49  fof(f297,plain,(
% 0.20/0.49    ~sP3(k1_wellord2(sK6),k3_relat_1(k1_wellord2(sK6)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f296,f257])).
% 0.20/0.49  fof(f257,plain,(
% 0.20/0.49    ~r1_tarski(sK8(k1_wellord2(sK6)),sK7(k1_wellord2(sK6)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f252,f81])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    sK7(k1_wellord2(sK6)) != sK8(k1_wellord2(sK6))),
% 0.20/0.49    inference(resolution,[],[f78,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X0] : (sP0(X0) | sK7(X0) != sK8(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0] : ((sP0(X0) | (sK7(X0) != sK8(X0) & r2_hidden(k4_tarski(sK8(X0),sK7(X0)),X0) & r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~sP0(X0)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f27,f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0] : (? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (sK7(X0) != sK8(X0) & r2_hidden(k4_tarski(sK8(X0),sK7(X0)),X0) & r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~sP0(X0)))),
% 0.20/0.49    inference(rectify,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~sP0(X0)))),
% 0.20/0.49    inference(nnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (sP0(X0) <=> ! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ~sP0(k1_wellord2(sK6))),
% 0.20/0.49    inference(subsumption_resolution,[],[f76,f43])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ~sP0(k1_wellord2(sK6)) | ~v1_relat_1(k1_wellord2(sK6))),
% 0.20/0.49    inference(resolution,[],[f74,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0] : (sP1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (sP1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(definition_folding,[],[f10,f16,f15])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : ((v4_relat_2(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | (~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => (v4_relat_2(X0) <=> ! [X1,X2] : ((r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => X1 = X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ~sP1(k1_wellord2(sK6)) | ~sP0(k1_wellord2(sK6))),
% 0.20/0.49    inference(resolution,[],[f42,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X0] : (v4_relat_2(X0) | ~sP0(X0) | ~sP1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0] : (((v4_relat_2(X0) | ~sP0(X0)) & (sP0(X0) | ~v4_relat_2(X0))) | ~sP1(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f16])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ~v4_relat_2(k1_wellord2(sK6))),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ~v4_relat_2(k1_wellord2(sK6))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f8,f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ? [X0] : ~v4_relat_2(k1_wellord2(X0)) => ~v4_relat_2(k1_wellord2(sK6))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ? [X0] : ~v4_relat_2(k1_wellord2(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,negated_conjecture,(
% 0.20/0.49    ~! [X0] : v4_relat_2(k1_wellord2(X0))),
% 0.20/0.49    inference(negated_conjecture,[],[f6])).
% 0.20/0.49  fof(f6,conjecture,(
% 0.20/0.49    ! [X0] : v4_relat_2(k1_wellord2(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_wellord2)).
% 0.20/0.49  fof(f252,plain,(
% 0.20/0.49    sK7(k1_wellord2(sK6)) = sK8(k1_wellord2(sK6)) | ~r1_tarski(sK8(k1_wellord2(sK6)),sK7(k1_wellord2(sK6)))),
% 0.20/0.49    inference(resolution,[],[f250,f67])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(flattening,[],[f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.49  fof(f250,plain,(
% 0.20/0.49    r1_tarski(sK7(k1_wellord2(sK6)),sK8(k1_wellord2(sK6)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f248,f135])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    r2_hidden(sK8(k1_wellord2(sK6)),sK6)),
% 0.20/0.49    inference(subsumption_resolution,[],[f132,f43])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    r2_hidden(sK8(k1_wellord2(sK6)),sK6) | ~v1_relat_1(k1_wellord2(sK6))),
% 0.20/0.49    inference(resolution,[],[f121,f64])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    ~sP5(k1_wellord2(sK6),sK6) | r2_hidden(sK8(k1_wellord2(sK6)),sK6)),
% 0.20/0.49    inference(resolution,[],[f108,f70])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    ( ! [X0] : (~sP4(X0,k1_wellord2(sK6)) | r2_hidden(sK8(k1_wellord2(sK6)),X0)) )),
% 0.20/0.49    inference(superposition,[],[f100,f53])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    r2_hidden(sK8(k1_wellord2(sK6)),k3_relat_1(k1_wellord2(sK6)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f91,f43])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    r2_hidden(sK8(k1_wellord2(sK6)),k3_relat_1(k1_wellord2(sK6))) | ~v1_relat_1(k1_wellord2(sK6))),
% 0.20/0.49    inference(resolution,[],[f79,f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.20/0.49    inference(flattening,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    r2_hidden(k4_tarski(sK7(k1_wellord2(sK6)),sK8(k1_wellord2(sK6))),k1_wellord2(sK6))),
% 0.20/0.49    inference(resolution,[],[f78,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0] : (sP0(X0) | r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f248,plain,(
% 0.20/0.49    ~r2_hidden(sK8(k1_wellord2(sK6)),sK6) | r1_tarski(sK7(k1_wellord2(sK6)),sK8(k1_wellord2(sK6)))),
% 0.20/0.49    inference(resolution,[],[f245,f92])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    ~sP2(sK8(k1_wellord2(sK6)),sK7(k1_wellord2(sK6)),k1_wellord2(sK6)) | r1_tarski(sK7(k1_wellord2(sK6)),sK8(k1_wellord2(sK6)))),
% 0.20/0.49    inference(resolution,[],[f79,f60])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(X1,X0) | ~r2_hidden(k4_tarski(X1,X0),X2) | ~sP2(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((~r1_tarski(X1,X0) | ~r2_hidden(k4_tarski(X1,X0),X2)) & (r1_tarski(X1,X0) | r2_hidden(k4_tarski(X1,X0),X2)))) & (((r2_hidden(k4_tarski(X1,X0),X2) | ~r1_tarski(X1,X0)) & (r1_tarski(X1,X0) | ~r2_hidden(k4_tarski(X1,X0),X2))) | ~sP2(X0,X1,X2)))),
% 0.20/0.49    inference(rectify,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ! [X3,X2,X1] : ((sP2(X3,X2,X1) | ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)))) & (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~sP2(X3,X2,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f18])).
% 0.20/0.49  fof(f245,plain,(
% 0.20/0.49    ( ! [X0] : (sP2(X0,sK7(k1_wellord2(sK6)),k1_wellord2(sK6)) | ~r2_hidden(X0,sK6)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f242,f43])).
% 0.20/0.49  fof(f242,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,sK6) | sP2(X0,sK7(k1_wellord2(sK6)),k1_wellord2(sK6)) | ~v1_relat_1(k1_wellord2(sK6))) )),
% 0.20/0.49    inference(resolution,[],[f183,f64])).
% 0.20/0.49  fof(f183,plain,(
% 0.20/0.49    ( ! [X0] : (~sP5(k1_wellord2(sK6),sK6) | ~r2_hidden(X0,sK6) | sP2(X0,sK7(k1_wellord2(sK6)),k1_wellord2(sK6))) )),
% 0.20/0.49    inference(resolution,[],[f165,f70])).
% 0.20/0.49  fof(f165,plain,(
% 0.20/0.49    ( ! [X6,X7] : (~sP4(sK6,X7) | sP2(X6,sK7(k1_wellord2(sK6)),X7) | ~r2_hidden(X6,sK6)) )),
% 0.20/0.49    inference(resolution,[],[f128,f54])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~sP3(X1,sK6) | ~r2_hidden(X0,sK6) | sP2(X0,sK7(k1_wellord2(sK6)),X1)) )),
% 0.20/0.49    inference(resolution,[],[f127,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X4,X0,X5,X1] : (sP2(X5,X4,X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~sP3(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ! [X0,X1] : ((sP3(X0,X1) | (~sP2(sK10(X0,X1),sK9(X0,X1),X0) & r2_hidden(sK10(X0,X1),X1) & r2_hidden(sK9(X0,X1),X1))) & (! [X4,X5] : (sP2(X5,X4,X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~sP3(X0,X1)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f35,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2,X3] : (~sP2(X3,X2,X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (~sP2(sK10(X0,X1),sK9(X0,X1),X0) & r2_hidden(sK10(X0,X1),X1) & r2_hidden(sK9(X0,X1),X1)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ! [X0,X1] : ((sP3(X0,X1) | ? [X2,X3] : (~sP2(X3,X2,X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X4,X5] : (sP2(X5,X4,X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~sP3(X0,X1)))),
% 0.20/0.49    inference(rectify,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X1,X0] : ((sP3(X1,X0) | ? [X2,X3] : (~sP2(X3,X2,X1) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & (! [X2,X3] : (sP2(X3,X2,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | ~sP3(X1,X0)))),
% 0.20/0.49    inference(nnf_transformation,[],[f19])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    r2_hidden(sK7(k1_wellord2(sK6)),sK6)),
% 0.20/0.49    inference(subsumption_resolution,[],[f124,f43])).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    r2_hidden(sK7(k1_wellord2(sK6)),sK6) | ~v1_relat_1(k1_wellord2(sK6))),
% 0.20/0.49    inference(resolution,[],[f118,f64])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    ~sP5(k1_wellord2(sK6),sK6) | r2_hidden(sK7(k1_wellord2(sK6)),sK6)),
% 0.20/0.49    inference(resolution,[],[f104,f70])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    ( ! [X0] : (~sP4(X0,k1_wellord2(sK6)) | r2_hidden(sK7(k1_wellord2(sK6)),X0)) )),
% 0.20/0.49    inference(superposition,[],[f99,f53])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    r2_hidden(sK7(k1_wellord2(sK6)),k3_relat_1(k1_wellord2(sK6)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f90,f43])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    r2_hidden(sK7(k1_wellord2(sK6)),k3_relat_1(k1_wellord2(sK6))) | ~v1_relat_1(k1_wellord2(sK6))),
% 0.20/0.49    inference(resolution,[],[f79,f68])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f296,plain,(
% 0.20/0.49    ~sP3(k1_wellord2(sK6),k3_relat_1(k1_wellord2(sK6))) | r1_tarski(sK8(k1_wellord2(sK6)),sK7(k1_wellord2(sK6)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f292,f100])).
% 0.20/0.49  fof(f292,plain,(
% 0.20/0.49    ~r2_hidden(sK8(k1_wellord2(sK6)),k3_relat_1(k1_wellord2(sK6))) | ~sP3(k1_wellord2(sK6),k3_relat_1(k1_wellord2(sK6))) | r1_tarski(sK8(k1_wellord2(sK6)),sK7(k1_wellord2(sK6)))),
% 0.20/0.49    inference(resolution,[],[f102,f111])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    ~sP2(sK7(k1_wellord2(sK6)),sK8(k1_wellord2(sK6)),k1_wellord2(sK6)) | r1_tarski(sK8(k1_wellord2(sK6)),sK7(k1_wellord2(sK6)))),
% 0.20/0.49    inference(resolution,[],[f80,f60])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    r2_hidden(k4_tarski(sK8(k1_wellord2(sK6)),sK7(k1_wellord2(sK6))),k1_wellord2(sK6))),
% 0.20/0.49    inference(resolution,[],[f78,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0] : (sP0(X0) | r2_hidden(k4_tarski(sK8(X0),sK7(X0)),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    ( ! [X2,X3] : (sP2(sK7(k1_wellord2(sK6)),X2,X3) | ~r2_hidden(X2,k3_relat_1(k1_wellord2(sK6))) | ~sP3(X3,k3_relat_1(k1_wellord2(sK6)))) )),
% 0.20/0.49    inference(resolution,[],[f99,f56])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (32225)------------------------------
% 0.20/0.49  % (32225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (32225)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (32225)Memory used [KB]: 1791
% 0.20/0.49  % (32225)Time elapsed: 0.084 s
% 0.20/0.49  % (32225)------------------------------
% 0.20/0.49  % (32225)------------------------------
% 0.20/0.49  % (32220)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.49  % (32216)Success in time 0.139 s
%------------------------------------------------------------------------------
