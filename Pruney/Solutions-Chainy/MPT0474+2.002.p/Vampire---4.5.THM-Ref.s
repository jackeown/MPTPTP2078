%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:11 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 295 expanded)
%              Number of leaves         :   13 (  87 expanded)
%              Depth                    :   36
%              Number of atoms          :  240 ( 960 expanded)
%              Number of equality atoms :   17 (  78 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f191,plain,(
    $false ),
    inference(subsumption_resolution,[],[f190,f44])).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f190,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f189,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f189,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f186,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f186,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f183,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP3(X1,X0)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f16,f22,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ! [X2,X3] :
          ( r2_hidden(k4_tarski(X2,X3),X1)
        <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ( k4_relat_1(X0) = X1
      <=> sP2(X0,X1) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).

fof(f183,plain,(
    ~ sP3(k4_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f182,f70])).

fof(f70,plain,(
    ! [X1] :
      ( sP2(X1,k4_relat_1(X1))
      | ~ sP3(k4_relat_1(X1),X1) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | k4_relat_1(X1) != X0
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( k4_relat_1(X1) = X0
          | ~ sP2(X1,X0) )
        & ( sP2(X1,X0)
          | k4_relat_1(X1) != X0 ) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ( ( k4_relat_1(X0) = X1
          | ~ sP2(X0,X1) )
        & ( sP2(X0,X1)
          | k4_relat_1(X0) != X1 ) )
      | ~ sP3(X1,X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f182,plain,(
    ! [X1] : ~ sP2(k1_xboole_0,X1) ),
    inference(subsumption_resolution,[],[f156,f166])).

fof(f166,plain,(
    ! [X0] : r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),X0) ),
    inference(subsumption_resolution,[],[f165,f44])).

fof(f165,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),X0)
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f164,f46])).

fof(f164,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),X0) ) ),
    inference(resolution,[],[f163,f68])).

fof(f68,plain,(
    ! [X0] :
      ( sP5(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( sP5(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f17,f25,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( sP4(X1,X0)
    <=> ! [X2,X3] :
          ( r2_hidden(k4_tarski(X2,X3),X1)
          | ~ r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> sP4(X1,X0) )
      | ~ sP5(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f163,plain,(
    ! [X2] :
      ( ~ sP5(k1_xboole_0)
      | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),X2) ) ),
    inference(subsumption_resolution,[],[f162,f45])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f162,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),X2)
      | ~ r1_tarski(k1_xboole_0,X2)
      | ~ sP5(k1_xboole_0) ) ),
    inference(resolution,[],[f146,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( sP4(X1,X0)
      | ~ r1_tarski(X0,X1)
      | ~ sP5(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ~ sP4(X1,X0) )
          & ( sP4(X1,X0)
            | ~ r1_tarski(X0,X1) ) )
      | ~ sP5(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f146,plain,(
    ! [X0] :
      ( ~ sP4(X0,k1_xboole_0)
      | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),X0) ) ),
    inference(resolution,[],[f143,f65])).

fof(f65,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ( ~ r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0)
          & r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X1) ) )
      & ( ! [X4,X5] :
            ( r2_hidden(k4_tarski(X4,X5),X0)
            | ~ r2_hidden(k4_tarski(X4,X5),X1) )
        | ~ sP4(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(k4_tarski(X2,X3),X1) )
     => ( ~ r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ? [X2,X3] :
            ( ~ r2_hidden(k4_tarski(X2,X3),X0)
            & r2_hidden(k4_tarski(X2,X3),X1) ) )
      & ( ! [X4,X5] :
            ( r2_hidden(k4_tarski(X4,X5),X0)
            | ~ r2_hidden(k4_tarski(X4,X5),X1) )
        | ~ sP4(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ( sP4(X1,X0)
        | ? [X2,X3] :
            ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            & r2_hidden(k4_tarski(X2,X3),X0) ) )
      & ( ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
        | ~ sP4(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f143,plain,(
    r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f142])).

fof(f142,plain,
    ( r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(resolution,[],[f137,f44])).

fof(f137,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),X0) ) ),
    inference(resolution,[],[f136,f46])).

fof(f136,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),X0)
      | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f132,f47])).

fof(f132,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f126,f62])).

fof(f126,plain,(
    ! [X0] :
      ( ~ sP3(k4_relat_1(X0),X0)
      | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),X0) ) ),
    inference(resolution,[],[f105,f70])).

fof(f105,plain,(
    ! [X2,X3] :
      ( ~ sP2(X2,X3)
      | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),X2)
      | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ) ),
    inference(resolution,[],[f102,f58])).

fof(f58,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ( ( ~ r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0)
            | ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) )
          & ( r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0)
            | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) ) ) )
      & ( ! [X4,X5] :
            ( ( r2_hidden(k4_tarski(X4,X5),X1)
              | ~ r2_hidden(k4_tarski(X5,X4),X0) )
            & ( r2_hidden(k4_tarski(X5,X4),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2,X3] :
            ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
      & ( ! [X4,X5] :
            ( ( r2_hidden(k4_tarski(X4,X5),X1)
              | ~ r2_hidden(k4_tarski(X5,X4),X0) )
            & ( r2_hidden(k4_tarski(X5,X4),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2,X3] :
            ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
      & ( ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f102,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK9(k1_xboole_0,k1_xboole_0),sK8(k1_xboole_0,k1_xboole_0)),X0)
      | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f101,f44])).

fof(f101,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK9(k1_xboole_0,k1_xboole_0),sK8(k1_xboole_0,k1_xboole_0)),X0)
      | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f98,f46])).

fof(f98,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | r2_hidden(k4_tarski(sK9(k1_xboole_0,k1_xboole_0),sK8(k1_xboole_0,k1_xboole_0)),X0)
      | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ) ),
    inference(resolution,[],[f97,f68])).

fof(f97,plain,(
    ! [X2] :
      ( ~ sP5(k1_xboole_0)
      | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | r2_hidden(k4_tarski(sK9(k1_xboole_0,k1_xboole_0),sK8(k1_xboole_0,k1_xboole_0)),X2) ) ),
    inference(subsumption_resolution,[],[f96,f45])).

fof(f96,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(sK9(k1_xboole_0,k1_xboole_0),sK8(k1_xboole_0,k1_xboole_0)),X2)
      | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,X2)
      | ~ sP5(k1_xboole_0) ) ),
    inference(resolution,[],[f83,f63])).

fof(f83,plain,(
    ! [X0] :
      ( ~ sP4(X0,k1_xboole_0)
      | r2_hidden(k4_tarski(sK9(k1_xboole_0,k1_xboole_0),sK8(k1_xboole_0,k1_xboole_0)),X0)
      | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ) ),
    inference(resolution,[],[f80,f65])).

fof(f80,plain,
    ( r2_hidden(k4_tarski(sK9(k1_xboole_0,k1_xboole_0),sK8(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(resolution,[],[f79,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0)
      | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f79,plain,(
    ~ sP2(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f78,f44])).

fof(f78,plain,
    ( ~ sP2(k1_xboole_0,k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f77,f46])).

fof(f77,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ sP2(k1_xboole_0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f76])).

fof(f76,plain,
    ( ~ sP2(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(resolution,[],[f73,f44])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ sP2(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != X0 ) ),
    inference(resolution,[],[f72,f46])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != X0
      | ~ sP2(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f71,f62])).

fof(f71,plain,(
    ! [X0] :
      ( ~ sP3(X0,k1_xboole_0)
      | ~ sP2(k1_xboole_0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f43,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_relat_1(X1) = X0
      | ~ sP2(X1,X0)
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f43,plain,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f10])).

fof(f10,negated_conjecture,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).

fof(f156,plain,(
    ! [X1] :
      ( ~ r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),X1)
      | ~ sP2(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f144,f58])).

fof(f144,plain,(
    ~ r2_hidden(k4_tarski(sK9(k1_xboole_0,k1_xboole_0),sK8(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(resolution,[],[f143,f81])).

fof(f81,plain,
    ( ~ r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ r2_hidden(k4_tarski(sK9(k1_xboole_0,k1_xboole_0),sK8(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(resolution,[],[f79,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0)
      | ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) ) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:54:32 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (30309)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (30317)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.31/0.53  % (30309)Refutation not found, incomplete strategy% (30309)------------------------------
% 1.31/0.53  % (30309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (30309)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (30309)Memory used [KB]: 10490
% 1.31/0.53  % (30309)Time elapsed: 0.094 s
% 1.31/0.53  % (30309)------------------------------
% 1.31/0.53  % (30309)------------------------------
% 1.31/0.53  % (30303)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.31/0.53  % (30303)Refutation not found, incomplete strategy% (30303)------------------------------
% 1.31/0.53  % (30303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (30303)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (30303)Memory used [KB]: 10490
% 1.31/0.53  % (30303)Time elapsed: 0.109 s
% 1.31/0.53  % (30303)------------------------------
% 1.31/0.53  % (30303)------------------------------
% 1.31/0.54  % (30308)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.31/0.54  % (30308)Refutation not found, incomplete strategy% (30308)------------------------------
% 1.31/0.54  % (30308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (30308)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (30308)Memory used [KB]: 6012
% 1.31/0.54  % (30308)Time elapsed: 0.111 s
% 1.31/0.54  % (30308)------------------------------
% 1.31/0.54  % (30308)------------------------------
% 1.31/0.54  % (30305)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.49/0.55  % (30307)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.49/0.55  % (30327)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.49/0.55  % (30316)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.49/0.55  % (30316)Refutation not found, incomplete strategy% (30316)------------------------------
% 1.49/0.55  % (30316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (30316)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (30316)Memory used [KB]: 6012
% 1.49/0.55  % (30316)Time elapsed: 0.131 s
% 1.49/0.55  % (30316)------------------------------
% 1.49/0.55  % (30316)------------------------------
% 1.49/0.55  % (30311)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.49/0.55  % (30323)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.49/0.56  % (30306)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.49/0.56  % (30311)Refutation found. Thanks to Tanya!
% 1.49/0.56  % SZS status Theorem for theBenchmark
% 1.49/0.56  % SZS output start Proof for theBenchmark
% 1.49/0.56  fof(f191,plain,(
% 1.49/0.56    $false),
% 1.49/0.56    inference(subsumption_resolution,[],[f190,f44])).
% 1.49/0.56  fof(f44,plain,(
% 1.49/0.56    v1_xboole_0(k1_xboole_0)),
% 1.49/0.56    inference(cnf_transformation,[],[f1])).
% 1.49/0.56  fof(f1,axiom,(
% 1.49/0.56    v1_xboole_0(k1_xboole_0)),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.49/0.56  fof(f190,plain,(
% 1.49/0.56    ~v1_xboole_0(k1_xboole_0)),
% 1.49/0.56    inference(resolution,[],[f189,f46])).
% 1.49/0.56  fof(f46,plain,(
% 1.49/0.56    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f12])).
% 1.49/0.56  fof(f12,plain,(
% 1.49/0.56    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.49/0.56    inference(ennf_transformation,[],[f3])).
% 1.49/0.56  fof(f3,axiom,(
% 1.49/0.56    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.49/0.56  fof(f189,plain,(
% 1.49/0.56    ~v1_relat_1(k1_xboole_0)),
% 1.49/0.56    inference(subsumption_resolution,[],[f186,f47])).
% 1.49/0.56  fof(f47,plain,(
% 1.49/0.56    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f13])).
% 1.49/0.56  fof(f13,plain,(
% 1.49/0.56    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(ennf_transformation,[],[f7])).
% 1.49/0.56  fof(f7,axiom,(
% 1.49/0.56    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.49/0.56  fof(f186,plain,(
% 1.49/0.56    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)),
% 1.49/0.56    inference(resolution,[],[f183,f62])).
% 1.49/0.56  fof(f62,plain,(
% 1.49/0.56    ( ! [X0,X1] : (sP3(X1,X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f23])).
% 1.49/0.56  fof(f23,plain,(
% 1.49/0.56    ! [X0] : (! [X1] : (sP3(X1,X0) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(definition_folding,[],[f16,f22,f21])).
% 1.49/0.56  fof(f21,plain,(
% 1.49/0.56    ! [X0,X1] : (sP2(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.49/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.49/0.56  fof(f22,plain,(
% 1.49/0.56    ! [X1,X0] : ((k4_relat_1(X0) = X1 <=> sP2(X0,X1)) | ~sP3(X1,X0))),
% 1.49/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.49/0.56  fof(f16,plain,(
% 1.49/0.56    ! [X0] : (! [X1] : ((k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(ennf_transformation,[],[f6])).
% 1.49/0.56  fof(f6,axiom,(
% 1.49/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0)))))),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).
% 1.49/0.56  fof(f183,plain,(
% 1.49/0.56    ~sP3(k4_relat_1(k1_xboole_0),k1_xboole_0)),
% 1.49/0.56    inference(resolution,[],[f182,f70])).
% 1.49/0.56  fof(f70,plain,(
% 1.49/0.56    ( ! [X1] : (sP2(X1,k4_relat_1(X1)) | ~sP3(k4_relat_1(X1),X1)) )),
% 1.49/0.56    inference(equality_resolution,[],[f56])).
% 1.49/0.56  fof(f56,plain,(
% 1.49/0.56    ( ! [X0,X1] : (sP2(X1,X0) | k4_relat_1(X1) != X0 | ~sP3(X0,X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f33])).
% 1.49/0.56  fof(f33,plain,(
% 1.49/0.56    ! [X0,X1] : (((k4_relat_1(X1) = X0 | ~sP2(X1,X0)) & (sP2(X1,X0) | k4_relat_1(X1) != X0)) | ~sP3(X0,X1))),
% 1.49/0.56    inference(rectify,[],[f32])).
% 1.49/0.56  fof(f32,plain,(
% 1.49/0.56    ! [X1,X0] : (((k4_relat_1(X0) = X1 | ~sP2(X0,X1)) & (sP2(X0,X1) | k4_relat_1(X0) != X1)) | ~sP3(X1,X0))),
% 1.49/0.56    inference(nnf_transformation,[],[f22])).
% 1.49/0.56  fof(f182,plain,(
% 1.49/0.56    ( ! [X1] : (~sP2(k1_xboole_0,X1)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f156,f166])).
% 1.49/0.56  fof(f166,plain,(
% 1.49/0.56    ( ! [X0] : (r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),X0)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f165,f44])).
% 1.49/0.56  fof(f165,plain,(
% 1.49/0.56    ( ! [X0] : (r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),X0) | ~v1_xboole_0(k1_xboole_0)) )),
% 1.49/0.56    inference(resolution,[],[f164,f46])).
% 1.49/0.56  fof(f164,plain,(
% 1.49/0.56    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),X0)) )),
% 1.49/0.56    inference(resolution,[],[f163,f68])).
% 1.49/0.56  fof(f68,plain,(
% 1.49/0.56    ( ! [X0] : (sP5(X0) | ~v1_relat_1(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f26])).
% 1.49/0.56  fof(f26,plain,(
% 1.49/0.56    ! [X0] : (sP5(X0) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(definition_folding,[],[f17,f25,f24])).
% 1.49/0.56  fof(f24,plain,(
% 1.49/0.56    ! [X1,X0] : (sP4(X1,X0) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.49/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.49/0.56  fof(f25,plain,(
% 1.49/0.56    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> sP4(X1,X0)) | ~sP5(X0))),
% 1.49/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 1.49/0.56  fof(f17,plain,(
% 1.49/0.56    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(ennf_transformation,[],[f5])).
% 1.49/0.56  fof(f5,axiom,(
% 1.49/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 1.49/0.56  fof(f163,plain,(
% 1.49/0.56    ( ! [X2] : (~sP5(k1_xboole_0) | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),X2)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f162,f45])).
% 1.49/0.56  fof(f45,plain,(
% 1.49/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f2])).
% 1.49/0.56  fof(f2,axiom,(
% 1.49/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.49/0.56  fof(f162,plain,(
% 1.49/0.56    ( ! [X2] : (r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),X2) | ~r1_tarski(k1_xboole_0,X2) | ~sP5(k1_xboole_0)) )),
% 1.49/0.56    inference(resolution,[],[f146,f63])).
% 1.49/0.56  fof(f63,plain,(
% 1.49/0.56    ( ! [X0,X1] : (sP4(X1,X0) | ~r1_tarski(X0,X1) | ~sP5(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f38])).
% 1.49/0.56  fof(f38,plain,(
% 1.49/0.56    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ~sP4(X1,X0)) & (sP4(X1,X0) | ~r1_tarski(X0,X1))) | ~sP5(X0))),
% 1.49/0.56    inference(nnf_transformation,[],[f25])).
% 1.49/0.56  fof(f146,plain,(
% 1.49/0.56    ( ! [X0] : (~sP4(X0,k1_xboole_0) | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),X0)) )),
% 1.49/0.56    inference(resolution,[],[f143,f65])).
% 1.49/0.56  fof(f65,plain,(
% 1.49/0.56    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(k4_tarski(X4,X5),X1) | ~sP4(X0,X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f42])).
% 1.49/0.56  fof(f42,plain,(
% 1.49/0.56    ! [X0,X1] : ((sP4(X0,X1) | (~r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0) & r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X1))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(k4_tarski(X4,X5),X1)) | ~sP4(X0,X1)))),
% 1.49/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f40,f41])).
% 1.49/0.56  fof(f41,plain,(
% 1.49/0.56    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X2,X3),X1)) => (~r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0) & r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X1)))),
% 1.49/0.56    introduced(choice_axiom,[])).
% 1.49/0.56  fof(f40,plain,(
% 1.49/0.56    ! [X0,X1] : ((sP4(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X2,X3),X1))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(k4_tarski(X4,X5),X1)) | ~sP4(X0,X1)))),
% 1.49/0.56    inference(rectify,[],[f39])).
% 1.49/0.56  fof(f39,plain,(
% 1.49/0.56    ! [X1,X0] : ((sP4(X1,X0) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~sP4(X1,X0)))),
% 1.49/0.56    inference(nnf_transformation,[],[f24])).
% 1.49/0.56  fof(f143,plain,(
% 1.49/0.56    r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 1.49/0.56    inference(duplicate_literal_removal,[],[f142])).
% 1.49/0.56  fof(f142,plain,(
% 1.49/0.56    r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 1.49/0.56    inference(resolution,[],[f137,f44])).
% 1.49/0.56  fof(f137,plain,(
% 1.49/0.56    ( ! [X0] : (~v1_xboole_0(X0) | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),X0)) )),
% 1.49/0.56    inference(resolution,[],[f136,f46])).
% 1.49/0.56  fof(f136,plain,(
% 1.49/0.56    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),X0) | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f132,f47])).
% 1.49/0.56  fof(f132,plain,(
% 1.49/0.56    ( ! [X0] : (r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),X0) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.49/0.56    inference(resolution,[],[f126,f62])).
% 1.49/0.56  fof(f126,plain,(
% 1.49/0.56    ( ! [X0] : (~sP3(k4_relat_1(X0),X0) | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),X0)) )),
% 1.49/0.56    inference(resolution,[],[f105,f70])).
% 1.49/0.56  fof(f105,plain,(
% 1.49/0.56    ( ! [X2,X3] : (~sP2(X2,X3) | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),X2) | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0)) )),
% 1.49/0.56    inference(resolution,[],[f102,f58])).
% 1.49/0.56  fof(f58,plain,(
% 1.49/0.56    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1) | ~sP2(X0,X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f37])).
% 1.49/0.56  fof(f37,plain,(
% 1.49/0.56    ! [X0,X1] : ((sP2(X0,X1) | ((~r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0) | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~sP2(X0,X1)))),
% 1.49/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f35,f36])).
% 1.49/0.56  fof(f36,plain,(
% 1.49/0.56    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1))) => ((~r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0) | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1))))),
% 1.49/0.56    introduced(choice_axiom,[])).
% 1.49/0.56  fof(f35,plain,(
% 1.49/0.56    ! [X0,X1] : ((sP2(X0,X1) | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~sP2(X0,X1)))),
% 1.49/0.56    inference(rectify,[],[f34])).
% 1.49/0.56  fof(f34,plain,(
% 1.49/0.56    ! [X0,X1] : ((sP2(X0,X1) | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X3,X2),X0)) & (r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~sP2(X0,X1)))),
% 1.49/0.56    inference(nnf_transformation,[],[f21])).
% 1.49/0.56  fof(f102,plain,(
% 1.49/0.56    ( ! [X0] : (r2_hidden(k4_tarski(sK9(k1_xboole_0,k1_xboole_0),sK8(k1_xboole_0,k1_xboole_0)),X0) | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f101,f44])).
% 1.49/0.56  fof(f101,plain,(
% 1.49/0.56    ( ! [X0] : (r2_hidden(k4_tarski(sK9(k1_xboole_0,k1_xboole_0),sK8(k1_xboole_0,k1_xboole_0)),X0) | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~v1_xboole_0(k1_xboole_0)) )),
% 1.49/0.56    inference(resolution,[],[f98,f46])).
% 1.49/0.56  fof(f98,plain,(
% 1.49/0.56    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | r2_hidden(k4_tarski(sK9(k1_xboole_0,k1_xboole_0),sK8(k1_xboole_0,k1_xboole_0)),X0) | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0)) )),
% 1.49/0.56    inference(resolution,[],[f97,f68])).
% 1.49/0.56  fof(f97,plain,(
% 1.49/0.56    ( ! [X2] : (~sP5(k1_xboole_0) | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK9(k1_xboole_0,k1_xboole_0),sK8(k1_xboole_0,k1_xboole_0)),X2)) )),
% 1.49/0.56    inference(subsumption_resolution,[],[f96,f45])).
% 1.49/0.56  fof(f96,plain,(
% 1.49/0.56    ( ! [X2] : (r2_hidden(k4_tarski(sK9(k1_xboole_0,k1_xboole_0),sK8(k1_xboole_0,k1_xboole_0)),X2) | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~r1_tarski(k1_xboole_0,X2) | ~sP5(k1_xboole_0)) )),
% 1.49/0.56    inference(resolution,[],[f83,f63])).
% 1.49/0.56  fof(f83,plain,(
% 1.49/0.56    ( ! [X0] : (~sP4(X0,k1_xboole_0) | r2_hidden(k4_tarski(sK9(k1_xboole_0,k1_xboole_0),sK8(k1_xboole_0,k1_xboole_0)),X0) | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0)) )),
% 1.49/0.56    inference(resolution,[],[f80,f65])).
% 1.49/0.56  fof(f80,plain,(
% 1.49/0.56    r2_hidden(k4_tarski(sK9(k1_xboole_0,k1_xboole_0),sK8(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 1.49/0.56    inference(resolution,[],[f79,f60])).
% 1.49/0.56  fof(f60,plain,(
% 1.49/0.56    ( ! [X0,X1] : (sP2(X0,X1) | r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0) | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f37])).
% 1.49/0.56  fof(f79,plain,(
% 1.49/0.56    ~sP2(k1_xboole_0,k1_xboole_0)),
% 1.49/0.56    inference(subsumption_resolution,[],[f78,f44])).
% 1.49/0.56  fof(f78,plain,(
% 1.49/0.56    ~sP2(k1_xboole_0,k1_xboole_0) | ~v1_xboole_0(k1_xboole_0)),
% 1.49/0.56    inference(resolution,[],[f77,f46])).
% 1.49/0.56  fof(f77,plain,(
% 1.49/0.56    ~v1_relat_1(k1_xboole_0) | ~sP2(k1_xboole_0,k1_xboole_0)),
% 1.49/0.56    inference(trivial_inequality_removal,[],[f76])).
% 1.49/0.56  fof(f76,plain,(
% 1.49/0.56    ~sP2(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 != k1_xboole_0),
% 1.49/0.56    inference(resolution,[],[f73,f44])).
% 1.49/0.56  fof(f73,plain,(
% 1.49/0.56    ( ! [X0] : (~v1_xboole_0(X0) | ~sP2(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 != X0) )),
% 1.49/0.56    inference(resolution,[],[f72,f46])).
% 1.49/0.56  fof(f72,plain,(
% 1.49/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != X0 | ~sP2(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.49/0.56    inference(resolution,[],[f71,f62])).
% 1.49/0.56  fof(f71,plain,(
% 1.49/0.56    ( ! [X0] : (~sP3(X0,k1_xboole_0) | ~sP2(k1_xboole_0,X0) | k1_xboole_0 != X0) )),
% 1.49/0.56    inference(superposition,[],[f43,f57])).
% 1.49/0.56  fof(f57,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k4_relat_1(X1) = X0 | ~sP2(X1,X0) | ~sP3(X0,X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f33])).
% 1.49/0.56  fof(f43,plain,(
% 1.49/0.56    k1_xboole_0 != k4_relat_1(k1_xboole_0)),
% 1.49/0.56    inference(cnf_transformation,[],[f11])).
% 1.49/0.56  fof(f11,plain,(
% 1.49/0.56    k1_xboole_0 != k4_relat_1(k1_xboole_0)),
% 1.49/0.56    inference(flattening,[],[f10])).
% 1.49/0.56  fof(f10,negated_conjecture,(
% 1.49/0.56    ~k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 1.49/0.56    inference(negated_conjecture,[],[f9])).
% 1.49/0.56  fof(f9,conjecture,(
% 1.49/0.56    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 1.49/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).
% 1.49/0.56  fof(f156,plain,(
% 1.49/0.56    ( ! [X1] : (~r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),X1) | ~sP2(k1_xboole_0,X1)) )),
% 1.49/0.56    inference(resolution,[],[f144,f58])).
% 1.49/0.56  fof(f144,plain,(
% 1.49/0.56    ~r2_hidden(k4_tarski(sK9(k1_xboole_0,k1_xboole_0),sK8(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 1.49/0.56    inference(resolution,[],[f143,f81])).
% 1.49/0.56  fof(f81,plain,(
% 1.49/0.56    ~r2_hidden(k4_tarski(sK8(k1_xboole_0,k1_xboole_0),sK9(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~r2_hidden(k4_tarski(sK9(k1_xboole_0,k1_xboole_0),sK8(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 1.49/0.56    inference(resolution,[],[f79,f61])).
% 1.49/0.56  fof(f61,plain,(
% 1.49/0.56    ( ! [X0,X1] : (sP2(X0,X1) | ~r2_hidden(k4_tarski(sK9(X0,X1),sK8(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f37])).
% 1.49/0.56  % SZS output end Proof for theBenchmark
% 1.49/0.56  % (30311)------------------------------
% 1.49/0.56  % (30311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (30311)Termination reason: Refutation
% 1.49/0.56  
% 1.49/0.56  % (30311)Memory used [KB]: 1663
% 1.49/0.56  % (30311)Time elapsed: 0.137 s
% 1.49/0.56  % (30311)------------------------------
% 1.49/0.56  % (30311)------------------------------
% 1.49/0.56  % (30302)Success in time 0.197 s
%------------------------------------------------------------------------------
