%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 963 expanded)
%              Number of leaves         :   12 ( 288 expanded)
%              Depth                    :   27
%              Number of atoms          :  252 (3491 expanded)
%              Number of equality atoms :   41 ( 630 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f306,plain,(
    $false ),
    inference(subsumption_resolution,[],[f281,f274])).

fof(f274,plain,(
    r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) ),
    inference(duplicate_literal_removal,[],[f273])).

fof(f273,plain,
    ( r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))
    | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) ),
    inference(forward_demodulation,[],[f244,f238])).

fof(f238,plain,(
    sK7(k6_relat_1(sK5),k6_relat_1(sK5)) = sK6(k6_relat_1(sK5),k6_relat_1(sK5)) ),
    inference(resolution,[],[f236,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | X0 != X1
        | ~ r2_hidden(X1,X2) )
      & ( ( X0 = X1
          & r2_hidden(X1,X2) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X3,X2,X0] :
      ( ( sP2(X3,X2,X0)
        | X2 != X3
        | ~ r2_hidden(X2,X0) )
      & ( ( X2 = X3
          & r2_hidden(X2,X0) )
        | ~ sP2(X3,X2,X0) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X3,X2,X0] :
      ( ( sP2(X3,X2,X0)
        | X2 != X3
        | ~ r2_hidden(X2,X0) )
      & ( ( X2 = X3
          & r2_hidden(X2,X0) )
        | ~ sP2(X3,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X3,X2,X0] :
      ( sP2(X3,X2,X0)
    <=> ( X2 = X3
        & r2_hidden(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f236,plain,(
    sP2(sK7(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK5) ),
    inference(subsumption_resolution,[],[f233,f34])).

fof(f34,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f233,plain,
    ( sP2(sK7(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK5)
    | ~ v1_relat_1(k6_relat_1(sK5)) ),
    inference(resolution,[],[f225,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( sP4(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( sP4(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f8,f14,f13,f12])).

fof(f13,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
    <=> ! [X2,X3] :
          ( r2_hidden(k4_tarski(X2,X3),X1)
        <=> sP2(X3,X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ( k6_relat_1(X0) = X1
      <=> sP3(X0,X1) )
      | ~ sP4(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

fof(f225,plain,
    ( ~ sP4(k6_relat_1(sK5),sK5)
    | sP2(sK7(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK5) ),
    inference(resolution,[],[f203,f53])).

fof(f53,plain,(
    ! [X1] :
      ( sP3(X1,k6_relat_1(X1))
      | ~ sP4(k6_relat_1(X1),X1) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | k6_relat_1(X1) != X0
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X1) = X0
          | ~ sP3(X1,X0) )
        & ( sP3(X1,X0)
          | k6_relat_1(X1) != X0 ) )
      | ~ sP4(X0,X1) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ( ( k6_relat_1(X0) = X1
          | ~ sP3(X0,X1) )
        & ( sP3(X0,X1)
          | k6_relat_1(X0) != X1 ) )
      | ~ sP4(X1,X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f203,plain,(
    ! [X0] :
      ( ~ sP3(X0,k6_relat_1(sK5))
      | sP2(sK7(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5)),X0) ) ),
    inference(resolution,[],[f197,f44])).

fof(f44,plain,(
    ! [X4,X0,X5,X1] :
      ( sP2(X5,X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ( ( ~ sP2(sK9(X0,X1),sK8(X0,X1),X0)
            | ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) )
          & ( sP2(sK9(X0,X1),sK8(X0,X1),X0)
            | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) ) ) )
      & ( ! [X4,X5] :
            ( ( r2_hidden(k4_tarski(X4,X5),X1)
              | ~ sP2(X5,X4,X0) )
            & ( sP2(X5,X4,X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
        | ~ sP3(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ sP2(X3,X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( sP2(X3,X2,X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ sP2(sK9(X0,X1),sK8(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) )
        & ( sP2(sK9(X0,X1),sK8(X0,X1),X0)
          | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ? [X2,X3] :
            ( ( ~ sP2(X3,X2,X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( sP2(X3,X2,X0)
              | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
      & ( ! [X4,X5] :
            ( ( r2_hidden(k4_tarski(X4,X5),X1)
              | ~ sP2(X5,X4,X0) )
            & ( sP2(X5,X4,X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
        | ~ sP3(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ? [X2,X3] :
            ( ( ~ sP2(X3,X2,X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( sP2(X3,X2,X0)
              | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
      & ( ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ sP2(X3,X2,X0) )
            & ( sP2(X3,X2,X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
        | ~ sP3(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f197,plain,(
    r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) ),
    inference(subsumption_resolution,[],[f167,f166])).

fof(f166,plain,
    ( r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))
    | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) ),
    inference(duplicate_literal_removal,[],[f157])).

fof(f157,plain,
    ( r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))
    | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))
    | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) ),
    inference(superposition,[],[f95,f144])).

fof(f144,plain,
    ( sK7(k6_relat_1(sK5),k6_relat_1(sK5)) = sK6(k6_relat_1(sK5),k6_relat_1(sK5))
    | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) ),
    inference(resolution,[],[f139,f49])).

fof(f139,plain,
    ( sP2(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5)),sK5)
    | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) ),
    inference(subsumption_resolution,[],[f136,f34])).

fof(f136,plain,
    ( r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))
    | sP2(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5)),sK5)
    | ~ v1_relat_1(k6_relat_1(sK5)) ),
    inference(resolution,[],[f104,f51])).

fof(f104,plain,
    ( ~ sP4(k6_relat_1(sK5),sK5)
    | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))
    | sP2(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5)),sK5) ),
    inference(resolution,[],[f97,f53])).

fof(f97,plain,(
    ! [X0] :
      ( ~ sP3(X0,k6_relat_1(sK5))
      | sP2(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5)),X0)
      | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) ) ),
    inference(resolution,[],[f95,f44])).

fof(f95,plain,
    ( r2_hidden(k4_tarski(sK7(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))
    | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( k6_relat_1(X0) != k6_relat_1(sK5)
      | r2_hidden(k4_tarski(sK7(k6_relat_1(sK5),k6_relat_1(X0)),sK6(k6_relat_1(sK5),k6_relat_1(X0))),k6_relat_1(sK5))
      | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(X0)),sK7(k6_relat_1(sK5),k6_relat_1(X0))),k6_relat_1(X0)) ) ),
    inference(resolution,[],[f66,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
      | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
            | ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) ) ) )
      & ( ! [X4,X5] :
            ( ( r2_hidden(k4_tarski(X4,X5),X1)
              | ~ r2_hidden(k4_tarski(X5,X4),X0) )
            & ( r2_hidden(k4_tarski(X5,X4),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2,X3] :
          ( r2_hidden(k4_tarski(X2,X3),X1)
        <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f66,plain,(
    ! [X0] :
      ( ~ sP0(k6_relat_1(sK5),k6_relat_1(X0))
      | k6_relat_1(X0) != k6_relat_1(sK5) ) ),
    inference(resolution,[],[f65,f34])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k6_relat_1(sK5) != X0
      | ~ sP0(k6_relat_1(sK5),X0) ) ),
    inference(subsumption_resolution,[],[f63,f34])).

fof(f63,plain,(
    ! [X0] :
      ( ~ sP0(k6_relat_1(sK5),X0)
      | k6_relat_1(sK5) != X0
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k6_relat_1(sK5)) ) ),
    inference(resolution,[],[f56,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f7,f10,f9])).

fof(f10,plain,(
    ! [X1,X0] :
      ( ( k4_relat_1(X0) = X1
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

fof(f56,plain,(
    ! [X0] :
      ( ~ sP1(X0,k6_relat_1(sK5))
      | ~ sP0(k6_relat_1(sK5),X0)
      | k6_relat_1(sK5) != X0 ) ),
    inference(superposition,[],[f33,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_relat_1(X1) = X0
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( k4_relat_1(X1) = X0
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | k4_relat_1(X1) != X0 ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ( ( k4_relat_1(X0) = X1
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | k4_relat_1(X0) != X1 ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f33,plain,(
    k6_relat_1(sK5) != k4_relat_1(k6_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k6_relat_1(sK5) != k4_relat_1(k6_relat_1(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f6,f16])).

fof(f16,plain,
    ( ? [X0] : k6_relat_1(X0) != k4_relat_1(k6_relat_1(X0))
   => k6_relat_1(sK5) != k4_relat_1(k6_relat_1(sK5)) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] : k6_relat_1(X0) != k4_relat_1(k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f167,plain,
    ( ~ r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))
    | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,
    ( ~ r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))
    | ~ r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))
    | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) ),
    inference(superposition,[],[f110,f144])).

fof(f110,plain,
    ( ~ r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))
    | ~ r2_hidden(k4_tarski(sK7(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) ),
    inference(equality_resolution,[],[f70])).

% (950)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f70,plain,(
    ! [X1] :
      ( k6_relat_1(sK5) != k6_relat_1(X1)
      | ~ r2_hidden(k4_tarski(sK7(k6_relat_1(sK5),k6_relat_1(X1)),sK6(k6_relat_1(sK5),k6_relat_1(X1))),k6_relat_1(sK5))
      | ~ r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(X1)),sK7(k6_relat_1(sK5),k6_relat_1(X1))),k6_relat_1(X1)) ) ),
    inference(resolution,[],[f66,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
      | ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f244,plain,
    ( r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))
    | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) ),
    inference(backward_demodulation,[],[f95,f238])).

fof(f281,plain,(
    ~ r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) ),
    inference(duplicate_literal_removal,[],[f280])).

fof(f280,plain,
    ( ~ r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))
    | ~ r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) ),
    inference(forward_demodulation,[],[f248,f238])).

fof(f248,plain,
    ( ~ r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))
    | ~ r2_hidden(k4_tarski(sK7(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) ),
    inference(backward_demodulation,[],[f110,f238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:14:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (968)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (952)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (944)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (952)Refutation not found, incomplete strategy% (952)------------------------------
% 0.20/0.51  % (952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (952)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (952)Memory used [KB]: 10490
% 0.20/0.51  % (952)Time elapsed: 0.088 s
% 0.20/0.51  % (952)------------------------------
% 0.20/0.51  % (952)------------------------------
% 0.20/0.51  % (954)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (947)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (945)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (945)Refutation not found, incomplete strategy% (945)------------------------------
% 0.20/0.51  % (945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (945)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (945)Memory used [KB]: 10490
% 0.20/0.51  % (945)Time elapsed: 0.087 s
% 0.20/0.51  % (945)------------------------------
% 0.20/0.51  % (945)------------------------------
% 0.20/0.51  % (975)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (973)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.52  % (971)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.52  % (955)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.52  % (951)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.52  % (978)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (953)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.53  % (967)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (977)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.53  % (954)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f306,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f281,f274])).
% 0.20/0.53  fof(f274,plain,(
% 0.20/0.53    r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f273])).
% 0.20/0.53  fof(f273,plain,(
% 0.20/0.53    r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))),
% 0.20/0.53    inference(forward_demodulation,[],[f244,f238])).
% 0.20/0.53  fof(f238,plain,(
% 0.20/0.53    sK7(k6_relat_1(sK5),k6_relat_1(sK5)) = sK6(k6_relat_1(sK5),k6_relat_1(sK5))),
% 0.20/0.53    inference(resolution,[],[f236,f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (X0 = X1 | ~sP2(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | X0 != X1 | ~r2_hidden(X1,X2)) & ((X0 = X1 & r2_hidden(X1,X2)) | ~sP2(X0,X1,X2)))),
% 0.20/0.53    inference(rectify,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X3,X2,X0] : ((sP2(X3,X2,X0) | X2 != X3 | ~r2_hidden(X2,X0)) & ((X2 = X3 & r2_hidden(X2,X0)) | ~sP2(X3,X2,X0)))),
% 0.20/0.53    inference(flattening,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X3,X2,X0] : ((sP2(X3,X2,X0) | (X2 != X3 | ~r2_hidden(X2,X0))) & ((X2 = X3 & r2_hidden(X2,X0)) | ~sP2(X3,X2,X0)))),
% 0.20/0.53    inference(nnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ! [X3,X2,X0] : (sP2(X3,X2,X0) <=> (X2 = X3 & r2_hidden(X2,X0)))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.53  fof(f236,plain,(
% 0.20/0.53    sP2(sK7(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK5)),
% 0.20/0.53    inference(subsumption_resolution,[],[f233,f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.53  fof(f233,plain,(
% 0.20/0.53    sP2(sK7(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK5) | ~v1_relat_1(k6_relat_1(sK5))),
% 0.20/0.53    inference(resolution,[],[f225,f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sP4(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0,X1] : (sP4(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(definition_folding,[],[f8,f14,f13,f12])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0,X1] : (sP3(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> sP2(X3,X2,X0)))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X1,X0] : ((k6_relat_1(X0) = X1 <=> sP3(X0,X1)) | ~sP4(X1,X0))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.20/0.53  fof(f8,plain,(
% 0.20/0.53    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => (k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).
% 0.20/0.53  fof(f225,plain,(
% 0.20/0.53    ~sP4(k6_relat_1(sK5),sK5) | sP2(sK7(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK5)),
% 0.20/0.53    inference(resolution,[],[f203,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X1] : (sP3(X1,k6_relat_1(X1)) | ~sP4(k6_relat_1(X1),X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sP3(X1,X0) | k6_relat_1(X1) != X0 | ~sP4(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1] : (((k6_relat_1(X1) = X0 | ~sP3(X1,X0)) & (sP3(X1,X0) | k6_relat_1(X1) != X0)) | ~sP4(X0,X1))),
% 0.20/0.53    inference(rectify,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X1,X0] : (((k6_relat_1(X0) = X1 | ~sP3(X0,X1)) & (sP3(X0,X1) | k6_relat_1(X0) != X1)) | ~sP4(X1,X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f14])).
% 0.20/0.53  fof(f203,plain,(
% 0.20/0.53    ( ! [X0] : (~sP3(X0,k6_relat_1(sK5)) | sP2(sK7(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5)),X0)) )),
% 0.20/0.53    inference(resolution,[],[f197,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X4,X0,X5,X1] : (sP2(X5,X4,X0) | ~r2_hidden(k4_tarski(X4,X5),X1) | ~sP3(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1] : ((sP3(X0,X1) | ((~sP2(sK9(X0,X1),sK8(X0,X1),X0) | ~r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)) & (sP2(sK9(X0,X1),sK8(X0,X1),X0) | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~sP2(X5,X4,X0)) & (sP2(X5,X4,X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~sP3(X0,X1)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f27,f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2,X3] : ((~sP2(X3,X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (sP2(X3,X2,X0) | r2_hidden(k4_tarski(X2,X3),X1))) => ((~sP2(sK9(X0,X1),sK8(X0,X1),X0) | ~r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)) & (sP2(sK9(X0,X1),sK8(X0,X1),X0) | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1] : ((sP3(X0,X1) | ? [X2,X3] : ((~sP2(X3,X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (sP2(X3,X2,X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~sP2(X5,X4,X0)) & (sP2(X5,X4,X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~sP3(X0,X1)))),
% 0.20/0.53    inference(rectify,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0,X1] : ((sP3(X0,X1) | ? [X2,X3] : ((~sP2(X3,X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (sP2(X3,X2,X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | ~sP2(X3,X2,X0)) & (sP2(X3,X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~sP3(X0,X1)))),
% 0.20/0.53    inference(nnf_transformation,[],[f13])).
% 0.20/0.53  fof(f197,plain,(
% 0.20/0.53    r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))),
% 0.20/0.53    inference(subsumption_resolution,[],[f167,f166])).
% 0.20/0.53  fof(f166,plain,(
% 0.20/0.53    r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f157])).
% 0.20/0.53  fof(f157,plain,(
% 0.20/0.53    r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))),
% 0.20/0.53    inference(superposition,[],[f95,f144])).
% 0.20/0.53  fof(f144,plain,(
% 0.20/0.53    sK7(k6_relat_1(sK5),k6_relat_1(sK5)) = sK6(k6_relat_1(sK5),k6_relat_1(sK5)) | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))),
% 0.20/0.53    inference(resolution,[],[f139,f49])).
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    sP2(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5)),sK5) | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))),
% 0.20/0.53    inference(subsumption_resolution,[],[f136,f34])).
% 0.20/0.53  fof(f136,plain,(
% 0.20/0.53    r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) | sP2(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5)),sK5) | ~v1_relat_1(k6_relat_1(sK5))),
% 0.20/0.53    inference(resolution,[],[f104,f51])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    ~sP4(k6_relat_1(sK5),sK5) | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) | sP2(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5)),sK5)),
% 0.20/0.53    inference(resolution,[],[f97,f53])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    ( ! [X0] : (~sP3(X0,k6_relat_1(sK5)) | sP2(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5)),X0) | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))) )),
% 0.20/0.53    inference(resolution,[],[f95,f44])).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    r2_hidden(k4_tarski(sK7(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))),
% 0.20/0.53    inference(equality_resolution,[],[f69])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X0] : (k6_relat_1(X0) != k6_relat_1(sK5) | r2_hidden(k4_tarski(sK7(k6_relat_1(sK5),k6_relat_1(X0)),sK6(k6_relat_1(sK5),k6_relat_1(X0))),k6_relat_1(sK5)) | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(X0)),sK7(k6_relat_1(sK5),k6_relat_1(X0))),k6_relat_1(X0))) )),
% 0.20/0.53    inference(resolution,[],[f66,f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sP0(X0,X1) | r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1] : ((sP0(X0,X1) | ((~r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~sP0(X0,X1)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f21,f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1))) => ((~r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~sP0(X0,X1)))),
% 0.20/0.53    inference(rectify,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X3,X2),X0)) & (r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~sP0(X0,X1)))),
% 0.20/0.53    inference(nnf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,plain,(
% 0.20/0.53    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ( ! [X0] : (~sP0(k6_relat_1(sK5),k6_relat_1(X0)) | k6_relat_1(X0) != k6_relat_1(sK5)) )),
% 0.20/0.53    inference(resolution,[],[f65,f34])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_relat_1(X0) | k6_relat_1(sK5) != X0 | ~sP0(k6_relat_1(sK5),X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f63,f34])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ( ! [X0] : (~sP0(k6_relat_1(sK5),X0) | k6_relat_1(sK5) != X0 | ~v1_relat_1(X0) | ~v1_relat_1(k6_relat_1(sK5))) )),
% 0.20/0.53    inference(resolution,[],[f56,f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sP1(X1,X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (sP1(X1,X0) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(definition_folding,[],[f7,f10,f9])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    ! [X1,X0] : ((k4_relat_1(X0) = X1 <=> sP0(X0,X1)) | ~sP1(X1,X0))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.53  fof(f7,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X0] : (~sP1(X0,k6_relat_1(sK5)) | ~sP0(k6_relat_1(sK5),X0) | k6_relat_1(sK5) != X0) )),
% 0.20/0.53    inference(superposition,[],[f33,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_relat_1(X1) = X0 | ~sP0(X1,X0) | ~sP1(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1] : (((k4_relat_1(X1) = X0 | ~sP0(X1,X0)) & (sP0(X1,X0) | k4_relat_1(X1) != X0)) | ~sP1(X0,X1))),
% 0.20/0.53    inference(rectify,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X1,X0] : (((k4_relat_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k4_relat_1(X0) != X1)) | ~sP1(X1,X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f10])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    k6_relat_1(sK5) != k4_relat_1(k6_relat_1(sK5))),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    k6_relat_1(sK5) != k4_relat_1(k6_relat_1(sK5))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f6,f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ? [X0] : k6_relat_1(X0) != k4_relat_1(k6_relat_1(X0)) => k6_relat_1(sK5) != k4_relat_1(k6_relat_1(sK5))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f6,plain,(
% 0.20/0.53    ? [X0] : k6_relat_1(X0) != k4_relat_1(k6_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,negated_conjecture,(
% 0.20/0.53    ~! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.20/0.53    inference(negated_conjecture,[],[f4])).
% 0.20/0.53  fof(f4,conjecture,(
% 0.20/0.53    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 0.20/0.53  fof(f167,plain,(
% 0.20/0.53    ~r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f156])).
% 0.20/0.53  fof(f156,plain,(
% 0.20/0.53    ~r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) | ~r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))),
% 0.20/0.53    inference(superposition,[],[f110,f144])).
% 0.20/0.53  fof(f110,plain,(
% 0.20/0.53    ~r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) | ~r2_hidden(k4_tarski(sK7(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))),
% 0.20/0.53    inference(equality_resolution,[],[f70])).
% 0.20/0.53  % (950)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X1] : (k6_relat_1(sK5) != k6_relat_1(X1) | ~r2_hidden(k4_tarski(sK7(k6_relat_1(sK5),k6_relat_1(X1)),sK6(k6_relat_1(sK5),k6_relat_1(X1))),k6_relat_1(sK5)) | ~r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(X1)),sK7(k6_relat_1(sK5),k6_relat_1(X1))),k6_relat_1(X1))) )),
% 0.20/0.53    inference(resolution,[],[f66,f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sP0(X0,X1) | ~r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f244,plain,(
% 0.20/0.53    r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) | r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK7(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))),
% 0.20/0.53    inference(backward_demodulation,[],[f95,f238])).
% 0.20/0.53  fof(f281,plain,(
% 0.20/0.53    ~r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f280])).
% 0.20/0.53  fof(f280,plain,(
% 0.20/0.53    ~r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) | ~r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))),
% 0.20/0.53    inference(forward_demodulation,[],[f248,f238])).
% 0.20/0.53  fof(f248,plain,(
% 0.20/0.53    ~r2_hidden(k4_tarski(sK6(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5)) | ~r2_hidden(k4_tarski(sK7(k6_relat_1(sK5),k6_relat_1(sK5)),sK6(k6_relat_1(sK5),k6_relat_1(sK5))),k6_relat_1(sK5))),
% 0.20/0.53    inference(backward_demodulation,[],[f110,f238])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (954)------------------------------
% 0.20/0.53  % (954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (954)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (954)Memory used [KB]: 1791
% 0.20/0.53  % (954)Time elapsed: 0.080 s
% 0.20/0.53  % (954)------------------------------
% 0.20/0.53  % (954)------------------------------
% 0.20/0.53  % (943)Success in time 0.174 s
%------------------------------------------------------------------------------
