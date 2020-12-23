%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0478+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:03 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 104 expanded)
%              Number of leaves         :   13 (  29 expanded)
%              Depth                    :   18
%              Number of atoms          :  236 ( 403 expanded)
%              Number of equality atoms :   19 (  28 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f238,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f237])).

fof(f237,plain,(
    ~ spl11_1 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f235,f102])).

fof(f102,plain,
    ( sP1(k6_relat_1(sK5))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl11_1
  <=> sP1(k6_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f235,plain,(
    ~ sP1(k6_relat_1(sK5)) ),
    inference(subsumption_resolution,[],[f232,f35])).

fof(f35,plain,(
    ~ r1_tarski(k6_relat_1(sK5),sK6) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(k6_relat_1(sK5),sK6)
    & ! [X2] :
        ( r2_hidden(k4_tarski(X2,X2),sK6)
        | ~ r2_hidden(X2,sK5) )
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f7,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k6_relat_1(X0),X1)
        & ! [X2] :
            ( r2_hidden(k4_tarski(X2,X2),X1)
            | ~ r2_hidden(X2,X0) )
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k6_relat_1(sK5),sK6)
      & ! [X2] :
          ( r2_hidden(k4_tarski(X2,X2),sK6)
          | ~ r2_hidden(X2,sK5) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k6_relat_1(X0),X1)
      & ! [X2] :
          ( r2_hidden(k4_tarski(X2,X2),X1)
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k6_relat_1(X0),X1)
      & ! [X2] :
          ( r2_hidden(k4_tarski(X2,X2),X1)
          | ~ r2_hidden(X2,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( ! [X2] :
              ( r2_hidden(X2,X0)
             => r2_hidden(k4_tarski(X2,X2),X1) )
         => r1_tarski(k6_relat_1(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r2_hidden(k4_tarski(X2,X2),X1) )
       => r1_tarski(k6_relat_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_relat_1)).

fof(f232,plain,
    ( r1_tarski(k6_relat_1(sK5),sK6)
    | ~ sP1(k6_relat_1(sK5)) ),
    inference(resolution,[],[f231,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ sP0(X1,X0)
      | r1_tarski(X0,X1)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ~ sP0(X1,X0) )
          & ( sP0(X1,X0)
            | ~ r1_tarski(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> sP0(X1,X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f231,plain,(
    sP0(sK6,k6_relat_1(sK5)) ),
    inference(resolution,[],[f224,f60])).

fof(f60,plain,(
    ! [X0] : sP3(X0,k6_relat_1(X0)) ),
    inference(subsumption_resolution,[],[f59,f36])).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f59,plain,(
    ! [X0] :
      ( sP3(X0,k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f53,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( sP4(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( sP4(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f9,f15,f14,f13])).

fof(f13,plain,(
    ! [X3,X2,X0] :
      ( sP2(X3,X2,X0)
    <=> ( X2 = X3
        & r2_hidden(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f14,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
    <=> ! [X2,X3] :
          ( r2_hidden(k4_tarski(X2,X3),X1)
        <=> sP2(X3,X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ( k6_relat_1(X0) = X1
      <=> sP3(X0,X1) )
      | ~ sP4(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f9,plain,(
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

fof(f53,plain,(
    ! [X1] :
      ( ~ sP4(k6_relat_1(X1),X1)
      | sP3(X1,k6_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f224,plain,(
    ! [X0] :
      ( ~ sP3(sK5,X0)
      | sP0(sK6,X0) ) ),
    inference(condensation,[],[f223])).

fof(f223,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X1)
      | sP0(sK6,X1)
      | ~ sP3(sK5,X1) ) ),
    inference(duplicate_literal_removal,[],[f222])).

fof(f222,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X1)
      | sP0(sK6,X1)
      | sP0(sK6,X1)
      | ~ sP3(sK5,X1) ) ),
    inference(resolution,[],[f216,f82])).

fof(f82,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK7(X5,X4),X3)
      | sP0(X5,X4)
      | ~ sP3(X3,X4) ) ),
    inference(resolution,[],[f74,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
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
    inference(nnf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X4,X2,X3] :
      ( sP2(sK8(X2,X3),sK7(X2,X3),X4)
      | ~ sP3(X4,X3)
      | sP0(X2,X3) ) ),
    inference(resolution,[],[f45,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
          & r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) ) )
      & ( ! [X4,X5] :
            ( r2_hidden(k4_tarski(X4,X5),X0)
            | ~ r2_hidden(k4_tarski(X4,X5),X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(k4_tarski(X2,X3),X1) )
     => ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( ~ r2_hidden(k4_tarski(X2,X3),X0)
            & r2_hidden(k4_tarski(X2,X3),X1) ) )
      & ( ! [X4,X5] :
            ( r2_hidden(k4_tarski(X4,X5),X0)
            | ~ r2_hidden(k4_tarski(X4,X5),X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2,X3] :
            ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            & r2_hidden(k4_tarski(X2,X3),X0) ) )
      & ( ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2,X3] :
          ( r2_hidden(k4_tarski(X2,X3),X1)
          | ~ r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f45,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X5),X1)
      | sP2(X5,X4,X0)
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ( ( ~ sP2(sK10(X0,X1),sK9(X0,X1),X0)
            | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) )
          & ( sP2(sK10(X0,X1),sK9(X0,X1),X0)
            | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) ) ) )
      & ( ! [X4,X5] :
            ( ( r2_hidden(k4_tarski(X4,X5),X1)
              | ~ sP2(X5,X4,X0) )
            & ( sP2(X5,X4,X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
        | ~ sP3(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ sP2(X3,X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( sP2(X3,X2,X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ sP2(sK10(X0,X1),sK9(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) )
        & ( sP2(sK10(X0,X1),sK9(X0,X1),X0)
          | r2_hidden(k4_tarski(sK9(X0,X1),sK10(X0,X1)),X1) ) ) ) ),
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
    inference(nnf_transformation,[],[f14])).

fof(f216,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(sK6,X0),sK5)
      | ~ sP3(X1,X0)
      | sP0(sK6,X0) ) ),
    inference(resolution,[],[f87,f34])).

fof(f34,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(X2,X2),sK6)
      | ~ r2_hidden(X2,sK5) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f87,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(k4_tarski(sK7(X4,X5),sK7(X4,X5)),X4)
      | sP0(X4,X5)
      | ~ sP3(X6,X5) ) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(k4_tarski(sK7(X4,X5),sK7(X4,X5)),X4)
      | sP0(X4,X5)
      | sP0(X4,X5)
      | ~ sP3(X6,X5) ) ),
    inference(superposition,[],[f41,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( sK8(X2,X1) = sK7(X2,X1)
      | sP0(X2,X1)
      | ~ sP3(X0,X1) ) ),
    inference(resolution,[],[f74,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f112,plain,(
    spl11_1 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl11_1 ),
    inference(subsumption_resolution,[],[f109,f36])).

fof(f109,plain,
    ( ~ v1_relat_1(k6_relat_1(sK5))
    | spl11_1 ),
    inference(resolution,[],[f103,f42])).

fof(f42,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f8,f11,f10])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

% (14993)Refutation not found, incomplete strategy% (14993)------------------------------
% (14993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(f103,plain,
    ( ~ sP1(k6_relat_1(sK5))
    | spl11_1 ),
    inference(avatar_component_clause,[],[f101])).

%------------------------------------------------------------------------------
