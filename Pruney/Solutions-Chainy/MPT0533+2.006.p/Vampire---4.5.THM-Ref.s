%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 119 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  318 ( 531 expanded)
%              Number of equality atoms :   21 (  26 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f561,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f43,f45,f70,f250,f177])).

fof(f177,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k6_relat_1(X2),X3)
      | ~ sP1(X4,X3)
      | ~ v1_relat_1(X3)
      | ~ r1_tarski(X2,X4) ) ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k6_relat_1(X2),X3)
      | ~ sP1(X4,X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X3)
      | r1_tarski(k6_relat_1(X2),X3)
      | ~ r1_tarski(X2,X4) ) ),
    inference(resolution,[],[f125,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1),X2)
      | ~ v1_relat_1(X1)
      | r1_tarski(k6_relat_1(X0),X1)
      | ~ r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f48,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK10(X0,X1),X1)
          & r2_hidden(sK10(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK10(X0,X1),X1)
        & r2_hidden(sK10(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

% (8265)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK7(X0,X1)),X1)
        & r2_hidden(sK7(X0,X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f15,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK7(X0,X1)),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r2_hidden(k4_tarski(X2,X2),X1) )
       => r1_tarski(k6_relat_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_relat_1)).

fof(f125,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(sK7(X6,X5),X7)
      | r1_tarski(k6_relat_1(X6),X5)
      | ~ sP1(X7,X5)
      | ~ v1_relat_1(X5) ) ),
    inference(resolution,[],[f86,f64])).

fof(f64,plain,(
    ! [X2,X1] :
      ( sP0(X1,X1,X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | X0 != X1
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | X0 != X1
        | ~ r2_hidden(X1,X2) )
      & ( ( X0 = X1
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X3,X2,X0] :
      ( ( sP0(X3,X2,X0)
        | X2 != X3
        | ~ r2_hidden(X2,X0) )
      & ( ( X2 = X3
          & r2_hidden(X2,X0) )
        | ~ sP0(X3,X2,X0) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X3,X2,X0] :
      ( ( sP0(X3,X2,X0)
        | X2 != X3
        | ~ r2_hidden(X2,X0) )
      & ( ( X2 = X3
          & r2_hidden(X2,X0) )
        | ~ sP0(X3,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X3,X2,X0] :
      ( sP0(X3,X2,X0)
    <=> ( X2 = X3
        & r2_hidden(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(sK7(X0,X1),sK7(X0,X1),X2)
      | ~ v1_relat_1(X1)
      | r1_tarski(k6_relat_1(X0),X1)
      | ~ sP1(X2,X1) ) ),
    inference(resolution,[],[f49,f53])).

fof(f53,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ sP0(X5,X4,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( ~ sP0(sK9(X0,X1),sK8(X0,X1),X0)
            | ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) )
          & ( sP0(sK9(X0,X1),sK8(X0,X1),X0)
            | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) ) ) )
      & ( ! [X4,X5] :
            ( ( r2_hidden(k4_tarski(X4,X5),X1)
              | ~ sP0(X5,X4,X0) )
            & ( sP0(X5,X4,X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ sP0(X3,X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( sP0(X3,X2,X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ sP0(sK9(X0,X1),sK8(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) )
        & ( sP0(sK9(X0,X1),sK8(X0,X1),X0)
          | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2,X3] :
            ( ( ~ sP0(X3,X2,X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( sP0(X3,X2,X0)
              | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
      & ( ! [X4,X5] :
            ( ( r2_hidden(k4_tarski(X4,X5),X1)
              | ~ sP0(X5,X4,X0) )
            & ( sP0(X5,X4,X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2,X3] :
            ( ( ~ sP0(X3,X2,X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( sP0(X3,X2,X0)
              | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
      & ( ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ sP0(X3,X2,X0) )
            & ( sP0(X3,X2,X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2,X3] :
          ( r2_hidden(k4_tarski(X2,X3),X1)
        <=> sP0(X3,X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK7(X0,X1)),X1)
      | r1_tarski(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f250,plain,(
    ~ r1_tarski(k6_relat_1(sK3),k6_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f249,f40])).

fof(f40,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK6))
    & r1_tarski(sK3,sK4)
    & r1_tarski(sK5,sK6)
    & v1_relat_1(sK6)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f10,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(sK3,sK5),k8_relat_1(sK4,X3))
          & r1_tarski(sK3,sK4)
          & r1_tarski(sK5,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

% (8254)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f23,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k8_relat_1(sK3,sK5),k8_relat_1(sK4,X3))
        & r1_tarski(sK3,sK4)
        & r1_tarski(sK5,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK6))
      & r1_tarski(sK3,sK4)
      & r1_tarski(sK5,sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_relat_1)).

fof(f249,plain,
    ( ~ r1_tarski(k6_relat_1(sK3),k6_relat_1(sK4))
    | ~ v1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f248,f41])).

fof(f41,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f24])).

fof(f248,plain,
    ( ~ r1_tarski(k6_relat_1(sK3),k6_relat_1(sK4))
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f234,f42])).

fof(f42,plain,(
    r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f24])).

fof(f234,plain,
    ( ~ r1_tarski(k6_relat_1(sK3),k6_relat_1(sK4))
    | ~ r1_tarski(sK5,sK6)
    | ~ v1_relat_1(sK6)
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f135,f44])).

fof(f44,plain,(
    ~ r1_tarski(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f24])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k8_relat_1(X2,X3),k8_relat_1(X1,X0))
      | ~ r1_tarski(k6_relat_1(X2),k6_relat_1(X1))
      | ~ r1_tarski(X3,X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f133,f45])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k8_relat_1(X2,X3),k8_relat_1(X1,X0))
      | ~ r1_tarski(k6_relat_1(X2),k6_relat_1(X1))
      | ~ r1_tarski(X3,X0)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k8_relat_1(X2,X3),k8_relat_1(X1,X0))
      | ~ r1_tarski(k6_relat_1(X2),k6_relat_1(X1))
      | ~ r1_tarski(X3,X0)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f100,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k8_relat_1(X1,X0),k5_relat_1(X2,X3))
      | ~ r1_tarski(k6_relat_1(X1),X3)
      | ~ r1_tarski(X0,X2)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f99,f45])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k8_relat_1(X1,X0),k5_relat_1(X2,X3))
      | ~ r1_tarski(k6_relat_1(X1),X3)
      | ~ r1_tarski(X0,X2)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k8_relat_1(X1,X0),k5_relat_1(X2,X3))
      | ~ r1_tarski(k6_relat_1(X1),X3)
      | ~ r1_tarski(X0,X2)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f46,f47])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  | ~ r1_tarski(X2,X3)
                  | ~ r1_tarski(X0,X1)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  | ~ r1_tarski(X2,X3)
                  | ~ r1_tarski(X0,X1)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ! [X3] :
                  ( v1_relat_1(X3)
                 => ( ( r1_tarski(X2,X3)
                      & r1_tarski(X0,X1) )
                   => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).

fof(f70,plain,(
    ! [X0] : sP1(X0,k6_relat_1(X0)) ),
    inference(subsumption_resolution,[],[f69,f45])).

fof(f69,plain,(
    ! [X0] :
      ( sP1(X0,k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f63,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f16,f20,f19,f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ( k6_relat_1(X0) = X1
      <=> sP1(X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).

fof(f63,plain,(
    ! [X1] :
      ( ~ sP2(k6_relat_1(X1),X1)
      | sP1(X1,k6_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | k6_relat_1(X1) != X0
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X1) = X0
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | k6_relat_1(X1) != X0 ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ( ( k6_relat_1(X0) = X1
          | ~ sP1(X0,X1) )
        & ( sP1(X0,X1)
          | k6_relat_1(X0) != X1 ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f43,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:14:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (8268)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.49  % (8251)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (8243)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (8237)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (8240)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (8239)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (8242)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (8250)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (8253)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (8262)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (8248)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (8245)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (8239)Refutation not found, incomplete strategy% (8239)------------------------------
% 0.21/0.54  % (8239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8239)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8239)Memory used [KB]: 10746
% 0.21/0.54  % (8239)Time elapsed: 0.110 s
% 0.21/0.54  % (8239)------------------------------
% 0.21/0.54  % (8239)------------------------------
% 0.21/0.54  % (8268)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f561,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f43,f45,f70,f250,f177])).
% 0.21/0.54  fof(f177,plain,(
% 0.21/0.54    ( ! [X4,X2,X3] : (r1_tarski(k6_relat_1(X2),X3) | ~sP1(X4,X3) | ~v1_relat_1(X3) | ~r1_tarski(X2,X4)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f176])).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    ( ! [X4,X2,X3] : (r1_tarski(k6_relat_1(X2),X3) | ~sP1(X4,X3) | ~v1_relat_1(X3) | ~v1_relat_1(X3) | r1_tarski(k6_relat_1(X2),X3) | ~r1_tarski(X2,X4)) )),
% 0.21/0.54    inference(resolution,[],[f125,f79])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1),X2) | ~v1_relat_1(X1) | r1_tarski(k6_relat_1(X0),X1) | ~r1_tarski(X0,X2)) )),
% 0.21/0.54    inference(resolution,[],[f48,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK10(X0,X1),X1) & r2_hidden(sK10(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f37,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK10(X0,X1),X1) & r2_hidden(sK10(X0,X1),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(rectify,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(nnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  % (8265)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(k6_relat_1(X0),X1) | (~r2_hidden(k4_tarski(sK7(X0,X1),sK7(X0,X1)),X1) & r2_hidden(sK7(X0,X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f15,f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0)) => (~r2_hidden(k4_tarski(sK7(X0,X1),sK7(X0,X1)),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(k6_relat_1(X0),X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(k6_relat_1(X0),X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0))) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (! [X2] : (r2_hidden(X2,X0) => r2_hidden(k4_tarski(X2,X2),X1)) => r1_tarski(k6_relat_1(X0),X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_relat_1)).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    ( ! [X6,X7,X5] : (~r2_hidden(sK7(X6,X5),X7) | r1_tarski(k6_relat_1(X6),X5) | ~sP1(X7,X5) | ~v1_relat_1(X5)) )),
% 0.21/0.54    inference(resolution,[],[f86,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X2,X1] : (sP0(X1,X1,X2) | ~r2_hidden(X1,X2)) )),
% 0.21/0.54    inference(equality_resolution,[],[f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | X0 != X1 | ~r2_hidden(X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | X0 != X1 | ~r2_hidden(X1,X2)) & ((X0 = X1 & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 0.21/0.54    inference(rectify,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X3,X2,X0] : ((sP0(X3,X2,X0) | X2 != X3 | ~r2_hidden(X2,X0)) & ((X2 = X3 & r2_hidden(X2,X0)) | ~sP0(X3,X2,X0)))),
% 0.21/0.54    inference(flattening,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X3,X2,X0] : ((sP0(X3,X2,X0) | (X2 != X3 | ~r2_hidden(X2,X0))) & ((X2 = X3 & r2_hidden(X2,X0)) | ~sP0(X3,X2,X0)))),
% 0.21/0.54    inference(nnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X3,X2,X0] : (sP0(X3,X2,X0) <=> (X2 = X3 & r2_hidden(X2,X0)))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~sP0(sK7(X0,X1),sK7(X0,X1),X2) | ~v1_relat_1(X1) | r1_tarski(k6_relat_1(X0),X1) | ~sP1(X2,X1)) )),
% 0.21/0.54    inference(resolution,[],[f49,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~sP0(X5,X4,X0) | ~sP1(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1] : ((sP1(X0,X1) | ((~sP0(sK9(X0,X1),sK8(X0,X1),X0) | ~r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)) & (sP0(sK9(X0,X1),sK8(X0,X1),X0) | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~sP0(X5,X4,X0)) & (sP0(X5,X4,X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~sP1(X0,X1)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f30,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2,X3] : ((~sP0(X3,X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (sP0(X3,X2,X0) | r2_hidden(k4_tarski(X2,X3),X1))) => ((~sP0(sK9(X0,X1),sK8(X0,X1),X0) | ~r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1)) & (sP0(sK9(X0,X1),sK8(X0,X1),X0) | r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X1))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1] : ((sP1(X0,X1) | ? [X2,X3] : ((~sP0(X3,X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (sP0(X3,X2,X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~sP0(X5,X4,X0)) & (sP0(X5,X4,X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~sP1(X0,X1)))),
% 0.21/0.54    inference(rectify,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : ((sP1(X0,X1) | ? [X2,X3] : ((~sP0(X3,X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (sP0(X3,X2,X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | ~sP0(X3,X2,X0)) & (sP0(X3,X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~sP1(X0,X1)))),
% 0.21/0.54    inference(nnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> sP0(X3,X2,X0)))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK7(X0,X1),sK7(X0,X1)),X1) | r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f250,plain,(
% 0.21/0.54    ~r1_tarski(k6_relat_1(sK3),k6_relat_1(sK4))),
% 0.21/0.54    inference(subsumption_resolution,[],[f249,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    v1_relat_1(sK5)),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    (~r1_tarski(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK6)) & r1_tarski(sK3,sK4) & r1_tarski(sK5,sK6) & v1_relat_1(sK6)) & v1_relat_1(sK5)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f10,f23,f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k8_relat_1(sK3,sK5),k8_relat_1(sK4,X3)) & r1_tarski(sK3,sK4) & r1_tarski(sK5,X3) & v1_relat_1(X3)) & v1_relat_1(sK5))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  % (8254)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ? [X3] : (~r1_tarski(k8_relat_1(sK3,sK5),k8_relat_1(sK4,X3)) & r1_tarski(sK3,sK4) & r1_tarski(sK5,X3) & v1_relat_1(X3)) => (~r1_tarski(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK6)) & r1_tarski(sK3,sK4) & r1_tarski(sK5,sK6) & v1_relat_1(sK6))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.21/0.54    inference(flattening,[],[f9])).
% 0.21/0.54  fof(f9,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 0.21/0.54    inference(negated_conjecture,[],[f7])).
% 0.21/0.54  fof(f7,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_relat_1)).
% 0.21/0.54  fof(f249,plain,(
% 0.21/0.54    ~r1_tarski(k6_relat_1(sK3),k6_relat_1(sK4)) | ~v1_relat_1(sK5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f248,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    v1_relat_1(sK6)),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f248,plain,(
% 0.21/0.54    ~r1_tarski(k6_relat_1(sK3),k6_relat_1(sK4)) | ~v1_relat_1(sK6) | ~v1_relat_1(sK5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f234,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    r1_tarski(sK5,sK6)),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f234,plain,(
% 0.21/0.54    ~r1_tarski(k6_relat_1(sK3),k6_relat_1(sK4)) | ~r1_tarski(sK5,sK6) | ~v1_relat_1(sK6) | ~v1_relat_1(sK5)),
% 0.21/0.54    inference(resolution,[],[f135,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ~r1_tarski(k8_relat_1(sK3,sK5),k8_relat_1(sK4,sK6))),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (r1_tarski(k8_relat_1(X2,X3),k8_relat_1(X1,X0)) | ~r1_tarski(k6_relat_1(X2),k6_relat_1(X1)) | ~r1_tarski(X3,X0) | ~v1_relat_1(X0) | ~v1_relat_1(X3)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f133,f45])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (r1_tarski(k8_relat_1(X2,X3),k8_relat_1(X1,X0)) | ~r1_tarski(k6_relat_1(X2),k6_relat_1(X1)) | ~r1_tarski(X3,X0) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~v1_relat_1(X3)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f130])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (r1_tarski(k8_relat_1(X2,X3),k8_relat_1(X1,X0)) | ~r1_tarski(k6_relat_1(X2),k6_relat_1(X1)) | ~r1_tarski(X3,X0) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~v1_relat_1(X3) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(superposition,[],[f100,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (r1_tarski(k8_relat_1(X1,X0),k5_relat_1(X2,X3)) | ~r1_tarski(k6_relat_1(X1),X3) | ~r1_tarski(X0,X2) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f99,f45])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (r1_tarski(k8_relat_1(X1,X0),k5_relat_1(X2,X3)) | ~r1_tarski(k6_relat_1(X1),X3) | ~r1_tarski(X0,X2) | ~v1_relat_1(X3) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f96])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (r1_tarski(k8_relat_1(X1,X0),k5_relat_1(X2,X3)) | ~r1_tarski(k6_relat_1(X1),X3) | ~r1_tarski(X0,X2) | ~v1_relat_1(X3) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X2) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(superposition,[],[f46,f47])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X0] : (sP1(X0,k6_relat_1(X0))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f69,f45])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X0] : (sP1(X0,k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.54    inference(resolution,[],[f63,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sP2(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1] : (sP2(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(definition_folding,[],[f16,f20,f19,f18])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X1,X0] : ((k6_relat_1(X0) = X1 <=> sP1(X0,X1)) | ~sP2(X1,X0))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X1] : (~sP2(k6_relat_1(X1),X1) | sP1(X1,k6_relat_1(X1))) )),
% 0.21/0.54    inference(equality_resolution,[],[f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sP1(X1,X0) | k6_relat_1(X1) != X0 | ~sP2(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1] : (((k6_relat_1(X1) = X0 | ~sP1(X1,X0)) & (sP1(X1,X0) | k6_relat_1(X1) != X0)) | ~sP2(X0,X1))),
% 0.21/0.54    inference(rectify,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X1,X0] : (((k6_relat_1(X0) = X1 | ~sP1(X0,X1)) & (sP1(X0,X1) | k6_relat_1(X0) != X1)) | ~sP2(X1,X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f20])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    r1_tarski(sK3,sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (8268)------------------------------
% 0.21/0.54  % (8268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8268)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (8268)Memory used [KB]: 2046
% 0.21/0.54  % (8268)Time elapsed: 0.126 s
% 0.21/0.54  % (8268)------------------------------
% 0.21/0.54  % (8268)------------------------------
% 0.21/0.55  % (8236)Success in time 0.179 s
%------------------------------------------------------------------------------
