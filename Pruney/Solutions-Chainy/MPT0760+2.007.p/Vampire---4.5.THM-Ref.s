%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   65 (  87 expanded)
%              Number of leaves         :   16 (  25 expanded)
%              Depth                    :   15
%              Number of atoms          :  299 ( 374 expanded)
%              Number of equality atoms :   60 (  83 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f254,plain,(
    $false ),
    inference(resolution,[],[f251,f57])).

fof(f57,plain,(
    ~ r2_hidden(sK4,k3_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k1_xboole_0 != k1_wellord1(sK5,sK4)
    & ~ r2_hidden(sK4,k3_relat_1(sK5))
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f19,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 != k1_wellord1(X1,X0)
        & ~ r2_hidden(X0,k3_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k1_xboole_0 != k1_wellord1(sK5,sK4)
      & ~ r2_hidden(sK4,k3_relat_1(sK5))
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != k1_wellord1(X1,X0)
      & ~ r2_hidden(X0,k3_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != k1_wellord1(X1,X0)
      & ~ r2_hidden(X0,k3_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k1_wellord1(X1,X0)
          | r2_hidden(X0,k3_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k1_wellord1(X1,X0)
        | r2_hidden(X0,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord1)).

fof(f251,plain,(
    r2_hidden(sK4,k3_relat_1(sK5)) ),
    inference(resolution,[],[f189,f116])).

fof(f116,plain,(
    sP2(k2_relat_1(sK5),k1_relat_1(sK5),k3_relat_1(sK5)) ),
    inference(superposition,[],[f112,f115])).

fof(f115,plain,(
    k3_relat_1(sK5) = k2_xboole_0(k1_relat_1(sK5),k2_relat_1(sK5)) ),
    inference(resolution,[],[f61,f56])).

fof(f56,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f112,plain,(
    ! [X0,X1] : sP2(X1,X0,k2_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,X0,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP2(X1,X0,X2) )
      & ( sP2(X1,X0,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP2(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( sP2(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f189,plain,(
    ! [X6,X7] :
      ( ~ sP2(k2_relat_1(sK5),X7,X6)
      | r2_hidden(sK4,X6) ) ),
    inference(resolution,[],[f166,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ( ~ r2_hidden(sK10(X0,X1,X2),X0)
              & ~ r2_hidden(sK10(X0,X1,X2),X1) )
            | ~ r2_hidden(sK10(X0,X1,X2),X2) )
          & ( r2_hidden(sK10(X0,X1,X2),X0)
            | r2_hidden(sK10(X0,X1,X2),X1)
            | r2_hidden(sK10(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X3,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X0)
            | r2_hidden(X3,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK10(X0,X1,X2),X0)
            & ~ r2_hidden(sK10(X0,X1,X2),X1) )
          | ~ r2_hidden(sK10(X0,X1,X2),X2) )
        & ( r2_hidden(sK10(X0,X1,X2),X0)
          | r2_hidden(sK10(X0,X1,X2),X1)
          | r2_hidden(sK10(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X3,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X0)
              | r2_hidden(X3,X1)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f166,plain,(
    r2_hidden(sK4,k2_relat_1(sK5)) ),
    inference(resolution,[],[f140,f110])).

fof(f110,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f39,f42,f41,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f140,plain,(
    r2_hidden(k4_tarski(sK6(sK5,sK4,k1_xboole_0),sK4),sK5) ),
    inference(trivial_inequality_removal,[],[f138])).

fof(f138,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(k4_tarski(sK6(sK5,sK4,k1_xboole_0),sK4),sK5) ),
    inference(superposition,[],[f58,f137])).

fof(f137,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_wellord1(sK5,X0)
      | r2_hidden(k4_tarski(sK6(sK5,X0,k1_xboole_0),X0),sK5) ) ),
    inference(resolution,[],[f128,f59])).

fof(f59,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f128,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X5,sK6(sK5,X4,X5))
      | k1_wellord1(sK5,X4) = X5
      | r2_hidden(k4_tarski(sK6(sK5,X4,X5),X4),sK5) ) ),
    inference(resolution,[],[f126,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f126,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(sK5,X0,X1),X1)
      | r2_hidden(k4_tarski(sK6(sK5,X0,X1),X0),sK5)
      | k1_wellord1(sK5,X0) = X1 ) ),
    inference(resolution,[],[f68,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK5,X0,X1)
      | k1_wellord1(sK5,X0) = X1 ) ),
    inference(resolution,[],[f118,f56])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_wellord1(X0,X1) = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f63,f70])).

fof(f70,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f21,f24,f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(k4_tarski(X3,X1),X0)
            & X1 != X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> sP0(X0,X1,X2) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0)
      | ~ sP0(X0,X1,X2)
      | k1_wellord1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ~ sP0(X0,X1,X2) )
          & ( sP0(X0,X1,X2)
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),X1),X0)
      | r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),X1),X0)
            | sK6(X0,X1,X2) = X1
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),X1),X0)
              & sK6(X0,X1,X2) != X1 )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(k4_tarski(X4,X1),X0)
              | X1 = X4 )
            & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                & X1 != X4 )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),X1),X0)
          | sK6(X0,X1,X2) = X1
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),X1),X0)
            & sK6(X0,X1,X2) != X1 )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
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
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
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
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
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
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f58,plain,(
    k1_xboole_0 != k1_wellord1(sK5,sK4) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:48:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (28862)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (28862)Refutation not found, incomplete strategy% (28862)------------------------------
% 0.22/0.51  % (28862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28854)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (28862)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (28862)Memory used [KB]: 10746
% 0.22/0.51  % (28862)Time elapsed: 0.055 s
% 0.22/0.51  % (28862)------------------------------
% 0.22/0.51  % (28862)------------------------------
% 0.22/0.52  % (28839)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (28846)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (28845)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (28852)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (28868)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (28843)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (28848)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (28840)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (28860)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (28853)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (28844)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (28869)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (28852)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f254,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(resolution,[],[f251,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ~r2_hidden(sK4,k3_relat_1(sK5))),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    k1_xboole_0 != k1_wellord1(sK5,sK4) & ~r2_hidden(sK4,k3_relat_1(sK5)) & v1_relat_1(sK5)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f19,f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ? [X0,X1] : (k1_xboole_0 != k1_wellord1(X1,X0) & ~r2_hidden(X0,k3_relat_1(X1)) & v1_relat_1(X1)) => (k1_xboole_0 != k1_wellord1(sK5,sK4) & ~r2_hidden(sK4,k3_relat_1(sK5)) & v1_relat_1(sK5))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ? [X0,X1] : (k1_xboole_0 != k1_wellord1(X1,X0) & ~r2_hidden(X0,k3_relat_1(X1)) & v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ? [X0,X1] : ((k1_xboole_0 != k1_wellord1(X1,X0) & ~r2_hidden(X0,k3_relat_1(X1))) & v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k1_wellord1(X1,X0) | r2_hidden(X0,k3_relat_1(X1))))),
% 0.22/0.54    inference(negated_conjecture,[],[f16])).
% 0.22/0.54  fof(f16,conjecture,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k1_wellord1(X1,X0) | r2_hidden(X0,k3_relat_1(X1))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord1)).
% 0.22/0.54  fof(f251,plain,(
% 0.22/0.54    r2_hidden(sK4,k3_relat_1(sK5))),
% 0.22/0.54    inference(resolution,[],[f189,f116])).
% 0.22/0.54  fof(f116,plain,(
% 0.22/0.54    sP2(k2_relat_1(sK5),k1_relat_1(sK5),k3_relat_1(sK5))),
% 0.22/0.54    inference(superposition,[],[f112,f115])).
% 0.22/0.54  fof(f115,plain,(
% 0.22/0.54    k3_relat_1(sK5) = k2_xboole_0(k1_relat_1(sK5),k2_relat_1(sK5))),
% 0.22/0.54    inference(resolution,[],[f61,f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    v1_relat_1(sK5)),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    ( ! [X0,X1] : (sP2(X1,X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f85])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (sP2(X1,X0,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP2(X1,X0,X2)) & (sP2(X1,X0,X2) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(nnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP2(X1,X0,X2))),
% 0.22/0.54    inference(definition_folding,[],[f1,f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X1,X0,X2] : (sP2(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.22/0.54  fof(f189,plain,(
% 0.22/0.54    ( ! [X6,X7] : (~sP2(k2_relat_1(sK5),X7,X6) | r2_hidden(sK4,X6)) )),
% 0.22/0.54    inference(resolution,[],[f166,f81])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X0) | r2_hidden(X4,X2) | ~sP2(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | (((~r2_hidden(sK10(X0,X1,X2),X0) & ~r2_hidden(sK10(X0,X1,X2),X1)) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (r2_hidden(sK10(X0,X1,X2),X0) | r2_hidden(sK10(X0,X1,X2),X1) | r2_hidden(sK10(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f46,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2))) => (((~r2_hidden(sK10(X0,X1,X2),X0) & ~r2_hidden(sK10(X0,X1,X2),X1)) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (r2_hidden(sK10(X0,X1,X2),X0) | r2_hidden(sK10(X0,X1,X2),X1) | r2_hidden(sK10(X0,X1,X2),X2))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.22/0.54    inference(rectify,[],[f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 0.22/0.54    inference(flattening,[],[f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 0.22/0.54    inference(nnf_transformation,[],[f26])).
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    r2_hidden(sK4,k2_relat_1(sK5))),
% 0.22/0.54    inference(resolution,[],[f140,f110])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X6,X5),X0) | r2_hidden(X5,k2_relat_1(X0))) )),
% 0.22/0.54    inference(equality_resolution,[],[f74])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f39,f42,f41,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0) => r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK9(X0,X5),X5),X0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.54    inference(rectify,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.22/0.54  fof(f140,plain,(
% 0.22/0.54    r2_hidden(k4_tarski(sK6(sK5,sK4,k1_xboole_0),sK4),sK5)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f138])).
% 0.22/0.54  fof(f138,plain,(
% 0.22/0.54    k1_xboole_0 != k1_xboole_0 | r2_hidden(k4_tarski(sK6(sK5,sK4,k1_xboole_0),sK4),sK5)),
% 0.22/0.54    inference(superposition,[],[f58,f137])).
% 0.22/0.54  fof(f137,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k1_wellord1(sK5,X0) | r2_hidden(k4_tarski(sK6(sK5,X0,k1_xboole_0),X0),sK5)) )),
% 0.22/0.54    inference(resolution,[],[f128,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    ( ! [X4,X5] : (~r1_tarski(X5,sK6(sK5,X4,X5)) | k1_wellord1(sK5,X4) = X5 | r2_hidden(k4_tarski(sK6(sK5,X4,X5),X4),sK5)) )),
% 0.22/0.54    inference(resolution,[],[f126,f77])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK6(sK5,X0,X1),X1) | r2_hidden(k4_tarski(sK6(sK5,X0,X1),X0),sK5) | k1_wellord1(sK5,X0) = X1) )),
% 0.22/0.54    inference(resolution,[],[f68,f119])).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~sP0(sK5,X0,X1) | k1_wellord1(sK5,X0) = X1) )),
% 0.22/0.54    inference(resolution,[],[f118,f56])).
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k1_wellord1(X0,X1) = X2 | ~sP0(X0,X1,X2)) )),
% 0.22/0.54    inference(resolution,[],[f63,f70])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    ( ! [X0] : (sP1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : (sP1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(definition_folding,[],[f21,f24,f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (sP0(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3)))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> sP0(X0,X1,X2)) | ~sP1(X0))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~sP1(X0) | ~sP0(X0,X1,X2) | k1_wellord1(X0,X1) = X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ~sP0(X0,X1,X2)) & (sP0(X0,X1,X2) | k1_wellord1(X0,X1) != X2)) | ~sP1(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f24])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(k4_tarski(sK6(X0,X1,X2),X1),X0) | r2_hidden(sK6(X0,X1,X2),X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(k4_tarski(sK6(X0,X1,X2),X1),X0) | sK6(X0,X1,X2) = X1 | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK6(X0,X1,X2),X1),X0) & sK6(X0,X1,X2) != X1) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK6(X0,X1,X2),X1),X0) | sK6(X0,X1,X2) = X1 | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK6(X0,X1,X2),X1),X0) & sK6(X0,X1,X2) != X1) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.54    inference(rectify,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.54    inference(flattening,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.54    inference(nnf_transformation,[],[f23])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    k1_xboole_0 != k1_wellord1(sK5,sK4)),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (28852)------------------------------
% 0.22/0.54  % (28852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28852)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (28852)Memory used [KB]: 6396
% 0.22/0.54  % (28852)Time elapsed: 0.120 s
% 0.22/0.54  % (28852)------------------------------
% 0.22/0.54  % (28852)------------------------------
% 0.22/0.54  % (28865)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (28837)Success in time 0.18 s
%------------------------------------------------------------------------------
