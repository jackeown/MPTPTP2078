%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 142 expanded)
%              Number of leaves         :   17 (  42 expanded)
%              Depth                    :   16
%              Number of atoms          :  277 ( 499 expanded)
%              Number of equality atoms :   30 (  59 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f181,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f177])).

fof(f177,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(resolution,[],[f175,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ sP1(k1_xboole_0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f44,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ~ sP1(X0,X1) )
      & ( sP1(X0,X1)
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> sP1(X0,X1) ) ),
    inference(definition_folding,[],[f6,f11,f10])).

fof(f10,plain,(
    ! [X0,X2] :
      ( sP0(X0,X2)
    <=> ? [X3] :
          ( r2_hidden(X3,X0)
          & r2_hidden(X2,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f11,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP0(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f44,plain,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(flattening,[],[f8])).

fof(f8,negated_conjecture,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f175,plain,(
    sP1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f129,f123])).

fof(f123,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f120,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( ~ r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X1,X3,X0] :
      ( ( sP2(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP2(X1,X3,X0) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X1,X3,X0] :
      ( ( sP2(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP2(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X1,X3,X0] :
      ( sP2(X1,X3,X0)
    <=> ( ~ r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f120,plain,(
    ! [X4,X2,X3] :
      ( sP2(X3,X2,X4)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(resolution,[],[f117,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | sP2(X2,X0,X1) ) ),
    inference(resolution,[],[f57,f80])).

fof(f80,plain,(
    ! [X0,X1] : sP3(X0,X1,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP3(X0,X1,X2) )
      & ( sP3(X0,X1,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP3(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f14,f13])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( sP3(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP2(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP2(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ( ~ sP2(X1,sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( sP2(X1,sK8(X0,X1,X2),X0)
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP2(X1,X4,X0) )
            & ( sP2(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP2(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP2(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP2(X1,sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( sP2(X1,sK8(X0,X1,X2),X0)
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP2(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP2(X1,X4,X0) )
            & ( sP2(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP2(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP2(X1,X3,X0) )
            & ( sP2(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f115,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ( ~ r2_hidden(X1,X0)
          & ~ r2_hidden(X1,X2) ) )
      & ( r2_hidden(X1,X0)
        | r2_hidden(X1,X2)
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X1,X3,X0] :
      ( ( sP4(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP4(X1,X3,X0) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X1,X3,X0] :
      ( ( sP4(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP4(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X1,X3,X0] :
      ( sP4(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ sP4(k1_xboole_0,X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f114,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | ~ sP4(X1,X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ( ( ~ sP4(X1,sK9(X0,X1,X2),X0)
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( sP4(X1,sK9(X0,X1,X2),X0)
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP4(X1,X4,X0) )
            & ( sP4(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP4(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP4(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP4(X1,sK9(X0,X1,X2),X0)
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( sP4(X1,sK9(X0,X1,X2),X0)
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP4(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP4(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP4(X1,X4,X0) )
            & ( sP4(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP4(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP4(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP4(X1,X3,X0) )
            & ( sP4(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( sP5(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP4(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f114,plain,(
    ! [X0] : sP5(X0,k1_xboole_0,X0) ),
    inference(superposition,[],[f81,f76])).

fof(f76,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f45,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f47,f46])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f81,plain,(
    ! [X0,X1] : sP5(X0,X1,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( sP5(X0,X1,X2)
      | k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f73,f75])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( sP5(X0,X1,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP5(X0,X1,X2) )
      & ( sP5(X0,X1,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP5(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f17,f16])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f129,plain,(
    ! [X4] :
      ( r2_hidden(sK6(k1_xboole_0,X4),X4)
      | sP1(k1_xboole_0,X4) ) ),
    inference(resolution,[],[f125,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( sP0(X0,sK6(X0,X1))
      | sP1(X0,X1)
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( ~ sP0(X0,sK6(X0,X1))
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sP0(X0,sK6(X0,X1))
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X0,X3) )
            & ( sP0(X0,X3)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ sP0(X0,X2)
            | ~ r2_hidden(X2,X1) )
          & ( sP0(X0,X2)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ sP0(X0,sK6(X0,X1))
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sP0(X0,sK6(X0,X1))
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X0,X2)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X0,X2)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X0,X3) )
            & ( sP0(X0,X3)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X0,X2)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X0,X2)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ sP0(X0,X2) )
            & ( sP0(X0,X2)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f125,plain,(
    ! [X1] : ~ sP0(k1_xboole_0,X1) ),
    inference(resolution,[],[f123,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | ~ r2_hidden(X1,X2) ) )
      & ( ( r2_hidden(sK7(X0,X1),X0)
          & r2_hidden(X1,sK7(X0,X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X0)
          & r2_hidden(X1,X3) )
     => ( r2_hidden(sK7(X0,X1),X0)
        & r2_hidden(X1,sK7(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | ~ r2_hidden(X1,X2) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X0)
            & r2_hidden(X1,X3) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X2] :
      ( ( sP0(X0,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X3) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X0)
            & r2_hidden(X2,X3) )
        | ~ sP0(X0,X2) ) ) ),
    inference(nnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:46:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (23964)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.51  % (23946)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (23955)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (23941)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (23955)Refutation not found, incomplete strategy% (23955)------------------------------
% 0.22/0.51  % (23955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (23955)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (23955)Memory used [KB]: 6140
% 0.22/0.51  % (23955)Time elapsed: 0.003 s
% 0.22/0.51  % (23955)------------------------------
% 0.22/0.51  % (23955)------------------------------
% 0.22/0.51  % (23945)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (23947)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (23967)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.51  % (23954)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (23967)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f181,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f177])).
% 0.22/0.52  fof(f177,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0),
% 0.22/0.52    inference(resolution,[],[f175,f83])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ( ! [X0] : (~sP1(k1_xboole_0,X0) | k1_xboole_0 != X0) )),
% 0.22/0.52    inference(superposition,[],[f44,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_tarski(X0) = X1 | ~sP1(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1] : ((k3_tarski(X0) = X1 | ~sP1(X0,X1)) & (sP1(X0,X1) | k3_tarski(X0) != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0,X1] : (k3_tarski(X0) = X1 <=> sP1(X0,X1))),
% 0.22/0.52    inference(definition_folding,[],[f6,f11,f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0,X2] : (sP0(X0,X2) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> sP0(X0,X2)))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 0.22/0.52    inference(flattening,[],[f8])).
% 0.22/0.52  fof(f8,negated_conjecture,(
% 0.22/0.52    ~k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.52    inference(negated_conjecture,[],[f7])).
% 0.22/0.52  fof(f7,conjecture,(
% 0.22/0.52    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    sP1(k1_xboole_0,k1_xboole_0)),
% 0.22/0.52    inference(resolution,[],[f129,f123])).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(condensation,[],[f121])).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(resolution,[],[f120,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP2(X0,X1,X2)))),
% 0.22/0.52    inference(rectify,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X1,X3,X0] : ((sP2(X1,X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP2(X1,X3,X0)))),
% 0.22/0.52    inference(flattening,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X1,X3,X0] : ((sP2(X1,X3,X0) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP2(X1,X3,X0)))),
% 0.22/0.52    inference(nnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X1,X3,X0] : (sP2(X1,X3,X0) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    ( ! [X4,X2,X3] : (sP2(X3,X2,X4) | ~r2_hidden(X2,k1_xboole_0)) )),
% 0.22/0.52    inference(resolution,[],[f117,f100])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | sP2(X2,X0,X1)) )),
% 0.22/0.52    inference(resolution,[],[f57,f80])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    ( ! [X0,X1] : (sP3(X0,X1,k4_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(equality_resolution,[],[f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP3(X0,X1,X2)) & (sP3(X0,X1,X2) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(nnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP3(X0,X1,X2))),
% 0.22/0.52    inference(definition_folding,[],[f2,f14,f13])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (sP3(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP2(X1,X3,X0)))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X1] : (~sP3(X0,X1,X2) | ~r2_hidden(X4,X2) | sP2(X1,X4,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ((~sP2(X1,sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sP2(X1,sK8(X0,X1,X2),X0) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP2(X1,X4,X0)) & (sP2(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP3(X0,X1,X2)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f29,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X2,X1,X0] : (? [X3] : ((~sP2(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP2(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP2(X1,sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sP2(X1,sK8(X0,X1,X2),X0) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : ((~sP2(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP2(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP2(X1,X4,X0)) & (sP2(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP3(X0,X1,X2)))),
% 0.22/0.52    inference(rectify,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : ((~sP2(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP2(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP2(X1,X3,X0)) & (sP2(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP3(X0,X1,X2)))),
% 0.22/0.52    inference(nnf_transformation,[],[f14])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(resolution,[],[f115,f72])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (sP4(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | (~r2_hidden(X1,X0) & ~r2_hidden(X1,X2))) & (r2_hidden(X1,X0) | r2_hidden(X1,X2) | ~sP4(X0,X1,X2)))),
% 0.22/0.52    inference(rectify,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ! [X1,X3,X0] : ((sP4(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~sP4(X1,X3,X0)))),
% 0.22/0.52    inference(flattening,[],[f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ! [X1,X3,X0] : ((sP4(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~sP4(X1,X3,X0)))),
% 0.22/0.52    inference(nnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X1,X3,X0] : (sP4(X1,X3,X0) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0)))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~sP4(k1_xboole_0,X0,X1) | r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(resolution,[],[f114,f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X1] : (~sP5(X0,X1,X2) | ~sP4(X1,X4,X0) | r2_hidden(X4,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | ((~sP4(X1,sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (sP4(X1,sK9(X0,X1,X2),X0) | r2_hidden(sK9(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP4(X1,X4,X0)) & (sP4(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP5(X0,X1,X2)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f37,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ! [X2,X1,X0] : (? [X3] : ((~sP4(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP4(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP4(X1,sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (sP4(X1,sK9(X0,X1,X2),X0) | r2_hidden(sK9(X0,X1,X2),X2))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | ? [X3] : ((~sP4(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP4(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP4(X1,X4,X0)) & (sP4(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP5(X0,X1,X2)))),
% 0.22/0.52    inference(rectify,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | ? [X3] : ((~sP4(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP4(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP4(X1,X3,X0)) & (sP4(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP5(X0,X1,X2)))),
% 0.22/0.52    inference(nnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (sP5(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP4(X1,X3,X0)))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    ( ! [X0] : (sP5(X0,k1_xboole_0,X0)) )),
% 0.22/0.52    inference(superposition,[],[f81,f76])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = X0) )),
% 0.22/0.52    inference(definition_unfolding,[],[f45,f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f47,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    ( ! [X0,X1] : (sP5(X0,X1,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) )),
% 0.22/0.52    inference(equality_resolution,[],[f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (sP5(X0,X1,X2) | k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) != X2) )),
% 0.22/0.52    inference(definition_unfolding,[],[f73,f75])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (sP5(X0,X1,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP5(X0,X1,X2)) & (sP5(X0,X1,X2) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(nnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP5(X0,X1,X2))),
% 0.22/0.52    inference(definition_folding,[],[f1,f17,f16])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    ( ! [X4] : (r2_hidden(sK6(k1_xboole_0,X4),X4) | sP1(k1_xboole_0,X4)) )),
% 0.22/0.52    inference(resolution,[],[f125,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0,X1] : (sP0(X0,sK6(X0,X1)) | sP1(X0,X1) | r2_hidden(sK6(X0,X1),X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1] : ((sP1(X0,X1) | ((~sP0(X0,sK6(X0,X1)) | ~r2_hidden(sK6(X0,X1),X1)) & (sP0(X0,sK6(X0,X1)) | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X0,X3)) & (sP0(X0,X3) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2] : ((~sP0(X0,X2) | ~r2_hidden(X2,X1)) & (sP0(X0,X2) | r2_hidden(X2,X1))) => ((~sP0(X0,sK6(X0,X1)) | ~r2_hidden(sK6(X0,X1),X1)) & (sP0(X0,sK6(X0,X1)) | r2_hidden(sK6(X0,X1),X1))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X0,X2) | ~r2_hidden(X2,X1)) & (sP0(X0,X2) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X0,X3)) & (sP0(X0,X3) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 0.22/0.52    inference(rectify,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X0,X2) | ~r2_hidden(X2,X1)) & (sP0(X0,X2) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~sP0(X0,X2)) & (sP0(X0,X2) | ~r2_hidden(X2,X1))) | ~sP1(X0,X1)))),
% 0.22/0.52    inference(nnf_transformation,[],[f11])).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    ( ! [X1] : (~sP0(k1_xboole_0,X1)) )),
% 0.22/0.52    inference(resolution,[],[f123,f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | ~sP0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (~r2_hidden(X2,X0) | ~r2_hidden(X1,X2))) & ((r2_hidden(sK7(X0,X1),X0) & r2_hidden(X1,sK7(X0,X1))) | ~sP0(X0,X1)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f24,f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X1,X3)) => (r2_hidden(sK7(X0,X1),X0) & r2_hidden(X1,sK7(X0,X1))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (~r2_hidden(X2,X0) | ~r2_hidden(X1,X2))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X1,X3)) | ~sP0(X0,X1)))),
% 0.22/0.52    inference(rectify,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X2] : ((sP0(X0,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~sP0(X0,X2)))),
% 0.22/0.52    inference(nnf_transformation,[],[f10])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (23967)------------------------------
% 0.22/0.52  % (23967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (23967)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (23967)Memory used [KB]: 6268
% 0.22/0.52  % (23967)Time elapsed: 0.099 s
% 0.22/0.52  % (23967)------------------------------
% 0.22/0.52  % (23967)------------------------------
% 0.22/0.52  % (23939)Success in time 0.158 s
%------------------------------------------------------------------------------
