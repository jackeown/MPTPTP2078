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
% DateTime   : Thu Dec  3 12:37:01 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 204 expanded)
%              Number of leaves         :   16 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  316 ( 851 expanded)
%              Number of equality atoms :  127 ( 287 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f202,plain,(
    $false ),
    inference(subsumption_resolution,[],[f198,f170])).

fof(f170,plain,(
    ! [X4] : ~ r2_hidden(X4,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f168,f110])).

fof(f110,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f51,f97])).

fof(f97,plain,(
    ! [X0] : sP0(X0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f83,f96])).

fof(f96,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f91,f41])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f91,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f45,f39])).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f83,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f15])).

fof(f15,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
              & r2_hidden(sK5(X0,X1,X2),X1) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
            & r2_hidden(sK5(X0,X1,X2),X1) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f168,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | r2_hidden(X4,X5) ) ),
    inference(resolution,[],[f156,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f156,plain,(
    ! [X3] : sP0(X3,X3,k1_xboole_0) ),
    inference(resolution,[],[f148,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(resolution,[],[f87,f86])).

fof(f86,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ( sK6(X0,X1,X2,X3) != X0
              & sK6(X0,X1,X2,X3) != X1
              & sK6(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
          & ( sK6(X0,X1,X2,X3) = X0
            | sK6(X0,X1,X2,X3) = X1
            | sK6(X0,X1,X2,X3) = X2
            | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f33,f34])).

fof(f34,plain,(
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
     => ( ( ( sK6(X0,X1,X2,X3) != X0
            & sK6(X0,X1,X2,X3) != X1
            & sK6(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
        & ( sK6(X0,X1,X2,X3) = X0
          | sK6(X0,X1,X2,X3) = X1
          | sK6(X0,X1,X2,X3) = X2
          | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

% (13069)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
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
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP1(X2,X1,X0,X3)
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
        | ~ sP1(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP1(X2,X1,X0,X3)
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
        | ~ sP1(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X2,X1,X0,X3] :
      ( sP1(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f87,plain,(
    ! [X2,X0,X1] : sP1(X2,X1,X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f67,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP1(X2,X1,X0,X3) )
      & ( sP1(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP1(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f14,f17])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f148,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(sK5(X1,X1,k1_xboole_0),X2)
      | sP0(X1,X1,k1_xboole_0) ) ),
    inference(resolution,[],[f140,f110])).

fof(f140,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK5(X2,X2,X3),X3)
      | sP0(X2,X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X2,X3] :
      ( sP0(X2,X2,X3)
      | r2_hidden(sK5(X2,X2,X3),X3)
      | r2_hidden(sK5(X2,X2,X3),X3)
      | sP0(X2,X2,X3) ) ),
    inference(resolution,[],[f54,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X0)
      | sP0(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f198,plain,(
    r2_hidden(sK3,k1_xboole_0) ),
    inference(superposition,[],[f115,f179])).

fof(f179,plain,(
    k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK3) ),
    inference(subsumption_resolution,[],[f175,f72])).

fof(f72,plain,(
    k3_enumset1(sK2,sK2,sK2,sK2,sK3) != k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f38,f70,f71])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f70])).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f69])).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    k2_tarski(sK2,sK3) != k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k2_tarski(sK2,sK3) != k1_tarski(sK4)
    & r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X1) != k1_tarski(X2)
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( k2_tarski(sK2,sK3) != k1_tarski(sK4)
      & r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k1_tarski(X2)
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).

fof(f175,plain,
    ( k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK3)
    | k3_enumset1(sK2,sK2,sK2,sK2,sK3) = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
    inference(resolution,[],[f76,f73])).

fof(f73,plain,(
    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f37,f70,f71])).

fof(f37,plain,(
    r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f20])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f46,f71,f71])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f115,plain,(
    ! [X6,X8,X7] : r2_hidden(X6,k3_enumset1(X7,X7,X7,X8,X6)) ),
    inference(resolution,[],[f87,f84])).

fof(f84,plain,(
    ! [X2,X5,X3,X1] :
      ( ~ sP1(X5,X1,X2,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:21:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (13053)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (13061)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (13056)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.51/0.57  % (13055)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.51/0.57  % (13071)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.51/0.57  % (13054)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.51/0.58  % (13063)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.51/0.58  % (13050)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.51/0.58  % (13056)Refutation found. Thanks to Tanya!
% 1.51/0.58  % SZS status Theorem for theBenchmark
% 1.76/0.59  % SZS output start Proof for theBenchmark
% 1.76/0.59  fof(f202,plain,(
% 1.76/0.59    $false),
% 1.76/0.59    inference(subsumption_resolution,[],[f198,f170])).
% 1.76/0.59  fof(f170,plain,(
% 1.76/0.59    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0)) )),
% 1.76/0.59    inference(subsumption_resolution,[],[f168,f110])).
% 1.76/0.59  fof(f110,plain,(
% 1.76/0.59    ( ! [X4,X3] : (~r2_hidden(X3,k1_xboole_0) | ~r2_hidden(X3,X4)) )),
% 1.76/0.59    inference(resolution,[],[f51,f97])).
% 1.76/0.59  fof(f97,plain,(
% 1.76/0.59    ( ! [X0] : (sP0(X0,k1_xboole_0,k1_xboole_0)) )),
% 1.76/0.59    inference(superposition,[],[f83,f96])).
% 1.76/0.59  fof(f96,plain,(
% 1.76/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.76/0.59    inference(resolution,[],[f91,f41])).
% 1.76/0.59  fof(f41,plain,(
% 1.76/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f4])).
% 1.76/0.59  fof(f4,axiom,(
% 1.76/0.59    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.76/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.76/0.59  fof(f91,plain,(
% 1.76/0.59    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.76/0.59    inference(resolution,[],[f45,f39])).
% 1.76/0.59  fof(f39,plain,(
% 1.76/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f3])).
% 1.76/0.59  fof(f3,axiom,(
% 1.76/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.76/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.76/0.59  fof(f45,plain,(
% 1.76/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f22])).
% 1.76/0.59  fof(f22,plain,(
% 1.76/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.76/0.59    inference(flattening,[],[f21])).
% 1.76/0.59  fof(f21,plain,(
% 1.76/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.76/0.59    inference(nnf_transformation,[],[f2])).
% 1.76/0.59  fof(f2,axiom,(
% 1.76/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.76/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.76/0.59  fof(f83,plain,(
% 1.76/0.59    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 1.76/0.59    inference(equality_resolution,[],[f56])).
% 1.76/0.59  fof(f56,plain,(
% 1.76/0.59    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.76/0.59    inference(cnf_transformation,[],[f30])).
% 1.76/0.59  fof(f30,plain,(
% 1.76/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.76/0.59    inference(nnf_transformation,[],[f16])).
% 1.76/0.59  fof(f16,plain,(
% 1.76/0.59    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.76/0.59    inference(definition_folding,[],[f1,f15])).
% 1.76/0.59  fof(f15,plain,(
% 1.76/0.59    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.76/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.76/0.59  fof(f1,axiom,(
% 1.76/0.59    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.76/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.76/0.59  fof(f51,plain,(
% 1.76/0.59    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f29])).
% 1.76/0.59  fof(f29,plain,(
% 1.76/0.59    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.76/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).
% 1.76/0.59  fof(f28,plain,(
% 1.76/0.59    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.76/0.59    introduced(choice_axiom,[])).
% 1.76/0.59  fof(f27,plain,(
% 1.76/0.59    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.76/0.59    inference(rectify,[],[f26])).
% 1.76/0.59  fof(f26,plain,(
% 1.76/0.59    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.76/0.59    inference(flattening,[],[f25])).
% 1.76/0.59  fof(f25,plain,(
% 1.76/0.59    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.76/0.59    inference(nnf_transformation,[],[f15])).
% 1.76/0.59  fof(f168,plain,(
% 1.76/0.59    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | r2_hidden(X4,X5)) )),
% 1.76/0.59    inference(resolution,[],[f156,f50])).
% 1.76/0.59  fof(f50,plain,(
% 1.76/0.59    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X1)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f29])).
% 1.76/0.59  fof(f156,plain,(
% 1.76/0.59    ( ! [X3] : (sP0(X3,X3,k1_xboole_0)) )),
% 1.76/0.59    inference(resolution,[],[f148,f113])).
% 1.76/0.59  fof(f113,plain,(
% 1.76/0.59    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 1.76/0.59    inference(resolution,[],[f87,f86])).
% 1.76/0.59  fof(f86,plain,(
% 1.76/0.59    ( ! [X0,X5,X3,X1] : (~sP1(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 1.76/0.59    inference(equality_resolution,[],[f60])).
% 1.76/0.59  fof(f60,plain,(
% 1.76/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP1(X0,X1,X2,X3)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f35])).
% 1.76/0.59  fof(f35,plain,(
% 1.76/0.59    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | (((sK6(X0,X1,X2,X3) != X0 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X2) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X0 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X2 | r2_hidden(sK6(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 1.76/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f33,f34])).
% 1.76/0.59  fof(f34,plain,(
% 1.76/0.59    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK6(X0,X1,X2,X3) != X0 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X2) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X0 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X2 | r2_hidden(sK6(X0,X1,X2,X3),X3))))),
% 1.76/0.59    introduced(choice_axiom,[])).
% 1.76/0.59  % (13069)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.76/0.59  fof(f33,plain,(
% 1.76/0.59    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 1.76/0.59    inference(rectify,[],[f32])).
% 1.76/0.59  fof(f32,plain,(
% 1.76/0.59    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 1.76/0.59    inference(flattening,[],[f31])).
% 1.76/0.59  fof(f31,plain,(
% 1.76/0.59    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 1.76/0.59    inference(nnf_transformation,[],[f17])).
% 1.76/0.59  fof(f17,plain,(
% 1.76/0.59    ! [X2,X1,X0,X3] : (sP1(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.76/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.76/0.59  fof(f87,plain,(
% 1.76/0.59    ( ! [X2,X0,X1] : (sP1(X2,X1,X0,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 1.76/0.59    inference(equality_resolution,[],[f78])).
% 1.76/0.59  fof(f78,plain,(
% 1.76/0.59    ( ! [X2,X0,X3,X1] : (sP1(X2,X1,X0,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.76/0.59    inference(definition_unfolding,[],[f67,f69])).
% 1.76/0.59  fof(f69,plain,(
% 1.76/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.76/0.59    inference(definition_unfolding,[],[f49,f58])).
% 1.76/0.59  fof(f58,plain,(
% 1.76/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f9])).
% 1.76/0.59  fof(f9,axiom,(
% 1.76/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.76/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.76/0.59  fof(f49,plain,(
% 1.76/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f8])).
% 1.76/0.59  fof(f8,axiom,(
% 1.76/0.59    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.76/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.76/0.59  fof(f67,plain,(
% 1.76/0.59    ( ! [X2,X0,X3,X1] : (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.76/0.59    inference(cnf_transformation,[],[f36])).
% 1.76/0.59  fof(f36,plain,(
% 1.76/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP1(X2,X1,X0,X3)) & (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.76/0.59    inference(nnf_transformation,[],[f18])).
% 1.76/0.59  fof(f18,plain,(
% 1.76/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP1(X2,X1,X0,X3))),
% 1.76/0.59    inference(definition_folding,[],[f14,f17])).
% 1.76/0.59  fof(f14,plain,(
% 1.76/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.76/0.59    inference(ennf_transformation,[],[f5])).
% 1.76/0.59  fof(f5,axiom,(
% 1.76/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.76/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.76/0.59  fof(f148,plain,(
% 1.76/0.59    ( ! [X2,X1] : (~r2_hidden(sK5(X1,X1,k1_xboole_0),X2) | sP0(X1,X1,k1_xboole_0)) )),
% 1.76/0.59    inference(resolution,[],[f140,f110])).
% 1.76/0.59  fof(f140,plain,(
% 1.76/0.59    ( ! [X2,X3] : (r2_hidden(sK5(X2,X2,X3),X3) | sP0(X2,X2,X3)) )),
% 1.76/0.59    inference(duplicate_literal_removal,[],[f138])).
% 1.76/0.59  fof(f138,plain,(
% 1.76/0.59    ( ! [X2,X3] : (sP0(X2,X2,X3) | r2_hidden(sK5(X2,X2,X3),X3) | r2_hidden(sK5(X2,X2,X3),X3) | sP0(X2,X2,X3)) )),
% 1.76/0.59    inference(resolution,[],[f54,f53])).
% 1.76/0.59  fof(f53,plain,(
% 1.76/0.59    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f29])).
% 1.76/0.59  fof(f54,plain,(
% 1.76/0.59    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X0) | sP0(X0,X1,X2) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f29])).
% 1.76/0.59  fof(f198,plain,(
% 1.76/0.59    r2_hidden(sK3,k1_xboole_0)),
% 1.76/0.59    inference(superposition,[],[f115,f179])).
% 1.76/0.59  fof(f179,plain,(
% 1.76/0.59    k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK3)),
% 1.76/0.59    inference(subsumption_resolution,[],[f175,f72])).
% 1.76/0.59  fof(f72,plain,(
% 1.76/0.59    k3_enumset1(sK2,sK2,sK2,sK2,sK3) != k3_enumset1(sK4,sK4,sK4,sK4,sK4)),
% 1.76/0.59    inference(definition_unfolding,[],[f38,f70,f71])).
% 1.76/0.59  fof(f71,plain,(
% 1.76/0.59    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.76/0.59    inference(definition_unfolding,[],[f40,f70])).
% 1.76/0.59  fof(f40,plain,(
% 1.76/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f6])).
% 1.76/0.59  fof(f6,axiom,(
% 1.76/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.76/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.76/0.59  fof(f70,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.76/0.59    inference(definition_unfolding,[],[f42,f69])).
% 1.76/0.59  fof(f42,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f7])).
% 1.76/0.59  fof(f7,axiom,(
% 1.76/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.76/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.76/0.59  fof(f38,plain,(
% 1.76/0.59    k2_tarski(sK2,sK3) != k1_tarski(sK4)),
% 1.76/0.59    inference(cnf_transformation,[],[f20])).
% 1.76/0.59  fof(f20,plain,(
% 1.76/0.59    k2_tarski(sK2,sK3) != k1_tarski(sK4) & r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4))),
% 1.76/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f19])).
% 1.76/0.59  fof(f19,plain,(
% 1.76/0.59    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k1_tarski(X2) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) => (k2_tarski(sK2,sK3) != k1_tarski(sK4) & r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4)))),
% 1.76/0.59    introduced(choice_axiom,[])).
% 1.76/0.59  fof(f13,plain,(
% 1.76/0.59    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k1_tarski(X2) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 1.76/0.59    inference(ennf_transformation,[],[f12])).
% 1.76/0.59  fof(f12,negated_conjecture,(
% 1.76/0.59    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 1.76/0.59    inference(negated_conjecture,[],[f11])).
% 1.76/0.59  fof(f11,conjecture,(
% 1.76/0.59    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 1.76/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).
% 1.76/0.59  fof(f175,plain,(
% 1.76/0.59    k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK3) | k3_enumset1(sK2,sK2,sK2,sK2,sK3) = k3_enumset1(sK4,sK4,sK4,sK4,sK4)),
% 1.76/0.59    inference(resolution,[],[f76,f73])).
% 1.76/0.59  fof(f73,plain,(
% 1.76/0.59    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))),
% 1.76/0.59    inference(definition_unfolding,[],[f37,f70,f71])).
% 1.76/0.59  fof(f37,plain,(
% 1.76/0.59    r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4))),
% 1.76/0.59    inference(cnf_transformation,[],[f20])).
% 1.76/0.59  fof(f76,plain,(
% 1.76/0.59    ( ! [X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 1.76/0.59    inference(definition_unfolding,[],[f46,f71,f71])).
% 1.76/0.59  fof(f46,plain,(
% 1.76/0.59    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.76/0.59    inference(cnf_transformation,[],[f24])).
% 1.76/0.59  fof(f24,plain,(
% 1.76/0.59    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.76/0.59    inference(flattening,[],[f23])).
% 1.76/0.59  fof(f23,plain,(
% 1.76/0.59    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.76/0.59    inference(nnf_transformation,[],[f10])).
% 1.76/0.59  fof(f10,axiom,(
% 1.76/0.59    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.76/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.76/0.59  fof(f115,plain,(
% 1.76/0.59    ( ! [X6,X8,X7] : (r2_hidden(X6,k3_enumset1(X7,X7,X7,X8,X6))) )),
% 1.76/0.59    inference(resolution,[],[f87,f84])).
% 1.76/0.59  fof(f84,plain,(
% 1.76/0.59    ( ! [X2,X5,X3,X1] : (~sP1(X5,X1,X2,X3) | r2_hidden(X5,X3)) )),
% 1.76/0.59    inference(equality_resolution,[],[f62])).
% 1.76/0.59  fof(f62,plain,(
% 1.76/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | ~sP1(X0,X1,X2,X3)) )),
% 1.76/0.59    inference(cnf_transformation,[],[f35])).
% 1.76/0.59  % SZS output end Proof for theBenchmark
% 1.76/0.59  % (13056)------------------------------
% 1.76/0.59  % (13056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.59  % (13056)Termination reason: Refutation
% 1.76/0.59  
% 1.76/0.59  % (13056)Memory used [KB]: 10746
% 1.76/0.59  % (13056)Time elapsed: 0.152 s
% 1.76/0.59  % (13056)------------------------------
% 1.76/0.59  % (13056)------------------------------
% 1.76/0.60  % (13073)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.76/0.60  % (13052)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.76/0.60  % (13049)Success in time 0.236 s
%------------------------------------------------------------------------------
