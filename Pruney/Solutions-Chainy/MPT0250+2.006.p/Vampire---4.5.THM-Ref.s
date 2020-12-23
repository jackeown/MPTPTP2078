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
% DateTime   : Thu Dec  3 12:38:20 EST 2020

% Result     : Theorem 3.19s
% Output     : Refutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 313 expanded)
%              Number of leaves         :   26 (  96 expanded)
%              Depth                    :   25
%              Number of atoms          :  390 ( 840 expanded)
%              Number of equality atoms :   70 ( 246 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2899,plain,(
    $false ),
    inference(resolution,[],[f2848,f117])).

fof(f117,plain,(
    ! [X2,X3,X1] : sP3(X3,X1,X2,X3) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | X0 != X3 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP3(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP3(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP3(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP3(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X1,X0] :
      ( sP3(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f2848,plain,(
    ! [X10,X8,X9] : ~ sP3(sK5,X8,X9,X10) ),
    inference(resolution,[],[f2838,f287])).

fof(f287,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k4_enumset1(X3,X3,X3,X3,X2,X1))
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(resolution,[],[f91,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] : sP4(X0,X1,X2,k4_enumset1(X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X0,X1,X2,X3)
      | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f98,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f70,f101])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f89,f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f89,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP4(X0,X1,X2,X3) )
      & ( sP4(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP4(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f25,f32,f31])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( sP4(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP3(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f91,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP4(X0,X1,X2,X3)
      | ~ sP3(X5,X2,X1,X0)
      | r2_hidden(X5,X3) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP4(X0,X1,X2,X3)
        | ( ( ~ sP3(sK9(X0,X1,X2,X3),X2,X1,X0)
            | ~ r2_hidden(sK9(X0,X1,X2,X3),X3) )
          & ( sP3(sK9(X0,X1,X2,X3),X2,X1,X0)
            | r2_hidden(sK9(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP3(X5,X2,X1,X0) )
            & ( sP3(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP4(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f50,f51])).

fof(f51,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP3(X4,X2,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP3(X4,X2,X1,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP3(sK9(X0,X1,X2,X3),X2,X1,X0)
          | ~ r2_hidden(sK9(X0,X1,X2,X3),X3) )
        & ( sP3(sK9(X0,X1,X2,X3),X2,X1,X0)
          | r2_hidden(sK9(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP4(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP3(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP3(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP3(X5,X2,X1,X0) )
            & ( sP3(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP4(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP4(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP3(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP3(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP3(X4,X2,X1,X0) )
            & ( sP3(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP4(X0,X1,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f2838,plain,(
    ! [X1] : ~ r2_hidden(sK5,X1) ),
    inference(subsumption_resolution,[],[f2837,f58])).

fof(f58,plain,(
    ~ r2_hidden(sK5,sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ r2_hidden(sK5,sK6)
    & r1_tarski(k2_xboole_0(k1_tarski(sK5),sK6),sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f20,f34])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK5,sK6)
      & r1_tarski(k2_xboole_0(k1_tarski(sK5),sK6),sK6) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f2837,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK5,X1)
      | r2_hidden(sK5,sK6) ) ),
    inference(duplicate_literal_removal,[],[f2825])).

fof(f2825,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK5,X1)
      | r2_hidden(sK5,sK6)
      | ~ r2_hidden(sK5,X1) ) ),
    inference(resolution,[],[f2818,f209])).

fof(f209,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f207,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | r2_hidden(X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( r2_hidden(X1,X2)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) ) ) )
      & ( ( ( ~ r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) )
          & ( r2_hidden(X1,X0)
            | r2_hidden(X1,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f207,plain,(
    ! [X14,X15,X16] :
      ( ~ sP2(k3_xboole_0(X15,X14),X16,X14)
      | ~ r2_hidden(X16,X15) ) ),
    inference(superposition,[],[f194,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f194,plain,(
    ! [X6,X8,X7] :
      ( ~ sP2(k3_xboole_0(X8,X7),X6,X8)
      | ~ r2_hidden(X6,X7) ) ),
    inference(resolution,[],[f145,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ sP2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ~ sP2(X2,X0,X1) )
      & ( sP2(X2,X0,X1)
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> sP2(X2,X0,X1) ) ),
    inference(definition_folding,[],[f24,f29])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f68,f107])).

fof(f107,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f60,f65])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f21,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f2818,plain,(
    ! [X0] :
      ( r2_hidden(sK5,k3_xboole_0(X0,sK6))
      | ~ r2_hidden(sK5,X0) ) ),
    inference(resolution,[],[f2801,f115])).

fof(f115,plain,(
    ! [X2,X3,X1] : sP3(X1,X1,X2,X3) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f2801,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,sK5,sK5,sK5)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k3_xboole_0(X1,sK6)) ) ),
    inference(resolution,[],[f2512,f287])).

fof(f2512,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK5))
      | r2_hidden(X0,k3_xboole_0(X1,sK6))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f2438,f118])).

fof(f2438,plain,(
    ! [X4,X5,X3] :
      ( ~ sP4(sK5,sK5,sK5,X3)
      | ~ r2_hidden(X4,X3)
      | r2_hidden(X4,k3_xboole_0(X5,sK6))
      | ~ r2_hidden(X4,X5) ) ),
    inference(resolution,[],[f2416,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2416,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(k3_xboole_0(X2,sK6),X0,X2)
      | ~ sP4(sK5,sK5,sK5,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f2358,f88])).

fof(f2358,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,sK6)))
      | ~ r2_hidden(X1,X0)
      | ~ sP4(sK5,sK5,sK5,X0) ) ),
    inference(resolution,[],[f2343,f68])).

fof(f2343,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,sK6)),X0)
      | ~ sP4(sK5,sK5,sK5,X0) ) ),
    inference(resolution,[],[f2175,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f72,f104])).

fof(f104,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f64,f103])).

fof(f103,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f63,f102])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f64,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f2175,plain,(
    ! [X15,X16] :
      ( r1_xboole_0(k5_xboole_0(X15,k3_xboole_0(X15,sK6)),k3_tarski(k4_enumset1(X16,X16,X16,X16,X16,sK6)))
      | ~ sP4(sK5,sK5,sK5,X16) ) ),
    inference(duplicate_literal_removal,[],[f2155])).

fof(f2155,plain,(
    ! [X15,X16] :
      ( r1_xboole_0(k5_xboole_0(X15,k3_xboole_0(X15,sK6)),k3_tarski(k4_enumset1(X16,X16,X16,X16,X16,sK6)))
      | ~ sP4(sK5,sK5,sK5,X16)
      | r1_xboole_0(k5_xboole_0(X15,k3_xboole_0(X15,sK6)),k3_tarski(k4_enumset1(X16,X16,X16,X16,X16,sK6))) ) ),
    inference(resolution,[],[f192,f473])).

fof(f473,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK7(X3,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,sK6))),sK6)
      | ~ sP4(sK5,sK5,sK5,X2)
      | r1_xboole_0(X3,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,sK6))) ) ),
    inference(resolution,[],[f423,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f423,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,sK6)))
      | ~ sP4(sK5,sK5,sK5,X0)
      | r2_hidden(X1,sK6) ) ),
    inference(resolution,[],[f410,f283])).

fof(f283,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f217,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f217,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
      | ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f74,f132])).

fof(f132,plain,(
    ! [X6,X7] :
      ( sP1(X6,X7,X6)
      | ~ r1_tarski(X6,X7) ) ),
    inference(superposition,[],[f114,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f114,plain,(
    ! [X0,X1] : sP1(X0,X1,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f27,f26])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( sP0(X1,sK8(X0,X1,X2),X0)
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( sP0(X1,sK8(X0,X1,X2),X0)
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f410,plain,(
    ! [X2] :
      ( r1_tarski(k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,sK6)),sK6)
      | ~ sP4(sK5,sK5,sK5,X2) ) ),
    inference(superposition,[],[f396,f108])).

fof(f108,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f62,f103,f103])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f396,plain,(
    ! [X0] :
      ( r1_tarski(k3_tarski(k4_enumset1(sK6,sK6,sK6,sK6,sK6,X0)),sK6)
      | ~ sP4(sK5,sK5,sK5,X0) ) ),
    inference(superposition,[],[f393,f112])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_enumset1(X0,X0,X0,X0,X1,X2) = X3
      | ~ sP4(X0,X1,X2,X3) ) ),
    inference(definition_unfolding,[],[f99,f102])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | ~ sP4(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f393,plain,(
    r1_tarski(k3_tarski(k4_enumset1(sK6,sK6,sK6,sK6,sK6,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK5))),sK6) ),
    inference(forward_demodulation,[],[f106,f108])).

fof(f106,plain,(
    r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK5),k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK5),k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK5),k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK5),k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK5),sK6)),sK6) ),
    inference(definition_unfolding,[],[f57,f104,f105])).

fof(f105,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f103])).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f57,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK5),sK6),sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X1)
      | r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ) ),
    inference(resolution,[],[f145,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:58:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.52  % (20169)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (20175)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (20172)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (20185)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (20193)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (20171)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (20176)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (20183)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (20174)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (20195)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (20199)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (20179)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (20170)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (20184)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (20181)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (20181)Refutation not found, incomplete strategy% (20181)------------------------------
% 0.21/0.54  % (20181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (20181)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (20181)Memory used [KB]: 10618
% 0.21/0.54  % (20181)Time elapsed: 0.140 s
% 0.21/0.54  % (20181)------------------------------
% 0.21/0.54  % (20181)------------------------------
% 0.21/0.55  % (20192)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (20182)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (20191)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (20189)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (20178)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (20198)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (20180)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (20180)Refutation not found, incomplete strategy% (20180)------------------------------
% 0.21/0.55  % (20180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (20180)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (20180)Memory used [KB]: 10618
% 0.21/0.55  % (20180)Time elapsed: 0.147 s
% 0.21/0.55  % (20180)------------------------------
% 0.21/0.55  % (20180)------------------------------
% 0.21/0.55  % (20196)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (20177)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (20190)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (20197)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (20194)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (20186)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (20188)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (20200)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 2.07/0.65  % (20271)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.07/0.69  % (20272)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.19/0.80  % (20198)Refutation found. Thanks to Tanya!
% 3.19/0.80  % SZS status Theorem for theBenchmark
% 3.19/0.80  % SZS output start Proof for theBenchmark
% 3.19/0.80  fof(f2899,plain,(
% 3.19/0.80    $false),
% 3.19/0.80    inference(resolution,[],[f2848,f117])).
% 3.19/0.80  fof(f117,plain,(
% 3.19/0.80    ( ! [X2,X3,X1] : (sP3(X3,X1,X2,X3)) )),
% 3.19/0.80    inference(equality_resolution,[],[f95])).
% 3.19/0.80  fof(f95,plain,(
% 3.19/0.80    ( ! [X2,X0,X3,X1] : (sP3(X0,X1,X2,X3) | X0 != X3) )),
% 3.19/0.80    inference(cnf_transformation,[],[f55])).
% 3.19/0.80  fof(f55,plain,(
% 3.19/0.80    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP3(X0,X1,X2,X3)))),
% 3.19/0.80    inference(rectify,[],[f54])).
% 3.19/0.80  fof(f54,plain,(
% 3.19/0.80    ! [X4,X2,X1,X0] : ((sP3(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP3(X4,X2,X1,X0)))),
% 3.19/0.80    inference(flattening,[],[f53])).
% 3.19/0.80  fof(f53,plain,(
% 3.19/0.80    ! [X4,X2,X1,X0] : ((sP3(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP3(X4,X2,X1,X0)))),
% 3.19/0.80    inference(nnf_transformation,[],[f31])).
% 3.19/0.80  fof(f31,plain,(
% 3.19/0.80    ! [X4,X2,X1,X0] : (sP3(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 3.19/0.80    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 3.19/0.80  fof(f2848,plain,(
% 3.19/0.80    ( ! [X10,X8,X9] : (~sP3(sK5,X8,X9,X10)) )),
% 3.19/0.80    inference(resolution,[],[f2838,f287])).
% 3.19/0.80  fof(f287,plain,(
% 3.19/0.80    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k4_enumset1(X3,X3,X3,X3,X2,X1)) | ~sP3(X0,X1,X2,X3)) )),
% 3.19/0.80    inference(resolution,[],[f91,f118])).
% 3.19/0.80  fof(f118,plain,(
% 3.19/0.80    ( ! [X2,X0,X1] : (sP4(X0,X1,X2,k4_enumset1(X0,X0,X0,X0,X1,X2))) )),
% 3.19/0.80    inference(equality_resolution,[],[f113])).
% 3.19/0.80  fof(f113,plain,(
% 3.19/0.80    ( ! [X2,X0,X3,X1] : (sP4(X0,X1,X2,X3) | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3) )),
% 3.19/0.80    inference(definition_unfolding,[],[f98,f102])).
% 3.19/0.80  fof(f102,plain,(
% 3.19/0.80    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 3.19/0.80    inference(definition_unfolding,[],[f70,f101])).
% 3.19/0.80  fof(f101,plain,(
% 3.19/0.80    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 3.19/0.80    inference(definition_unfolding,[],[f89,f100])).
% 3.19/0.80  fof(f100,plain,(
% 3.19/0.80    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.19/0.80    inference(cnf_transformation,[],[f15])).
% 3.19/0.80  fof(f15,axiom,(
% 3.19/0.80    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.19/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 3.19/0.80  fof(f89,plain,(
% 3.19/0.80    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.19/0.80    inference(cnf_transformation,[],[f14])).
% 3.19/0.80  fof(f14,axiom,(
% 3.19/0.80    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.19/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 3.19/0.80  fof(f70,plain,(
% 3.19/0.80    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.19/0.80    inference(cnf_transformation,[],[f13])).
% 3.19/0.80  fof(f13,axiom,(
% 3.19/0.80    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.19/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 3.19/0.80  fof(f98,plain,(
% 3.19/0.80    ( ! [X2,X0,X3,X1] : (sP4(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.19/0.80    inference(cnf_transformation,[],[f56])).
% 3.19/0.80  fof(f56,plain,(
% 3.19/0.80    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP4(X0,X1,X2,X3)) & (sP4(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 3.19/0.80    inference(nnf_transformation,[],[f33])).
% 3.19/0.80  fof(f33,plain,(
% 3.19/0.80    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP4(X0,X1,X2,X3))),
% 3.19/0.80    inference(definition_folding,[],[f25,f32,f31])).
% 3.19/0.80  fof(f32,plain,(
% 3.19/0.80    ! [X0,X1,X2,X3] : (sP4(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP3(X4,X2,X1,X0)))),
% 3.19/0.80    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 3.19/0.80  fof(f25,plain,(
% 3.19/0.80    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.19/0.80    inference(ennf_transformation,[],[f10])).
% 3.19/0.80  fof(f10,axiom,(
% 3.19/0.80    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.19/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 3.19/0.80  fof(f91,plain,(
% 3.19/0.80    ( ! [X2,X0,X5,X3,X1] : (~sP4(X0,X1,X2,X3) | ~sP3(X5,X2,X1,X0) | r2_hidden(X5,X3)) )),
% 3.19/0.80    inference(cnf_transformation,[],[f52])).
% 3.19/0.80  fof(f52,plain,(
% 3.19/0.80    ! [X0,X1,X2,X3] : ((sP4(X0,X1,X2,X3) | ((~sP3(sK9(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK9(X0,X1,X2,X3),X3)) & (sP3(sK9(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK9(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP3(X5,X2,X1,X0)) & (sP3(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP4(X0,X1,X2,X3)))),
% 3.19/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f50,f51])).
% 3.19/0.80  fof(f51,plain,(
% 3.19/0.80    ! [X3,X2,X1,X0] : (? [X4] : ((~sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP3(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP3(sK9(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK9(X0,X1,X2,X3),X3)) & (sP3(sK9(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK9(X0,X1,X2,X3),X3))))),
% 3.19/0.80    introduced(choice_axiom,[])).
% 3.19/0.80  fof(f50,plain,(
% 3.19/0.80    ! [X0,X1,X2,X3] : ((sP4(X0,X1,X2,X3) | ? [X4] : ((~sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP3(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP3(X5,X2,X1,X0)) & (sP3(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP4(X0,X1,X2,X3)))),
% 3.19/0.80    inference(rectify,[],[f49])).
% 3.19/0.80  fof(f49,plain,(
% 3.19/0.80    ! [X0,X1,X2,X3] : ((sP4(X0,X1,X2,X3) | ? [X4] : ((~sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP3(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP3(X4,X2,X1,X0)) & (sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP4(X0,X1,X2,X3)))),
% 3.19/0.80    inference(nnf_transformation,[],[f32])).
% 3.19/0.80  fof(f2838,plain,(
% 3.19/0.80    ( ! [X1] : (~r2_hidden(sK5,X1)) )),
% 3.19/0.80    inference(subsumption_resolution,[],[f2837,f58])).
% 3.19/0.80  fof(f58,plain,(
% 3.19/0.80    ~r2_hidden(sK5,sK6)),
% 3.19/0.80    inference(cnf_transformation,[],[f35])).
% 3.19/0.80  fof(f35,plain,(
% 3.19/0.80    ~r2_hidden(sK5,sK6) & r1_tarski(k2_xboole_0(k1_tarski(sK5),sK6),sK6)),
% 3.19/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f20,f34])).
% 3.19/0.80  fof(f34,plain,(
% 3.19/0.80    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK5,sK6) & r1_tarski(k2_xboole_0(k1_tarski(sK5),sK6),sK6))),
% 3.19/0.80    introduced(choice_axiom,[])).
% 3.19/0.80  fof(f20,plain,(
% 3.19/0.80    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 3.19/0.80    inference(ennf_transformation,[],[f18])).
% 3.19/0.80  fof(f18,negated_conjecture,(
% 3.19/0.80    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 3.19/0.80    inference(negated_conjecture,[],[f17])).
% 3.19/0.80  fof(f17,conjecture,(
% 3.19/0.80    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 3.19/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).
% 3.19/0.80  fof(f2837,plain,(
% 3.19/0.80    ( ! [X1] : (~r2_hidden(sK5,X1) | r2_hidden(sK5,sK6)) )),
% 3.19/0.80    inference(duplicate_literal_removal,[],[f2825])).
% 3.19/0.80  fof(f2825,plain,(
% 3.19/0.80    ( ! [X1] : (~r2_hidden(sK5,X1) | r2_hidden(sK5,sK6) | ~r2_hidden(sK5,X1)) )),
% 3.19/0.80    inference(resolution,[],[f2818,f209])).
% 3.19/0.80  fof(f209,plain,(
% 3.19/0.80    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 3.19/0.80    inference(resolution,[],[f207,f86])).
% 3.19/0.80  fof(f86,plain,(
% 3.19/0.80    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) )),
% 3.19/0.80    inference(cnf_transformation,[],[f47])).
% 3.19/0.80  fof(f47,plain,(
% 3.19/0.80    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~r2_hidden(X1,X2)))) & (((~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & (r2_hidden(X1,X0) | r2_hidden(X1,X2))) | ~sP2(X0,X1,X2)))),
% 3.19/0.80    inference(rectify,[],[f46])).
% 3.19/0.80  fof(f46,plain,(
% 3.19/0.80    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~sP2(X2,X0,X1)))),
% 3.19/0.80    inference(nnf_transformation,[],[f29])).
% 3.19/0.80  fof(f29,plain,(
% 3.19/0.80    ! [X2,X0,X1] : (sP2(X2,X0,X1) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 3.19/0.80    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 3.19/0.80  fof(f207,plain,(
% 3.19/0.80    ( ! [X14,X15,X16] : (~sP2(k3_xboole_0(X15,X14),X16,X14) | ~r2_hidden(X16,X15)) )),
% 3.19/0.80    inference(superposition,[],[f194,f61])).
% 3.19/0.80  fof(f61,plain,(
% 3.19/0.80    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.19/0.80    inference(cnf_transformation,[],[f1])).
% 3.19/0.80  fof(f1,axiom,(
% 3.19/0.80    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.19/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.19/0.80  fof(f194,plain,(
% 3.19/0.80    ( ! [X6,X8,X7] : (~sP2(k3_xboole_0(X8,X7),X6,X8) | ~r2_hidden(X6,X7)) )),
% 3.19/0.80    inference(resolution,[],[f145,f88])).
% 3.19/0.80  fof(f88,plain,(
% 3.19/0.80    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP2(X2,X0,X1)) )),
% 3.19/0.80    inference(cnf_transformation,[],[f48])).
% 3.19/0.80  fof(f48,plain,(
% 3.19/0.80    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP2(X2,X0,X1)) & (sP2(X2,X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 3.19/0.80    inference(nnf_transformation,[],[f30])).
% 3.19/0.80  fof(f30,plain,(
% 3.19/0.80    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> sP2(X2,X0,X1))),
% 3.19/0.80    inference(definition_folding,[],[f24,f29])).
% 3.19/0.80  fof(f24,plain,(
% 3.19/0.80    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 3.19/0.80    inference(ennf_transformation,[],[f3])).
% 3.19/0.80  fof(f3,axiom,(
% 3.19/0.80    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 3.19/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 3.19/0.80  fof(f145,plain,(
% 3.19/0.80    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) | ~r2_hidden(X0,X1)) )),
% 3.19/0.80    inference(resolution,[],[f68,f107])).
% 3.19/0.80  fof(f107,plain,(
% 3.19/0.80    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 3.19/0.80    inference(definition_unfolding,[],[f60,f65])).
% 3.19/0.80  fof(f65,plain,(
% 3.19/0.80    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.19/0.80    inference(cnf_transformation,[],[f5])).
% 3.19/0.80  fof(f5,axiom,(
% 3.19/0.80    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.19/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.19/0.80  fof(f60,plain,(
% 3.19/0.80    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.19/0.80    inference(cnf_transformation,[],[f8])).
% 3.19/0.80  fof(f8,axiom,(
% 3.19/0.80    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.19/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 3.19/0.80  fof(f68,plain,(
% 3.19/0.80    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.19/0.80    inference(cnf_transformation,[],[f37])).
% 3.19/0.80  fof(f37,plain,(
% 3.19/0.80    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.19/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f21,f36])).
% 3.19/0.80  fof(f36,plain,(
% 3.19/0.80    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 3.19/0.80    introduced(choice_axiom,[])).
% 3.19/0.80  fof(f21,plain,(
% 3.19/0.80    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.19/0.80    inference(ennf_transformation,[],[f19])).
% 3.19/0.80  fof(f19,plain,(
% 3.19/0.80    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.19/0.80    inference(rectify,[],[f4])).
% 3.19/0.80  fof(f4,axiom,(
% 3.19/0.80    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.19/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 3.19/0.80  fof(f2818,plain,(
% 3.19/0.80    ( ! [X0] : (r2_hidden(sK5,k3_xboole_0(X0,sK6)) | ~r2_hidden(sK5,X0)) )),
% 3.19/0.80    inference(resolution,[],[f2801,f115])).
% 3.19/0.80  fof(f115,plain,(
% 3.19/0.80    ( ! [X2,X3,X1] : (sP3(X1,X1,X2,X3)) )),
% 3.19/0.80    inference(equality_resolution,[],[f97])).
% 3.19/0.80  fof(f97,plain,(
% 3.19/0.80    ( ! [X2,X0,X3,X1] : (sP3(X0,X1,X2,X3) | X0 != X1) )),
% 3.19/0.80    inference(cnf_transformation,[],[f55])).
% 3.19/0.80  fof(f2801,plain,(
% 3.19/0.80    ( ! [X0,X1] : (~sP3(X0,sK5,sK5,sK5) | ~r2_hidden(X0,X1) | r2_hidden(X0,k3_xboole_0(X1,sK6))) )),
% 3.19/0.80    inference(resolution,[],[f2512,f287])).
% 3.19/0.80  fof(f2512,plain,(
% 3.19/0.80    ( ! [X0,X1] : (~r2_hidden(X0,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK5)) | r2_hidden(X0,k3_xboole_0(X1,sK6)) | ~r2_hidden(X0,X1)) )),
% 3.19/0.80    inference(resolution,[],[f2438,f118])).
% 3.19/0.80  fof(f2438,plain,(
% 3.19/0.80    ( ! [X4,X5,X3] : (~sP4(sK5,sK5,sK5,X3) | ~r2_hidden(X4,X3) | r2_hidden(X4,k3_xboole_0(X5,sK6)) | ~r2_hidden(X4,X5)) )),
% 3.19/0.80    inference(resolution,[],[f2416,f85])).
% 3.19/0.80  fof(f85,plain,(
% 3.19/0.80    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 3.19/0.80    inference(cnf_transformation,[],[f47])).
% 3.19/0.80  fof(f2416,plain,(
% 3.19/0.80    ( ! [X2,X0,X1] : (~sP2(k3_xboole_0(X2,sK6),X0,X2) | ~sP4(sK5,sK5,sK5,X1) | ~r2_hidden(X0,X1)) )),
% 3.19/0.80    inference(resolution,[],[f2358,f88])).
% 3.19/0.80  fof(f2358,plain,(
% 3.19/0.80    ( ! [X2,X0,X1] : (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,sK6))) | ~r2_hidden(X1,X0) | ~sP4(sK5,sK5,sK5,X0)) )),
% 3.19/0.80    inference(resolution,[],[f2343,f68])).
% 3.19/0.80  fof(f2343,plain,(
% 3.19/0.80    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,sK6)),X0) | ~sP4(sK5,sK5,sK5,X0)) )),
% 3.19/0.80    inference(resolution,[],[f2175,f110])).
% 3.19/0.80  fof(f110,plain,(
% 3.19/0.80    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))) | r1_xboole_0(X0,X1)) )),
% 3.19/0.80    inference(definition_unfolding,[],[f72,f104])).
% 3.19/0.80  fof(f104,plain,(
% 3.19/0.80    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 3.19/0.80    inference(definition_unfolding,[],[f64,f103])).
% 3.19/0.80  fof(f103,plain,(
% 3.19/0.80    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 3.19/0.80    inference(definition_unfolding,[],[f63,f102])).
% 3.19/0.80  fof(f63,plain,(
% 3.19/0.80    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.19/0.80    inference(cnf_transformation,[],[f12])).
% 3.19/0.80  fof(f12,axiom,(
% 3.19/0.80    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.19/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.19/0.80  fof(f64,plain,(
% 3.19/0.80    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 3.19/0.80    inference(cnf_transformation,[],[f16])).
% 3.19/0.80  fof(f16,axiom,(
% 3.19/0.80    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 3.19/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.19/0.80  fof(f72,plain,(
% 3.19/0.80    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 3.19/0.80    inference(cnf_transformation,[],[f23])).
% 3.19/0.81  fof(f23,plain,(
% 3.19/0.81    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.19/0.81    inference(ennf_transformation,[],[f7])).
% 3.19/0.81  fof(f7,axiom,(
% 3.19/0.81    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.19/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 3.19/0.81  fof(f2175,plain,(
% 3.19/0.81    ( ! [X15,X16] : (r1_xboole_0(k5_xboole_0(X15,k3_xboole_0(X15,sK6)),k3_tarski(k4_enumset1(X16,X16,X16,X16,X16,sK6))) | ~sP4(sK5,sK5,sK5,X16)) )),
% 3.19/0.81    inference(duplicate_literal_removal,[],[f2155])).
% 3.19/0.81  fof(f2155,plain,(
% 3.19/0.81    ( ! [X15,X16] : (r1_xboole_0(k5_xboole_0(X15,k3_xboole_0(X15,sK6)),k3_tarski(k4_enumset1(X16,X16,X16,X16,X16,sK6))) | ~sP4(sK5,sK5,sK5,X16) | r1_xboole_0(k5_xboole_0(X15,k3_xboole_0(X15,sK6)),k3_tarski(k4_enumset1(X16,X16,X16,X16,X16,sK6)))) )),
% 3.19/0.81    inference(resolution,[],[f192,f473])).
% 3.19/0.81  fof(f473,plain,(
% 3.19/0.81    ( ! [X2,X3] : (r2_hidden(sK7(X3,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,sK6))),sK6) | ~sP4(sK5,sK5,sK5,X2) | r1_xboole_0(X3,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,sK6)))) )),
% 3.19/0.81    inference(resolution,[],[f423,f67])).
% 3.19/0.81  fof(f67,plain,(
% 3.19/0.81    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.19/0.81    inference(cnf_transformation,[],[f37])).
% 3.19/0.81  fof(f423,plain,(
% 3.19/0.81    ( ! [X0,X1] : (~r2_hidden(X1,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,sK6))) | ~sP4(sK5,sK5,sK5,X0) | r2_hidden(X1,sK6)) )),
% 3.19/0.81    inference(resolution,[],[f410,f283])).
% 3.19/0.81  fof(f283,plain,(
% 3.19/0.81    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 3.19/0.81    inference(resolution,[],[f217,f79])).
% 3.19/0.81  fof(f79,plain,(
% 3.19/0.81    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X0)) )),
% 3.19/0.81    inference(cnf_transformation,[],[f44])).
% 3.19/0.81  fof(f44,plain,(
% 3.19/0.81    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 3.19/0.81    inference(rectify,[],[f43])).
% 3.19/0.81  fof(f43,plain,(
% 3.19/0.81    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 3.19/0.81    inference(flattening,[],[f42])).
% 3.19/0.81  fof(f42,plain,(
% 3.19/0.81    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 3.19/0.81    inference(nnf_transformation,[],[f26])).
% 3.19/0.81  fof(f26,plain,(
% 3.19/0.81    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 3.19/0.81    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.19/0.81  fof(f217,plain,(
% 3.19/0.81    ( ! [X2,X0,X1] : (sP0(X2,X0,X1) | ~r2_hidden(X0,X1) | ~r1_tarski(X1,X2)) )),
% 3.19/0.81    inference(resolution,[],[f74,f132])).
% 3.19/0.81  fof(f132,plain,(
% 3.19/0.81    ( ! [X6,X7] : (sP1(X6,X7,X6) | ~r1_tarski(X6,X7)) )),
% 3.19/0.81    inference(superposition,[],[f114,f69])).
% 3.19/0.81  fof(f69,plain,(
% 3.19/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.19/0.81    inference(cnf_transformation,[],[f22])).
% 3.19/0.81  fof(f22,plain,(
% 3.19/0.81    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.19/0.81    inference(ennf_transformation,[],[f6])).
% 3.19/0.81  fof(f6,axiom,(
% 3.19/0.81    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.19/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.19/0.81  fof(f114,plain,(
% 3.19/0.81    ( ! [X0,X1] : (sP1(X0,X1,k3_xboole_0(X0,X1))) )),
% 3.19/0.81    inference(equality_resolution,[],[f81])).
% 3.19/0.81  fof(f81,plain,(
% 3.19/0.81    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.19/0.81    inference(cnf_transformation,[],[f45])).
% 3.19/0.81  fof(f45,plain,(
% 3.19/0.81    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k3_xboole_0(X0,X1) != X2))),
% 3.19/0.81    inference(nnf_transformation,[],[f28])).
% 3.19/0.81  fof(f28,plain,(
% 3.19/0.81    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 3.19/0.81    inference(definition_folding,[],[f2,f27,f26])).
% 3.19/0.81  fof(f27,plain,(
% 3.19/0.81    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 3.19/0.81    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.19/0.81  fof(f2,axiom,(
% 3.19/0.81    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.19/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 3.19/0.81  fof(f74,plain,(
% 3.19/0.81    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X1,X4,X0)) )),
% 3.19/0.81    inference(cnf_transformation,[],[f41])).
% 3.19/0.81  fof(f41,plain,(
% 3.19/0.81    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sP0(X1,sK8(X0,X1,X2),X0) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 3.19/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f39,f40])).
% 3.19/0.81  fof(f40,plain,(
% 3.19/0.81    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sP0(X1,sK8(X0,X1,X2),X0) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 3.19/0.81    introduced(choice_axiom,[])).
% 3.19/0.81  fof(f39,plain,(
% 3.19/0.81    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 3.19/0.81    inference(rectify,[],[f38])).
% 3.19/0.81  fof(f38,plain,(
% 3.19/0.81    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 3.19/0.81    inference(nnf_transformation,[],[f27])).
% 3.19/0.81  fof(f410,plain,(
% 3.19/0.81    ( ! [X2] : (r1_tarski(k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,sK6)),sK6) | ~sP4(sK5,sK5,sK5,X2)) )),
% 3.19/0.81    inference(superposition,[],[f396,f108])).
% 3.19/0.81  fof(f108,plain,(
% 3.19/0.81    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0)) )),
% 3.19/0.81    inference(definition_unfolding,[],[f62,f103,f103])).
% 3.19/0.81  fof(f62,plain,(
% 3.19/0.81    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.19/0.81    inference(cnf_transformation,[],[f9])).
% 3.19/0.81  fof(f9,axiom,(
% 3.19/0.81    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.19/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.19/0.81  fof(f396,plain,(
% 3.19/0.81    ( ! [X0] : (r1_tarski(k3_tarski(k4_enumset1(sK6,sK6,sK6,sK6,sK6,X0)),sK6) | ~sP4(sK5,sK5,sK5,X0)) )),
% 3.19/0.81    inference(superposition,[],[f393,f112])).
% 3.19/0.81  fof(f112,plain,(
% 3.19/0.81    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = X3 | ~sP4(X0,X1,X2,X3)) )),
% 3.19/0.81    inference(definition_unfolding,[],[f99,f102])).
% 3.19/0.81  fof(f99,plain,(
% 3.19/0.81    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | ~sP4(X0,X1,X2,X3)) )),
% 3.19/0.81    inference(cnf_transformation,[],[f56])).
% 3.19/0.81  fof(f393,plain,(
% 3.19/0.81    r1_tarski(k3_tarski(k4_enumset1(sK6,sK6,sK6,sK6,sK6,k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK5))),sK6)),
% 3.19/0.81    inference(forward_demodulation,[],[f106,f108])).
% 3.19/0.81  fof(f106,plain,(
% 3.19/0.81    r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK5),k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK5),k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK5),k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK5),k4_enumset1(sK5,sK5,sK5,sK5,sK5,sK5),sK6)),sK6)),
% 3.19/0.81    inference(definition_unfolding,[],[f57,f104,f105])).
% 3.19/0.81  fof(f105,plain,(
% 3.19/0.81    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 3.19/0.81    inference(definition_unfolding,[],[f59,f103])).
% 3.19/0.81  fof(f59,plain,(
% 3.19/0.81    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.19/0.81    inference(cnf_transformation,[],[f11])).
% 3.19/0.81  fof(f11,axiom,(
% 3.19/0.81    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.19/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 3.19/0.81  fof(f57,plain,(
% 3.19/0.81    r1_tarski(k2_xboole_0(k1_tarski(sK5),sK6),sK6)),
% 3.19/0.81    inference(cnf_transformation,[],[f35])).
% 3.19/0.81  fof(f192,plain,(
% 3.19/0.81    ( ! [X2,X0,X1] : (~r2_hidden(sK7(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X1) | r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) )),
% 3.19/0.81    inference(resolution,[],[f145,f66])).
% 3.19/0.81  fof(f66,plain,(
% 3.19/0.81    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.19/0.81    inference(cnf_transformation,[],[f37])).
% 3.19/0.81  % SZS output end Proof for theBenchmark
% 3.19/0.81  % (20198)------------------------------
% 3.19/0.81  % (20198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.19/0.81  % (20198)Termination reason: Refutation
% 3.19/0.81  
% 3.19/0.81  % (20198)Memory used [KB]: 7547
% 3.19/0.81  % (20198)Time elapsed: 0.387 s
% 3.19/0.81  % (20198)------------------------------
% 3.19/0.81  % (20198)------------------------------
% 3.19/0.81  % (20166)Success in time 0.447 s
%------------------------------------------------------------------------------
