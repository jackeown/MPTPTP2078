%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 175 expanded)
%              Number of leaves         :   19 (  55 expanded)
%              Depth                    :   19
%              Number of atoms          :  189 ( 396 expanded)
%              Number of equality atoms :   99 ( 230 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f394,plain,(
    $false ),
    inference(subsumption_resolution,[],[f393,f35])).

fof(f35,plain,(
    sK2 != sK4 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK2 != sK4
    & sK2 != sK3
    & r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK2 != sK4
      & sK2 != sK3
      & r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f393,plain,(
    sK2 = sK4 ),
    inference(subsumption_resolution,[],[f389,f34])).

fof(f34,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f24])).

fof(f389,plain,
    ( sK2 = sK3
    | sK2 = sK4 ),
    inference(resolution,[],[f387,f70])).

fof(f70,plain,(
    ! [X2,X3,X1] : sP0(X1,X1,X2,X3) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP0(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP0(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP0(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP0(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X4,X2,X1,X0] :
      ( sP0(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f387,plain,(
    ! [X1] :
      ( ~ sP0(X1,sK2,sK4,sK3)
      | sK3 = X1
      | sK4 = X1 ) ),
    inference(duplicate_literal_removal,[],[f385])).

fof(f385,plain,(
    ! [X1] :
      ( ~ sP0(X1,sK2,sK4,sK3)
      | sK3 = X1
      | sK3 = X1
      | sK4 = X1 ) ),
    inference(resolution,[],[f380,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | X0 = X2
      | X0 = X3
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f380,plain,(
    ! [X1] :
      ( sP0(X1,sK4,sK3,sK3)
      | ~ sP0(X1,sK2,sK4,sK3) ) ),
    inference(resolution,[],[f239,f75])).

% (10152)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f75,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X4,k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7))
      | sP0(X4,X7,X6,X5) ) ),
    inference(resolution,[],[f73,f45])).

fof(f45,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | ~ r2_hidden(X5,X3)
      | sP0(X5,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ~ sP0(sK5(X0,X1,X2,X3),X2,X1,X0)
            | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
          & ( sP0(sK5(X0,X1,X2,X3),X2,X1,X0)
            | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X5,X2,X1,X0) )
            & ( sP0(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).

% (10142)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f27,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP0(X4,X2,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP0(X4,X2,X1,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP0(sK5(X0,X1,X2,X3),X2,X1,X0)
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( sP0(sK5(X0,X1,X2,X3),X2,X1,X0)
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP0(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X5,X2,X1,X0) )
            & ( sP0(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP0(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP0(X4,X2,X1,X0) )
            & ( sP0(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( sP1(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP0(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f73,plain,(
    ! [X2,X0,X1] : sP1(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f53,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f44,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f55,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP1(X0,X1,X2,X3) )
      & ( sP1(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP1(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f19,f21,f20])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

% (10141)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f239,plain,(
    ! [X1] :
      ( r2_hidden(X1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
      | ~ sP0(X1,sK2,sK4,sK3) ) ),
    inference(superposition,[],[f74,f226])).

fof(f226,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4,sK2) ),
    inference(resolution,[],[f97,f67])).

fof(f67,plain,(
    r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f33,f65,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f63])).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f64])).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f24])).

fof(f97,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7))
      | k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0) ) ),
    inference(forward_demodulation,[],[f96,f37])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f96,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0) = k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_xboole_0)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)) ) ),
    inference(forward_demodulation,[],[f95,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f95,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0) = k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)) ) ),
    inference(superposition,[],[f66,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) ),
    inference(definition_unfolding,[],[f58,f59,f57,f65])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(resolution,[],[f73,f46])).

fof(f46,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | ~ sP0(X5,X2,X1,X0)
      | r2_hidden(X5,X3) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:13:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.48  % (10148)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.48  % (10148)Refutation not found, incomplete strategy% (10148)------------------------------
% 0.21/0.48  % (10148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (10166)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.49  % (10148)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (10148)Memory used [KB]: 10618
% 0.21/0.49  % (10148)Time elapsed: 0.072 s
% 0.21/0.49  % (10148)------------------------------
% 0.21/0.49  % (10148)------------------------------
% 0.21/0.52  % (10140)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (10161)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (10166)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f394,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f393,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    sK2 != sK4),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    sK2 != sK4 & sK2 != sK3 & r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK2 != sK4 & sK2 != sK3 & r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.21/0.52    inference(negated_conjecture,[],[f15])).
% 0.21/0.52  fof(f15,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 0.21/0.52  fof(f393,plain,(
% 0.21/0.52    sK2 = sK4),
% 0.21/0.52    inference(subsumption_resolution,[],[f389,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    sK2 != sK3),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f389,plain,(
% 0.21/0.52    sK2 = sK3 | sK2 = sK4),
% 0.21/0.52    inference(resolution,[],[f387,f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X2,X3,X1] : (sP0(X1,X1,X2,X3)) )),
% 0.21/0.52    inference(equality_resolution,[],[f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP0(X0,X1,X2,X3)))),
% 0.21/0.52    inference(rectify,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X4,X2,X1,X0] : ((sP0(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP0(X4,X2,X1,X0)))),
% 0.21/0.52    inference(flattening,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X4,X2,X1,X0] : ((sP0(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP0(X4,X2,X1,X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X4,X2,X1,X0] : (sP0(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.52  fof(f387,plain,(
% 0.21/0.52    ( ! [X1] : (~sP0(X1,sK2,sK4,sK3) | sK3 = X1 | sK4 = X1) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f385])).
% 0.21/0.52  fof(f385,plain,(
% 0.21/0.52    ( ! [X1] : (~sP0(X1,sK2,sK4,sK3) | sK3 = X1 | sK3 = X1 | sK4 = X1) )),
% 0.21/0.52    inference(resolution,[],[f380,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | X0 = X2 | X0 = X3 | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f380,plain,(
% 0.21/0.52    ( ! [X1] : (sP0(X1,sK4,sK3,sK3) | ~sP0(X1,sK2,sK4,sK3)) )),
% 0.21/0.52    inference(resolution,[],[f239,f75])).
% 0.21/0.52  % (10152)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X6,X4,X7,X5] : (~r2_hidden(X4,k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7)) | sP0(X4,X7,X6,X5)) )),
% 0.21/0.52    inference(resolution,[],[f73,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X2,X0,X5,X3,X1] : (~sP1(X0,X1,X2,X3) | ~r2_hidden(X5,X3) | sP0(X5,X2,X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ((~sP0(sK5(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sP0(sK5(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X5,X2,X1,X0)) & (sP0(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).
% 0.21/0.52  % (10142)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X3,X2,X1,X0] : (? [X4] : ((~sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP0(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP0(sK5(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sP0(sK5(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : ((~sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP0(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X5,X2,X1,X0)) & (sP0(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.21/0.52    inference(rectify,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : ((~sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP0(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP0(X4,X2,X1,X0)) & (sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.21/0.52    inference(nnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (sP1(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP0(X4,X2,X1,X0)))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sP1(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 0.21/0.52    inference(equality_resolution,[],[f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.21/0.52    inference(definition_unfolding,[],[f53,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f43,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f44,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f55,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f56,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP1(X0,X1,X2,X3)) & (sP1(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.52    inference(nnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP1(X0,X1,X2,X3))),
% 0.21/0.53    inference(definition_folding,[],[f19,f21,f20])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  % (10141)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.53  fof(f239,plain,(
% 0.21/0.53    ( ! [X1] : (r2_hidden(X1,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | ~sP0(X1,sK2,sK4,sK3)) )),
% 0.21/0.53    inference(superposition,[],[f74,f226])).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4,sK2)),
% 0.21/0.53    inference(resolution,[],[f97,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 0.21/0.53    inference(definition_unfolding,[],[f33,f65,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f39,f63])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f38,f64])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)) | k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f96,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0) = k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k1_xboole_0) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f95,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0) = k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7))) )),
% 0.21/0.53    inference(superposition,[],[f66,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f58,f59,f57,f65])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f40,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1)) | ~sP0(X0,X1,X2,X3)) )),
% 0.21/0.53    inference(resolution,[],[f73,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X2,X0,X5,X3,X1] : (~sP1(X0,X1,X2,X3) | ~sP0(X5,X2,X1,X0) | r2_hidden(X5,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (10166)------------------------------
% 0.21/0.53  % (10166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10166)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (10166)Memory used [KB]: 6652
% 0.21/0.53  % (10166)Time elapsed: 0.119 s
% 0.21/0.53  % (10166)------------------------------
% 0.21/0.53  % (10166)------------------------------
% 0.21/0.53  % (10167)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (10145)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (10138)Success in time 0.175 s
%------------------------------------------------------------------------------
