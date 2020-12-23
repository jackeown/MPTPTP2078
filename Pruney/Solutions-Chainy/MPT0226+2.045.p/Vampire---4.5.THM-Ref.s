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
% DateTime   : Thu Dec  3 12:36:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 236 expanded)
%              Number of leaves         :   16 (  74 expanded)
%              Depth                    :   20
%              Number of atoms          :  195 ( 503 expanded)
%              Number of equality atoms :  143 ( 392 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f324,plain,(
    $false ),
    inference(subsumption_resolution,[],[f323,f35])).

fof(f35,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK1 != sK2
    & k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK1 != sK2
      & k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(f323,plain,(
    sK1 = sK2 ),
    inference(resolution,[],[f321,f129])).

fof(f129,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X8,k1_tarski(X7))
      | X7 = X8 ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X8,X7] :
      ( X7 = X8
      | X7 = X8
      | ~ r2_hidden(X8,k1_tarski(X7))
      | X7 = X8 ) ),
    inference(resolution,[],[f47,f81])).

fof(f81,plain,(
    ! [X0] : sP0(X0,X0,X0,k1_tarski(X0)) ),
    inference(superposition,[],[f72,f38])).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f72,plain,(
    ! [X0,X1] : sP0(X1,X0,X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f64,f39])).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

% (6535)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | X1 = X5
      | X2 = X5
      | ~ r2_hidden(X5,X3)
      | X0 = X5 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK3(X0,X1,X2,X3) != X0
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X0
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X2
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
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
     => ( ( ( sK3(X0,X1,X2,X3) != X0
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X0
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X2
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
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
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f321,plain,(
    r2_hidden(sK1,k1_tarski(sK2)) ),
    inference(superposition,[],[f76,f317])).

fof(f317,plain,(
    k1_tarski(sK2) = k2_tarski(sK2,sK1) ),
    inference(superposition,[],[f316,f86])).

fof(f86,plain,(
    k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f85,f37])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f85,plain,(
    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)) = k5_xboole_0(k1_tarski(sK2),k1_xboole_0) ),
    inference(superposition,[],[f40,f34])).

fof(f34,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f316,plain,(
    ! [X10,X9] : k2_tarski(X9,X10) = k2_xboole_0(k1_tarski(X9),k1_tarski(X10)) ),
    inference(forward_demodulation,[],[f311,f201])).

fof(f201,plain,(
    ! [X2,X1] : k2_enumset1(X2,X2,X2,X1) = k2_tarski(X2,X1) ),
    inference(superposition,[],[f193,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

fof(f193,plain,(
    ! [X6,X7] : k2_enumset1(X7,X6,X6,X6) = k2_tarski(X6,X7) ),
    inference(superposition,[],[f187,f169])).

fof(f169,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X1,X1,X2) = k2_enumset1(X1,X0,X0,X2) ),
    inference(superposition,[],[f168,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f168,plain,(
    ! [X14,X17,X15,X16] : k3_enumset1(X14,X15,X16,X16,X17) = k2_enumset1(X16,X15,X14,X17) ),
    inference(forward_demodulation,[],[f166,f167])).

fof(f167,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(forward_demodulation,[],[f163,f46])).

fof(f163,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(superposition,[],[f162,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f162,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(forward_demodulation,[],[f161,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f161,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(superposition,[],[f160,f46])).

fof(f160,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(forward_demodulation,[],[f159,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f159,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(superposition,[],[f158,f57])).

fof(f158,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(forward_demodulation,[],[f157,f59])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f157,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(superposition,[],[f60,f58])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

fof(f166,plain,(
    ! [X14,X17,X15,X16] : k3_enumset1(X14,X15,X16,X16,X17) = k2_xboole_0(k1_enumset1(X16,X15,X14),k1_tarski(X17)) ),
    inference(superposition,[],[f162,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X1,X0,X0) ),
    inference(superposition,[],[f45,f44])).

fof(f187,plain,(
    ! [X8,X9] : k2_enumset1(X9,X8,X8,X9) = k2_tarski(X9,X8) ),
    inference(forward_demodulation,[],[f175,f39])).

fof(f175,plain,(
    ! [X8,X9] : k1_enumset1(X9,X9,X8) = k2_enumset1(X9,X8,X8,X9) ),
    inference(superposition,[],[f169,f89])).

fof(f311,plain,(
    ! [X10,X9] : k2_enumset1(X9,X9,X9,X10) = k2_xboole_0(k1_tarski(X9),k1_tarski(X10)) ),
    inference(superposition,[],[f167,f115])).

fof(f115,plain,(
    ! [X5] : k1_enumset1(X5,X5,X5) = k1_tarski(X5) ),
    inference(resolution,[],[f56,f81])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f76,plain,(
    ! [X0,X1] : r2_hidden(X1,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f71,f39])).

fof(f71,plain,(
    ! [X6,X8,X7] : r2_hidden(X6,k1_enumset1(X7,X8,X6)) ),
    inference(resolution,[],[f64,f61])).

fof(f61,plain,(
    ! [X2,X5,X3,X1] :
      ( ~ sP0(X5,X1,X2,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:52:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (6545)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.50  % (6537)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (6545)Refutation not found, incomplete strategy% (6545)------------------------------
% 0.22/0.51  % (6545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (6537)Refutation not found, incomplete strategy% (6537)------------------------------
% 0.22/0.51  % (6537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (6537)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (6537)Memory used [KB]: 6140
% 0.22/0.51  % (6537)Time elapsed: 0.058 s
% 0.22/0.51  % (6537)------------------------------
% 0.22/0.51  % (6537)------------------------------
% 0.22/0.51  % (6545)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (6545)Memory used [KB]: 1663
% 0.22/0.51  % (6545)Time elapsed: 0.057 s
% 0.22/0.51  % (6545)------------------------------
% 0.22/0.51  % (6545)------------------------------
% 0.22/0.51  % (6529)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (6529)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (6524)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (6526)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f324,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f323,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    sK1 != sK2),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    sK1 != sK2 & k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK1 != sK2 & k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.22/0.52    inference(negated_conjecture,[],[f17])).
% 0.22/0.52  fof(f17,conjecture,(
% 0.22/0.52    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).
% 0.22/0.52  fof(f323,plain,(
% 0.22/0.52    sK1 = sK2),
% 0.22/0.52    inference(resolution,[],[f321,f129])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    ( ! [X8,X7] : (~r2_hidden(X8,k1_tarski(X7)) | X7 = X8) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f126])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    ( ! [X8,X7] : (X7 = X8 | X7 = X8 | ~r2_hidden(X8,k1_tarski(X7)) | X7 = X8) )),
% 0.22/0.52    inference(resolution,[],[f47,f81])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    ( ! [X0] : (sP0(X0,X0,X0,k1_tarski(X0))) )),
% 0.22/0.52    inference(superposition,[],[f72,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X0,X1] : (sP0(X1,X0,X0,k2_tarski(X0,X1))) )),
% 0.22/0.52    inference(superposition,[],[f64,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 0.22/0.52    inference(equality_resolution,[],[f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.22/0.52    inference(nnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 0.22/0.52    inference(definition_folding,[],[f23,f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.52  % (6535)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3) | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3) | X0 = X5) )),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK3(X0,X1,X2,X3) != X0 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X2) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X0 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X2 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X0 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X2) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X0 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X2 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.22/0.52    inference(rectify,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.22/0.52    inference(flattening,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.22/0.52    inference(nnf_transformation,[],[f24])).
% 0.22/0.52  fof(f321,plain,(
% 0.22/0.52    r2_hidden(sK1,k1_tarski(sK2))),
% 0.22/0.52    inference(superposition,[],[f76,f317])).
% 0.22/0.52  fof(f317,plain,(
% 0.22/0.52    k1_tarski(sK2) = k2_tarski(sK2,sK1)),
% 0.22/0.52    inference(superposition,[],[f316,f86])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),
% 0.22/0.52    inference(forward_demodulation,[],[f85,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)) = k5_xboole_0(k1_tarski(sK2),k1_xboole_0)),
% 0.22/0.52    inference(superposition,[],[f40,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.52  fof(f316,plain,(
% 0.22/0.52    ( ! [X10,X9] : (k2_tarski(X9,X10) = k2_xboole_0(k1_tarski(X9),k1_tarski(X10))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f311,f201])).
% 0.22/0.52  fof(f201,plain,(
% 0.22/0.52    ( ! [X2,X1] : (k2_enumset1(X2,X2,X2,X1) = k2_tarski(X2,X1)) )),
% 0.22/0.52    inference(superposition,[],[f193,f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
% 0.22/0.52  fof(f193,plain,(
% 0.22/0.52    ( ! [X6,X7] : (k2_enumset1(X7,X6,X6,X6) = k2_tarski(X6,X7)) )),
% 0.22/0.52    inference(superposition,[],[f187,f169])).
% 0.22/0.52  fof(f169,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X1,X1,X2) = k2_enumset1(X1,X0,X0,X2)) )),
% 0.22/0.52    inference(superposition,[],[f168,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.52  fof(f168,plain,(
% 0.22/0.52    ( ! [X14,X17,X15,X16] : (k3_enumset1(X14,X15,X16,X16,X17) = k2_enumset1(X16,X15,X14,X17)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f166,f167])).
% 0.22/0.52  fof(f167,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f163,f46])).
% 0.22/0.52  fof(f163,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.22/0.52    inference(superposition,[],[f162,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.52  fof(f162,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f161,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.22/0.52    inference(superposition,[],[f160,f46])).
% 0.22/0.52  fof(f160,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f159,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.52  fof(f159,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.22/0.52    inference(superposition,[],[f158,f57])).
% 0.22/0.52  fof(f158,plain,(
% 0.22/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f157,f59])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 0.22/0.52    inference(superposition,[],[f60,f58])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).
% 0.22/0.52  fof(f166,plain,(
% 0.22/0.52    ( ! [X14,X17,X15,X16] : (k3_enumset1(X14,X15,X16,X16,X17) = k2_xboole_0(k1_enumset1(X16,X15,X14),k1_tarski(X17))) )),
% 0.22/0.52    inference(superposition,[],[f162,f89])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X1,X0,X0)) )),
% 0.22/0.52    inference(superposition,[],[f45,f44])).
% 0.22/0.52  fof(f187,plain,(
% 0.22/0.52    ( ! [X8,X9] : (k2_enumset1(X9,X8,X8,X9) = k2_tarski(X9,X8)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f175,f39])).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    ( ! [X8,X9] : (k1_enumset1(X9,X9,X8) = k2_enumset1(X9,X8,X8,X9)) )),
% 0.22/0.52    inference(superposition,[],[f169,f89])).
% 0.22/0.52  fof(f311,plain,(
% 0.22/0.52    ( ! [X10,X9] : (k2_enumset1(X9,X9,X9,X10) = k2_xboole_0(k1_tarski(X9),k1_tarski(X10))) )),
% 0.22/0.52    inference(superposition,[],[f167,f115])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    ( ! [X5] : (k1_enumset1(X5,X5,X5) = k1_tarski(X5)) )),
% 0.22/0.52    inference(resolution,[],[f56,f81])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) = X3) )),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(X1,k2_tarski(X0,X1))) )),
% 0.22/0.52    inference(superposition,[],[f71,f39])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X6,X8,X7] : (r2_hidden(X6,k1_enumset1(X7,X8,X6))) )),
% 0.22/0.52    inference(resolution,[],[f64,f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X2,X5,X3,X1] : (~sP0(X5,X1,X2,X3) | r2_hidden(X5,X3)) )),
% 0.22/0.52    inference(equality_resolution,[],[f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (6529)------------------------------
% 0.22/0.52  % (6529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6529)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (6529)Memory used [KB]: 6396
% 0.22/0.52  % (6529)Time elapsed: 0.069 s
% 0.22/0.52  % (6529)------------------------------
% 0.22/0.52  % (6529)------------------------------
% 0.22/0.53  % (6521)Success in time 0.16 s
%------------------------------------------------------------------------------
