%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 372 expanded)
%              Number of leaves         :   18 ( 117 expanded)
%              Depth                    :   19
%              Number of atoms          :  146 ( 526 expanded)
%              Number of equality atoms :   99 ( 449 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f207,plain,(
    $false ),
    inference(resolution,[],[f201,f101])).

% (795)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f101,plain,(
    ! [X4,X2,X7,X5,X3,X1] : r2_hidden(X7,k6_enumset1(X7,X7,X7,X1,X2,X3,X4,X5)) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X6,X4,X2,X7,X5,X3,X1] :
      ( r2_hidden(X7,X6)
      | k6_enumset1(X7,X7,X7,X1,X2,X3,X4,X5) != X6 ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( X0 != X7
      | r2_hidden(X7,X6)
      | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(definition_unfolding,[],[f56,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( X0 != X7
      | r2_hidden(X7,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

fof(f201,plain,(
    ! [X4] : ~ r2_hidden(sK2,X4) ),
    inference(subsumption_resolution,[],[f199,f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X7,X3,X1] : r2_hidden(X7,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X7)) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X6,X4,X2,X0,X7,X3,X1] :
      ( r2_hidden(X7,X6)
      | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X7) != X6 ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( X5 != X7
      | r2_hidden(X7,X6)
      | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( X5 != X7
      | r2_hidden(X7,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f199,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(sK2,X4) ) ),
    inference(backward_demodulation,[],[f177,f189])).

fof(f189,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f188,f91])).

fof(f188,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | sK0 = sK1 ) ),
    inference(subsumption_resolution,[],[f185,f91])).

fof(f185,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(sK1,X3)
      | sK0 = sK1 ) ),
    inference(resolution,[],[f174,f126])).

fof(f126,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK0,k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(sK0,X3)
      | ~ r2_hidden(sK1,X2)
      | sK0 = sK1 ) ),
    inference(superposition,[],[f44,f116])).

fof(f116,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | sK0 = sK1 ),
    inference(superposition,[],[f25,f114])).

fof(f114,plain,
    ( sK0 = sK2
    | sK0 = sK1 ),
    inference(superposition,[],[f113,f112])).

fof(f112,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f24,f111])).

fof(f111,plain,(
    sK1 = k1_mcart_1(sK0) ),
    inference(superposition,[],[f32,f25])).

fof(f32,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f24,plain,
    ( sK0 = k1_mcart_1(sK0)
    | sK0 = k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f113,plain,(
    sK2 = k2_mcart_1(sK0) ),
    inference(superposition,[],[f33,f25])).

fof(f33,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f17])).

fof(f25,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f174,plain,(
    ! [X2,X3] : ~ r2_hidden(X2,k2_zfmisc_1(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) ),
    inference(subsumption_resolution,[],[f171,f104])).

fof(f104,plain,(
    ! [X1] : k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(forward_demodulation,[],[f103,f26])).

fof(f26,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f103,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(forward_demodulation,[],[f89,f70])).

fof(f70,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f28,f67])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f41,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f45,f62])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f89,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f39,f69,f68,f69,f69])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f31,f67])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f66])).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f171,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k2_zfmisc_1(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))
      | k1_xboole_0 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ) ),
    inference(resolution,[],[f72,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f69])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f177,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(sK2,X4) ) ),
    inference(resolution,[],[f173,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK2,X1)
      | ~ r2_hidden(sK1,X0) ) ),
    inference(superposition,[],[f44,f25])).

fof(f173,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) ),
    inference(subsumption_resolution,[],[f170,f104])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))
      | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(resolution,[],[f72,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:32:25 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.47  % (799)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (801)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.49  % (809)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.49  % (815)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.49  % (793)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (796)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.50  % (809)Refutation not found, incomplete strategy% (809)------------------------------
% 0.20/0.50  % (809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (809)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (809)Memory used [KB]: 10746
% 0.20/0.50  % (809)Time elapsed: 0.070 s
% 0.20/0.50  % (809)------------------------------
% 0.20/0.50  % (809)------------------------------
% 0.20/0.50  % (796)Refutation not found, incomplete strategy% (796)------------------------------
% 0.20/0.50  % (796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (796)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (796)Memory used [KB]: 10618
% 0.20/0.50  % (796)Time elapsed: 0.102 s
% 0.20/0.50  % (796)------------------------------
% 0.20/0.50  % (796)------------------------------
% 0.20/0.50  % (807)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.50  % (789)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (807)Refutation not found, incomplete strategy% (807)------------------------------
% 0.20/0.51  % (807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (807)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (807)Memory used [KB]: 10746
% 0.20/0.51  % (807)Time elapsed: 0.118 s
% 0.20/0.51  % (807)------------------------------
% 0.20/0.51  % (807)------------------------------
% 0.20/0.51  % (793)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (791)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f207,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(resolution,[],[f201,f101])).
% 0.20/0.51  % (795)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    ( ! [X4,X2,X7,X5,X3,X1] : (r2_hidden(X7,k6_enumset1(X7,X7,X7,X1,X2,X3,X4,X5))) )),
% 0.20/0.51    inference(equality_resolution,[],[f100])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X7,X5,X3,X1] : (r2_hidden(X7,X6) | k6_enumset1(X7,X7,X7,X1,X2,X3,X4,X5) != X6) )),
% 0.20/0.51    inference(equality_resolution,[],[f80])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (X0 != X7 | r2_hidden(X7,X6) | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6) )),
% 0.20/0.51    inference(definition_unfolding,[],[f56,f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f46,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (X0 != X7 | r2_hidden(X7,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 0.20/0.51    inference(ennf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> ~(X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).
% 0.20/0.51  fof(f201,plain,(
% 0.20/0.51    ( ! [X4] : (~r2_hidden(sK2,X4)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f199,f91])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X7,X3,X1] : (r2_hidden(X7,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X7))) )),
% 0.20/0.51    inference(equality_resolution,[],[f90])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r2_hidden(X7,X6) | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X7) != X6) )),
% 0.20/0.51    inference(equality_resolution,[],[f75])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (X5 != X7 | r2_hidden(X7,X6) | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6) )),
% 0.20/0.51    inference(definition_unfolding,[],[f61,f62])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (X5 != X7 | r2_hidden(X7,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f199,plain,(
% 0.20/0.51    ( ! [X4] : (~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK2,X4)) )),
% 0.20/0.51    inference(backward_demodulation,[],[f177,f189])).
% 0.20/0.51  fof(f189,plain,(
% 0.20/0.51    sK0 = sK1),
% 0.20/0.51    inference(resolution,[],[f188,f91])).
% 0.20/0.51  fof(f188,plain,(
% 0.20/0.51    ( ! [X3] : (~r2_hidden(sK1,X3) | sK0 = sK1) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f185,f91])).
% 0.20/0.51  fof(f185,plain,(
% 0.20/0.51    ( ! [X3] : (~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK1,X3) | sK0 = sK1) )),
% 0.20/0.51    inference(resolution,[],[f174,f126])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    ( ! [X2,X3] : (r2_hidden(sK0,k2_zfmisc_1(X2,X3)) | ~r2_hidden(sK0,X3) | ~r2_hidden(sK1,X2) | sK0 = sK1) )),
% 0.20/0.51    inference(superposition,[],[f44,f116])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    sK0 = k4_tarski(sK1,sK0) | sK0 = sK1),
% 0.20/0.51    inference(superposition,[],[f25,f114])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    sK0 = sK2 | sK0 = sK1),
% 0.20/0.51    inference(superposition,[],[f113,f112])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    sK0 = k2_mcart_1(sK0) | sK0 = sK1),
% 0.20/0.51    inference(backward_demodulation,[],[f24,f111])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    sK1 = k1_mcart_1(sK0)),
% 0.20/0.51    inference(superposition,[],[f32,f25])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,axiom,(
% 0.20/0.51    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    sK0 = k1_mcart_1(sK0) | sK0 = k2_mcart_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.20/0.51    inference(ennf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.20/0.51    inference(negated_conjecture,[],[f18])).
% 0.20/0.51  fof(f18,conjecture,(
% 0.20/0.51    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    sK2 = k2_mcart_1(sK0)),
% 0.20/0.51    inference(superposition,[],[f33,f25])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    sK0 = k4_tarski(sK1,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.20/0.51  fof(f174,plain,(
% 0.20/0.51    ( ! [X2,X3] : (~r2_hidden(X2,k2_zfmisc_1(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f171,f104])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    ( ! [X1] : (k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f103,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 0.20/0.51    inference(forward_demodulation,[],[f89,f70])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f28,f67])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f29,f66])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f30,f65])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f40,f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f41,f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f45,f62])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,axiom,(
% 0.20/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.51    inference(rectify,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 0.20/0.51    inference(equality_resolution,[],[f73])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    ( ! [X0,X1] : (X0 != X1 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f39,f69,f68,f69,f69])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f31,f67])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f27,f66])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,axiom,(
% 0.20/0.51    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.20/0.51  fof(f171,plain,(
% 0.20/0.51    ( ! [X2,X3] : (~r2_hidden(X2,k2_zfmisc_1(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) | k1_xboole_0 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) )),
% 0.20/0.51    inference(resolution,[],[f72,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f36,f69])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.51  fof(f177,plain,(
% 0.20/0.51    ( ! [X4] : (~r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK2,X4)) )),
% 0.20/0.51    inference(resolution,[],[f173,f125])).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK2,X1) | ~r2_hidden(sK1,X0)) )),
% 0.20/0.51    inference(superposition,[],[f44,f25])).
% 0.20/0.51  fof(f173,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f170,f104])).
% 0.20/0.51  fof(f170,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.51    inference(resolution,[],[f72,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (793)------------------------------
% 0.20/0.51  % (793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (793)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (793)Memory used [KB]: 6268
% 0.20/0.51  % (793)Time elapsed: 0.091 s
% 0.20/0.51  % (793)------------------------------
% 0.20/0.51  % (793)------------------------------
% 0.20/0.51  % (798)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (800)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (784)Success in time 0.165 s
%------------------------------------------------------------------------------
