%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:40 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   85 (1191 expanded)
%              Number of leaves         :   18 ( 381 expanded)
%              Depth                    :   21
%              Number of atoms          :  142 (1542 expanded)
%              Number of equality atoms :  113 (1447 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f433,plain,(
    $false ),
    inference(subsumption_resolution,[],[f432,f25])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f432,plain,(
    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f383,f386])).

fof(f386,plain,(
    k1_xboole_0 = k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f70,f364])).

fof(f364,plain,(
    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(subsumption_resolution,[],[f362,f305])).

fof(f305,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f164,f150])).

fof(f150,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(superposition,[],[f109,f24])).

fof(f24,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f109,plain,(
    ! [X0] : k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2)) = k6_enumset1(k4_tarski(sK1,X0),k4_tarski(sK1,X0),k4_tarski(sK1,X0),k4_tarski(sK1,X0),k4_tarski(sK1,X0),k4_tarski(sK1,X0),k4_tarski(sK1,X0),sK0) ),
    inference(superposition,[],[f76,f24])).

fof(f76,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(definition_unfolding,[],[f40,f69,f66,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f42,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f43,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f66])).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f164,plain,(
    ! [X0] : r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2))) ),
    inference(resolution,[],[f153,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f35,f69])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f153,plain,(
    ! [X1] : r2_hidden(sK0,k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,sK2))) ),
    inference(superposition,[],[f95,f109])).

fof(f95,plain,(
    ! [X4,X2,X0,X8,X5,X3,X1] : r2_hidden(X8,k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X8)) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X8,X7,X5,X3,X1] :
      ( r2_hidden(X8,X7)
      | k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X8) != X7 ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( X6 != X8
      | r2_hidden(X8,X7)
      | k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) != X7 ) ),
    inference(definition_unfolding,[],[f61,f45])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( X6 != X8
      | r2_hidden(X8,X7)
      | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ( X6 = X8
            | X5 = X8
            | X4 = X8
            | X3 = X8
            | X2 = X8
            | X1 = X8
            | X0 = X8 ) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X6 != X8
              & X5 != X8
              & X4 != X8
              & X3 != X8
              & X2 != X8
              & X1 != X8
              & X0 != X8 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_enumset1)).

fof(f362,plain,
    ( ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(duplicate_literal_removal,[],[f348])).

fof(f348,plain,
    ( ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[],[f139,f339])).

fof(f339,plain,
    ( sK0 = sK1
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f337,f113])).

fof(f113,plain,(
    sK1 = k1_mcart_1(sK0) ),
    inference(superposition,[],[f31,f24])).

fof(f31,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f337,plain,
    ( sK0 = k1_mcart_1(sK0)
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[],[f31,f326])).

fof(f326,plain,
    ( sK0 = k4_tarski(sK0,sK2)
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(subsumption_resolution,[],[f325,f305])).

fof(f325,plain,
    ( ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK0 = k4_tarski(sK0,sK2) ),
    inference(superposition,[],[f146,f117])).

fof(f117,plain,
    ( sK0 = sK2
    | sK0 = k4_tarski(sK0,sK2) ),
    inference(forward_demodulation,[],[f116,f114])).

fof(f114,plain,(
    sK2 = k2_mcart_1(sK0) ),
    inference(superposition,[],[f32,f24])).

fof(f32,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f17])).

fof(f116,plain,
    ( sK0 = k4_tarski(sK0,sK2)
    | sK0 = k2_mcart_1(sK0) ),
    inference(superposition,[],[f24,f115])).

fof(f115,plain,
    ( sK0 = sK1
    | sK0 = k2_mcart_1(sK0) ),
    inference(backward_demodulation,[],[f23,f113])).

fof(f23,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f146,plain,
    ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[],[f131,f24])).

fof(f131,plain,(
    ! [X1] :
      ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_tarski(sK1,X1)))
      | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X1) ) ),
    inference(superposition,[],[f34,f110])).

fof(f110,plain,(
    ! [X1] : k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X1)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_tarski(sK1,X1)) ),
    inference(superposition,[],[f76,f24])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(f139,plain,
    ( ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(superposition,[],[f130,f24])).

fof(f130,plain,(
    ! [X0] :
      ( ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_tarski(sK1,X0)))
      | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ) ),
    inference(superposition,[],[f33,f110])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f29,f69,f67,f69,f66])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f66])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f29,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(f383,plain,(
    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f93,f364])).

fof(f93,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f38,f69,f68,f69,f69])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f30,f67])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:46:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (19014)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (19014)Refutation not found, incomplete strategy% (19014)------------------------------
% 0.21/0.51  % (19014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19014)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (19014)Memory used [KB]: 6140
% 0.21/0.51  % (19014)Time elapsed: 0.098 s
% 0.21/0.51  % (19014)------------------------------
% 0.21/0.51  % (19014)------------------------------
% 0.21/0.52  % (19011)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (19024)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (19021)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (19031)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (19035)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (19013)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (19021)Refutation not found, incomplete strategy% (19021)------------------------------
% 0.21/0.53  % (19021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19021)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (19021)Memory used [KB]: 10618
% 0.21/0.53  % (19021)Time elapsed: 0.106 s
% 0.21/0.53  % (19021)------------------------------
% 0.21/0.53  % (19021)------------------------------
% 1.30/0.54  % (19036)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.30/0.54  % (19027)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.30/0.54  % (19010)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.30/0.54  % (19030)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.30/0.54  % (19018)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.30/0.54  % (19010)Refutation not found, incomplete strategy% (19010)------------------------------
% 1.30/0.54  % (19010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (19010)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (19010)Memory used [KB]: 1663
% 1.30/0.54  % (19010)Time elapsed: 0.122 s
% 1.30/0.54  % (19010)------------------------------
% 1.30/0.54  % (19010)------------------------------
% 1.30/0.54  % (19015)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.30/0.55  % (19038)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.30/0.55  % (19027)Refutation not found, incomplete strategy% (19027)------------------------------
% 1.30/0.55  % (19027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (19039)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.30/0.55  % (19027)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (19027)Memory used [KB]: 10618
% 1.30/0.55  % (19027)Time elapsed: 0.126 s
% 1.30/0.55  % (19027)------------------------------
% 1.30/0.55  % (19027)------------------------------
% 1.30/0.55  % (19029)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.30/0.55  % (19037)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.45/0.55  % (19031)Refutation found. Thanks to Tanya!
% 1.45/0.55  % SZS status Theorem for theBenchmark
% 1.45/0.55  % SZS output start Proof for theBenchmark
% 1.45/0.55  fof(f433,plain,(
% 1.45/0.55    $false),
% 1.45/0.55    inference(subsumption_resolution,[],[f432,f25])).
% 1.45/0.55  fof(f25,plain,(
% 1.45/0.55    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 1.45/0.55    inference(cnf_transformation,[],[f2])).
% 1.45/0.55  fof(f2,axiom,(
% 1.45/0.55    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.45/0.55  fof(f432,plain,(
% 1.45/0.55    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.45/0.55    inference(forward_demodulation,[],[f383,f386])).
% 1.45/0.55  fof(f386,plain,(
% 1.45/0.55    k1_xboole_0 = k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 1.45/0.55    inference(superposition,[],[f70,f364])).
% 1.45/0.55  fof(f364,plain,(
% 1.45/0.55    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.45/0.55    inference(subsumption_resolution,[],[f362,f305])).
% 1.45/0.55  fof(f305,plain,(
% 1.45/0.55    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.45/0.55    inference(superposition,[],[f164,f150])).
% 1.45/0.55  fof(f150,plain,(
% 1.45/0.55    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 1.45/0.55    inference(superposition,[],[f109,f24])).
% 1.45/0.55  fof(f24,plain,(
% 1.45/0.55    sK0 = k4_tarski(sK1,sK2)),
% 1.45/0.55    inference(cnf_transformation,[],[f20])).
% 1.45/0.55  fof(f20,plain,(
% 1.45/0.55    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 1.45/0.55    inference(ennf_transformation,[],[f19])).
% 1.45/0.55  fof(f19,negated_conjecture,(
% 1.45/0.55    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.45/0.55    inference(negated_conjecture,[],[f18])).
% 1.45/0.55  fof(f18,conjecture,(
% 1.45/0.55    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.45/0.55  fof(f109,plain,(
% 1.45/0.55    ( ! [X0] : (k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2)) = k6_enumset1(k4_tarski(sK1,X0),k4_tarski(sK1,X0),k4_tarski(sK1,X0),k4_tarski(sK1,X0),k4_tarski(sK1,X0),k4_tarski(sK1,X0),k4_tarski(sK1,X0),sK0)) )),
% 1.45/0.55    inference(superposition,[],[f76,f24])).
% 1.45/0.55  fof(f76,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 1.45/0.55    inference(definition_unfolding,[],[f40,f69,f66,f66])).
% 1.45/0.55  fof(f66,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.45/0.55    inference(definition_unfolding,[],[f28,f65])).
% 1.45/0.55  fof(f65,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.45/0.55    inference(definition_unfolding,[],[f39,f64])).
% 1.45/0.55  fof(f64,plain,(
% 1.45/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.45/0.55    inference(definition_unfolding,[],[f42,f63])).
% 1.45/0.55  fof(f63,plain,(
% 1.45/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.45/0.55    inference(definition_unfolding,[],[f43,f62])).
% 1.45/0.55  fof(f62,plain,(
% 1.45/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.45/0.55    inference(definition_unfolding,[],[f44,f45])).
% 1.45/0.55  fof(f45,plain,(
% 1.45/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f9])).
% 1.45/0.55  fof(f9,axiom,(
% 1.45/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.45/0.55  fof(f44,plain,(
% 1.45/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f8])).
% 1.45/0.55  fof(f8,axiom,(
% 1.45/0.55    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.45/0.55  fof(f43,plain,(
% 1.45/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f7])).
% 1.45/0.55  fof(f7,axiom,(
% 1.45/0.55    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.45/0.55  fof(f42,plain,(
% 1.45/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f6])).
% 1.45/0.55  fof(f6,axiom,(
% 1.45/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.45/0.55  fof(f39,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f5])).
% 1.45/0.55  fof(f5,axiom,(
% 1.45/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.45/0.55  fof(f28,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f4])).
% 1.45/0.55  fof(f4,axiom,(
% 1.45/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.45/0.55  fof(f69,plain,(
% 1.45/0.55    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.45/0.55    inference(definition_unfolding,[],[f26,f66])).
% 1.45/0.55  fof(f26,plain,(
% 1.45/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f3])).
% 1.45/0.55  fof(f3,axiom,(
% 1.45/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.45/0.55  fof(f40,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 1.45/0.55    inference(cnf_transformation,[],[f14])).
% 1.45/0.55  fof(f14,axiom,(
% 1.45/0.55    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 1.45/0.55  fof(f164,plain,(
% 1.45/0.55    ( ! [X0] : (r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2)))) )),
% 1.45/0.55    inference(resolution,[],[f153,f72])).
% 1.45/0.55  fof(f72,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 1.45/0.55    inference(definition_unfolding,[],[f35,f69])).
% 1.45/0.55  fof(f35,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f10])).
% 1.45/0.55  fof(f10,axiom,(
% 1.45/0.55    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.45/0.55  fof(f153,plain,(
% 1.45/0.55    ( ! [X1] : (r2_hidden(sK0,k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,sK2)))) )),
% 1.45/0.55    inference(superposition,[],[f95,f109])).
% 1.45/0.55  fof(f95,plain,(
% 1.45/0.55    ( ! [X4,X2,X0,X8,X5,X3,X1] : (r2_hidden(X8,k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X8))) )),
% 1.45/0.55    inference(equality_resolution,[],[f94])).
% 1.45/0.55  fof(f94,plain,(
% 1.45/0.55    ( ! [X4,X2,X0,X8,X7,X5,X3,X1] : (r2_hidden(X8,X7) | k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X8) != X7) )),
% 1.45/0.55    inference(equality_resolution,[],[f77])).
% 1.45/0.55  fof(f77,plain,(
% 1.45/0.55    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (X6 != X8 | r2_hidden(X8,X7) | k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) != X7) )),
% 1.45/0.55    inference(definition_unfolding,[],[f61,f45])).
% 1.45/0.55  fof(f61,plain,(
% 1.45/0.55    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (X6 != X8 | r2_hidden(X8,X7) | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7) )),
% 1.45/0.55    inference(cnf_transformation,[],[f22])).
% 1.45/0.55  fof(f22,plain,(
% 1.45/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> ! [X8] : (r2_hidden(X8,X7) <=> (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8)))),
% 1.45/0.55    inference(ennf_transformation,[],[f15])).
% 1.45/0.55  fof(f15,axiom,(
% 1.45/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> ! [X8] : (r2_hidden(X8,X7) <=> ~(X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)))),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_enumset1)).
% 1.45/0.55  fof(f362,plain,(
% 1.45/0.55    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.45/0.55    inference(duplicate_literal_removal,[],[f348])).
% 1.45/0.55  fof(f348,plain,(
% 1.45/0.55    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.45/0.55    inference(superposition,[],[f139,f339])).
% 1.45/0.55  fof(f339,plain,(
% 1.45/0.55    sK0 = sK1 | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.45/0.55    inference(forward_demodulation,[],[f337,f113])).
% 1.45/0.55  fof(f113,plain,(
% 1.45/0.55    sK1 = k1_mcart_1(sK0)),
% 1.45/0.55    inference(superposition,[],[f31,f24])).
% 1.45/0.55  fof(f31,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.45/0.55    inference(cnf_transformation,[],[f17])).
% 1.45/0.55  fof(f17,axiom,(
% 1.45/0.55    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.45/0.55  fof(f337,plain,(
% 1.45/0.55    sK0 = k1_mcart_1(sK0) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.45/0.55    inference(superposition,[],[f31,f326])).
% 1.45/0.55  fof(f326,plain,(
% 1.45/0.55    sK0 = k4_tarski(sK0,sK2) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.45/0.55    inference(subsumption_resolution,[],[f325,f305])).
% 1.45/0.55  fof(f325,plain,(
% 1.45/0.55    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK0 = k4_tarski(sK0,sK2)),
% 1.45/0.55    inference(superposition,[],[f146,f117])).
% 1.45/0.55  fof(f117,plain,(
% 1.45/0.55    sK0 = sK2 | sK0 = k4_tarski(sK0,sK2)),
% 1.45/0.55    inference(forward_demodulation,[],[f116,f114])).
% 1.45/0.55  fof(f114,plain,(
% 1.45/0.55    sK2 = k2_mcart_1(sK0)),
% 1.45/0.55    inference(superposition,[],[f32,f24])).
% 1.45/0.55  fof(f32,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.45/0.55    inference(cnf_transformation,[],[f17])).
% 1.45/0.55  fof(f116,plain,(
% 1.45/0.55    sK0 = k4_tarski(sK0,sK2) | sK0 = k2_mcart_1(sK0)),
% 1.45/0.55    inference(superposition,[],[f24,f115])).
% 1.45/0.55  fof(f115,plain,(
% 1.45/0.55    sK0 = sK1 | sK0 = k2_mcart_1(sK0)),
% 1.45/0.55    inference(backward_demodulation,[],[f23,f113])).
% 1.45/0.55  fof(f23,plain,(
% 1.45/0.55    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 1.45/0.55    inference(cnf_transformation,[],[f20])).
% 1.45/0.55  fof(f146,plain,(
% 1.45/0.55    ~r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 1.45/0.55    inference(superposition,[],[f131,f24])).
% 1.45/0.55  fof(f131,plain,(
% 1.45/0.55    ( ! [X1] : (~r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_tarski(sK1,X1))) | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X1)) )),
% 1.45/0.55    inference(superposition,[],[f34,f110])).
% 1.45/0.55  fof(f110,plain,(
% 1.45/0.55    ( ! [X1] : (k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X1)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_tarski(sK1,X1))) )),
% 1.45/0.55    inference(superposition,[],[f76,f24])).
% 1.45/0.55  fof(f34,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0) )),
% 1.45/0.55    inference(cnf_transformation,[],[f21])).
% 1.45/0.55  fof(f21,plain,(
% 1.45/0.55    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 1.45/0.55    inference(ennf_transformation,[],[f11])).
% 1.45/0.55  fof(f11,axiom,(
% 1.45/0.55    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).
% 1.45/0.55  fof(f139,plain,(
% 1.45/0.55    ~r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 1.45/0.55    inference(superposition,[],[f130,f24])).
% 1.45/0.55  fof(f130,plain,(
% 1.45/0.55    ( ! [X0] : (~r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_tarski(sK1,X0))) | k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) )),
% 1.45/0.55    inference(superposition,[],[f33,f110])).
% 1.45/0.55  fof(f33,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0) )),
% 1.45/0.55    inference(cnf_transformation,[],[f21])).
% 1.45/0.55  fof(f70,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.45/0.55    inference(definition_unfolding,[],[f29,f69,f67,f69,f66])).
% 1.45/0.55  fof(f67,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.45/0.55    inference(definition_unfolding,[],[f27,f66])).
% 1.45/0.55  fof(f27,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.45/0.55    inference(cnf_transformation,[],[f16])).
% 1.45/0.55  fof(f16,axiom,(
% 1.45/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.45/0.55  fof(f29,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.45/0.55    inference(cnf_transformation,[],[f12])).
% 1.45/0.55  fof(f12,axiom,(
% 1.45/0.55    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 1.45/0.55  fof(f383,plain,(
% 1.45/0.55    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))),
% 1.45/0.55    inference(superposition,[],[f93,f364])).
% 1.45/0.55  fof(f93,plain,(
% 1.45/0.55    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 1.45/0.55    inference(equality_resolution,[],[f73])).
% 1.45/0.55  fof(f73,plain,(
% 1.45/0.55    ( ! [X0,X1] : (X0 != X1 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 1.45/0.55    inference(definition_unfolding,[],[f38,f69,f68,f69,f69])).
% 1.45/0.55  fof(f68,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.45/0.55    inference(definition_unfolding,[],[f30,f67])).
% 1.45/0.55  fof(f30,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.45/0.55    inference(cnf_transformation,[],[f1])).
% 1.45/0.55  fof(f1,axiom,(
% 1.45/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.45/0.55  fof(f38,plain,(
% 1.45/0.55    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.45/0.55    inference(cnf_transformation,[],[f13])).
% 1.45/0.55  fof(f13,axiom,(
% 1.45/0.55    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.45/0.55  % SZS output end Proof for theBenchmark
% 1.45/0.55  % (19031)------------------------------
% 1.45/0.55  % (19031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (19031)Termination reason: Refutation
% 1.45/0.55  
% 1.45/0.55  % (19031)Memory used [KB]: 2046
% 1.45/0.55  % (19031)Time elapsed: 0.055 s
% 1.45/0.55  % (19031)------------------------------
% 1.45/0.55  % (19031)------------------------------
% 1.45/0.55  % (19026)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.45/0.55  % (19012)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.45/0.55  % (19009)Success in time 0.182 s
%------------------------------------------------------------------------------
