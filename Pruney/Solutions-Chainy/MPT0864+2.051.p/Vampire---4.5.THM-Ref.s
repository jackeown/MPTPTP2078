%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:38 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 519 expanded)
%              Number of leaves         :   19 ( 167 expanded)
%              Depth                    :   17
%              Number of atoms          :  165 ( 668 expanded)
%              Number of equality atoms :   94 ( 550 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f286,plain,(
    $false ),
    inference(resolution,[],[f273,f103])).

fof(f103,plain,(
    ! [X6,X4,X2,X3,X1] : r2_hidden(X6,k6_enumset1(X6,X6,X6,X6,X1,X2,X3,X4)) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X6,X4,X2,X5,X3,X1] :
      ( r2_hidden(X6,X5)
      | k6_enumset1(X6,X6,X6,X6,X1,X2,X3,X4) != X5 ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( X0 != X6
      | r2_hidden(X6,X5)
      | k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) != X5 ) ),
    inference(definition_unfolding,[],[f58,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f50,f63])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( X0 != X6
      | r2_hidden(X6,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

fof(f273,plain,(
    ! [X4] : ~ r2_hidden(sK2,X4) ),
    inference(subsumption_resolution,[],[f271,f95])).

fof(f95,plain,(
    ! [X6,X2,X0,X3,X1] : r2_hidden(X6,k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X6)) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X6,X2,X0,X5,X3,X1] :
      ( r2_hidden(X6,X5)
      | k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X6) != X5 ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( X4 != X6
      | r2_hidden(X6,X5)
      | k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) != X5 ) ),
    inference(definition_unfolding,[],[f62,f65])).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( X4 != X6
      | r2_hidden(X6,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f271,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(sK2,X4) ) ),
    inference(backward_demodulation,[],[f236,f259])).

fof(f259,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f256,f169])).

fof(f169,plain,(
    ! [X0,X1] : r2_hidden(X0,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(resolution,[],[f74,f106])).

fof(f106,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(backward_demodulation,[],[f71,f73])).

fof(f73,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f45,f65])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f27,f69])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f70])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f68])).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f256,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | sK0 = sK1 ) ),
    inference(subsumption_resolution,[],[f255,f95])).

fof(f255,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(sK1,X3)
      | sK0 = sK1 ) ),
    inference(subsumption_resolution,[],[f251,f207])).

fof(f207,plain,(
    ! [X0,X1] : k1_xboole_0 != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(subsumption_resolution,[],[f206,f173])).

fof(f173,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k4_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) ),
    inference(resolution,[],[f77,f106])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f40,f68])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f206,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)
      | ~ r2_hidden(X1,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k4_xboole_0(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) ),
    inference(superposition,[],[f80,f105])).

fof(f105,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(backward_demodulation,[],[f72,f73])).

fof(f72,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f28,f69])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f43,f68,f68])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f251,plain,(
    ! [X3] :
      ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
      | ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(sK1,X3)
      | sK0 = sK1 ) ),
    inference(resolution,[],[f171,f129])).

fof(f129,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK0,k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(sK0,X3)
      | ~ r2_hidden(sK1,X2)
      | sK0 = sK1 ) ),
    inference(superposition,[],[f48,f117])).

fof(f117,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | sK0 = sK1 ),
    inference(superposition,[],[f25,f115])).

fof(f115,plain,
    ( sK0 = sK2
    | sK0 = sK1 ),
    inference(superposition,[],[f114,f113])).

fof(f113,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f24,f112])).

fof(f112,plain,(
    sK1 = k1_mcart_1(sK0) ),
    inference(superposition,[],[f32,f25])).

fof(f32,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f24,plain,
    ( sK0 = k1_mcart_1(sK0)
    | sK0 = k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f114,plain,(
    sK2 = k2_mcart_1(sK0) ),
    inference(superposition,[],[f33,f25])).

fof(f33,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f18])).

fof(f25,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f171,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k2_zfmisc_1(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))
      | k1_xboole_0 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ) ),
    inference(resolution,[],[f75,f35])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f70])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f236,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(sK2,X4) ) ),
    inference(subsumption_resolution,[],[f232,f207])).

fof(f232,plain,(
    ! [X4] :
      ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
      | ~ r2_hidden(sK2,X4)
      | ~ r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ) ),
    inference(resolution,[],[f170,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK2,X1)
      | ~ r2_hidden(sK1,X0) ) ),
    inference(superposition,[],[f48,f25])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))
      | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(resolution,[],[f75,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:58:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.50  % (12637)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (12654)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (12645)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (12643)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (12652)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (12640)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (12635)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (12641)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (12640)Refutation not found, incomplete strategy% (12640)------------------------------
% 0.21/0.51  % (12640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12640)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (12640)Memory used [KB]: 10618
% 0.21/0.51  % (12640)Time elapsed: 0.116 s
% 0.21/0.51  % (12640)------------------------------
% 0.21/0.51  % (12640)------------------------------
% 0.21/0.51  % (12641)Refutation not found, incomplete strategy% (12641)------------------------------
% 0.21/0.51  % (12641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12641)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (12641)Memory used [KB]: 10618
% 0.21/0.51  % (12641)Time elapsed: 0.116 s
% 0.21/0.51  % (12641)------------------------------
% 0.21/0.51  % (12641)------------------------------
% 0.21/0.52  % (12658)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (12642)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (12659)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (12646)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (12655)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (12651)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (12645)Refutation not found, incomplete strategy% (12645)------------------------------
% 0.21/0.53  % (12645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12645)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12645)Memory used [KB]: 6140
% 0.21/0.53  % (12645)Time elapsed: 0.004 s
% 0.21/0.53  % (12645)------------------------------
% 0.21/0.53  % (12645)------------------------------
% 0.21/0.53  % (12630)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (12630)Refutation not found, incomplete strategy% (12630)------------------------------
% 0.21/0.53  % (12630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12630)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12630)Memory used [KB]: 1663
% 0.21/0.53  % (12630)Time elapsed: 0.123 s
% 0.21/0.53  % (12630)------------------------------
% 0.21/0.53  % (12630)------------------------------
% 0.21/0.53  % (12633)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (12632)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (12634)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (12631)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (12652)Refutation not found, incomplete strategy% (12652)------------------------------
% 0.21/0.54  % (12652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12644)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (12656)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (12647)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (12648)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (12638)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (12657)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (12647)Refutation not found, incomplete strategy% (12647)------------------------------
% 0.21/0.54  % (12647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12636)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (12639)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (12650)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (12649)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (12653)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (12647)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (12647)Memory used [KB]: 10618
% 0.21/0.55  % (12647)Time elapsed: 0.141 s
% 0.21/0.55  % (12647)------------------------------
% 0.21/0.55  % (12647)------------------------------
% 0.21/0.55  % (12652)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (12652)Memory used [KB]: 10746
% 0.21/0.55  % (12652)Time elapsed: 0.114 s
% 0.21/0.55  % (12652)------------------------------
% 0.21/0.55  % (12652)------------------------------
% 0.21/0.56  % (12639)Refutation not found, incomplete strategy% (12639)------------------------------
% 0.21/0.56  % (12639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (12639)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (12639)Memory used [KB]: 10618
% 0.21/0.56  % (12639)Time elapsed: 0.159 s
% 0.21/0.56  % (12639)------------------------------
% 0.21/0.56  % (12639)------------------------------
% 1.61/0.57  % (12636)Refutation found. Thanks to Tanya!
% 1.61/0.57  % SZS status Theorem for theBenchmark
% 1.61/0.58  % SZS output start Proof for theBenchmark
% 1.61/0.58  fof(f286,plain,(
% 1.61/0.58    $false),
% 1.61/0.58    inference(resolution,[],[f273,f103])).
% 1.61/0.58  fof(f103,plain,(
% 1.61/0.58    ( ! [X6,X4,X2,X3,X1] : (r2_hidden(X6,k6_enumset1(X6,X6,X6,X6,X1,X2,X3,X4))) )),
% 1.61/0.58    inference(equality_resolution,[],[f102])).
% 1.61/0.58  fof(f102,plain,(
% 1.61/0.58    ( ! [X6,X4,X2,X5,X3,X1] : (r2_hidden(X6,X5) | k6_enumset1(X6,X6,X6,X6,X1,X2,X3,X4) != X5) )),
% 1.61/0.58    inference(equality_resolution,[],[f86])).
% 1.61/0.58  fof(f86,plain,(
% 1.61/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (X0 != X6 | r2_hidden(X6,X5) | k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) != X5) )),
% 1.61/0.58    inference(definition_unfolding,[],[f58,f65])).
% 1.61/0.58  fof(f65,plain,(
% 1.61/0.58    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.61/0.58    inference(definition_unfolding,[],[f49,f64])).
% 1.61/0.58  fof(f64,plain,(
% 1.61/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.61/0.58    inference(definition_unfolding,[],[f50,f63])).
% 1.61/0.58  fof(f63,plain,(
% 1.61/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f10])).
% 1.61/0.58  fof(f10,axiom,(
% 1.61/0.58    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.61/0.58  fof(f50,plain,(
% 1.61/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f9])).
% 1.61/0.58  fof(f9,axiom,(
% 1.61/0.58    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.61/0.58  fof(f49,plain,(
% 1.61/0.58    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f8])).
% 1.61/0.58  fof(f8,axiom,(
% 1.61/0.58    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.61/0.58  fof(f58,plain,(
% 1.61/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (X0 != X6 | r2_hidden(X6,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 1.61/0.58    inference(cnf_transformation,[],[f23])).
% 1.61/0.58  fof(f23,plain,(
% 1.61/0.58    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 1.61/0.58    inference(ennf_transformation,[],[f17])).
% 1.61/0.58  fof(f17,axiom,(
% 1.61/0.58    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).
% 1.61/0.58  fof(f273,plain,(
% 1.61/0.58    ( ! [X4] : (~r2_hidden(sK2,X4)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f271,f95])).
% 1.61/0.58  fof(f95,plain,(
% 1.61/0.58    ( ! [X6,X2,X0,X3,X1] : (r2_hidden(X6,k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X6))) )),
% 1.61/0.58    inference(equality_resolution,[],[f94])).
% 1.61/0.58  fof(f94,plain,(
% 1.61/0.58    ( ! [X6,X2,X0,X5,X3,X1] : (r2_hidden(X6,X5) | k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X6) != X5) )),
% 1.61/0.58    inference(equality_resolution,[],[f82])).
% 1.61/0.58  fof(f82,plain,(
% 1.61/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (X4 != X6 | r2_hidden(X6,X5) | k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) != X5) )),
% 1.61/0.58    inference(definition_unfolding,[],[f62,f65])).
% 1.61/0.58  fof(f62,plain,(
% 1.61/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (X4 != X6 | r2_hidden(X6,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 1.61/0.58    inference(cnf_transformation,[],[f23])).
% 1.61/0.58  fof(f271,plain,(
% 1.61/0.58    ( ! [X4] : (~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK2,X4)) )),
% 1.61/0.58    inference(backward_demodulation,[],[f236,f259])).
% 1.61/0.58  fof(f259,plain,(
% 1.61/0.58    sK0 = sK1),
% 1.61/0.58    inference(resolution,[],[f256,f169])).
% 1.61/0.58  fof(f169,plain,(
% 1.61/0.58    ( ! [X0,X1] : (r2_hidden(X0,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) )),
% 1.61/0.58    inference(resolution,[],[f74,f106])).
% 1.61/0.58  fof(f106,plain,(
% 1.61/0.58    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 1.61/0.58    inference(backward_demodulation,[],[f71,f73])).
% 1.61/0.58  fof(f73,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.61/0.58    inference(definition_unfolding,[],[f31,f69])).
% 1.61/0.58  fof(f69,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.61/0.58    inference(definition_unfolding,[],[f29,f68])).
% 1.61/0.58  fof(f68,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.61/0.58    inference(definition_unfolding,[],[f30,f67])).
% 1.61/0.58  fof(f67,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.61/0.58    inference(definition_unfolding,[],[f38,f66])).
% 1.61/0.58  fof(f66,plain,(
% 1.61/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.61/0.58    inference(definition_unfolding,[],[f45,f65])).
% 1.61/0.58  fof(f45,plain,(
% 1.61/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f7])).
% 1.61/0.58  fof(f7,axiom,(
% 1.61/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.61/0.58  fof(f38,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f6])).
% 1.61/0.58  fof(f6,axiom,(
% 1.61/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.61/0.58  fof(f30,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f5])).
% 1.61/0.58  fof(f5,axiom,(
% 1.61/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.61/0.58  fof(f29,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.61/0.58    inference(cnf_transformation,[],[f12])).
% 1.61/0.58  fof(f12,axiom,(
% 1.61/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.61/0.58  fof(f31,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.61/0.58    inference(cnf_transformation,[],[f3])).
% 1.61/0.58  fof(f3,axiom,(
% 1.61/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.61/0.58  fof(f71,plain,(
% 1.61/0.58    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.61/0.58    inference(definition_unfolding,[],[f27,f69])).
% 1.61/0.58  fof(f27,plain,(
% 1.61/0.58    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.61/0.58    inference(cnf_transformation,[],[f2])).
% 1.61/0.58  fof(f2,axiom,(
% 1.61/0.58    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.61/0.58  fof(f74,plain,(
% 1.61/0.58    ( ! [X0,X1] : (~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.61/0.58    inference(definition_unfolding,[],[f37,f70])).
% 1.61/0.58  fof(f70,plain,(
% 1.61/0.58    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.61/0.58    inference(definition_unfolding,[],[f26,f68])).
% 1.61/0.58  fof(f26,plain,(
% 1.61/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f4])).
% 1.61/0.58  fof(f4,axiom,(
% 1.61/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.61/0.58  fof(f37,plain,(
% 1.61/0.58    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f11])).
% 1.61/0.58  fof(f11,axiom,(
% 1.61/0.58    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.61/0.58  fof(f256,plain,(
% 1.61/0.58    ( ! [X3] : (~r2_hidden(sK1,X3) | sK0 = sK1) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f255,f95])).
% 1.61/0.58  fof(f255,plain,(
% 1.61/0.58    ( ! [X3] : (~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK1,X3) | sK0 = sK1) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f251,f207])).
% 1.61/0.58  fof(f207,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k1_xboole_0 != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f206,f173])).
% 1.61/0.58  fof(f173,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),k4_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) )),
% 1.61/0.58    inference(resolution,[],[f77,f106])).
% 1.61/0.58  fof(f77,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 1.61/0.58    inference(definition_unfolding,[],[f40,f68])).
% 1.61/0.58  fof(f40,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f15])).
% 1.61/0.58  fof(f15,axiom,(
% 1.61/0.58    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.61/0.58  fof(f206,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (k1_xboole_0 != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) | ~r2_hidden(X1,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k4_xboole_0(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 1.61/0.58    inference(superposition,[],[f80,f105])).
% 1.61/0.58  fof(f105,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 1.61/0.58    inference(backward_demodulation,[],[f72,f73])).
% 1.61/0.58  fof(f72,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.61/0.58    inference(definition_unfolding,[],[f28,f69])).
% 1.61/0.58  fof(f28,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 1.61/0.58    inference(cnf_transformation,[],[f1])).
% 1.61/0.58  fof(f1,axiom,(
% 1.61/0.58    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.61/0.58  fof(f80,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2)) )),
% 1.61/0.58    inference(definition_unfolding,[],[f43,f68,f68])).
% 1.61/0.58  fof(f43,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f16])).
% 1.61/0.58  fof(f16,axiom,(
% 1.61/0.58    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 1.61/0.58  fof(f251,plain,(
% 1.61/0.58    ( ! [X3] : (k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK1,X3) | sK0 = sK1) )),
% 1.61/0.58    inference(resolution,[],[f171,f129])).
% 1.61/0.58  fof(f129,plain,(
% 1.61/0.58    ( ! [X2,X3] : (r2_hidden(sK0,k2_zfmisc_1(X2,X3)) | ~r2_hidden(sK0,X3) | ~r2_hidden(sK1,X2) | sK0 = sK1) )),
% 1.61/0.58    inference(superposition,[],[f48,f117])).
% 1.61/0.58  fof(f117,plain,(
% 1.61/0.58    sK0 = k4_tarski(sK1,sK0) | sK0 = sK1),
% 1.61/0.58    inference(superposition,[],[f25,f115])).
% 1.61/0.58  fof(f115,plain,(
% 1.61/0.58    sK0 = sK2 | sK0 = sK1),
% 1.61/0.58    inference(superposition,[],[f114,f113])).
% 1.61/0.58  fof(f113,plain,(
% 1.61/0.58    sK0 = k2_mcart_1(sK0) | sK0 = sK1),
% 1.61/0.58    inference(backward_demodulation,[],[f24,f112])).
% 1.61/0.58  fof(f112,plain,(
% 1.61/0.58    sK1 = k1_mcart_1(sK0)),
% 1.61/0.58    inference(superposition,[],[f32,f25])).
% 1.61/0.58  fof(f32,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.61/0.58    inference(cnf_transformation,[],[f18])).
% 1.61/0.58  fof(f18,axiom,(
% 1.61/0.58    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.61/0.58  fof(f24,plain,(
% 1.61/0.58    sK0 = k1_mcart_1(sK0) | sK0 = k2_mcart_1(sK0)),
% 1.61/0.58    inference(cnf_transformation,[],[f21])).
% 1.61/0.58  fof(f21,plain,(
% 1.61/0.58    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 1.61/0.58    inference(ennf_transformation,[],[f20])).
% 1.61/0.58  fof(f20,negated_conjecture,(
% 1.61/0.58    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.61/0.58    inference(negated_conjecture,[],[f19])).
% 1.61/0.58  fof(f19,conjecture,(
% 1.61/0.58    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.61/0.58  fof(f114,plain,(
% 1.61/0.58    sK2 = k2_mcart_1(sK0)),
% 1.61/0.58    inference(superposition,[],[f33,f25])).
% 1.61/0.58  fof(f33,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.61/0.58    inference(cnf_transformation,[],[f18])).
% 1.61/0.58  fof(f25,plain,(
% 1.61/0.58    sK0 = k4_tarski(sK1,sK2)),
% 1.61/0.58    inference(cnf_transformation,[],[f21])).
% 1.61/0.58  fof(f48,plain,(
% 1.61/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f13])).
% 1.61/0.58  fof(f13,axiom,(
% 1.61/0.58    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.61/0.58  fof(f171,plain,(
% 1.61/0.58    ( ! [X2,X3] : (~r2_hidden(X2,k2_zfmisc_1(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) | k1_xboole_0 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) )),
% 1.61/0.58    inference(resolution,[],[f75,f35])).
% 1.61/0.58  fof(f35,plain,(
% 1.61/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0) )),
% 1.61/0.58    inference(cnf_transformation,[],[f22])).
% 1.76/0.58  fof(f22,plain,(
% 1.76/0.58    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 1.76/0.58    inference(ennf_transformation,[],[f14])).
% 1.76/0.58  fof(f14,axiom,(
% 1.76/0.58    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 1.76/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).
% 1.76/0.58  fof(f75,plain,(
% 1.76/0.58    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.76/0.58    inference(definition_unfolding,[],[f36,f70])).
% 1.76/0.58  fof(f36,plain,(
% 1.76/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.76/0.58    inference(cnf_transformation,[],[f11])).
% 1.76/0.58  fof(f236,plain,(
% 1.76/0.58    ( ! [X4] : (~r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK2,X4)) )),
% 1.76/0.58    inference(subsumption_resolution,[],[f232,f207])).
% 1.76/0.58  fof(f232,plain,(
% 1.76/0.58    ( ! [X4] : (k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~r2_hidden(sK2,X4) | ~r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) )),
% 1.76/0.58    inference(resolution,[],[f170,f128])).
% 1.76/0.58  fof(f128,plain,(
% 1.76/0.58    ( ! [X0,X1] : (r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK2,X1) | ~r2_hidden(sK1,X0)) )),
% 1.76/0.58    inference(superposition,[],[f48,f25])).
% 1.76/0.58  fof(f170,plain,(
% 1.76/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.76/0.58    inference(resolution,[],[f75,f34])).
% 1.76/0.58  fof(f34,plain,(
% 1.76/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0) )),
% 1.76/0.58    inference(cnf_transformation,[],[f22])).
% 1.76/0.58  % SZS output end Proof for theBenchmark
% 1.76/0.58  % (12636)------------------------------
% 1.76/0.58  % (12636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.58  % (12636)Termination reason: Refutation
% 1.76/0.58  
% 1.76/0.58  % (12636)Memory used [KB]: 6396
% 1.76/0.58  % (12636)Time elapsed: 0.166 s
% 1.76/0.58  % (12636)------------------------------
% 1.76/0.58  % (12636)------------------------------
% 1.76/0.58  % (12629)Success in time 0.227 s
%------------------------------------------------------------------------------
