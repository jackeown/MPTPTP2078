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
% DateTime   : Thu Dec  3 12:58:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 652 expanded)
%              Number of leaves         :   20 ( 213 expanded)
%              Depth                    :   17
%              Number of atoms          :  142 ( 750 expanded)
%              Number of equality atoms :  113 ( 709 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(subsumption_resolution,[],[f172,f125])).

fof(f125,plain,(
    ! [X1] : k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(backward_demodulation,[],[f106,f124])).

fof(f124,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f123,f74])).

fof(f74,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f31,f70])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f50,f63])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f123,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(superposition,[],[f75,f73])).

fof(f73,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f30,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f68])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

% (26891)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f75,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) ),
    inference(definition_unfolding,[],[f32,f71,f69])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f36,f70])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f106,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(forward_demodulation,[],[f94,f74])).

fof(f94,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f44,f72,f71,f72,f72])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f68])).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f172,plain,(
    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f169,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))
      | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(resolution,[],[f77,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

% (26904)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f72])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f169,plain,(
    ! [X0] : r2_hidden(sK0,k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
    inference(superposition,[],[f140,f159])).

fof(f159,plain,(
    sK0 = k4_tarski(sK0,sK2) ),
    inference(backward_demodulation,[],[f28,f158])).

fof(f158,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f157,f125])).

fof(f157,plain,
    ( sK0 = sK1
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f153,f121])).

fof(f121,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k2_zfmisc_1(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))
      | k1_xboole_0 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ) ),
    inference(resolution,[],[f77,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f153,plain,(
    ! [X1] :
      ( r2_hidden(sK0,k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
      | sK0 = sK1 ) ),
    inference(superposition,[],[f136,f117])).

fof(f117,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | sK0 = sK1 ),
    inference(superposition,[],[f28,f115])).

fof(f115,plain,
    ( sK0 = sK2
    | sK0 = sK1 ),
    inference(superposition,[],[f114,f113])).

fof(f113,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f27,f112])).

fof(f112,plain,(
    sK1 = k1_mcart_1(sK0) ),
    inference(superposition,[],[f37,f28])).

fof(f37,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f27,plain,
    ( sK0 = k1_mcart_1(sK0)
    | sK0 = k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f114,plain,(
    sK2 = k2_mcart_1(sK0) ),
    inference(superposition,[],[f38,f28])).

fof(f38,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f19])).

fof(f136,plain,(
    ! [X6,X4,X5] : r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X6),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5))) ),
    inference(superposition,[],[f104,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f47,f68,f72,f68])).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f104,plain,(
    ! [X6,X4,X2,X3,X1] : r2_hidden(X6,k6_enumset1(X6,X6,X6,X6,X1,X2,X3,X4)) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
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

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( X0 != X6
      | r2_hidden(X6,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

fof(f28,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f140,plain,(
    ! [X17,X18,X16] : r2_hidden(k4_tarski(X18,X17),k2_zfmisc_1(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X18),k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X17))) ),
    inference(superposition,[],[f96,f80])).

fof(f96,plain,(
    ! [X6,X2,X0,X3,X1] : r2_hidden(X6,k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X6)) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
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
    inference(cnf_transformation,[],[f26])).

% (26897)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:34:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.56  % (26886)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (26886)Refutation not found, incomplete strategy% (26886)------------------------------
% 0.22/0.56  % (26886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (26878)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.57  % (26886)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (26886)Memory used [KB]: 10618
% 0.22/0.57  % (26886)Time elapsed: 0.126 s
% 0.22/0.57  % (26886)------------------------------
% 0.22/0.57  % (26886)------------------------------
% 0.22/0.57  % (26887)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.57  % (26887)Refutation not found, incomplete strategy% (26887)------------------------------
% 0.22/0.57  % (26887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (26887)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (26887)Memory used [KB]: 10618
% 0.22/0.57  % (26887)Time elapsed: 0.131 s
% 0.22/0.57  % (26887)------------------------------
% 0.22/0.57  % (26887)------------------------------
% 0.22/0.57  % (26879)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.58  % (26883)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.58  % (26906)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.59  % (26883)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 1.82/0.59  % (26880)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.82/0.59  % SZS output start Proof for theBenchmark
% 1.82/0.59  fof(f173,plain,(
% 1.82/0.59    $false),
% 1.82/0.59    inference(subsumption_resolution,[],[f172,f125])).
% 1.82/0.59  fof(f125,plain,(
% 1.82/0.59    ( ! [X1] : (k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 1.82/0.59    inference(backward_demodulation,[],[f106,f124])).
% 1.82/0.59  fof(f124,plain,(
% 1.82/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.82/0.59    inference(forward_demodulation,[],[f123,f74])).
% 1.82/0.59  fof(f74,plain,(
% 1.82/0.59    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.82/0.59    inference(definition_unfolding,[],[f31,f70])).
% 1.82/0.59  fof(f70,plain,(
% 1.82/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.82/0.59    inference(definition_unfolding,[],[f34,f68])).
% 1.82/0.59  fof(f68,plain,(
% 1.82/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.82/0.59    inference(definition_unfolding,[],[f35,f67])).
% 1.82/0.59  fof(f67,plain,(
% 1.82/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.82/0.59    inference(definition_unfolding,[],[f45,f66])).
% 1.82/0.59  fof(f66,plain,(
% 1.82/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.82/0.59    inference(definition_unfolding,[],[f48,f65])).
% 1.82/0.60  fof(f65,plain,(
% 1.82/0.60    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.82/0.60    inference(definition_unfolding,[],[f49,f64])).
% 1.82/0.60  fof(f64,plain,(
% 1.82/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.82/0.60    inference(definition_unfolding,[],[f50,f63])).
% 1.82/0.60  fof(f63,plain,(
% 1.82/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f11])).
% 1.82/0.60  fof(f11,axiom,(
% 1.82/0.60    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.82/0.60  fof(f50,plain,(
% 1.82/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f10])).
% 1.82/0.60  fof(f10,axiom,(
% 1.82/0.60    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.82/0.60  fof(f49,plain,(
% 1.82/0.60    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f9])).
% 1.82/0.60  fof(f9,axiom,(
% 1.82/0.60    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.82/0.60  fof(f48,plain,(
% 1.82/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f8])).
% 1.82/0.60  fof(f8,axiom,(
% 1.82/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.82/0.60  fof(f45,plain,(
% 1.82/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f7])).
% 1.82/0.60  fof(f7,axiom,(
% 1.82/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.82/0.60  fof(f35,plain,(
% 1.82/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f6])).
% 1.82/0.60  fof(f6,axiom,(
% 1.82/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.82/0.60  fof(f34,plain,(
% 1.82/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.82/0.60    inference(cnf_transformation,[],[f18])).
% 1.82/0.60  fof(f18,axiom,(
% 1.82/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.82/0.60  fof(f31,plain,(
% 1.82/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.82/0.60    inference(cnf_transformation,[],[f23])).
% 1.82/0.60  fof(f23,plain,(
% 1.82/0.60    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.82/0.60    inference(rectify,[],[f2])).
% 1.82/0.60  fof(f2,axiom,(
% 1.82/0.60    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.82/0.60  fof(f123,plain,(
% 1.82/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) )),
% 1.82/0.60    inference(superposition,[],[f75,f73])).
% 1.82/0.60  fof(f73,plain,(
% 1.82/0.60    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.82/0.60    inference(definition_unfolding,[],[f30,f69])).
% 1.82/0.60  fof(f69,plain,(
% 1.82/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.82/0.60    inference(definition_unfolding,[],[f33,f68])).
% 1.82/0.60  fof(f33,plain,(
% 1.82/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.82/0.60    inference(cnf_transformation,[],[f13])).
% 1.82/0.60  fof(f13,axiom,(
% 1.82/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.82/0.60  fof(f30,plain,(
% 1.82/0.60    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.82/0.60    inference(cnf_transformation,[],[f22])).
% 1.82/0.60  fof(f22,plain,(
% 1.82/0.60    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.82/0.60    inference(rectify,[],[f1])).
% 1.82/0.60  fof(f1,axiom,(
% 1.82/0.60    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.82/0.60  % (26891)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.82/0.60  fof(f75,plain,(
% 1.82/0.60    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) )),
% 1.82/0.60    inference(definition_unfolding,[],[f32,f71,f69])).
% 1.82/0.60  fof(f71,plain,(
% 1.82/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.82/0.60    inference(definition_unfolding,[],[f36,f70])).
% 1.82/0.60  fof(f36,plain,(
% 1.82/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.82/0.60    inference(cnf_transformation,[],[f3])).
% 1.82/0.60  fof(f3,axiom,(
% 1.82/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.82/0.60  fof(f32,plain,(
% 1.82/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 1.82/0.60    inference(cnf_transformation,[],[f4])).
% 1.82/0.60  fof(f4,axiom,(
% 1.82/0.60    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.82/0.60  fof(f106,plain,(
% 1.82/0.60    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 1.82/0.60    inference(forward_demodulation,[],[f94,f74])).
% 1.82/0.60  fof(f94,plain,(
% 1.82/0.60    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 1.82/0.60    inference(equality_resolution,[],[f78])).
% 1.82/0.60  fof(f78,plain,(
% 1.82/0.60    ( ! [X0,X1] : (X0 != X1 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 1.82/0.60    inference(definition_unfolding,[],[f44,f72,f71,f72,f72])).
% 1.82/0.60  fof(f72,plain,(
% 1.82/0.60    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.82/0.60    inference(definition_unfolding,[],[f29,f68])).
% 1.82/0.60  fof(f29,plain,(
% 1.82/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f5])).
% 1.82/0.60  fof(f5,axiom,(
% 1.82/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.82/0.60  fof(f44,plain,(
% 1.82/0.60    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.82/0.60    inference(cnf_transformation,[],[f15])).
% 1.82/0.60  fof(f15,axiom,(
% 1.82/0.60    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.82/0.60  fof(f172,plain,(
% 1.82/0.60    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.82/0.60    inference(resolution,[],[f169,f120])).
% 1.82/0.60  fof(f120,plain,(
% 1.82/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.82/0.60    inference(resolution,[],[f77,f39])).
% 1.82/0.60  fof(f39,plain,(
% 1.82/0.60    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0) )),
% 1.82/0.60    inference(cnf_transformation,[],[f25])).
% 1.82/0.60  % (26904)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.82/0.60  fof(f25,plain,(
% 1.82/0.60    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 1.82/0.60    inference(ennf_transformation,[],[f14])).
% 1.82/0.60  fof(f14,axiom,(
% 1.82/0.60    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).
% 1.82/0.60  fof(f77,plain,(
% 1.82/0.60    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.82/0.60    inference(definition_unfolding,[],[f41,f72])).
% 1.82/0.60  fof(f41,plain,(
% 1.82/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f12])).
% 1.82/0.60  fof(f12,axiom,(
% 1.82/0.60    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.82/0.60  fof(f169,plain,(
% 1.82/0.60    ( ! [X0] : (r2_hidden(sK0,k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) )),
% 1.82/0.60    inference(superposition,[],[f140,f159])).
% 1.82/0.60  fof(f159,plain,(
% 1.82/0.60    sK0 = k4_tarski(sK0,sK2)),
% 1.82/0.60    inference(backward_demodulation,[],[f28,f158])).
% 1.82/0.60  fof(f158,plain,(
% 1.82/0.60    sK0 = sK1),
% 1.82/0.60    inference(subsumption_resolution,[],[f157,f125])).
% 1.82/0.60  fof(f157,plain,(
% 1.82/0.60    sK0 = sK1 | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.82/0.60    inference(resolution,[],[f153,f121])).
% 1.82/0.60  fof(f121,plain,(
% 1.82/0.60    ( ! [X2,X3] : (~r2_hidden(X2,k2_zfmisc_1(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) | k1_xboole_0 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) )),
% 1.82/0.60    inference(resolution,[],[f77,f40])).
% 1.82/0.60  fof(f40,plain,(
% 1.82/0.60    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0) )),
% 1.82/0.60    inference(cnf_transformation,[],[f25])).
% 1.82/0.60  fof(f153,plain,(
% 1.82/0.60    ( ! [X1] : (r2_hidden(sK0,k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | sK0 = sK1) )),
% 1.82/0.60    inference(superposition,[],[f136,f117])).
% 1.82/0.60  fof(f117,plain,(
% 1.82/0.60    sK0 = k4_tarski(sK1,sK0) | sK0 = sK1),
% 1.82/0.60    inference(superposition,[],[f28,f115])).
% 1.82/0.60  fof(f115,plain,(
% 1.82/0.60    sK0 = sK2 | sK0 = sK1),
% 1.82/0.60    inference(superposition,[],[f114,f113])).
% 1.82/0.60  fof(f113,plain,(
% 1.82/0.60    sK0 = k2_mcart_1(sK0) | sK0 = sK1),
% 1.82/0.60    inference(backward_demodulation,[],[f27,f112])).
% 1.82/0.60  fof(f112,plain,(
% 1.82/0.60    sK1 = k1_mcart_1(sK0)),
% 1.82/0.60    inference(superposition,[],[f37,f28])).
% 1.82/0.60  fof(f37,plain,(
% 1.82/0.60    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.82/0.60    inference(cnf_transformation,[],[f19])).
% 1.82/0.60  fof(f19,axiom,(
% 1.82/0.60    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.82/0.60  fof(f27,plain,(
% 1.82/0.60    sK0 = k1_mcart_1(sK0) | sK0 = k2_mcart_1(sK0)),
% 1.82/0.60    inference(cnf_transformation,[],[f24])).
% 1.82/0.60  fof(f24,plain,(
% 1.82/0.60    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 1.82/0.60    inference(ennf_transformation,[],[f21])).
% 1.82/0.60  fof(f21,negated_conjecture,(
% 1.82/0.60    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.82/0.60    inference(negated_conjecture,[],[f20])).
% 1.82/0.60  fof(f20,conjecture,(
% 1.82/0.60    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.82/0.60  fof(f114,plain,(
% 1.82/0.60    sK2 = k2_mcart_1(sK0)),
% 1.82/0.60    inference(superposition,[],[f38,f28])).
% 1.82/0.60  fof(f38,plain,(
% 1.82/0.60    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.82/0.60    inference(cnf_transformation,[],[f19])).
% 1.82/0.60  fof(f136,plain,(
% 1.82/0.60    ( ! [X6,X4,X5] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X6),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5)))) )),
% 1.82/0.60    inference(superposition,[],[f104,f80])).
% 1.82/0.60  fof(f80,plain,(
% 1.82/0.60    ( ! [X2,X0,X1] : (k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 1.82/0.60    inference(definition_unfolding,[],[f47,f68,f72,f68])).
% 1.82/0.60  fof(f47,plain,(
% 1.82/0.60    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 1.82/0.60    inference(cnf_transformation,[],[f16])).
% 1.82/0.60  fof(f16,axiom,(
% 1.82/0.60    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 1.82/0.60  fof(f104,plain,(
% 1.82/0.60    ( ! [X6,X4,X2,X3,X1] : (r2_hidden(X6,k6_enumset1(X6,X6,X6,X6,X1,X2,X3,X4))) )),
% 1.82/0.60    inference(equality_resolution,[],[f103])).
% 1.82/0.60  fof(f103,plain,(
% 1.82/0.60    ( ! [X6,X4,X2,X5,X3,X1] : (r2_hidden(X6,X5) | k6_enumset1(X6,X6,X6,X6,X1,X2,X3,X4) != X5) )),
% 1.82/0.60    inference(equality_resolution,[],[f86])).
% 1.82/0.60  fof(f86,plain,(
% 1.82/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (X0 != X6 | r2_hidden(X6,X5) | k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) != X5) )),
% 1.82/0.60    inference(definition_unfolding,[],[f58,f65])).
% 1.82/0.60  fof(f58,plain,(
% 1.82/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (X0 != X6 | r2_hidden(X6,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 1.82/0.60    inference(cnf_transformation,[],[f26])).
% 1.82/0.60  fof(f26,plain,(
% 1.82/0.60    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 1.82/0.60    inference(ennf_transformation,[],[f17])).
% 1.82/0.60  fof(f17,axiom,(
% 1.82/0.60    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 1.82/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).
% 1.82/0.60  fof(f28,plain,(
% 1.82/0.60    sK0 = k4_tarski(sK1,sK2)),
% 1.82/0.60    inference(cnf_transformation,[],[f24])).
% 1.82/0.60  fof(f140,plain,(
% 1.82/0.60    ( ! [X17,X18,X16] : (r2_hidden(k4_tarski(X18,X17),k2_zfmisc_1(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X18),k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X17)))) )),
% 1.82/0.60    inference(superposition,[],[f96,f80])).
% 1.82/0.60  fof(f96,plain,(
% 1.82/0.60    ( ! [X6,X2,X0,X3,X1] : (r2_hidden(X6,k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X6))) )),
% 1.82/0.60    inference(equality_resolution,[],[f95])).
% 1.82/0.60  fof(f95,plain,(
% 1.82/0.60    ( ! [X6,X2,X0,X5,X3,X1] : (r2_hidden(X6,X5) | k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X6) != X5) )),
% 1.82/0.60    inference(equality_resolution,[],[f82])).
% 1.82/0.60  fof(f82,plain,(
% 1.82/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (X4 != X6 | r2_hidden(X6,X5) | k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) != X5) )),
% 1.82/0.60    inference(definition_unfolding,[],[f62,f65])).
% 1.82/0.60  fof(f62,plain,(
% 1.82/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (X4 != X6 | r2_hidden(X6,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 1.82/0.60    inference(cnf_transformation,[],[f26])).
% 1.82/0.60  % (26897)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.82/0.60  % SZS output end Proof for theBenchmark
% 1.82/0.60  % (26883)------------------------------
% 1.82/0.60  % (26883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.60  % (26883)Termination reason: Refutation
% 1.82/0.60  
% 1.82/0.60  % (26883)Memory used [KB]: 6396
% 1.82/0.60  % (26883)Time elapsed: 0.160 s
% 1.82/0.60  % (26883)------------------------------
% 1.82/0.60  % (26883)------------------------------
% 1.82/0.61  % (26882)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.82/0.61  % (26876)Success in time 0.241 s
%------------------------------------------------------------------------------
