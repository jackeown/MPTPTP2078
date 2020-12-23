%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:25 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 439 expanded)
%              Number of leaves         :   21 ( 138 expanded)
%              Depth                    :   19
%              Number of atoms          :  168 ( 537 expanded)
%              Number of equality atoms :   91 ( 410 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f644,plain,(
    $false ),
    inference(subsumption_resolution,[],[f95,f642])).

fof(f642,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(resolution,[],[f634,f87])).

fof(f87,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | k1_xboole_0 != k3_xboole_0(X2,X3) ) ),
    inference(inner_rewriting,[],[f86])).

fof(f86,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != k3_xboole_0(X2,X3)
      | ~ r2_hidden(X4,k3_xboole_0(X2,X3)) ) ),
    inference(resolution,[],[f58,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

% (29734)Refutation not found, incomplete strategy% (29734)------------------------------
% (29734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29734)Termination reason: Refutation not found, incomplete strategy

% (29734)Memory used [KB]: 10618
% (29734)Time elapsed: 0.157 s
% (29734)------------------------------
% (29734)------------------------------
fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f634,plain,(
    r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f625,f110])).

fof(f110,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f47,f109])).

fof(f109,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f106,f44])).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f106,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f52,f98])).

fof(f98,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f95,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f625,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f79,f622])).

fof(f622,plain,(
    k1_xboole_0 = k1_tarski(k1_xboole_0) ),
    inference(backward_demodulation,[],[f613,f621])).

fof(f621,plain,(
    k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f620,f41])).

fof(f41,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f620,plain,(
    k3_tarski(k1_xboole_0) = sK0 ),
    inference(superposition,[],[f195,f613])).

fof(f195,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(backward_demodulation,[],[f83,f194])).

fof(f194,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f193,f46])).

fof(f46,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f193,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k2_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f174,f71])).

fof(f71,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f49,f44])).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f174,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f53,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f83,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0)) ),
    inference(superposition,[],[f50,f45])).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f613,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f606,f96])).

fof(f96,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6) ),
    inference(backward_demodulation,[],[f91,f95])).

fof(f91,plain,(
    ! [X6] : k3_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f52,f71])).

fof(f606,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_xboole_0,k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f587,f604])).

fof(f604,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f599,f40])).

fof(f40,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f31])).

fof(f31,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f599,plain,(
    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(superposition,[],[f285,f587])).

fof(f285,plain,(
    ! [X10,X9] : k2_xboole_0(k4_xboole_0(X9,X10),X9) = X9 ),
    inference(backward_demodulation,[],[f208,f284])).

fof(f284,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k4_xboole_0(X6,X7)) = X6 ),
    inference(backward_demodulation,[],[f261,f269])).

fof(f269,plain,(
    ! [X6,X5] : k5_xboole_0(k3_xboole_0(X5,X6),k4_xboole_0(X5,X6)) = X5 ),
    inference(superposition,[],[f246,f52])).

fof(f246,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f240,f49])).

fof(f240,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f216,f71])).

fof(f216,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f64,f43])).

fof(f64,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f261,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k4_xboole_0(X6,X7)) = k5_xboole_0(k3_xboole_0(X6,X7),k4_xboole_0(X6,X7)) ),
    inference(backward_demodulation,[],[f186,f248])).

fof(f248,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f240,f52])).

fof(f186,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k4_xboole_0(X6,X7)) = k5_xboole_0(k5_xboole_0(X6,k4_xboole_0(X6,X7)),k4_xboole_0(X6,X7)) ),
    inference(superposition,[],[f53,f115])).

fof(f115,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f84,f48])).

fof(f84,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f56,f47])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f208,plain,(
    ! [X10,X9] : k2_xboole_0(k4_xboole_0(X9,X10),X9) = k2_xboole_0(X9,k4_xboole_0(X9,X10)) ),
    inference(forward_demodulation,[],[f207,f186])).

fof(f207,plain,(
    ! [X10,X9] : k2_xboole_0(k4_xboole_0(X9,X10),X9) = k5_xboole_0(k5_xboole_0(X9,k4_xboole_0(X9,X10)),k4_xboole_0(X9,X10)) ),
    inference(forward_demodulation,[],[f188,f49])).

fof(f188,plain,(
    ! [X10,X9] : k2_xboole_0(k4_xboole_0(X9,X10),X9) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X9,X10),X9),k4_xboole_0(X9,X10)) ),
    inference(superposition,[],[f53,f84])).

% (29735)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f587,plain,(
    k1_tarski(sK0) = k4_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f564,f44])).

fof(f564,plain,(
    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k1_xboole_0) ),
    inference(superposition,[],[f363,f40])).

fof(f363,plain,(
    ! [X10,X9] : k4_xboole_0(X10,X9) = k5_xboole_0(X9,k2_xboole_0(X9,X10)) ),
    inference(superposition,[],[f240,f243])).

fof(f243,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f225,f89])).

fof(f89,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f52,f48])).

fof(f225,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f64,f53])).

fof(f79,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_tarski(k1_xboole_0))
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f69,f42])).

fof(f42,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f69,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).

% (29732)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f94,f56])).

fof(f94,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f47,f93])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f88,f43])).

fof(f88,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f52,f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:02:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (29718)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (29746)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (29726)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (29740)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (29740)Refutation not found, incomplete strategy% (29740)------------------------------
% 0.21/0.52  % (29740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29724)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (29740)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29740)Memory used [KB]: 1663
% 0.21/0.52  % (29740)Time elapsed: 0.060 s
% 0.21/0.52  % (29731)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (29740)------------------------------
% 0.21/0.52  % (29740)------------------------------
% 0.21/0.53  % (29729)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (29717)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (29736)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (29722)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (29721)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (29719)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (29737)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (29720)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.43/0.54  % (29725)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.43/0.54  % (29738)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.43/0.54  % (29747)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.43/0.54  % (29733)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.43/0.54  % (29716)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.43/0.55  % (29742)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.43/0.55  % (29730)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.43/0.55  % (29745)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.43/0.55  % (29743)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.43/0.55  % (29727)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.43/0.55  % (29724)Refutation found. Thanks to Tanya!
% 1.43/0.55  % SZS status Theorem for theBenchmark
% 1.43/0.55  % (29739)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.43/0.55  % (29728)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.43/0.56  % (29737)Refutation not found, incomplete strategy% (29737)------------------------------
% 1.43/0.56  % (29737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (29734)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.57/0.56  % (29737)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  % (29737)Memory used [KB]: 10746
% 1.57/0.56  % (29737)Time elapsed: 0.142 s
% 1.57/0.56  % (29737)------------------------------
% 1.57/0.56  % (29737)------------------------------
% 1.57/0.56  % SZS output start Proof for theBenchmark
% 1.57/0.56  fof(f644,plain,(
% 1.57/0.56    $false),
% 1.57/0.56    inference(subsumption_resolution,[],[f95,f642])).
% 1.57/0.56  fof(f642,plain,(
% 1.57/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.57/0.56    inference(resolution,[],[f634,f87])).
% 1.57/0.56  fof(f87,plain,(
% 1.57/0.56    ( ! [X4,X2,X3] : (~r2_hidden(X4,k1_xboole_0) | k1_xboole_0 != k3_xboole_0(X2,X3)) )),
% 1.57/0.56    inference(inner_rewriting,[],[f86])).
% 1.57/0.56  fof(f86,plain,(
% 1.57/0.56    ( ! [X4,X2,X3] : (k1_xboole_0 != k3_xboole_0(X2,X3) | ~r2_hidden(X4,k3_xboole_0(X2,X3))) )),
% 1.57/0.56    inference(resolution,[],[f58,f55])).
% 1.57/0.56  fof(f55,plain,(
% 1.57/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.57/0.56    inference(cnf_transformation,[],[f34])).
% 1.57/0.56  fof(f34,plain,(
% 1.57/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.57/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f33])).
% 1.57/0.56  fof(f33,plain,(
% 1.57/0.56    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 1.57/0.56    introduced(choice_axiom,[])).
% 1.57/0.56  fof(f29,plain,(
% 1.57/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.57/0.56    inference(ennf_transformation,[],[f27])).
% 1.57/0.56  fof(f27,plain,(
% 1.57/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.57/0.56    inference(rectify,[],[f5])).
% 1.57/0.56  fof(f5,axiom,(
% 1.57/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.57/0.56  % (29734)Refutation not found, incomplete strategy% (29734)------------------------------
% 1.57/0.56  % (29734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (29734)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  % (29734)Memory used [KB]: 10618
% 1.57/0.56  % (29734)Time elapsed: 0.157 s
% 1.57/0.56  % (29734)------------------------------
% 1.57/0.56  % (29734)------------------------------
% 1.57/0.56  fof(f58,plain,(
% 1.57/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.57/0.56    inference(cnf_transformation,[],[f35])).
% 1.57/0.56  fof(f35,plain,(
% 1.57/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.57/0.56    inference(nnf_transformation,[],[f3])).
% 1.57/0.56  fof(f3,axiom,(
% 1.57/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.57/0.56  fof(f634,plain,(
% 1.57/0.56    r2_hidden(k1_xboole_0,k1_xboole_0)),
% 1.57/0.56    inference(resolution,[],[f625,f110])).
% 1.57/0.56  fof(f110,plain,(
% 1.57/0.56    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.57/0.56    inference(superposition,[],[f47,f109])).
% 1.57/0.56  fof(f109,plain,(
% 1.57/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.57/0.56    inference(forward_demodulation,[],[f106,f44])).
% 1.57/0.56  fof(f44,plain,(
% 1.57/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.57/0.56    inference(cnf_transformation,[],[f9])).
% 1.57/0.56  fof(f9,axiom,(
% 1.57/0.56    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.57/0.56  fof(f106,plain,(
% 1.57/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 1.57/0.56    inference(superposition,[],[f52,f98])).
% 1.57/0.56  fof(f98,plain,(
% 1.57/0.56    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 1.57/0.56    inference(superposition,[],[f95,f48])).
% 1.57/0.56  fof(f48,plain,(
% 1.57/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f1])).
% 1.57/0.56  fof(f1,axiom,(
% 1.57/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.57/0.56  fof(f52,plain,(
% 1.57/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.57/0.56    inference(cnf_transformation,[],[f6])).
% 1.57/0.56  fof(f6,axiom,(
% 1.57/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.57/0.56  fof(f47,plain,(
% 1.57/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f8])).
% 1.57/0.56  fof(f8,axiom,(
% 1.57/0.56    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.57/0.56  fof(f625,plain,(
% 1.57/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | r2_hidden(X0,k1_xboole_0)) )),
% 1.57/0.56    inference(backward_demodulation,[],[f79,f622])).
% 1.57/0.56  fof(f622,plain,(
% 1.57/0.56    k1_xboole_0 = k1_tarski(k1_xboole_0)),
% 1.57/0.56    inference(backward_demodulation,[],[f613,f621])).
% 1.57/0.56  fof(f621,plain,(
% 1.57/0.56    k1_xboole_0 = sK0),
% 1.57/0.56    inference(forward_demodulation,[],[f620,f41])).
% 1.57/0.56  fof(f41,plain,(
% 1.57/0.56    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.57/0.56    inference(cnf_transformation,[],[f23])).
% 1.57/0.56  fof(f23,axiom,(
% 1.57/0.56    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 1.57/0.56  fof(f620,plain,(
% 1.57/0.56    k3_tarski(k1_xboole_0) = sK0),
% 1.57/0.56    inference(superposition,[],[f195,f613])).
% 1.57/0.56  fof(f195,plain,(
% 1.57/0.56    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 1.57/0.56    inference(backward_demodulation,[],[f83,f194])).
% 1.57/0.56  fof(f194,plain,(
% 1.57/0.56    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.57/0.56    inference(forward_demodulation,[],[f193,f46])).
% 1.57/0.56  fof(f46,plain,(
% 1.57/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.57/0.56    inference(cnf_transformation,[],[f26])).
% 1.57/0.56  fof(f26,plain,(
% 1.57/0.56    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.57/0.56    inference(rectify,[],[f4])).
% 1.57/0.56  fof(f4,axiom,(
% 1.57/0.56    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.57/0.56  fof(f193,plain,(
% 1.57/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = k2_xboole_0(X0,X0)) )),
% 1.57/0.56    inference(forward_demodulation,[],[f174,f71])).
% 1.57/0.56  fof(f71,plain,(
% 1.57/0.56    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.57/0.56    inference(superposition,[],[f49,f44])).
% 1.57/0.56  fof(f49,plain,(
% 1.57/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f2])).
% 1.57/0.56  fof(f2,axiom,(
% 1.57/0.56    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.57/0.56  fof(f174,plain,(
% 1.57/0.56    ( ! [X0] : (k2_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0))) )),
% 1.57/0.56    inference(superposition,[],[f53,f43])).
% 1.57/0.56  fof(f43,plain,(
% 1.57/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f11])).
% 1.57/0.56  fof(f11,axiom,(
% 1.57/0.56    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.57/0.56  fof(f53,plain,(
% 1.57/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.57/0.56    inference(cnf_transformation,[],[f12])).
% 1.57/0.56  fof(f12,axiom,(
% 1.57/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.57/0.56  fof(f83,plain,(
% 1.57/0.56    ( ! [X0] : (k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))) )),
% 1.57/0.56    inference(superposition,[],[f50,f45])).
% 1.57/0.56  fof(f45,plain,(
% 1.57/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f13])).
% 1.57/0.56  fof(f13,axiom,(
% 1.57/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.57/0.56  fof(f50,plain,(
% 1.57/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.57/0.56    inference(cnf_transformation,[],[f21])).
% 1.57/0.56  fof(f21,axiom,(
% 1.57/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.57/0.56  fof(f613,plain,(
% 1.57/0.56    k1_xboole_0 = k1_tarski(sK0)),
% 1.57/0.56    inference(forward_demodulation,[],[f606,f96])).
% 1.57/0.56  fof(f96,plain,(
% 1.57/0.56    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6)) )),
% 1.57/0.56    inference(backward_demodulation,[],[f91,f95])).
% 1.57/0.56  fof(f91,plain,(
% 1.57/0.56    ( ! [X6] : (k3_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,X6)) )),
% 1.57/0.56    inference(superposition,[],[f52,f71])).
% 1.57/0.56  fof(f606,plain,(
% 1.57/0.56    k1_tarski(sK0) = k4_xboole_0(k1_xboole_0,k1_tarski(sK0))),
% 1.57/0.56    inference(backward_demodulation,[],[f587,f604])).
% 1.57/0.56  fof(f604,plain,(
% 1.57/0.56    k1_xboole_0 = sK1),
% 1.57/0.56    inference(forward_demodulation,[],[f599,f40])).
% 1.57/0.56  fof(f40,plain,(
% 1.57/0.56    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.57/0.56    inference(cnf_transformation,[],[f32])).
% 1.57/0.56  fof(f32,plain,(
% 1.57/0.56    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.57/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f31])).
% 1.57/0.56  fof(f31,plain,(
% 1.57/0.56    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.57/0.56    introduced(choice_axiom,[])).
% 1.57/0.56  fof(f28,plain,(
% 1.57/0.56    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 1.57/0.56    inference(ennf_transformation,[],[f25])).
% 1.57/0.56  fof(f25,negated_conjecture,(
% 1.57/0.56    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.57/0.56    inference(negated_conjecture,[],[f24])).
% 1.57/0.56  fof(f24,conjecture,(
% 1.57/0.56    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.57/0.56  fof(f599,plain,(
% 1.57/0.56    sK1 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.57/0.56    inference(superposition,[],[f285,f587])).
% 1.57/0.56  fof(f285,plain,(
% 1.57/0.56    ( ! [X10,X9] : (k2_xboole_0(k4_xboole_0(X9,X10),X9) = X9) )),
% 1.57/0.56    inference(backward_demodulation,[],[f208,f284])).
% 1.57/0.56  fof(f284,plain,(
% 1.57/0.56    ( ! [X6,X7] : (k2_xboole_0(X6,k4_xboole_0(X6,X7)) = X6) )),
% 1.57/0.56    inference(backward_demodulation,[],[f261,f269])).
% 1.57/0.56  fof(f269,plain,(
% 1.57/0.56    ( ! [X6,X5] : (k5_xboole_0(k3_xboole_0(X5,X6),k4_xboole_0(X5,X6)) = X5) )),
% 1.57/0.56    inference(superposition,[],[f246,f52])).
% 1.57/0.56  fof(f246,plain,(
% 1.57/0.56    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 1.57/0.56    inference(superposition,[],[f240,f49])).
% 1.57/0.56  fof(f240,plain,(
% 1.57/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.57/0.56    inference(forward_demodulation,[],[f216,f71])).
% 1.57/0.56  fof(f216,plain,(
% 1.57/0.56    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.57/0.56    inference(superposition,[],[f64,f43])).
% 1.57/0.56  fof(f64,plain,(
% 1.57/0.56    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.57/0.56    inference(cnf_transformation,[],[f10])).
% 1.57/0.56  fof(f10,axiom,(
% 1.57/0.56    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.57/0.56  fof(f261,plain,(
% 1.57/0.56    ( ! [X6,X7] : (k2_xboole_0(X6,k4_xboole_0(X6,X7)) = k5_xboole_0(k3_xboole_0(X6,X7),k4_xboole_0(X6,X7))) )),
% 1.57/0.56    inference(backward_demodulation,[],[f186,f248])).
% 1.57/0.56  fof(f248,plain,(
% 1.57/0.56    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 1.57/0.56    inference(superposition,[],[f240,f52])).
% 1.57/0.56  fof(f186,plain,(
% 1.57/0.56    ( ! [X6,X7] : (k2_xboole_0(X6,k4_xboole_0(X6,X7)) = k5_xboole_0(k5_xboole_0(X6,k4_xboole_0(X6,X7)),k4_xboole_0(X6,X7))) )),
% 1.57/0.56    inference(superposition,[],[f53,f115])).
% 1.57/0.56  fof(f115,plain,(
% 1.57/0.56    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 1.57/0.56    inference(superposition,[],[f84,f48])).
% 1.57/0.56  fof(f84,plain,(
% 1.57/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 1.57/0.56    inference(resolution,[],[f56,f47])).
% 1.57/0.56  fof(f56,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.57/0.56    inference(cnf_transformation,[],[f30])).
% 1.57/0.56  fof(f30,plain,(
% 1.57/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.57/0.56    inference(ennf_transformation,[],[f7])).
% 1.57/0.56  fof(f7,axiom,(
% 1.57/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.57/0.56  fof(f208,plain,(
% 1.57/0.56    ( ! [X10,X9] : (k2_xboole_0(k4_xboole_0(X9,X10),X9) = k2_xboole_0(X9,k4_xboole_0(X9,X10))) )),
% 1.57/0.56    inference(forward_demodulation,[],[f207,f186])).
% 1.57/0.56  fof(f207,plain,(
% 1.57/0.56    ( ! [X10,X9] : (k2_xboole_0(k4_xboole_0(X9,X10),X9) = k5_xboole_0(k5_xboole_0(X9,k4_xboole_0(X9,X10)),k4_xboole_0(X9,X10))) )),
% 1.57/0.56    inference(forward_demodulation,[],[f188,f49])).
% 1.57/0.56  fof(f188,plain,(
% 1.57/0.56    ( ! [X10,X9] : (k2_xboole_0(k4_xboole_0(X9,X10),X9) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X9,X10),X9),k4_xboole_0(X9,X10))) )),
% 1.57/0.56    inference(superposition,[],[f53,f84])).
% 1.57/0.56  % (29735)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.57/0.56  fof(f587,plain,(
% 1.57/0.56    k1_tarski(sK0) = k4_xboole_0(sK1,k1_tarski(sK0))),
% 1.57/0.56    inference(forward_demodulation,[],[f564,f44])).
% 1.57/0.56  fof(f564,plain,(
% 1.57/0.56    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k1_xboole_0)),
% 1.57/0.56    inference(superposition,[],[f363,f40])).
% 1.57/0.56  fof(f363,plain,(
% 1.57/0.56    ( ! [X10,X9] : (k4_xboole_0(X10,X9) = k5_xboole_0(X9,k2_xboole_0(X9,X10))) )),
% 1.57/0.56    inference(superposition,[],[f240,f243])).
% 1.57/0.56  fof(f243,plain,(
% 1.57/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.57/0.56    inference(forward_demodulation,[],[f225,f89])).
% 1.57/0.56  fof(f89,plain,(
% 1.57/0.56    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 1.57/0.56    inference(superposition,[],[f52,f48])).
% 1.57/0.56  fof(f225,plain,(
% 1.57/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 1.57/0.56    inference(superposition,[],[f64,f53])).
% 1.57/0.56  fof(f79,plain,(
% 1.57/0.56    ( ! [X0] : (r2_hidden(X0,k1_tarski(k1_xboole_0)) | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.57/0.56    inference(superposition,[],[f69,f42])).
% 1.57/0.56  fof(f42,plain,(
% 1.57/0.56    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 1.57/0.56    inference(cnf_transformation,[],[f22])).
% 1.57/0.56  fof(f22,axiom,(
% 1.57/0.56    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 1.57/0.56  fof(f69,plain,(
% 1.57/0.56    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.57/0.56    inference(equality_resolution,[],[f60])).
% 1.57/0.56  fof(f60,plain,(
% 1.57/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.57/0.56    inference(cnf_transformation,[],[f39])).
% 1.57/0.56  fof(f39,plain,(
% 1.57/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.57/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).
% 1.57/0.56  % (29732)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.57/0.56  fof(f38,plain,(
% 1.57/0.56    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.57/0.56    introduced(choice_axiom,[])).
% 1.57/0.56  fof(f37,plain,(
% 1.57/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.57/0.56    inference(rectify,[],[f36])).
% 1.57/0.56  fof(f36,plain,(
% 1.57/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.57/0.56    inference(nnf_transformation,[],[f20])).
% 1.57/0.56  fof(f20,axiom,(
% 1.57/0.56    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.57/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.57/0.56  fof(f95,plain,(
% 1.57/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.57/0.56    inference(resolution,[],[f94,f56])).
% 1.57/0.56  fof(f94,plain,(
% 1.57/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.57/0.56    inference(superposition,[],[f47,f93])).
% 1.57/0.56  fof(f93,plain,(
% 1.57/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.57/0.56    inference(forward_demodulation,[],[f88,f43])).
% 1.57/0.56  fof(f88,plain,(
% 1.57/0.56    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 1.57/0.56    inference(superposition,[],[f52,f46])).
% 1.57/0.56  % SZS output end Proof for theBenchmark
% 1.57/0.56  % (29724)------------------------------
% 1.57/0.56  % (29724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (29724)Termination reason: Refutation
% 1.57/0.56  
% 1.57/0.56  % (29724)Memory used [KB]: 6652
% 1.57/0.56  % (29724)Time elapsed: 0.102 s
% 1.57/0.56  % (29724)------------------------------
% 1.57/0.56  % (29724)------------------------------
% 1.57/0.56  % (29732)Refutation not found, incomplete strategy% (29732)------------------------------
% 1.57/0.56  % (29732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (29732)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  % (29732)Memory used [KB]: 6140
% 1.57/0.56  % (29732)Time elapsed: 0.002 s
% 1.57/0.56  % (29732)------------------------------
% 1.57/0.56  % (29732)------------------------------
% 1.57/0.56  % (29713)Success in time 0.202 s
%------------------------------------------------------------------------------
