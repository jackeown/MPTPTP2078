%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  126 (22831 expanded)
%              Number of leaves         :   18 (6554 expanded)
%              Depth                    :   34
%              Number of atoms          :  142 (34438 expanded)
%              Number of equality atoms :  116 (17635 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f460,plain,(
    $false ),
    inference(subsumption_resolution,[],[f456,f27])).

fof(f27,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f456,plain,(
    sK1 != k5_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f373,f452])).

fof(f452,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(forward_demodulation,[],[f425,f27])).

fof(f425,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X6,k1_xboole_0) ),
    inference(backward_demodulation,[],[f277,f417])).

fof(f417,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f414,f416])).

fof(f416,plain,(
    ! [X4] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_xboole_0,X4),k4_xboole_0(k1_xboole_0,X4)) ),
    inference(backward_demodulation,[],[f343,f412])).

fof(f412,plain,(
    ! [X14] : k4_xboole_0(k1_xboole_0,X14) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X14,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f362,f411])).

fof(f411,plain,(
    ! [X8] : k4_xboole_0(k1_xboole_0,X8) = k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8))) ),
    inference(forward_demodulation,[],[f410,f27])).

fof(f410,plain,(
    ! [X8] : k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8))) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X8),k1_xboole_0) ),
    inference(forward_demodulation,[],[f409,f343])).

fof(f409,plain,(
    ! [X8] : k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8))) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X8),k5_xboole_0(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,k4_xboole_0(X8,k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f408,f254])).

fof(f254,plain,(
    ! [X2,X1] : k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2) ),
    inference(forward_demodulation,[],[f238,f215])).

fof(f215,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f206,f54])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f34,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f206,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f201,f54])).

fof(f201,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f198,f110])).

fof(f110,plain,(
    ! [X0] : k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f45,f89])).

fof(f89,plain,(
    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f83,f80])).

fof(f80,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f79,f76])).

fof(f76,plain,(
    k1_xboole_0 = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f73,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f73,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f66,f24])).

fof(f24,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f66,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r1_tarski(k3_enumset1(X0,X0,X0,X0,sK0),sK1) ) ),
    inference(resolution,[],[f24,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f48,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f79,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(resolution,[],[f73,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f37,f33])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

% (18125)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f83,plain,(
    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) ),
    inference(superposition,[],[f54,f76])).

fof(f45,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f198,plain,(
    ! [X0] : k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f110,f195])).

fof(f195,plain,(
    ! [X0] : k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,X0)) ),
    inference(backward_demodulation,[],[f184,f193])).

fof(f193,plain,(
    ! [X0] : k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0)) ),
    inference(superposition,[],[f45,f189])).

fof(f189,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f183,f27])).

fof(f183,plain,(
    k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f110,f89])).

fof(f184,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f110,f110])).

fof(f238,plain,(
    ! [X2,X1] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2) ),
    inference(superposition,[],[f60,f215])).

fof(f60,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f44,f33,f33])).

fof(f44,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f408,plain,(
    ! [X8] : k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8))) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X8),k5_xboole_0(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k4_xboole_0(k1_xboole_0,X8),k1_xboole_0))) ),
    inference(forward_demodulation,[],[f394,f45])).

fof(f394,plain,(
    ! [X8] : k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X8),k1_xboole_0)) ),
    inference(superposition,[],[f58,f324])).

fof(f324,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f309,f215])).

fof(f309,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0) ),
    inference(resolution,[],[f278,f41])).

fof(f278,plain,(
    ! [X7] : r1_tarski(k4_xboole_0(k1_xboole_0,X7),X7) ),
    inference(superposition,[],[f29,f234])).

fof(f234,plain,(
    ! [X2] : k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f215,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f30,f33,f33])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f36,f52,f33])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f51])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f362,plain,(
    ! [X14] : k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X14,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f259,f361])).

fof(f361,plain,(
    ! [X0] : k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f349,f254])).

fof(f349,plain,(
    ! [X0] : k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(superposition,[],[f277,f215])).

fof(f259,plain,(
    ! [X14] : k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14))) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14)) ),
    inference(forward_demodulation,[],[f258,f215])).

fof(f258,plain,(
    ! [X14] : k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14))) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X14))) ),
    inference(forward_demodulation,[],[f257,f54])).

fof(f257,plain,(
    ! [X14] : k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14))) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X14),k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X14))))) ),
    inference(forward_demodulation,[],[f256,f56])).

fof(f256,plain,(
    ! [X14] : k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14))) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X14),k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k4_xboole_0(k1_xboole_0,X14),k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f255,f45])).

fof(f255,plain,(
    ! [X14] : k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X14),k1_xboole_0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k4_xboole_0(k1_xboole_0,X14),k1_xboole_0))) ),
    inference(forward_demodulation,[],[f248,f58])).

fof(f248,plain,(
    ! [X14] : k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k1_xboole_0)) = k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14))) ),
    inference(superposition,[],[f57,f215])).

fof(f57,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f35,f52,f52])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f343,plain,(
    ! [X4] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_xboole_0,X4),k4_xboole_0(k1_xboole_0,k4_xboole_0(X4,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f334,f254])).

fof(f334,plain,(
    ! [X4] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_xboole_0,X4),k4_xboole_0(k4_xboole_0(k1_xboole_0,X4),k1_xboole_0)) ),
    inference(superposition,[],[f54,f309])).

fof(f414,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
    inference(backward_demodulation,[],[f361,f412])).

fof(f277,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X6,k4_xboole_0(k1_xboole_0,X6)) ),
    inference(superposition,[],[f54,f234])).

fof(f373,plain,(
    sK1 != k5_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f302,f372])).

fof(f372,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f371,f89])).

fof(f371,plain,(
    k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f370,f80])).

fof(f370,plain,(
    k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f360,f206])).

fof(f360,plain,(
    k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f110,f277])).

fof(f302,plain,(
    sK1 != k5_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f293,f277])).

fof(f293,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(sK1,k4_xboole_0(k1_xboole_0,sK1)),k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f222,f292])).

fof(f292,plain,(
    ! [X3] : k3_tarski(k3_enumset1(X3,X3,X3,X3,k1_xboole_0)) = k5_xboole_0(X3,k4_xboole_0(k1_xboole_0,X3)) ),
    inference(forward_demodulation,[],[f291,f206])).

fof(f291,plain,(
    ! [X3] : k3_tarski(k3_enumset1(X3,X3,X3,X3,k1_xboole_0)) = k5_xboole_0(X3,k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3))) ),
    inference(forward_demodulation,[],[f274,f45])).

fof(f274,plain,(
    ! [X3] : k3_tarski(k3_enumset1(X3,X3,X3,X3,k1_xboole_0)) = k5_xboole_0(k5_xboole_0(X3,k1_xboole_0),k4_xboole_0(k1_xboole_0,X3)) ),
    inference(superposition,[],[f58,f234])).

fof(f222,plain,(
    sK1 != k5_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0)),k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f150,f215])).

fof(f150,plain,(
    sK1 != k5_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(backward_demodulation,[],[f107,f149])).

fof(f149,plain,(
    k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f148,f139])).

fof(f139,plain,(
    k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f54,f90])).

fof(f90,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f84,f80])).

fof(f84,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(superposition,[],[f56,f76])).

fof(f148,plain,(
    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0)) = k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f138,f86])).

fof(f86,plain,(
    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0)) ),
    inference(superposition,[],[f57,f76])).

fof(f138,plain,(
    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f58,f90])).

fof(f107,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(backward_demodulation,[],[f93,f102])).

fof(f102,plain,(
    k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f56,f80])).

fof(f93,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f70,f92])).

fof(f92,plain,(
    ! [X0] : k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,X0))) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0) ),
    inference(forward_demodulation,[],[f88,f80])).

fof(f88,plain,(
    ! [X0] : k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),X0) ),
    inference(superposition,[],[f60,f76])).

fof(f70,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) ),
    inference(forward_demodulation,[],[f69,f56])).

fof(f69,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f55,f58])).

fof(f55,plain,(
    sK1 != k3_tarski(k3_enumset1(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f25,f52,f53,f53])).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f51])).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f25,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:19:11 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.21/0.50  % (18105)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.50  % (18129)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (18113)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (18121)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.51  % (18109)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (18122)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.51  % (18114)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (18106)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (18107)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (18127)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (18129)Refutation not found, incomplete strategy% (18129)------------------------------
% 0.21/0.52  % (18129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18121)Refutation not found, incomplete strategy% (18121)------------------------------
% 0.21/0.52  % (18121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18123)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (18129)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (18129)Memory used [KB]: 10618
% 0.21/0.52  % (18129)Time elapsed: 0.113 s
% 0.21/0.52  % (18129)------------------------------
% 0.21/0.52  % (18129)------------------------------
% 0.21/0.52  % (18119)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (18123)Refutation not found, incomplete strategy% (18123)------------------------------
% 0.21/0.53  % (18123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18123)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (18123)Memory used [KB]: 1663
% 0.21/0.53  % (18123)Time elapsed: 0.118 s
% 0.21/0.53  % (18123)------------------------------
% 0.21/0.53  % (18123)------------------------------
% 0.21/0.53  % (18121)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (18121)Memory used [KB]: 10618
% 0.21/0.53  % (18121)Time elapsed: 0.113 s
% 0.21/0.53  % (18121)------------------------------
% 0.21/0.53  % (18121)------------------------------
% 0.21/0.53  % (18122)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (18134)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (18112)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (18124)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (18110)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (18133)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (18111)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (18108)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (18128)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (18115)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (18130)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (18116)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (18120)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (18118)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (18126)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (18117)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f460,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f456,f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.54  fof(f456,plain,(
% 0.21/0.54    sK1 != k5_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.54    inference(backward_demodulation,[],[f373,f452])).
% 0.21/0.54  fof(f452,plain,(
% 0.21/0.54    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = X6) )),
% 0.21/0.54    inference(forward_demodulation,[],[f425,f27])).
% 0.21/0.54  fof(f425,plain,(
% 0.21/0.54    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X6,k1_xboole_0)) )),
% 0.21/0.54    inference(backward_demodulation,[],[f277,f417])).
% 0.21/0.54  fof(f417,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(backward_demodulation,[],[f414,f416])).
% 0.21/0.54  fof(f416,plain,(
% 0.21/0.54    ( ! [X4] : (k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_xboole_0,X4),k4_xboole_0(k1_xboole_0,X4))) )),
% 0.21/0.54    inference(backward_demodulation,[],[f343,f412])).
% 0.21/0.54  fof(f412,plain,(
% 0.21/0.54    ( ! [X14] : (k4_xboole_0(k1_xboole_0,X14) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X14,k1_xboole_0))) )),
% 0.21/0.54    inference(backward_demodulation,[],[f362,f411])).
% 0.21/0.54  fof(f411,plain,(
% 0.21/0.54    ( ! [X8] : (k4_xboole_0(k1_xboole_0,X8) = k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8)))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f410,f27])).
% 0.21/0.54  fof(f410,plain,(
% 0.21/0.54    ( ! [X8] : (k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8))) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X8),k1_xboole_0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f409,f343])).
% 0.21/0.54  fof(f409,plain,(
% 0.21/0.54    ( ! [X8] : (k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8))) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X8),k5_xboole_0(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,k4_xboole_0(X8,k1_xboole_0))))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f408,f254])).
% 0.21/0.54  fof(f254,plain,(
% 0.21/0.54    ( ! [X2,X1] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f238,f215])).
% 0.21/0.54  fof(f215,plain,(
% 0.21/0.54    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) )),
% 0.21/0.54    inference(superposition,[],[f206,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f34,f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.54  fof(f206,plain,(
% 0.21/0.54    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) )),
% 0.21/0.54    inference(superposition,[],[f201,f54])).
% 0.21/0.54  fof(f201,plain,(
% 0.21/0.54    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f198,f110])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    ( ! [X0] : (k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(superposition,[],[f45,f89])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.54    inference(forward_demodulation,[],[f83,f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),
% 0.21/0.54    inference(forward_demodulation,[],[f79,f76])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    k1_xboole_0 = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.54    inference(resolution,[],[f73,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.54    inference(resolution,[],[f66,f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    r2_hidden(sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.21/0.54    inference(negated_conjecture,[],[f20])).
% 0.21/0.54  fof(f20,conjecture,(
% 0.21/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,sK0),sK1)) )),
% 0.21/0.54    inference(resolution,[],[f24,f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f48,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f32,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f43,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 0.21/0.54    inference(resolution,[],[f73,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f37,f33])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  % (18125)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0))),
% 0.21/0.54    inference(superposition,[],[f54,f76])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.54  fof(f198,plain,(
% 0.21/0.54    ( ! [X0] : (k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 0.21/0.54    inference(superposition,[],[f110,f195])).
% 0.21/0.54  fof(f195,plain,(
% 0.21/0.54    ( ! [X0] : (k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,X0))) )),
% 0.21/0.54    inference(backward_demodulation,[],[f184,f193])).
% 0.21/0.54  fof(f193,plain,(
% 0.21/0.54    ( ! [X0] : (k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0))) )),
% 0.21/0.54    inference(superposition,[],[f45,f189])).
% 0.21/0.54  fof(f189,plain,(
% 0.21/0.54    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.54    inference(forward_demodulation,[],[f183,f27])).
% 0.21/0.54  fof(f183,plain,(
% 0.21/0.54    k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.54    inference(superposition,[],[f110,f89])).
% 0.21/0.54  fof(f184,plain,(
% 0.21/0.54    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k1_xboole_0,X0))) )),
% 0.21/0.54    inference(superposition,[],[f110,f110])).
% 0.21/0.54  fof(f238,plain,(
% 0.21/0.54    ( ! [X2,X1] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2)) )),
% 0.21/0.54    inference(superposition,[],[f60,f215])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f44,f33,f33])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.54  fof(f408,plain,(
% 0.21/0.54    ( ! [X8] : (k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8))) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X8),k5_xboole_0(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k4_xboole_0(k1_xboole_0,X8),k1_xboole_0)))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f394,f45])).
% 0.21/0.54  fof(f394,plain,(
% 0.21/0.54    ( ! [X8] : (k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(k1_xboole_0,X8)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X8),k1_xboole_0))) )),
% 0.21/0.54    inference(superposition,[],[f58,f324])).
% 0.21/0.54  fof(f324,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))) )),
% 0.21/0.54    inference(superposition,[],[f309,f215])).
% 0.21/0.54  fof(f309,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0)) )),
% 0.21/0.54    inference(resolution,[],[f278,f41])).
% 0.21/0.54  fof(f278,plain,(
% 0.21/0.54    ( ! [X7] : (r1_tarski(k4_xboole_0(k1_xboole_0,X7),X7)) )),
% 0.21/0.54    inference(superposition,[],[f29,f234])).
% 0.21/0.54  fof(f234,plain,(
% 0.21/0.54    ( ! [X2] : (k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0))) )),
% 0.21/0.54    inference(superposition,[],[f215,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f30,f33,f33])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f36,f52,f33])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f31,f51])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.21/0.54  fof(f362,plain,(
% 0.21/0.54    ( ! [X14] : (k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X14,k1_xboole_0))) )),
% 0.21/0.54    inference(backward_demodulation,[],[f259,f361])).
% 0.21/0.54  fof(f361,plain,(
% 0.21/0.54    ( ! [X0] : (k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f349,f254])).
% 0.21/0.54  fof(f349,plain,(
% 0.21/0.54    ( ! [X0] : (k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0)) )),
% 0.21/0.54    inference(superposition,[],[f277,f215])).
% 0.21/0.54  fof(f259,plain,(
% 0.21/0.54    ( ! [X14] : (k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14))) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f258,f215])).
% 0.21/0.54  fof(f258,plain,(
% 0.21/0.54    ( ! [X14] : (k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14))) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X14)))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f257,f54])).
% 0.21/0.54  fof(f257,plain,(
% 0.21/0.54    ( ! [X14] : (k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14))) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X14),k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X14)))))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f256,f56])).
% 0.21/0.54  fof(f256,plain,(
% 0.21/0.54    ( ! [X14] : (k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14))) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X14),k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k4_xboole_0(k1_xboole_0,X14),k1_xboole_0))))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f255,f45])).
% 0.21/0.54  fof(f255,plain,(
% 0.21/0.54    ( ! [X14] : (k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(k1_xboole_0,X14),k1_xboole_0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k4_xboole_0(k1_xboole_0,X14),k1_xboole_0)))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f248,f58])).
% 0.21/0.54  fof(f248,plain,(
% 0.21/0.54    ( ! [X14] : (k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k1_xboole_0)) = k3_tarski(k3_enumset1(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,X14)))) )),
% 0.21/0.54    inference(superposition,[],[f57,f215])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X1,X0)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f35,f52,f52])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.54  fof(f343,plain,(
% 0.21/0.54    ( ! [X4] : (k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_xboole_0,X4),k4_xboole_0(k1_xboole_0,k4_xboole_0(X4,k1_xboole_0)))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f334,f254])).
% 0.21/0.54  fof(f334,plain,(
% 0.21/0.54    ( ! [X4] : (k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_xboole_0,X4),k4_xboole_0(k4_xboole_0(k1_xboole_0,X4),k1_xboole_0))) )),
% 0.21/0.54    inference(superposition,[],[f54,f309])).
% 0.21/0.54  fof(f414,plain,(
% 0.21/0.54    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))) )),
% 0.21/0.54    inference(backward_demodulation,[],[f361,f412])).
% 0.21/0.54  fof(f277,plain,(
% 0.21/0.54    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X6,k4_xboole_0(k1_xboole_0,X6))) )),
% 0.21/0.54    inference(superposition,[],[f54,f234])).
% 0.21/0.54  fof(f373,plain,(
% 0.21/0.54    sK1 != k5_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0)),
% 0.21/0.54    inference(backward_demodulation,[],[f302,f372])).
% 0.21/0.54  fof(f372,plain,(
% 0.21/0.54    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.54    inference(forward_demodulation,[],[f371,f89])).
% 0.21/0.54  fof(f371,plain,(
% 0.21/0.54    k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.54    inference(forward_demodulation,[],[f370,f80])).
% 0.21/0.54  fof(f370,plain,(
% 0.21/0.54    k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.54    inference(forward_demodulation,[],[f360,f206])).
% 0.21/0.54  fof(f360,plain,(
% 0.21/0.54    k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 0.21/0.54    inference(superposition,[],[f110,f277])).
% 0.21/0.54  fof(f302,plain,(
% 0.21/0.54    sK1 != k5_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 0.21/0.54    inference(backward_demodulation,[],[f293,f277])).
% 0.21/0.54  fof(f293,plain,(
% 0.21/0.54    sK1 != k5_xboole_0(k5_xboole_0(sK1,k4_xboole_0(k1_xboole_0,sK1)),k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 0.21/0.54    inference(backward_demodulation,[],[f222,f292])).
% 0.21/0.54  fof(f292,plain,(
% 0.21/0.54    ( ! [X3] : (k3_tarski(k3_enumset1(X3,X3,X3,X3,k1_xboole_0)) = k5_xboole_0(X3,k4_xboole_0(k1_xboole_0,X3))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f291,f206])).
% 0.21/0.54  fof(f291,plain,(
% 0.21/0.54    ( ! [X3] : (k3_tarski(k3_enumset1(X3,X3,X3,X3,k1_xboole_0)) = k5_xboole_0(X3,k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3)))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f274,f45])).
% 0.21/0.54  fof(f274,plain,(
% 0.21/0.54    ( ! [X3] : (k3_tarski(k3_enumset1(X3,X3,X3,X3,k1_xboole_0)) = k5_xboole_0(k5_xboole_0(X3,k1_xboole_0),k4_xboole_0(k1_xboole_0,X3))) )),
% 0.21/0.54    inference(superposition,[],[f58,f234])).
% 0.21/0.54  fof(f222,plain,(
% 0.21/0.54    sK1 != k5_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0)),k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 0.21/0.54    inference(backward_demodulation,[],[f150,f215])).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    sK1 != k5_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),
% 0.21/0.54    inference(backward_demodulation,[],[f107,f149])).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0))),
% 0.21/0.54    inference(backward_demodulation,[],[f148,f139])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.54    inference(superposition,[],[f54,f90])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 0.21/0.54    inference(forward_demodulation,[],[f84,f80])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    k4_xboole_0(sK1,k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),
% 0.21/0.54    inference(superposition,[],[f56,f76])).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0)) = k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.54    inference(forward_demodulation,[],[f138,f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0))),
% 0.21/0.54    inference(superposition,[],[f57,f76])).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.54    inference(superposition,[],[f58,f90])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),
% 0.21/0.54    inference(backward_demodulation,[],[f93,f102])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 0.21/0.54    inference(superposition,[],[f56,f80])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 0.21/0.54    inference(backward_demodulation,[],[f70,f92])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ( ! [X0] : (k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,X0))) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f88,f80])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X0] : (k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0),X0)) )),
% 0.21/0.54    inference(superposition,[],[f60,f76])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))),
% 0.21/0.54    inference(forward_demodulation,[],[f69,f56])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),
% 0.21/0.54    inference(superposition,[],[f55,f58])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    sK1 != k3_tarski(k3_enumset1(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 0.21/0.54    inference(definition_unfolding,[],[f25,f52,f53,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f28,f51])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (18122)------------------------------
% 0.21/0.54  % (18122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18122)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (18122)Memory used [KB]: 2046
% 0.21/0.54  % (18122)Time elapsed: 0.119 s
% 0.21/0.54  % (18122)------------------------------
% 0.21/0.54  % (18122)------------------------------
% 0.21/0.55  % (18104)Success in time 0.19 s
%------------------------------------------------------------------------------
