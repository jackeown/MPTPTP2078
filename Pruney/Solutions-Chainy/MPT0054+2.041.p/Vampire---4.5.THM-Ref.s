%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:03 EST 2020

% Result     : Theorem 5.19s
% Output     : Refutation 5.19s
% Verified   : 
% Statistics : Number of formulae       :   50 (  92 expanded)
%              Number of leaves         :   10 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :   53 ( 101 expanded)
%              Number of equality atoms :   45 (  83 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22925,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f22924])).

fof(f22924,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f18,f20697])).

fof(f20697,plain,(
    ! [X39,X40] : k4_xboole_0(X39,X40) = k4_xboole_0(X39,k3_xboole_0(X39,X40)) ),
    inference(forward_demodulation,[],[f20526,f10756])).

fof(f10756,plain,(
    ! [X23,X21,X22] : k4_xboole_0(X23,X21) = k4_xboole_0(k4_xboole_0(X23,X21),k3_xboole_0(X22,X21)) ),
    inference(superposition,[],[f460,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f22,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f460,plain,(
    ! [X24,X23,X25] : k4_xboole_0(X24,k2_xboole_0(X25,X23)) = k4_xboole_0(k4_xboole_0(X24,k2_xboole_0(X25,X23)),X23) ),
    inference(forward_demodulation,[],[f459,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f459,plain,(
    ! [X24,X23,X25] : k4_xboole_0(k4_xboole_0(X24,k2_xboole_0(X25,X23)),X23) = k4_xboole_0(k4_xboole_0(X24,X25),X23) ),
    inference(forward_demodulation,[],[f444,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f23,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f444,plain,(
    ! [X24,X23,X25] : k4_xboole_0(k4_xboole_0(X24,k2_xboole_0(X25,X23)),X23) = k4_xboole_0(k2_xboole_0(X23,k4_xboole_0(X24,X25)),X23) ),
    inference(superposition,[],[f40,f77])).

fof(f77,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X5,k4_xboole_0(X3,X4)) = k2_xboole_0(X5,k4_xboole_0(X3,k2_xboole_0(X4,X5))) ),
    inference(superposition,[],[f24,f27])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f20526,plain,(
    ! [X39,X40] : k4_xboole_0(k4_xboole_0(X39,X40),k3_xboole_0(X39,X40)) = k4_xboole_0(X39,k3_xboole_0(X39,X40)) ),
    inference(superposition,[],[f23,f20369])).

fof(f20369,plain,(
    ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = X4 ),
    inference(forward_demodulation,[],[f20203,f200])).

fof(f200,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(superposition,[],[f121,f21])).

fof(f121,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f99,f22])).

fof(f99,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f28,f60])).

fof(f60,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f36,f24])).

fof(f36,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f35,f21])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f26,f19])).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f20203,plain,(
    ! [X4,X5] : k3_xboole_0(X4,k2_xboole_0(X5,X4)) = k2_xboole_0(k4_xboole_0(X4,X5),k3_xboole_0(X4,X5)) ),
    inference(superposition,[],[f106,f193])).

fof(f193,plain,(
    ! [X12,X11] : k2_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(X12,X11),X11) ),
    inference(forward_demodulation,[],[f182,f84])).

fof(f84,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) ),
    inference(resolution,[],[f48,f26])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f44,f21])).

fof(f44,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X2,X3),k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f19,f23])).

fof(f182,plain,(
    ! [X12,X11] : k2_xboole_0(k4_xboole_0(X12,X11),X11) = k2_xboole_0(k4_xboole_0(X12,X11),k2_xboole_0(X11,X12)) ),
    inference(superposition,[],[f58,f24])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f55,f24])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f24,f23])).

fof(f106,plain,(
    ! [X21,X22,X20] : k2_xboole_0(k4_xboole_0(X20,X21),k3_xboole_0(X20,X22)) = k3_xboole_0(X20,k2_xboole_0(k4_xboole_0(X20,X21),X22)) ),
    inference(superposition,[],[f28,f35])).

fof(f18,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:53:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.42  % (26054)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.13/0.42  % (26057)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.13/0.42  % (26060)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.45  % (26065)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.20/0.46  % (26061)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.46  % (26056)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.47  % (26064)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.47  % (26062)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.47  % (26058)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.47  % (26059)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.48  % (26063)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.48  % (26055)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 5.19/1.03  % (26055)Time limit reached!
% 5.19/1.03  % (26055)------------------------------
% 5.19/1.03  % (26055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.19/1.03  % (26055)Termination reason: Time limit
% 5.19/1.03  % (26055)Termination phase: Saturation
% 5.19/1.03  
% 5.19/1.03  % (26055)Memory used [KB]: 23794
% 5.19/1.03  % (26055)Time elapsed: 0.600 s
% 5.19/1.03  % (26055)------------------------------
% 5.19/1.03  % (26055)------------------------------
% 5.19/1.05  % (26057)Refutation found. Thanks to Tanya!
% 5.19/1.05  % SZS status Theorem for theBenchmark
% 5.19/1.05  % SZS output start Proof for theBenchmark
% 5.19/1.05  fof(f22925,plain,(
% 5.19/1.05    $false),
% 5.19/1.05    inference(trivial_inequality_removal,[],[f22924])).
% 5.19/1.05  fof(f22924,plain,(
% 5.19/1.05    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)),
% 5.19/1.05    inference(superposition,[],[f18,f20697])).
% 5.19/1.05  fof(f20697,plain,(
% 5.19/1.05    ( ! [X39,X40] : (k4_xboole_0(X39,X40) = k4_xboole_0(X39,k3_xboole_0(X39,X40))) )),
% 5.19/1.05    inference(forward_demodulation,[],[f20526,f10756])).
% 5.19/1.05  fof(f10756,plain,(
% 5.19/1.05    ( ! [X23,X21,X22] : (k4_xboole_0(X23,X21) = k4_xboole_0(k4_xboole_0(X23,X21),k3_xboole_0(X22,X21))) )),
% 5.19/1.05    inference(superposition,[],[f460,f30])).
% 5.19/1.05  fof(f30,plain,(
% 5.19/1.05    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0) )),
% 5.19/1.05    inference(superposition,[],[f22,f20])).
% 5.19/1.05  fof(f20,plain,(
% 5.19/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.19/1.05    inference(cnf_transformation,[],[f2])).
% 5.19/1.05  fof(f2,axiom,(
% 5.19/1.05    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.19/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.19/1.05  fof(f22,plain,(
% 5.19/1.05    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 5.19/1.05    inference(cnf_transformation,[],[f4])).
% 5.19/1.05  fof(f4,axiom,(
% 5.19/1.05    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 5.19/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 5.19/1.05  fof(f460,plain,(
% 5.19/1.05    ( ! [X24,X23,X25] : (k4_xboole_0(X24,k2_xboole_0(X25,X23)) = k4_xboole_0(k4_xboole_0(X24,k2_xboole_0(X25,X23)),X23)) )),
% 5.19/1.05    inference(forward_demodulation,[],[f459,f27])).
% 5.19/1.05  fof(f27,plain,(
% 5.19/1.05    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 5.19/1.05    inference(cnf_transformation,[],[f10])).
% 5.19/1.05  fof(f10,axiom,(
% 5.19/1.05    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 5.19/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 5.19/1.05  fof(f459,plain,(
% 5.19/1.05    ( ! [X24,X23,X25] : (k4_xboole_0(k4_xboole_0(X24,k2_xboole_0(X25,X23)),X23) = k4_xboole_0(k4_xboole_0(X24,X25),X23)) )),
% 5.19/1.05    inference(forward_demodulation,[],[f444,f40])).
% 5.19/1.05  fof(f40,plain,(
% 5.19/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 5.19/1.05    inference(superposition,[],[f23,f21])).
% 5.19/1.05  fof(f21,plain,(
% 5.19/1.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 5.19/1.05    inference(cnf_transformation,[],[f1])).
% 5.19/1.05  fof(f1,axiom,(
% 5.19/1.05    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 5.19/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 5.19/1.05  fof(f23,plain,(
% 5.19/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 5.19/1.05    inference(cnf_transformation,[],[f9])).
% 5.19/1.05  fof(f9,axiom,(
% 5.19/1.05    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 5.19/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 5.19/1.05  fof(f444,plain,(
% 5.19/1.05    ( ! [X24,X23,X25] : (k4_xboole_0(k4_xboole_0(X24,k2_xboole_0(X25,X23)),X23) = k4_xboole_0(k2_xboole_0(X23,k4_xboole_0(X24,X25)),X23)) )),
% 5.19/1.05    inference(superposition,[],[f40,f77])).
% 5.19/1.05  fof(f77,plain,(
% 5.19/1.05    ( ! [X4,X5,X3] : (k2_xboole_0(X5,k4_xboole_0(X3,X4)) = k2_xboole_0(X5,k4_xboole_0(X3,k2_xboole_0(X4,X5)))) )),
% 5.19/1.05    inference(superposition,[],[f24,f27])).
% 5.19/1.05  fof(f24,plain,(
% 5.19/1.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 5.19/1.05    inference(cnf_transformation,[],[f8])).
% 5.19/1.05  fof(f8,axiom,(
% 5.19/1.05    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 5.19/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 5.19/1.05  fof(f20526,plain,(
% 5.19/1.05    ( ! [X39,X40] : (k4_xboole_0(k4_xboole_0(X39,X40),k3_xboole_0(X39,X40)) = k4_xboole_0(X39,k3_xboole_0(X39,X40))) )),
% 5.19/1.05    inference(superposition,[],[f23,f20369])).
% 5.19/1.05  fof(f20369,plain,(
% 5.19/1.05    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = X4) )),
% 5.19/1.05    inference(forward_demodulation,[],[f20203,f200])).
% 5.19/1.05  fof(f200,plain,(
% 5.19/1.05    ( ! [X2,X1] : (k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1) )),
% 5.19/1.05    inference(superposition,[],[f121,f21])).
% 5.19/1.05  fof(f121,plain,(
% 5.19/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 5.19/1.05    inference(forward_demodulation,[],[f99,f22])).
% 5.19/1.05  fof(f99,plain,(
% 5.19/1.05    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 5.19/1.05    inference(superposition,[],[f28,f60])).
% 5.19/1.05  fof(f60,plain,(
% 5.19/1.05    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 5.19/1.05    inference(superposition,[],[f36,f24])).
% 5.19/1.05  fof(f36,plain,(
% 5.19/1.05    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 5.19/1.05    inference(superposition,[],[f35,f21])).
% 5.19/1.05  fof(f35,plain,(
% 5.19/1.05    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 5.19/1.05    inference(resolution,[],[f26,f19])).
% 5.19/1.05  fof(f19,plain,(
% 5.19/1.05    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 5.19/1.05    inference(cnf_transformation,[],[f7])).
% 5.19/1.05  fof(f7,axiom,(
% 5.19/1.05    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 5.19/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 5.19/1.05  fof(f26,plain,(
% 5.19/1.05    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 5.19/1.05    inference(cnf_transformation,[],[f16])).
% 5.19/1.05  fof(f16,plain,(
% 5.19/1.05    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 5.19/1.05    inference(ennf_transformation,[],[f3])).
% 5.19/1.05  fof(f3,axiom,(
% 5.19/1.05    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 5.19/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 5.19/1.05  fof(f28,plain,(
% 5.19/1.05    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 5.19/1.05    inference(cnf_transformation,[],[f5])).
% 5.19/1.05  fof(f5,axiom,(
% 5.19/1.05    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 5.19/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).
% 5.19/1.05  fof(f20203,plain,(
% 5.19/1.05    ( ! [X4,X5] : (k3_xboole_0(X4,k2_xboole_0(X5,X4)) = k2_xboole_0(k4_xboole_0(X4,X5),k3_xboole_0(X4,X5))) )),
% 5.19/1.05    inference(superposition,[],[f106,f193])).
% 5.19/1.05  fof(f193,plain,(
% 5.19/1.05    ( ! [X12,X11] : (k2_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(X12,X11),X11)) )),
% 5.19/1.05    inference(forward_demodulation,[],[f182,f84])).
% 5.19/1.05  fof(f84,plain,(
% 5.19/1.05    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0))) )),
% 5.19/1.05    inference(resolution,[],[f48,f26])).
% 5.19/1.05  fof(f48,plain,(
% 5.19/1.05    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0))) )),
% 5.19/1.05    inference(superposition,[],[f44,f21])).
% 5.19/1.05  fof(f44,plain,(
% 5.19/1.05    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),k2_xboole_0(X2,X3))) )),
% 5.19/1.05    inference(superposition,[],[f19,f23])).
% 5.19/1.05  fof(f182,plain,(
% 5.19/1.05    ( ! [X12,X11] : (k2_xboole_0(k4_xboole_0(X12,X11),X11) = k2_xboole_0(k4_xboole_0(X12,X11),k2_xboole_0(X11,X12))) )),
% 5.19/1.05    inference(superposition,[],[f58,f24])).
% 5.19/1.05  fof(f58,plain,(
% 5.19/1.05    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))) )),
% 5.19/1.05    inference(forward_demodulation,[],[f55,f24])).
% 5.19/1.05  fof(f55,plain,(
% 5.19/1.05    ( ! [X0,X1] : (k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 5.19/1.05    inference(superposition,[],[f24,f23])).
% 5.19/1.05  fof(f106,plain,(
% 5.19/1.05    ( ! [X21,X22,X20] : (k2_xboole_0(k4_xboole_0(X20,X21),k3_xboole_0(X20,X22)) = k3_xboole_0(X20,k2_xboole_0(k4_xboole_0(X20,X21),X22))) )),
% 5.19/1.05    inference(superposition,[],[f28,f35])).
% 5.19/1.05  fof(f18,plain,(
% 5.19/1.05    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 5.19/1.05    inference(cnf_transformation,[],[f14])).
% 5.19/1.05  fof(f14,plain,(
% 5.19/1.05    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.19/1.05    inference(ennf_transformation,[],[f13])).
% 5.19/1.05  fof(f13,negated_conjecture,(
% 5.19/1.05    ~! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.19/1.05    inference(negated_conjecture,[],[f12])).
% 5.19/1.05  fof(f12,conjecture,(
% 5.19/1.05    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.19/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 5.19/1.05  % SZS output end Proof for theBenchmark
% 5.19/1.05  % (26057)------------------------------
% 5.19/1.05  % (26057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.19/1.05  % (26057)Termination reason: Refutation
% 5.19/1.05  
% 5.19/1.05  % (26057)Memory used [KB]: 25713
% 5.19/1.05  % (26057)Time elapsed: 0.636 s
% 5.19/1.05  % (26057)------------------------------
% 5.19/1.05  % (26057)------------------------------
% 5.19/1.06  % (26053)Success in time 0.696 s
%------------------------------------------------------------------------------
