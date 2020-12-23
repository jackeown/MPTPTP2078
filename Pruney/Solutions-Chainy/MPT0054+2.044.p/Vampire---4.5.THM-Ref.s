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
% DateTime   : Thu Dec  3 12:30:03 EST 2020

% Result     : Theorem 45.14s
% Output     : Refutation 45.14s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 194 expanded)
%              Number of leaves         :   12 (  62 expanded)
%              Depth                    :   18
%              Number of atoms          :   86 ( 216 expanded)
%              Number of equality atoms :   64 ( 173 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f168674,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f168673])).

fof(f168673,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f17,f129370])).

fof(f129370,plain,(
    ! [X78,X79] : k4_xboole_0(X78,X79) = k4_xboole_0(X78,k3_xboole_0(X78,X79)) ),
    inference(forward_demodulation,[],[f128980,f42913])).

fof(f42913,plain,(
    ! [X134,X132,X133] : k4_xboole_0(X134,X132) = k4_xboole_0(k4_xboole_0(X134,X132),k3_xboole_0(X133,X132)) ),
    inference(superposition,[],[f691,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f21,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f691,plain,(
    ! [X28,X29,X27] : k4_xboole_0(X28,k2_xboole_0(X29,X27)) = k4_xboole_0(k4_xboole_0(X28,k2_xboole_0(X29,X27)),X27) ),
    inference(forward_demodulation,[],[f690,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f690,plain,(
    ! [X28,X29,X27] : k4_xboole_0(k4_xboole_0(X28,k2_xboole_0(X29,X27)),X27) = k4_xboole_0(k4_xboole_0(X28,X29),X27) ),
    inference(forward_demodulation,[],[f656,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f22,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f656,plain,(
    ! [X28,X29,X27] : k4_xboole_0(k4_xboole_0(X28,k2_xboole_0(X29,X27)),X27) = k4_xboole_0(k2_xboole_0(X27,k4_xboole_0(X28,X29)),X27) ),
    inference(superposition,[],[f34,f58])).

fof(f58,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X5,k4_xboole_0(X3,X4)) = k2_xboole_0(X5,k4_xboole_0(X3,k2_xboole_0(X4,X5))) ),
    inference(superposition,[],[f23,f25])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f128980,plain,(
    ! [X78,X79] : k4_xboole_0(X78,k3_xboole_0(X78,X79)) = k4_xboole_0(k4_xboole_0(X78,X79),k3_xboole_0(X78,X79)) ),
    inference(superposition,[],[f22,f76661])).

fof(f76661,plain,(
    ! [X136,X137] : k2_xboole_0(k4_xboole_0(X136,X137),k3_xboole_0(X136,X137)) = X136 ),
    inference(forward_demodulation,[],[f76591,f140])).

fof(f140,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4 ),
    inference(superposition,[],[f29,f31])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f24,f18])).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f76591,plain,(
    ! [X136,X137] : k2_xboole_0(X136,k4_xboole_0(X136,X137)) = k2_xboole_0(k4_xboole_0(X136,X137),k3_xboole_0(X136,X137)) ),
    inference(resolution,[],[f538,f42682])).

fof(f42682,plain,(
    ! [X316,X317] : r1_tarski(k4_xboole_0(X317,k4_xboole_0(X317,X316)),X316) ),
    inference(superposition,[],[f543,f42361])).

fof(f42361,plain,(
    ! [X10,X11] : k2_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X11,X10))) = X10 ),
    inference(forward_demodulation,[],[f42360,f140])).

fof(f42360,plain,(
    ! [X10,X11] : k2_xboole_0(X10,k4_xboole_0(X10,X11)) = k2_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X11,X10))) ),
    inference(forward_demodulation,[],[f42072,f3795])).

fof(f3795,plain,(
    ! [X37,X35,X36] : k2_xboole_0(X36,k4_xboole_0(X37,k4_xboole_0(X35,X36))) = k2_xboole_0(X36,k4_xboole_0(X37,X35)) ),
    inference(forward_demodulation,[],[f3723,f634])).

fof(f634,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X3,k4_xboole_0(X4,X2)) = k2_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2))) ),
    inference(superposition,[],[f58,f20])).

fof(f3723,plain,(
    ! [X37,X35,X36] : k2_xboole_0(X36,k4_xboole_0(X37,k4_xboole_0(X35,X36))) = k2_xboole_0(X36,k4_xboole_0(X37,k2_xboole_0(X36,X35))) ),
    inference(superposition,[],[f58,f604])).

fof(f604,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X3,X2),X2) ),
    inference(forward_demodulation,[],[f603,f195])).

fof(f195,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k2_xboole_0(k4_xboole_0(X11,X10),k2_xboole_0(X10,X11)) ),
    inference(forward_demodulation,[],[f194,f23])).

fof(f194,plain,(
    ! [X10,X11] : k2_xboole_0(X10,k4_xboole_0(X11,X10)) = k2_xboole_0(k4_xboole_0(X11,X10),k2_xboole_0(X10,X11)) ),
    inference(forward_demodulation,[],[f180,f20])).

fof(f180,plain,(
    ! [X10,X11] : k2_xboole_0(k4_xboole_0(X11,X10),X10) = k2_xboole_0(k4_xboole_0(X11,X10),k2_xboole_0(X10,X11)) ),
    inference(superposition,[],[f39,f23])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f37,f23])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f23,f22])).

fof(f603,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X3,X2),X2) = k2_xboole_0(k4_xboole_0(X3,X2),k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f580,f23])).

fof(f580,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X3,X2),k2_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(superposition,[],[f23,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f22,f23])).

fof(f42072,plain,(
    ! [X10,X11] : k2_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,X10))) = k2_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X11,X10))) ),
    inference(superposition,[],[f678,f38])).

fof(f678,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X2,X0),X1)) ),
    inference(forward_demodulation,[],[f677,f454])).

fof(f454,plain,(
    ! [X33,X34,X32] : k4_xboole_0(k2_xboole_0(X33,X34),X32) = k4_xboole_0(k2_xboole_0(X34,k2_xboole_0(X32,X33)),X32) ),
    inference(superposition,[],[f34,f79])).

fof(f79,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f26,f20])).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f677,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1)) ),
    inference(forward_demodulation,[],[f644,f58])).

fof(f644,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f58,f22])).

fof(f543,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f515,f20])).

fof(f515,plain,(
    ! [X4,X5] : r1_tarski(X4,k2_xboole_0(X4,X5)) ),
    inference(superposition,[],[f340,f216])).

fof(f216,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k2_xboole_0(X5,X6)) = X5 ),
    inference(forward_demodulation,[],[f208,f21])).

fof(f208,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k3_xboole_0(X5,X6)) = k3_xboole_0(X5,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f27,f164])).

fof(f164,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f140,f23])).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f340,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f270,f19])).

fof(f270,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f43,f18])).

fof(f43,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(k4_xboole_0(X8,X6),k3_xboole_0(X6,X7))
      | r1_tarski(X8,X6) ) ),
    inference(superposition,[],[f28,f21])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f538,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | k2_xboole_0(X0,X1) = k2_xboole_0(X1,k3_xboole_0(X0,X2)) ) ),
    inference(forward_demodulation,[],[f528,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X2)) ),
    inference(superposition,[],[f27,f20])).

fof(f528,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | k2_xboole_0(X0,X1) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) ) ),
    inference(superposition,[],[f40,f22])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = X0 ) ),
    inference(resolution,[],[f28,f24])).

fof(f17,plain,(
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
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:19:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.42  % (30661)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.23/0.42  % (30668)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.23/0.44  % (30672)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.23/0.44  % (30670)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.23/0.44  % (30666)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.23/0.45  % (30669)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.23/0.45  % (30664)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.23/0.47  % (30660)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.23/0.47  % (30667)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.23/0.47  % (30671)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.23/0.48  % (30662)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.23/0.49  % (30663)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 4.96/1.00  % (30661)Time limit reached!
% 4.96/1.00  % (30661)------------------------------
% 4.96/1.00  % (30661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.96/1.00  % (30661)Termination reason: Time limit
% 4.96/1.00  % (30661)Termination phase: Saturation
% 4.96/1.00  
% 4.96/1.00  % (30661)Memory used [KB]: 23027
% 4.96/1.00  % (30661)Time elapsed: 0.600 s
% 4.96/1.00  % (30661)------------------------------
% 4.96/1.00  % (30661)------------------------------
% 8.74/1.46  % (30660)Time limit reached!
% 8.74/1.46  % (30660)------------------------------
% 8.74/1.46  % (30660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.74/1.46  % (30660)Termination reason: Time limit
% 8.74/1.46  % (30660)Termination phase: Saturation
% 8.74/1.46  
% 8.74/1.46  % (30660)Memory used [KB]: 39018
% 8.74/1.46  % (30660)Time elapsed: 1.0000 s
% 8.74/1.48  % (30660)------------------------------
% 8.74/1.48  % (30660)------------------------------
% 45.14/6.03  % (30663)Refutation found. Thanks to Tanya!
% 45.14/6.03  % SZS status Theorem for theBenchmark
% 45.14/6.03  % SZS output start Proof for theBenchmark
% 45.14/6.03  fof(f168674,plain,(
% 45.14/6.03    $false),
% 45.14/6.03    inference(trivial_inequality_removal,[],[f168673])).
% 45.14/6.03  fof(f168673,plain,(
% 45.14/6.03    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)),
% 45.14/6.03    inference(superposition,[],[f17,f129370])).
% 45.14/6.03  fof(f129370,plain,(
% 45.14/6.03    ( ! [X78,X79] : (k4_xboole_0(X78,X79) = k4_xboole_0(X78,k3_xboole_0(X78,X79))) )),
% 45.14/6.03    inference(forward_demodulation,[],[f128980,f42913])).
% 45.14/6.03  fof(f42913,plain,(
% 45.14/6.03    ( ! [X134,X132,X133] : (k4_xboole_0(X134,X132) = k4_xboole_0(k4_xboole_0(X134,X132),k3_xboole_0(X133,X132))) )),
% 45.14/6.03    inference(superposition,[],[f691,f29])).
% 45.14/6.03  fof(f29,plain,(
% 45.14/6.03    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0) )),
% 45.14/6.03    inference(superposition,[],[f21,f19])).
% 45.14/6.03  fof(f19,plain,(
% 45.14/6.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 45.14/6.03    inference(cnf_transformation,[],[f2])).
% 45.14/6.03  fof(f2,axiom,(
% 45.14/6.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 45.14/6.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 45.14/6.03  fof(f21,plain,(
% 45.14/6.03    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 45.14/6.03    inference(cnf_transformation,[],[f3])).
% 45.14/6.03  fof(f3,axiom,(
% 45.14/6.03    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 45.14/6.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 45.14/6.03  fof(f691,plain,(
% 45.14/6.03    ( ! [X28,X29,X27] : (k4_xboole_0(X28,k2_xboole_0(X29,X27)) = k4_xboole_0(k4_xboole_0(X28,k2_xboole_0(X29,X27)),X27)) )),
% 45.14/6.03    inference(forward_demodulation,[],[f690,f25])).
% 45.14/6.03  fof(f25,plain,(
% 45.14/6.03    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 45.14/6.03    inference(cnf_transformation,[],[f9])).
% 45.14/6.03  fof(f9,axiom,(
% 45.14/6.03    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 45.14/6.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 45.14/6.03  fof(f690,plain,(
% 45.14/6.03    ( ! [X28,X29,X27] : (k4_xboole_0(k4_xboole_0(X28,k2_xboole_0(X29,X27)),X27) = k4_xboole_0(k4_xboole_0(X28,X29),X27)) )),
% 45.14/6.03    inference(forward_demodulation,[],[f656,f34])).
% 45.14/6.03  fof(f34,plain,(
% 45.14/6.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 45.14/6.03    inference(superposition,[],[f22,f20])).
% 45.14/6.03  fof(f20,plain,(
% 45.14/6.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 45.14/6.03    inference(cnf_transformation,[],[f1])).
% 45.14/6.03  fof(f1,axiom,(
% 45.14/6.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 45.14/6.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 45.14/6.03  fof(f22,plain,(
% 45.14/6.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 45.14/6.03    inference(cnf_transformation,[],[f8])).
% 45.14/6.03  fof(f8,axiom,(
% 45.14/6.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 45.14/6.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 45.14/6.03  fof(f656,plain,(
% 45.14/6.03    ( ! [X28,X29,X27] : (k4_xboole_0(k4_xboole_0(X28,k2_xboole_0(X29,X27)),X27) = k4_xboole_0(k2_xboole_0(X27,k4_xboole_0(X28,X29)),X27)) )),
% 45.14/6.03    inference(superposition,[],[f34,f58])).
% 45.14/6.03  fof(f58,plain,(
% 45.14/6.03    ( ! [X4,X5,X3] : (k2_xboole_0(X5,k4_xboole_0(X3,X4)) = k2_xboole_0(X5,k4_xboole_0(X3,k2_xboole_0(X4,X5)))) )),
% 45.14/6.03    inference(superposition,[],[f23,f25])).
% 45.14/6.03  fof(f23,plain,(
% 45.14/6.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 45.14/6.03    inference(cnf_transformation,[],[f7])).
% 45.14/6.03  fof(f7,axiom,(
% 45.14/6.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 45.14/6.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 45.14/6.03  fof(f128980,plain,(
% 45.14/6.03    ( ! [X78,X79] : (k4_xboole_0(X78,k3_xboole_0(X78,X79)) = k4_xboole_0(k4_xboole_0(X78,X79),k3_xboole_0(X78,X79))) )),
% 45.14/6.03    inference(superposition,[],[f22,f76661])).
% 45.14/6.03  fof(f76661,plain,(
% 45.14/6.03    ( ! [X136,X137] : (k2_xboole_0(k4_xboole_0(X136,X137),k3_xboole_0(X136,X137)) = X136) )),
% 45.14/6.03    inference(forward_demodulation,[],[f76591,f140])).
% 45.14/6.03  fof(f140,plain,(
% 45.14/6.03    ( ! [X4,X5] : (k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4) )),
% 45.14/6.03    inference(superposition,[],[f29,f31])).
% 45.14/6.03  fof(f31,plain,(
% 45.14/6.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 45.14/6.03    inference(resolution,[],[f24,f18])).
% 45.14/6.03  fof(f18,plain,(
% 45.14/6.03    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 45.14/6.03    inference(cnf_transformation,[],[f6])).
% 45.14/6.03  fof(f6,axiom,(
% 45.14/6.03    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 45.14/6.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 45.14/6.03  fof(f24,plain,(
% 45.14/6.03    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 45.14/6.03    inference(cnf_transformation,[],[f15])).
% 45.14/6.03  fof(f15,plain,(
% 45.14/6.03    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 45.14/6.03    inference(ennf_transformation,[],[f5])).
% 45.14/6.03  fof(f5,axiom,(
% 45.14/6.03    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 45.14/6.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 45.14/6.03  fof(f76591,plain,(
% 45.14/6.03    ( ! [X136,X137] : (k2_xboole_0(X136,k4_xboole_0(X136,X137)) = k2_xboole_0(k4_xboole_0(X136,X137),k3_xboole_0(X136,X137))) )),
% 45.14/6.03    inference(resolution,[],[f538,f42682])).
% 45.14/6.03  fof(f42682,plain,(
% 45.14/6.03    ( ! [X316,X317] : (r1_tarski(k4_xboole_0(X317,k4_xboole_0(X317,X316)),X316)) )),
% 45.14/6.03    inference(superposition,[],[f543,f42361])).
% 45.14/6.03  fof(f42361,plain,(
% 45.14/6.03    ( ! [X10,X11] : (k2_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X11,X10))) = X10) )),
% 45.14/6.03    inference(forward_demodulation,[],[f42360,f140])).
% 45.14/6.03  fof(f42360,plain,(
% 45.14/6.03    ( ! [X10,X11] : (k2_xboole_0(X10,k4_xboole_0(X10,X11)) = k2_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X11,X10)))) )),
% 45.14/6.03    inference(forward_demodulation,[],[f42072,f3795])).
% 45.14/6.03  fof(f3795,plain,(
% 45.14/6.03    ( ! [X37,X35,X36] : (k2_xboole_0(X36,k4_xboole_0(X37,k4_xboole_0(X35,X36))) = k2_xboole_0(X36,k4_xboole_0(X37,X35))) )),
% 45.14/6.03    inference(forward_demodulation,[],[f3723,f634])).
% 45.14/6.03  fof(f634,plain,(
% 45.14/6.03    ( ! [X4,X2,X3] : (k2_xboole_0(X3,k4_xboole_0(X4,X2)) = k2_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2)))) )),
% 45.14/6.03    inference(superposition,[],[f58,f20])).
% 45.14/6.03  fof(f3723,plain,(
% 45.14/6.03    ( ! [X37,X35,X36] : (k2_xboole_0(X36,k4_xboole_0(X37,k4_xboole_0(X35,X36))) = k2_xboole_0(X36,k4_xboole_0(X37,k2_xboole_0(X36,X35)))) )),
% 45.14/6.03    inference(superposition,[],[f58,f604])).
% 45.14/6.03  fof(f604,plain,(
% 45.14/6.03    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X3,X2),X2)) )),
% 45.14/6.03    inference(forward_demodulation,[],[f603,f195])).
% 45.14/6.03  fof(f195,plain,(
% 45.14/6.03    ( ! [X10,X11] : (k2_xboole_0(X10,X11) = k2_xboole_0(k4_xboole_0(X11,X10),k2_xboole_0(X10,X11))) )),
% 45.14/6.03    inference(forward_demodulation,[],[f194,f23])).
% 45.14/6.03  fof(f194,plain,(
% 45.14/6.03    ( ! [X10,X11] : (k2_xboole_0(X10,k4_xboole_0(X11,X10)) = k2_xboole_0(k4_xboole_0(X11,X10),k2_xboole_0(X10,X11))) )),
% 45.14/6.03    inference(forward_demodulation,[],[f180,f20])).
% 45.14/6.03  fof(f180,plain,(
% 45.14/6.03    ( ! [X10,X11] : (k2_xboole_0(k4_xboole_0(X11,X10),X10) = k2_xboole_0(k4_xboole_0(X11,X10),k2_xboole_0(X10,X11))) )),
% 45.14/6.03    inference(superposition,[],[f39,f23])).
% 45.14/6.03  fof(f39,plain,(
% 45.14/6.03    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))) )),
% 45.14/6.03    inference(forward_demodulation,[],[f37,f23])).
% 45.14/6.03  fof(f37,plain,(
% 45.14/6.03    ( ! [X0,X1] : (k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 45.14/6.03    inference(superposition,[],[f23,f22])).
% 45.14/6.03  fof(f603,plain,(
% 45.14/6.03    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X3,X2),X2) = k2_xboole_0(k4_xboole_0(X3,X2),k2_xboole_0(X2,X3))) )),
% 45.14/6.03    inference(forward_demodulation,[],[f580,f23])).
% 45.14/6.03  fof(f580,plain,(
% 45.14/6.03    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X3,X2),k2_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,k4_xboole_0(X3,X2)))) )),
% 45.14/6.03    inference(superposition,[],[f23,f38])).
% 45.14/6.03  fof(f38,plain,(
% 45.14/6.03    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 45.14/6.03    inference(superposition,[],[f22,f23])).
% 45.14/6.03  fof(f42072,plain,(
% 45.14/6.03    ( ! [X10,X11] : (k2_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,X10))) = k2_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X11,X10)))) )),
% 45.14/6.03    inference(superposition,[],[f678,f38])).
% 45.14/6.03  fof(f678,plain,(
% 45.14/6.03    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X2,X0),X1))) )),
% 45.14/6.03    inference(forward_demodulation,[],[f677,f454])).
% 45.14/6.03  fof(f454,plain,(
% 45.14/6.03    ( ! [X33,X34,X32] : (k4_xboole_0(k2_xboole_0(X33,X34),X32) = k4_xboole_0(k2_xboole_0(X34,k2_xboole_0(X32,X33)),X32)) )),
% 45.14/6.03    inference(superposition,[],[f34,f79])).
% 45.14/6.03  fof(f79,plain,(
% 45.14/6.03    ( ! [X4,X5,X3] : (k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4))) )),
% 45.14/6.03    inference(superposition,[],[f26,f20])).
% 45.14/6.03  fof(f26,plain,(
% 45.14/6.03    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 45.14/6.03    inference(cnf_transformation,[],[f11])).
% 45.14/6.03  fof(f11,axiom,(
% 45.14/6.03    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 45.14/6.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 45.14/6.03  fof(f677,plain,(
% 45.14/6.03    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1))) )),
% 45.14/6.03    inference(forward_demodulation,[],[f644,f58])).
% 45.14/6.03  fof(f644,plain,(
% 45.14/6.03    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 45.14/6.03    inference(superposition,[],[f58,f22])).
% 45.14/6.03  fof(f543,plain,(
% 45.14/6.03    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) )),
% 45.14/6.03    inference(superposition,[],[f515,f20])).
% 45.14/6.03  fof(f515,plain,(
% 45.14/6.03    ( ! [X4,X5] : (r1_tarski(X4,k2_xboole_0(X4,X5))) )),
% 45.14/6.03    inference(superposition,[],[f340,f216])).
% 45.14/6.03  fof(f216,plain,(
% 45.14/6.03    ( ! [X6,X5] : (k3_xboole_0(X5,k2_xboole_0(X5,X6)) = X5) )),
% 45.14/6.03    inference(forward_demodulation,[],[f208,f21])).
% 45.14/6.03  fof(f208,plain,(
% 45.14/6.03    ( ! [X6,X5] : (k2_xboole_0(X5,k3_xboole_0(X5,X6)) = k3_xboole_0(X5,k2_xboole_0(X5,X6))) )),
% 45.14/6.03    inference(superposition,[],[f27,f164])).
% 45.14/6.03  fof(f164,plain,(
% 45.14/6.03    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 45.14/6.03    inference(superposition,[],[f140,f23])).
% 45.14/6.03  fof(f27,plain,(
% 45.14/6.03    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 45.14/6.03    inference(cnf_transformation,[],[f4])).
% 45.14/6.03  fof(f4,axiom,(
% 45.14/6.03    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 45.14/6.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).
% 45.14/6.03  fof(f340,plain,(
% 45.14/6.03    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 45.14/6.03    inference(superposition,[],[f270,f19])).
% 45.14/6.03  fof(f270,plain,(
% 45.14/6.03    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 45.14/6.03    inference(resolution,[],[f43,f18])).
% 45.14/6.03  fof(f43,plain,(
% 45.14/6.03    ( ! [X6,X8,X7] : (~r1_tarski(k4_xboole_0(X8,X6),k3_xboole_0(X6,X7)) | r1_tarski(X8,X6)) )),
% 45.14/6.03    inference(superposition,[],[f28,f21])).
% 45.14/6.03  fof(f28,plain,(
% 45.14/6.03    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 45.14/6.03    inference(cnf_transformation,[],[f16])).
% 45.14/6.03  fof(f16,plain,(
% 45.14/6.03    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 45.14/6.03    inference(ennf_transformation,[],[f10])).
% 45.14/6.03  fof(f10,axiom,(
% 45.14/6.03    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 45.14/6.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 45.14/6.03  fof(f538,plain,(
% 45.14/6.03    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | k2_xboole_0(X0,X1) = k2_xboole_0(X1,k3_xboole_0(X0,X2))) )),
% 45.14/6.03    inference(forward_demodulation,[],[f528,f103])).
% 45.14/6.03  fof(f103,plain,(
% 45.14/6.03    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X2))) )),
% 45.14/6.03    inference(superposition,[],[f27,f20])).
% 45.14/6.03  fof(f528,plain,(
% 45.14/6.03    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | k2_xboole_0(X0,X1) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2))) )),
% 45.14/6.03    inference(superposition,[],[f40,f22])).
% 45.14/6.03  fof(f40,plain,(
% 45.14/6.03    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = X0) )),
% 45.14/6.03    inference(resolution,[],[f28,f24])).
% 45.14/6.03  fof(f17,plain,(
% 45.14/6.03    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 45.14/6.03    inference(cnf_transformation,[],[f14])).
% 45.14/6.03  fof(f14,plain,(
% 45.14/6.03    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 45.14/6.03    inference(ennf_transformation,[],[f13])).
% 45.14/6.03  fof(f13,negated_conjecture,(
% 45.14/6.03    ~! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 45.14/6.03    inference(negated_conjecture,[],[f12])).
% 45.14/6.03  fof(f12,conjecture,(
% 45.14/6.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 45.14/6.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 45.14/6.03  % SZS output end Proof for theBenchmark
% 45.14/6.03  % (30663)------------------------------
% 45.14/6.03  % (30663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 45.14/6.03  % (30663)Termination reason: Refutation
% 45.14/6.03  
% 45.14/6.03  % (30663)Memory used [KB]: 158632
% 45.14/6.03  % (30663)Time elapsed: 5.593 s
% 45.14/6.03  % (30663)------------------------------
% 45.14/6.03  % (30663)------------------------------
% 45.14/6.04  % (30658)Success in time 5.671 s
%------------------------------------------------------------------------------
