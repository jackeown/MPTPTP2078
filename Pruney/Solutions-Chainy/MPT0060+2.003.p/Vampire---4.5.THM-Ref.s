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
% DateTime   : Thu Dec  3 12:30:13 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 147 expanded)
%              Number of leaves         :   10 (  46 expanded)
%              Depth                    :   19
%              Number of atoms          :   59 ( 172 expanded)
%              Number of equality atoms :   43 ( 121 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2312,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f2311])).

fof(f2311,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f1788,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1788,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    inference(backward_demodulation,[],[f863,f1781])).

fof(f1781,plain,(
    ! [X12,X11] : k4_xboole_0(X11,X12) = k3_xboole_0(k4_xboole_0(X11,X12),X11) ),
    inference(backward_demodulation,[],[f1585,f1734])).

fof(f1734,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(superposition,[],[f1728,f72])).

fof(f72,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = X2 ),
    inference(forward_demodulation,[],[f71,f25])).

fof(f25,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f24,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f21,f16])).

fof(f16,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f71,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f66,f17])).

fof(f66,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f18,f20])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1728,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X0),X1) = X1 ),
    inference(resolution,[],[f1706,f21])).

fof(f1706,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X1,X1),X0) ),
    inference(superposition,[],[f1443,f24])).

fof(f1443,plain,(
    ! [X10,X11,X9] : r1_tarski(k4_xboole_0(X10,X10),k2_xboole_0(k4_xboole_0(X9,X10),X11)) ),
    inference(forward_demodulation,[],[f1442,f947])).

fof(f947,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X0) = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f23,f34])).

fof(f34,plain,(
    ! [X10,X9] : k4_xboole_0(k4_xboole_0(X9,X10),X9) = k4_xboole_0(X9,X9) ),
    inference(superposition,[],[f19,f24])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f1442,plain,(
    ! [X10,X11,X9] : r1_tarski(k4_xboole_0(X10,k2_xboole_0(X9,X10)),k2_xboole_0(k4_xboole_0(X9,X10),X11)) ),
    inference(forward_demodulation,[],[f1421,f993])).

fof(f993,plain,(
    ! [X6,X8,X7] : k4_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,X8)) = k4_xboole_0(X7,k2_xboole_0(X6,X8)) ),
    inference(forward_demodulation,[],[f942,f23])).

fof(f942,plain,(
    ! [X6,X8,X7] : k4_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,X8)) = k4_xboole_0(k4_xboole_0(X7,X6),X8) ),
    inference(superposition,[],[f23,f31])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f19,f17])).

fof(f1421,plain,(
    ! [X10,X11,X9] : r1_tarski(k4_xboole_0(k2_xboole_0(X9,X10),k2_xboole_0(X9,X10)),k2_xboole_0(k4_xboole_0(X9,X10),X11)) ),
    inference(superposition,[],[f1108,f19])).

fof(f1108,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,X0),k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(forward_demodulation,[],[f1107,f947])).

fof(f1107,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X0)),k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(forward_demodulation,[],[f1090,f18])).

fof(f1090,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))),k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(superposition,[],[f1000,f23])).

fof(f1000,plain,(
    ! [X8,X9] : r1_tarski(k4_xboole_0(X8,X8),k2_xboole_0(X8,X9)) ),
    inference(backward_demodulation,[],[f115,f947])).

fof(f115,plain,(
    ! [X8,X9] : r1_tarski(k4_xboole_0(X8,k2_xboole_0(X9,X8)),k2_xboole_0(X8,X9)) ),
    inference(superposition,[],[f38,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f35,f18])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f18,f19])).

fof(f38,plain,(
    ! [X6,X7] : r1_tarski(k4_xboole_0(X6,X7),k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f16,f19])).

fof(f1585,plain,(
    ! [X12,X11] : k3_xboole_0(k4_xboole_0(X11,X12),X11) = k3_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X12)) ),
    inference(superposition,[],[f1338,f25])).

fof(f1338,plain,(
    ! [X8,X9] : k3_xboole_0(X8,k2_xboole_0(X9,X8)) = k3_xboole_0(X8,X8) ),
    inference(forward_demodulation,[],[f1289,f20])).

fof(f1289,plain,(
    ! [X8,X9] : k3_xboole_0(X8,k2_xboole_0(X9,X8)) = k4_xboole_0(X8,k4_xboole_0(X8,X8)) ),
    inference(superposition,[],[f20,f947])).

fof(f863,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK1),sK0),sK2) ),
    inference(superposition,[],[f15,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f15,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))
   => k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:30:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (28706)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.45  % (28697)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.46  % (28705)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (28700)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (28699)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (28701)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (28703)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (28714)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  % (28704)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (28708)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (28710)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (28708)Refutation not found, incomplete strategy% (28708)------------------------------
% 0.22/0.50  % (28708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (28708)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (28708)Memory used [KB]: 10618
% 0.22/0.50  % (28708)Time elapsed: 0.083 s
% 0.22/0.50  % (28708)------------------------------
% 0.22/0.50  % (28708)------------------------------
% 0.22/0.50  % (28698)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (28713)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.50  % (28709)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.50  % (28702)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.51  % (28711)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.51  % (28712)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.52  % (28707)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 1.59/0.56  % (28713)Refutation found. Thanks to Tanya!
% 1.59/0.56  % SZS status Theorem for theBenchmark
% 1.59/0.56  % SZS output start Proof for theBenchmark
% 1.59/0.56  fof(f2312,plain,(
% 1.59/0.56    $false),
% 1.59/0.56    inference(trivial_inequality_removal,[],[f2311])).
% 1.59/0.56  fof(f2311,plain,(
% 1.59/0.56    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 1.59/0.56    inference(superposition,[],[f1788,f23])).
% 1.59/0.56  fof(f23,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.59/0.56    inference(cnf_transformation,[],[f6])).
% 1.59/0.56  fof(f6,axiom,(
% 1.59/0.56    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.59/0.56  fof(f1788,plain,(
% 1.59/0.56    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)),
% 1.59/0.56    inference(backward_demodulation,[],[f863,f1781])).
% 1.59/0.56  fof(f1781,plain,(
% 1.59/0.56    ( ! [X12,X11] : (k4_xboole_0(X11,X12) = k3_xboole_0(k4_xboole_0(X11,X12),X11)) )),
% 1.59/0.56    inference(backward_demodulation,[],[f1585,f1734])).
% 1.59/0.56  fof(f1734,plain,(
% 1.59/0.56    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 1.59/0.56    inference(superposition,[],[f1728,f72])).
% 1.59/0.56  fof(f72,plain,(
% 1.59/0.56    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = X2) )),
% 1.59/0.56    inference(forward_demodulation,[],[f71,f25])).
% 1.59/0.56  fof(f25,plain,(
% 1.59/0.56    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 1.59/0.56    inference(superposition,[],[f24,f17])).
% 1.59/0.56  fof(f17,plain,(
% 1.59/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f1])).
% 1.59/0.56  fof(f1,axiom,(
% 1.59/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.59/0.56  fof(f24,plain,(
% 1.59/0.56    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 1.59/0.56    inference(resolution,[],[f21,f16])).
% 1.59/0.56  fof(f16,plain,(
% 1.59/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f3])).
% 1.59/0.56  fof(f3,axiom,(
% 1.59/0.56    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.59/0.56  fof(f21,plain,(
% 1.59/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.59/0.56    inference(cnf_transformation,[],[f12])).
% 1.59/0.56  fof(f12,plain,(
% 1.59/0.56    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.59/0.56    inference(ennf_transformation,[],[f2])).
% 1.59/0.56  fof(f2,axiom,(
% 1.59/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.59/0.56  fof(f71,plain,(
% 1.59/0.56    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3))) )),
% 1.59/0.56    inference(forward_demodulation,[],[f66,f17])).
% 1.59/0.56  fof(f66,plain,(
% 1.59/0.56    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3))) )),
% 1.59/0.56    inference(superposition,[],[f18,f20])).
% 1.59/0.56  fof(f20,plain,(
% 1.59/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f7])).
% 1.59/0.56  fof(f7,axiom,(
% 1.59/0.56    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.59/0.56  fof(f18,plain,(
% 1.59/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.59/0.56    inference(cnf_transformation,[],[f4])).
% 1.59/0.56  fof(f4,axiom,(
% 1.59/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.59/0.56  fof(f1728,plain,(
% 1.59/0.56    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X0),X1) = X1) )),
% 1.59/0.56    inference(resolution,[],[f1706,f21])).
% 1.59/0.56  fof(f1706,plain,(
% 1.59/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,X1),X0)) )),
% 1.59/0.56    inference(superposition,[],[f1443,f24])).
% 1.59/0.56  fof(f1443,plain,(
% 1.59/0.56    ( ! [X10,X11,X9] : (r1_tarski(k4_xboole_0(X10,X10),k2_xboole_0(k4_xboole_0(X9,X10),X11))) )),
% 1.59/0.56    inference(forward_demodulation,[],[f1442,f947])).
% 1.59/0.56  fof(f947,plain,(
% 1.59/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = k4_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 1.59/0.56    inference(superposition,[],[f23,f34])).
% 1.59/0.56  fof(f34,plain,(
% 1.59/0.56    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(X9,X10),X9) = k4_xboole_0(X9,X9)) )),
% 1.59/0.56    inference(superposition,[],[f19,f24])).
% 1.59/0.56  fof(f19,plain,(
% 1.59/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f5])).
% 1.59/0.56  fof(f5,axiom,(
% 1.59/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.59/0.56  fof(f1442,plain,(
% 1.59/0.56    ( ! [X10,X11,X9] : (r1_tarski(k4_xboole_0(X10,k2_xboole_0(X9,X10)),k2_xboole_0(k4_xboole_0(X9,X10),X11))) )),
% 1.59/0.56    inference(forward_demodulation,[],[f1421,f993])).
% 1.59/0.56  fof(f993,plain,(
% 1.59/0.56    ( ! [X6,X8,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,X8)) = k4_xboole_0(X7,k2_xboole_0(X6,X8))) )),
% 1.59/0.56    inference(forward_demodulation,[],[f942,f23])).
% 1.59/0.56  fof(f942,plain,(
% 1.59/0.56    ( ! [X6,X8,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,X8)) = k4_xboole_0(k4_xboole_0(X7,X6),X8)) )),
% 1.59/0.56    inference(superposition,[],[f23,f31])).
% 1.59/0.56  fof(f31,plain,(
% 1.59/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 1.59/0.56    inference(superposition,[],[f19,f17])).
% 1.59/0.56  fof(f1421,plain,(
% 1.59/0.56    ( ! [X10,X11,X9] : (r1_tarski(k4_xboole_0(k2_xboole_0(X9,X10),k2_xboole_0(X9,X10)),k2_xboole_0(k4_xboole_0(X9,X10),X11))) )),
% 1.59/0.56    inference(superposition,[],[f1108,f19])).
% 1.59/0.56  fof(f1108,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 1.59/0.56    inference(forward_demodulation,[],[f1107,f947])).
% 1.59/0.56  fof(f1107,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X0)),k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 1.59/0.56    inference(forward_demodulation,[],[f1090,f18])).
% 1.59/0.56  fof(f1090,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))),k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 1.59/0.56    inference(superposition,[],[f1000,f23])).
% 1.59/0.56  fof(f1000,plain,(
% 1.59/0.56    ( ! [X8,X9] : (r1_tarski(k4_xboole_0(X8,X8),k2_xboole_0(X8,X9))) )),
% 1.59/0.56    inference(backward_demodulation,[],[f115,f947])).
% 1.59/0.56  fof(f115,plain,(
% 1.59/0.56    ( ! [X8,X9] : (r1_tarski(k4_xboole_0(X8,k2_xboole_0(X9,X8)),k2_xboole_0(X8,X9))) )),
% 1.59/0.56    inference(superposition,[],[f38,f39])).
% 1.59/0.56  fof(f39,plain,(
% 1.59/0.56    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))) )),
% 1.59/0.56    inference(forward_demodulation,[],[f35,f18])).
% 1.59/0.56  fof(f35,plain,(
% 1.59/0.56    ( ! [X0,X1] : (k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 1.59/0.56    inference(superposition,[],[f18,f19])).
% 1.59/0.56  fof(f38,plain,(
% 1.59/0.56    ( ! [X6,X7] : (r1_tarski(k4_xboole_0(X6,X7),k2_xboole_0(X6,X7))) )),
% 1.59/0.56    inference(superposition,[],[f16,f19])).
% 1.59/0.56  fof(f1585,plain,(
% 1.59/0.56    ( ! [X12,X11] : (k3_xboole_0(k4_xboole_0(X11,X12),X11) = k3_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X12))) )),
% 1.59/0.56    inference(superposition,[],[f1338,f25])).
% 1.59/0.56  fof(f1338,plain,(
% 1.59/0.56    ( ! [X8,X9] : (k3_xboole_0(X8,k2_xboole_0(X9,X8)) = k3_xboole_0(X8,X8)) )),
% 1.59/0.56    inference(forward_demodulation,[],[f1289,f20])).
% 1.59/0.56  fof(f1289,plain,(
% 1.59/0.56    ( ! [X8,X9] : (k3_xboole_0(X8,k2_xboole_0(X9,X8)) = k4_xboole_0(X8,k4_xboole_0(X8,X8))) )),
% 1.59/0.56    inference(superposition,[],[f20,f947])).
% 1.59/0.56  fof(f863,plain,(
% 1.59/0.56    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK1),sK0),sK2)),
% 1.59/0.56    inference(superposition,[],[f15,f22])).
% 1.59/0.56  fof(f22,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f8])).
% 1.59/0.56  fof(f8,axiom,(
% 1.59/0.56    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.59/0.56  fof(f15,plain,(
% 1.59/0.56    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 1.59/0.56    inference(cnf_transformation,[],[f14])).
% 1.59/0.56  fof(f14,plain,(
% 1.59/0.56    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 1.59/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 1.59/0.56  fof(f13,plain,(
% 1.59/0.56    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) => k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 1.59/0.56    introduced(choice_axiom,[])).
% 1.59/0.56  fof(f11,plain,(
% 1.59/0.56    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 1.59/0.56    inference(ennf_transformation,[],[f10])).
% 1.59/0.56  fof(f10,negated_conjecture,(
% 1.59/0.56    ~! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 1.59/0.56    inference(negated_conjecture,[],[f9])).
% 1.59/0.56  fof(f9,conjecture,(
% 1.59/0.56    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).
% 1.59/0.56  % SZS output end Proof for theBenchmark
% 1.59/0.56  % (28713)------------------------------
% 1.59/0.56  % (28713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.56  % (28713)Termination reason: Refutation
% 1.59/0.56  
% 1.59/0.56  % (28713)Memory used [KB]: 7291
% 1.59/0.56  % (28713)Time elapsed: 0.132 s
% 1.59/0.56  % (28713)------------------------------
% 1.59/0.56  % (28713)------------------------------
% 1.59/0.56  % (28696)Success in time 0.197 s
%------------------------------------------------------------------------------
