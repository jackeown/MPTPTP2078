%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:58 EST 2020

% Result     : Theorem 2.93s
% Output     : Refutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 147 expanded)
%              Number of leaves         :   13 (  49 expanded)
%              Depth                    :   16
%              Number of atoms          :   71 ( 171 expanded)
%              Number of equality atoms :   60 ( 137 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8053,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8052,f54])).

fof(f54,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f52,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f52,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f50,f21])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f50,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f26,f21])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f8052,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f8051,f159])).

fof(f159,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X4,k2_xboole_0(X2,X3))) ),
    inference(superposition,[],[f143,f24])).

fof(f143,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    inference(forward_demodulation,[],[f127,f20])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f127,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4)) = k4_xboole_0(k1_xboole_0,X4) ),
    inference(superposition,[],[f31,f41])).

fof(f41,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f30,f22])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f8051,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f8050,f31])).

fof(f8050,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f351,f7949])).

fof(f7949,plain,(
    ! [X109,X110,X108] : k4_xboole_0(X110,k2_xboole_0(X108,X109)) = k4_xboole_0(k2_xboole_0(X110,k4_xboole_0(X109,X108)),k2_xboole_0(X108,X109)) ),
    inference(superposition,[],[f2296,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f26,f24])).

fof(f2296,plain,(
    ! [X35,X33,X34] : k4_xboole_0(k2_xboole_0(X35,k4_xboole_0(X33,X34)),X33) = k4_xboole_0(X35,X33) ),
    inference(superposition,[],[f146,f2137])).

fof(f2137,plain,(
    ! [X21,X22] : k2_xboole_0(k4_xboole_0(X21,X22),X21) = X21 ),
    inference(superposition,[],[f39,f1985])).

fof(f1985,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3 ),
    inference(superposition,[],[f1902,f21])).

fof(f1902,plain,(
    ! [X2,X3] : k4_xboole_0(k2_xboole_0(X2,k4_xboole_0(X2,X3)),k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f1767,f24])).

fof(f1767,plain,(
    ! [X2,X3] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,X3),X2),k1_xboole_0) = X2 ),
    inference(superposition,[],[f325,f42])).

fof(f42,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(resolution,[],[f30,f34])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f22,f24])).

fof(f325,plain,(
    ! [X30,X31,X32] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X30,X31),X32),k4_xboole_0(X30,k2_xboole_0(X31,X32))) = X32 ),
    inference(superposition,[],[f284,f31])).

fof(f284,plain,(
    ! [X24,X25] : k4_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,X25)) = X25 ),
    inference(forward_demodulation,[],[f283,f21])).

fof(f283,plain,(
    ! [X24,X25] : k4_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,X25)) = k4_xboole_0(X25,k1_xboole_0) ),
    inference(forward_demodulation,[],[f259,f42])).

fof(f259,plain,(
    ! [X24,X25] : k4_xboole_0(X25,k4_xboole_0(X25,k2_xboole_0(X24,X25))) = k4_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,X25)) ),
    inference(superposition,[],[f33,f26])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f25,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f39,plain,(
    ! [X2,X3] : k2_xboole_0(X3,X2) = k2_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(resolution,[],[f28,f34])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f146,plain,(
    ! [X12,X10,X11] : k4_xboole_0(k2_xboole_0(X10,X11),k2_xboole_0(X11,X12)) = k4_xboole_0(X10,k2_xboole_0(X11,X12)) ),
    inference(forward_demodulation,[],[f130,f31])).

fof(f130,plain,(
    ! [X12,X10,X11] : k4_xboole_0(k2_xboole_0(X10,X11),k2_xboole_0(X11,X12)) = k4_xboole_0(k4_xboole_0(X10,X11),X12) ),
    inference(superposition,[],[f31,f26])).

fof(f351,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f350,f33])).

fof(f350,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) ),
    inference(backward_demodulation,[],[f32,f328])).

fof(f328,plain,(
    ! [X6,X8,X7] : k4_xboole_0(X7,X8) = k4_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(k4_xboole_0(X6,X7),X8)) ),
    inference(superposition,[],[f31,f284])).

fof(f32,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f19,f25,f27,f27])).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f19,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).

fof(f16,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (10018)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.43  % (10007)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (10006)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (10016)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (10020)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (10010)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (10012)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (10013)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (10022)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (10019)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (10011)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (10014)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (10008)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (10009)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (10023)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (10015)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.51  % (10021)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (10017)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.51  % (10017)Refutation not found, incomplete strategy% (10017)------------------------------
% 0.21/0.51  % (10017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (10017)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (10017)Memory used [KB]: 10490
% 0.21/0.51  % (10017)Time elapsed: 0.110 s
% 0.21/0.51  % (10017)------------------------------
% 0.21/0.51  % (10017)------------------------------
% 2.93/0.75  % (10020)Refutation found. Thanks to Tanya!
% 2.93/0.75  % SZS status Theorem for theBenchmark
% 3.33/0.77  % SZS output start Proof for theBenchmark
% 3.33/0.77  fof(f8053,plain,(
% 3.33/0.77    $false),
% 3.33/0.77    inference(subsumption_resolution,[],[f8052,f54])).
% 3.33/0.77  fof(f54,plain,(
% 3.33/0.77    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 3.33/0.77    inference(superposition,[],[f52,f24])).
% 3.33/0.77  fof(f24,plain,(
% 3.33/0.77    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.33/0.77    inference(cnf_transformation,[],[f1])).
% 3.33/0.77  fof(f1,axiom,(
% 3.33/0.77    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.33/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.33/0.77  fof(f52,plain,(
% 3.33/0.77    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 3.33/0.77    inference(forward_demodulation,[],[f50,f21])).
% 3.33/0.77  fof(f21,plain,(
% 3.33/0.77    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.33/0.77    inference(cnf_transformation,[],[f6])).
% 3.33/0.77  fof(f6,axiom,(
% 3.33/0.77    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.33/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 3.33/0.77  fof(f50,plain,(
% 3.33/0.77    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 3.33/0.77    inference(superposition,[],[f26,f21])).
% 3.33/0.77  fof(f26,plain,(
% 3.33/0.77    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 3.33/0.77    inference(cnf_transformation,[],[f7])).
% 3.33/0.77  fof(f7,axiom,(
% 3.33/0.77    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 3.33/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 3.33/0.77  fof(f8052,plain,(
% 3.33/0.77    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 3.33/0.77    inference(forward_demodulation,[],[f8051,f159])).
% 3.33/0.77  fof(f159,plain,(
% 3.33/0.77    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X4,k2_xboole_0(X2,X3)))) )),
% 3.33/0.77    inference(superposition,[],[f143,f24])).
% 3.33/0.77  fof(f143,plain,(
% 3.33/0.77    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4))) )),
% 3.33/0.77    inference(forward_demodulation,[],[f127,f20])).
% 3.33/0.77  fof(f20,plain,(
% 3.33/0.77    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 3.33/0.77    inference(cnf_transformation,[],[f10])).
% 3.33/0.77  fof(f10,axiom,(
% 3.33/0.77    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 3.33/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 3.33/0.77  fof(f127,plain,(
% 3.33/0.77    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4)) = k4_xboole_0(k1_xboole_0,X4)) )),
% 3.33/0.77    inference(superposition,[],[f31,f41])).
% 3.33/0.77  fof(f41,plain,(
% 3.33/0.77    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.33/0.77    inference(resolution,[],[f30,f22])).
% 3.33/0.77  fof(f22,plain,(
% 3.33/0.77    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.33/0.77    inference(cnf_transformation,[],[f11])).
% 3.33/0.77  fof(f11,axiom,(
% 3.33/0.77    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.33/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.33/0.77  fof(f30,plain,(
% 3.33/0.77    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 3.33/0.77    inference(cnf_transformation,[],[f18])).
% 3.33/0.77  fof(f18,plain,(
% 3.33/0.77    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.33/0.77    inference(nnf_transformation,[],[f4])).
% 3.33/0.77  fof(f4,axiom,(
% 3.33/0.77    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.33/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 3.33/0.77  fof(f31,plain,(
% 3.33/0.77    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.33/0.77    inference(cnf_transformation,[],[f8])).
% 3.33/0.77  fof(f8,axiom,(
% 3.33/0.77    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.33/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 3.33/0.77  fof(f8051,plain,(
% 3.33/0.77    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 3.33/0.77    inference(forward_demodulation,[],[f8050,f31])).
% 3.33/0.77  fof(f8050,plain,(
% 3.33/0.77    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 3.33/0.77    inference(backward_demodulation,[],[f351,f7949])).
% 3.33/0.77  fof(f7949,plain,(
% 3.33/0.77    ( ! [X109,X110,X108] : (k4_xboole_0(X110,k2_xboole_0(X108,X109)) = k4_xboole_0(k2_xboole_0(X110,k4_xboole_0(X109,X108)),k2_xboole_0(X108,X109))) )),
% 3.33/0.77    inference(superposition,[],[f2296,f48])).
% 3.33/0.77  fof(f48,plain,(
% 3.33/0.77    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 3.33/0.77    inference(superposition,[],[f26,f24])).
% 3.33/0.77  fof(f2296,plain,(
% 3.33/0.77    ( ! [X35,X33,X34] : (k4_xboole_0(k2_xboole_0(X35,k4_xboole_0(X33,X34)),X33) = k4_xboole_0(X35,X33)) )),
% 3.33/0.77    inference(superposition,[],[f146,f2137])).
% 3.33/0.77  fof(f2137,plain,(
% 3.33/0.77    ( ! [X21,X22] : (k2_xboole_0(k4_xboole_0(X21,X22),X21) = X21) )),
% 3.33/0.77    inference(superposition,[],[f39,f1985])).
% 3.33/0.77  fof(f1985,plain,(
% 3.33/0.77    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3) )),
% 3.33/0.77    inference(superposition,[],[f1902,f21])).
% 3.33/0.77  fof(f1902,plain,(
% 3.33/0.77    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X2,k4_xboole_0(X2,X3)),k1_xboole_0) = X2) )),
% 3.33/0.77    inference(forward_demodulation,[],[f1767,f24])).
% 3.33/0.77  fof(f1767,plain,(
% 3.33/0.77    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,X3),X2),k1_xboole_0) = X2) )),
% 3.33/0.77    inference(superposition,[],[f325,f42])).
% 3.33/0.77  fof(f42,plain,(
% 3.33/0.77    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))) )),
% 3.33/0.77    inference(resolution,[],[f30,f34])).
% 3.33/0.77  fof(f34,plain,(
% 3.33/0.77    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 3.33/0.77    inference(superposition,[],[f22,f24])).
% 3.33/0.77  fof(f325,plain,(
% 3.33/0.77    ( ! [X30,X31,X32] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X30,X31),X32),k4_xboole_0(X30,k2_xboole_0(X31,X32))) = X32) )),
% 3.33/0.77    inference(superposition,[],[f284,f31])).
% 3.33/0.77  fof(f284,plain,(
% 3.33/0.77    ( ! [X24,X25] : (k4_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,X25)) = X25) )),
% 3.33/0.77    inference(forward_demodulation,[],[f283,f21])).
% 3.33/0.77  fof(f283,plain,(
% 3.33/0.77    ( ! [X24,X25] : (k4_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,X25)) = k4_xboole_0(X25,k1_xboole_0)) )),
% 3.33/0.77    inference(forward_demodulation,[],[f259,f42])).
% 3.33/0.77  fof(f259,plain,(
% 3.33/0.77    ( ! [X24,X25] : (k4_xboole_0(X25,k4_xboole_0(X25,k2_xboole_0(X24,X25))) = k4_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,X25))) )),
% 3.33/0.77    inference(superposition,[],[f33,f26])).
% 3.33/0.77  fof(f33,plain,(
% 3.33/0.77    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.33/0.77    inference(definition_unfolding,[],[f23,f25,f25])).
% 3.33/0.78  fof(f25,plain,(
% 3.33/0.78    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.33/0.78    inference(cnf_transformation,[],[f9])).
% 3.33/0.78  fof(f9,axiom,(
% 3.33/0.78    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.33/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.33/0.78  fof(f23,plain,(
% 3.33/0.78    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.33/0.78    inference(cnf_transformation,[],[f2])).
% 3.33/0.78  fof(f2,axiom,(
% 3.33/0.78    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.33/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.33/0.78  fof(f39,plain,(
% 3.33/0.78    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = k2_xboole_0(X2,k2_xboole_0(X3,X2))) )),
% 3.33/0.78    inference(resolution,[],[f28,f34])).
% 3.33/0.78  fof(f28,plain,(
% 3.33/0.78    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 3.33/0.78    inference(cnf_transformation,[],[f15])).
% 3.33/0.78  fof(f15,plain,(
% 3.33/0.78    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.33/0.78    inference(ennf_transformation,[],[f5])).
% 3.33/0.78  fof(f5,axiom,(
% 3.33/0.78    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.33/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 3.33/0.78  fof(f146,plain,(
% 3.33/0.78    ( ! [X12,X10,X11] : (k4_xboole_0(k2_xboole_0(X10,X11),k2_xboole_0(X11,X12)) = k4_xboole_0(X10,k2_xboole_0(X11,X12))) )),
% 3.33/0.78    inference(forward_demodulation,[],[f130,f31])).
% 3.33/0.78  fof(f130,plain,(
% 3.33/0.78    ( ! [X12,X10,X11] : (k4_xboole_0(k2_xboole_0(X10,X11),k2_xboole_0(X11,X12)) = k4_xboole_0(k4_xboole_0(X10,X11),X12)) )),
% 3.33/0.78    inference(superposition,[],[f31,f26])).
% 3.33/0.78  fof(f351,plain,(
% 3.33/0.78    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 3.33/0.78    inference(forward_demodulation,[],[f350,f33])).
% 3.33/0.78  fof(f350,plain,(
% 3.33/0.78    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))),
% 3.33/0.78    inference(backward_demodulation,[],[f32,f328])).
% 3.33/0.78  fof(f328,plain,(
% 3.33/0.78    ( ! [X6,X8,X7] : (k4_xboole_0(X7,X8) = k4_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(k4_xboole_0(X6,X7),X8))) )),
% 3.33/0.78    inference(superposition,[],[f31,f284])).
% 3.33/0.78  fof(f32,plain,(
% 3.33/0.78    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 3.33/0.78    inference(definition_unfolding,[],[f19,f25,f27,f27])).
% 3.33/0.78  fof(f27,plain,(
% 3.33/0.78    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 3.33/0.78    inference(cnf_transformation,[],[f3])).
% 3.33/0.78  fof(f3,axiom,(
% 3.33/0.78    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 3.33/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 3.33/0.78  fof(f19,plain,(
% 3.33/0.78    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 3.33/0.78    inference(cnf_transformation,[],[f17])).
% 3.33/0.78  fof(f17,plain,(
% 3.33/0.78    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 3.33/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).
% 3.33/0.78  fof(f16,plain,(
% 3.33/0.78    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 3.33/0.78    introduced(choice_axiom,[])).
% 3.33/0.78  fof(f14,plain,(
% 3.33/0.78    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 3.33/0.78    inference(ennf_transformation,[],[f13])).
% 3.33/0.78  fof(f13,negated_conjecture,(
% 3.33/0.78    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 3.33/0.78    inference(negated_conjecture,[],[f12])).
% 3.33/0.78  fof(f12,conjecture,(
% 3.33/0.78    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 3.33/0.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 3.33/0.78  % SZS output end Proof for theBenchmark
% 3.33/0.78  % (10020)------------------------------
% 3.33/0.78  % (10020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.33/0.78  % (10020)Termination reason: Refutation
% 3.33/0.78  
% 3.33/0.78  % (10020)Memory used [KB]: 10490
% 3.33/0.78  % (10020)Time elapsed: 0.303 s
% 3.33/0.78  % (10020)------------------------------
% 3.33/0.78  % (10020)------------------------------
% 3.33/0.78  % (10005)Success in time 0.423 s
%------------------------------------------------------------------------------
