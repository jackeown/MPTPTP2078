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
% DateTime   : Thu Dec  3 12:30:56 EST 2020

% Result     : Theorem 1.92s
% Output     : Refutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 368 expanded)
%              Number of leaves         :   11 ( 109 expanded)
%              Depth                    :   23
%              Number of atoms          :   98 ( 551 expanded)
%              Number of equality atoms :   76 ( 401 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1225,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1224,f21])).

fof(f21,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f1224,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f1213,f582])).

fof(f582,plain,(
    sK1 = k2_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f579,f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f579,plain,(
    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f27,f561])).

fof(f561,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f476,f350])).

fof(f350,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f107,f18])).

fof(f18,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f107,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f104,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f104,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f98,f27])).

fof(f98,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f32,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f35,f23])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f22,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f476,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[],[f32,f456])).

fof(f456,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[],[f391,f44])).

fof(f44,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f25,f24])).

fof(f391,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f36,f60])).

fof(f60,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f37,f19])).

fof(f19,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f31,f26])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f28,f26])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1213,plain,(
    sK2 = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f1212,f25])).

fof(f1212,plain,(
    sK2 = k2_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f1206,f24])).

fof(f1206,plain,(
    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f27,f1197])).

fof(f1197,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f1188,f104])).

fof(f1188,plain,(
    k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f987,f925])).

fof(f925,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK0) ),
    inference(backward_demodulation,[],[f18,f924])).

fof(f924,plain,(
    sK0 = sK3 ),
    inference(backward_demodulation,[],[f788,f923])).

fof(f923,plain,(
    sK0 = k2_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f917,f24])).

fof(f917,plain,(
    k2_xboole_0(sK0,sK3) = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f27,f899])).

fof(f899,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK0) ),
    inference(superposition,[],[f629,f118])).

fof(f118,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f104,f18])).

fof(f629,plain,(
    ! [X0] : k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f498,f25])).

fof(f498,plain,(
    ! [X0] : k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[],[f32,f478])).

fof(f478,plain,(
    sK3 = k4_xboole_0(sK3,sK1) ),
    inference(superposition,[],[f392,f44])).

fof(f392,plain,(
    sK3 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f36,f61])).

fof(f61,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f37,f20])).

fof(f20,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f788,plain,(
    sK3 = k2_xboole_0(sK0,sK3) ),
    inference(superposition,[],[f787,f25])).

fof(f787,plain,(
    sK3 = k2_xboole_0(sK3,sK0) ),
    inference(forward_demodulation,[],[f782,f24])).

fof(f782,plain,(
    k2_xboole_0(sK3,sK0) = k2_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[],[f27,f771])).

fof(f771,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f759,f107])).

fof(f759,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK3) ),
    inference(superposition,[],[f520,f18])).

fof(f520,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[],[f32,f500])).

fof(f500,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f389,f44])).

fof(f389,plain,(
    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f36,f58])).

fof(f58,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f37,f40])).

fof(f40,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f29,f19])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f987,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK0)) ),
    inference(backward_demodulation,[],[f841,f924])).

fof(f841,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK3)) ),
    inference(superposition,[],[f546,f25])).

fof(f546,plain,(
    ! [X0] : k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[],[f32,f522])).

fof(f522,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f390,f44])).

fof(f390,plain,(
    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f36,f59])).

fof(f59,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f37,f41])).

fof(f41,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f29,f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:39:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (6852)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (6869)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (6860)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (6873)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (6871)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (6876)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (6872)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (6875)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (6874)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (6847)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (6851)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (6848)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (6865)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (6850)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (6853)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (6849)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (6868)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (6863)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (6864)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (6864)Refutation not found, incomplete strategy% (6864)------------------------------
% 0.21/0.55  % (6864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (6864)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (6864)Memory used [KB]: 10618
% 0.21/0.55  % (6864)Time elapsed: 0.138 s
% 0.21/0.55  % (6864)------------------------------
% 0.21/0.55  % (6864)------------------------------
% 0.21/0.55  % (6867)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (6866)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (6857)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (6856)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (6855)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (6859)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (6858)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (6861)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.58  % (6870)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.58  % (6862)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.58  % (6862)Refutation not found, incomplete strategy% (6862)------------------------------
% 0.21/0.58  % (6862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (6862)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (6862)Memory used [KB]: 6140
% 0.21/0.59  % (6862)Time elapsed: 0.005 s
% 0.21/0.59  % (6862)------------------------------
% 0.21/0.59  % (6862)------------------------------
% 0.21/0.59  % (6854)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.92/0.61  % (6853)Refutation found. Thanks to Tanya!
% 1.92/0.61  % SZS status Theorem for theBenchmark
% 1.92/0.61  % SZS output start Proof for theBenchmark
% 1.92/0.61  fof(f1225,plain,(
% 1.92/0.61    $false),
% 1.92/0.61    inference(subsumption_resolution,[],[f1224,f21])).
% 1.92/0.61  fof(f21,plain,(
% 1.92/0.61    sK1 != sK2),
% 1.92/0.61    inference(cnf_transformation,[],[f16])).
% 1.92/0.61  fof(f16,plain,(
% 1.92/0.61    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 1.92/0.61    inference(flattening,[],[f15])).
% 1.92/0.61  fof(f15,plain,(
% 1.92/0.61    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 1.92/0.61    inference(ennf_transformation,[],[f14])).
% 1.92/0.61  fof(f14,negated_conjecture,(
% 1.92/0.61    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.92/0.61    inference(negated_conjecture,[],[f13])).
% 1.92/0.61  fof(f13,conjecture,(
% 1.92/0.61    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 1.92/0.61  fof(f1224,plain,(
% 1.92/0.61    sK1 = sK2),
% 1.92/0.61    inference(forward_demodulation,[],[f1213,f582])).
% 1.92/0.61  fof(f582,plain,(
% 1.92/0.61    sK1 = k2_xboole_0(sK1,sK2)),
% 1.92/0.61    inference(forward_demodulation,[],[f579,f24])).
% 1.92/0.61  fof(f24,plain,(
% 1.92/0.61    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.92/0.61    inference(cnf_transformation,[],[f4])).
% 1.92/0.61  fof(f4,axiom,(
% 1.92/0.61    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.92/0.61  fof(f579,plain,(
% 1.92/0.61    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK2)),
% 1.92/0.61    inference(superposition,[],[f27,f561])).
% 1.92/0.61  fof(f561,plain,(
% 1.92/0.61    k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 1.92/0.61    inference(superposition,[],[f476,f350])).
% 1.92/0.61  fof(f350,plain,(
% 1.92/0.61    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 1.92/0.61    inference(superposition,[],[f107,f18])).
% 1.92/0.61  fof(f18,plain,(
% 1.92/0.61    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.92/0.61    inference(cnf_transformation,[],[f16])).
% 1.92/0.61  fof(f107,plain,(
% 1.92/0.61    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X1))) )),
% 1.92/0.61    inference(superposition,[],[f104,f25])).
% 1.92/0.61  fof(f25,plain,(
% 1.92/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f1])).
% 1.92/0.61  fof(f1,axiom,(
% 1.92/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.92/0.61  fof(f104,plain,(
% 1.92/0.61    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5))) )),
% 1.92/0.61    inference(forward_demodulation,[],[f98,f27])).
% 1.92/0.61  fof(f98,plain,(
% 1.92/0.61    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 1.92/0.61    inference(superposition,[],[f32,f39])).
% 1.92/0.61  fof(f39,plain,(
% 1.92/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.92/0.61    inference(backward_demodulation,[],[f35,f23])).
% 1.92/0.61  fof(f23,plain,(
% 1.92/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.92/0.61    inference(cnf_transformation,[],[f7])).
% 1.92/0.61  fof(f7,axiom,(
% 1.92/0.61    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.92/0.61  fof(f35,plain,(
% 1.92/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.92/0.61    inference(definition_unfolding,[],[f22,f26])).
% 1.92/0.61  fof(f26,plain,(
% 1.92/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.92/0.61    inference(cnf_transformation,[],[f10])).
% 1.92/0.61  fof(f10,axiom,(
% 1.92/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.92/0.61  fof(f22,plain,(
% 1.92/0.61    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f5])).
% 1.92/0.61  fof(f5,axiom,(
% 1.92/0.61    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.92/0.61  fof(f32,plain,(
% 1.92/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.92/0.61    inference(cnf_transformation,[],[f8])).
% 1.92/0.61  fof(f8,axiom,(
% 1.92/0.61    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.92/0.61  fof(f476,plain,(
% 1.92/0.61    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0)) )),
% 1.92/0.61    inference(superposition,[],[f32,f456])).
% 1.92/0.61  fof(f456,plain,(
% 1.92/0.61    sK2 = k4_xboole_0(sK2,sK0)),
% 1.92/0.61    inference(superposition,[],[f391,f44])).
% 1.92/0.61  fof(f44,plain,(
% 1.92/0.61    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.92/0.61    inference(superposition,[],[f25,f24])).
% 1.92/0.61  fof(f391,plain,(
% 1.92/0.61    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0))),
% 1.92/0.61    inference(superposition,[],[f36,f60])).
% 1.92/0.61  fof(f60,plain,(
% 1.92/0.61    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 1.92/0.61    inference(resolution,[],[f37,f19])).
% 1.92/0.61  fof(f19,plain,(
% 1.92/0.61    r1_xboole_0(sK2,sK0)),
% 1.92/0.61    inference(cnf_transformation,[],[f16])).
% 1.92/0.61  fof(f37,plain,(
% 1.92/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.92/0.61    inference(definition_unfolding,[],[f31,f26])).
% 1.92/0.61  fof(f31,plain,(
% 1.92/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f2])).
% 1.92/0.61  fof(f2,axiom,(
% 1.92/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.92/0.61  fof(f36,plain,(
% 1.92/0.61    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 1.92/0.61    inference(definition_unfolding,[],[f28,f26])).
% 1.92/0.61  fof(f28,plain,(
% 1.92/0.61    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.92/0.61    inference(cnf_transformation,[],[f12])).
% 1.92/0.61  fof(f12,axiom,(
% 1.92/0.61    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.92/0.61  fof(f27,plain,(
% 1.92/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.92/0.61    inference(cnf_transformation,[],[f6])).
% 1.92/0.61  fof(f6,axiom,(
% 1.92/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.92/0.61  fof(f1213,plain,(
% 1.92/0.61    sK2 = k2_xboole_0(sK1,sK2)),
% 1.92/0.61    inference(superposition,[],[f1212,f25])).
% 1.92/0.61  fof(f1212,plain,(
% 1.92/0.61    sK2 = k2_xboole_0(sK2,sK1)),
% 1.92/0.61    inference(forward_demodulation,[],[f1206,f24])).
% 1.92/0.61  fof(f1206,plain,(
% 1.92/0.61    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0)),
% 1.92/0.61    inference(superposition,[],[f27,f1197])).
% 1.92/0.61  fof(f1197,plain,(
% 1.92/0.61    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 1.92/0.61    inference(forward_demodulation,[],[f1188,f104])).
% 1.92/0.61  fof(f1188,plain,(
% 1.92/0.61    k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,sK2)),
% 1.92/0.61    inference(superposition,[],[f987,f925])).
% 1.92/0.61  fof(f925,plain,(
% 1.92/0.61    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK0)),
% 1.92/0.61    inference(backward_demodulation,[],[f18,f924])).
% 1.92/0.61  fof(f924,plain,(
% 1.92/0.61    sK0 = sK3),
% 1.92/0.61    inference(backward_demodulation,[],[f788,f923])).
% 1.92/0.61  fof(f923,plain,(
% 1.92/0.61    sK0 = k2_xboole_0(sK0,sK3)),
% 1.92/0.61    inference(forward_demodulation,[],[f917,f24])).
% 1.92/0.61  fof(f917,plain,(
% 1.92/0.61    k2_xboole_0(sK0,sK3) = k2_xboole_0(sK0,k1_xboole_0)),
% 1.92/0.61    inference(superposition,[],[f27,f899])).
% 1.92/0.61  fof(f899,plain,(
% 1.92/0.61    k1_xboole_0 = k4_xboole_0(sK3,sK0)),
% 1.92/0.61    inference(superposition,[],[f629,f118])).
% 1.92/0.61  fof(f118,plain,(
% 1.92/0.61    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.92/0.61    inference(superposition,[],[f104,f18])).
% 1.92/0.61  fof(f629,plain,(
% 1.92/0.61    ( ! [X0] : (k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(X0,sK1))) )),
% 1.92/0.61    inference(superposition,[],[f498,f25])).
% 1.92/0.61  fof(f498,plain,(
% 1.92/0.61    ( ! [X0] : (k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0)) )),
% 1.92/0.61    inference(superposition,[],[f32,f478])).
% 1.92/0.61  fof(f478,plain,(
% 1.92/0.61    sK3 = k4_xboole_0(sK3,sK1)),
% 1.92/0.61    inference(superposition,[],[f392,f44])).
% 1.92/0.61  fof(f392,plain,(
% 1.92/0.61    sK3 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1))),
% 1.92/0.61    inference(superposition,[],[f36,f61])).
% 1.92/0.61  fof(f61,plain,(
% 1.92/0.61    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 1.92/0.61    inference(resolution,[],[f37,f20])).
% 1.92/0.61  fof(f20,plain,(
% 1.92/0.61    r1_xboole_0(sK3,sK1)),
% 1.92/0.61    inference(cnf_transformation,[],[f16])).
% 1.92/0.61  fof(f788,plain,(
% 1.92/0.61    sK3 = k2_xboole_0(sK0,sK3)),
% 1.92/0.61    inference(superposition,[],[f787,f25])).
% 1.92/0.61  fof(f787,plain,(
% 1.92/0.61    sK3 = k2_xboole_0(sK3,sK0)),
% 1.92/0.61    inference(forward_demodulation,[],[f782,f24])).
% 1.92/0.61  fof(f782,plain,(
% 1.92/0.61    k2_xboole_0(sK3,sK0) = k2_xboole_0(sK3,k1_xboole_0)),
% 1.92/0.61    inference(superposition,[],[f27,f771])).
% 1.92/0.61  fof(f771,plain,(
% 1.92/0.61    k1_xboole_0 = k4_xboole_0(sK0,sK3)),
% 1.92/0.61    inference(forward_demodulation,[],[f759,f107])).
% 1.92/0.61  fof(f759,plain,(
% 1.92/0.61    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK3)),
% 1.92/0.61    inference(superposition,[],[f520,f18])).
% 1.92/0.61  fof(f520,plain,(
% 1.92/0.61    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)) )),
% 1.92/0.61    inference(superposition,[],[f32,f500])).
% 1.92/0.61  fof(f500,plain,(
% 1.92/0.61    sK0 = k4_xboole_0(sK0,sK2)),
% 1.92/0.61    inference(superposition,[],[f389,f44])).
% 1.92/0.61  fof(f389,plain,(
% 1.92/0.61    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2))),
% 1.92/0.61    inference(superposition,[],[f36,f58])).
% 1.92/0.61  fof(f58,plain,(
% 1.92/0.61    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.92/0.61    inference(resolution,[],[f37,f40])).
% 1.92/0.61  fof(f40,plain,(
% 1.92/0.61    r1_xboole_0(sK0,sK2)),
% 1.92/0.61    inference(resolution,[],[f29,f19])).
% 1.92/0.61  fof(f29,plain,(
% 1.92/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f17])).
% 1.92/0.61  fof(f17,plain,(
% 1.92/0.61    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.92/0.61    inference(ennf_transformation,[],[f3])).
% 1.92/0.61  fof(f3,axiom,(
% 1.92/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.92/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.92/0.61  fof(f987,plain,(
% 1.92/0.61    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK0))) )),
% 1.92/0.61    inference(backward_demodulation,[],[f841,f924])).
% 1.92/0.61  fof(f841,plain,(
% 1.92/0.61    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK3))) )),
% 1.92/0.61    inference(superposition,[],[f546,f25])).
% 1.92/0.61  fof(f546,plain,(
% 1.92/0.61    ( ! [X0] : (k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0)) )),
% 1.92/0.61    inference(superposition,[],[f32,f522])).
% 1.92/0.61  fof(f522,plain,(
% 1.92/0.61    sK1 = k4_xboole_0(sK1,sK3)),
% 1.92/0.61    inference(superposition,[],[f390,f44])).
% 1.92/0.61  fof(f390,plain,(
% 1.92/0.61    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))),
% 1.92/0.61    inference(superposition,[],[f36,f59])).
% 1.92/0.61  fof(f59,plain,(
% 1.92/0.61    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 1.92/0.61    inference(resolution,[],[f37,f41])).
% 1.92/0.61  fof(f41,plain,(
% 1.92/0.61    r1_xboole_0(sK1,sK3)),
% 1.92/0.61    inference(resolution,[],[f29,f20])).
% 1.92/0.61  % SZS output end Proof for theBenchmark
% 1.92/0.61  % (6853)------------------------------
% 1.92/0.61  % (6853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.92/0.61  % (6853)Termination reason: Refutation
% 1.92/0.61  
% 1.92/0.61  % (6853)Memory used [KB]: 7164
% 1.92/0.61  % (6853)Time elapsed: 0.193 s
% 1.92/0.61  % (6853)------------------------------
% 1.92/0.61  % (6853)------------------------------
% 1.92/0.62  % (6846)Success in time 0.254 s
%------------------------------------------------------------------------------
