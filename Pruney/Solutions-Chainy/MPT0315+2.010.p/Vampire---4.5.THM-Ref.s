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
% DateTime   : Thu Dec  3 12:42:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 (  84 expanded)
%              Number of leaves         :    8 (  27 expanded)
%              Depth                    :   17
%              Number of atoms          :   60 ( 120 expanded)
%              Number of equality atoms :   37 (  73 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f262,plain,(
    $false ),
    inference(resolution,[],[f251,f12])).

fof(f12,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      & ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          | r1_xboole_0(X0,X1) )
       => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f251,plain,(
    ! [X10,X11] : r1_xboole_0(k2_zfmisc_1(sK0,X10),k2_zfmisc_1(sK1,X11)) ),
    inference(forward_demodulation,[],[f241,f14])).

fof(f14,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f241,plain,(
    ! [X10,X11] : r1_xboole_0(k4_xboole_0(k2_zfmisc_1(sK0,X10),k1_xboole_0),k2_zfmisc_1(sK1,X11)) ),
    inference(superposition,[],[f24,f184])).

fof(f184,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,X2),k4_xboole_0(k2_zfmisc_1(sK0,X2),k2_zfmisc_1(sK1,X3))) ),
    inference(forward_demodulation,[],[f183,f27])).

fof(f27,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f183,plain,(
    ! [X2,X3] : k4_xboole_0(k2_zfmisc_1(sK0,X2),k4_xboole_0(k2_zfmisc_1(sK0,X2),k2_zfmisc_1(sK1,X3))) = k2_zfmisc_1(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f178,f28])).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f23,f14])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f13,f16])).

fof(f16,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f13,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f178,plain,(
    ! [X2,X3] : k4_xboole_0(k2_zfmisc_1(sK0,X2),k4_xboole_0(k2_zfmisc_1(sK0,X2),k2_zfmisc_1(sK1,X3))) = k2_zfmisc_1(k4_xboole_0(sK0,sK0),k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(superposition,[],[f25,f173])).

fof(f173,plain,(
    sK0 = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f166,f12])).

fof(f166,plain,(
    ! [X10,X11] :
      ( r1_xboole_0(k2_zfmisc_1(X10,sK2),k2_zfmisc_1(X11,sK3))
      | sK0 = k4_xboole_0(sK0,sK1) ) ),
    inference(forward_demodulation,[],[f156,f14])).

fof(f156,plain,(
    ! [X10,X11] :
      ( r1_xboole_0(k4_xboole_0(k2_zfmisc_1(X10,sK2),k1_xboole_0),k2_zfmisc_1(X11,sK3))
      | sK0 = k4_xboole_0(sK0,sK1) ) ),
    inference(superposition,[],[f24,f109])).

fof(f109,plain,(
    ! [X14,X13] :
      ( k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(X13,sK2),k4_xboole_0(k2_zfmisc_1(X13,sK2),k2_zfmisc_1(X14,sK3)))
      | sK0 = k4_xboole_0(sK0,sK1) ) ),
    inference(forward_demodulation,[],[f108,f26])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f108,plain,(
    ! [X14,X13] :
      ( k4_xboole_0(k2_zfmisc_1(X13,sK2),k4_xboole_0(k2_zfmisc_1(X13,sK2),k2_zfmisc_1(X14,sK3))) = k2_zfmisc_1(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k1_xboole_0)
      | sK0 = k4_xboole_0(sK0,sK1) ) ),
    inference(forward_demodulation,[],[f81,f28])).

fof(f81,plain,(
    ! [X14,X13] :
      ( k4_xboole_0(k2_zfmisc_1(X13,sK2),k4_xboole_0(k2_zfmisc_1(X13,sK2),k2_zfmisc_1(X14,sK3))) = k2_zfmisc_1(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(sK2,sK2))
      | sK0 = k4_xboole_0(sK0,sK1) ) ),
    inference(superposition,[],[f25,f32])).

fof(f32,plain,
    ( sK2 = k4_xboole_0(sK2,sK3)
    | sK0 = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f30,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f30,plain,
    ( r1_xboole_0(sK0,sK1)
    | sK2 = k4_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f18,f11])).

fof(f11,plain,
    ( r1_xboole_0(sK2,sK3)
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(definition_unfolding,[],[f22,f16,f16,f16])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f24,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1) ),
    inference(definition_unfolding,[],[f15,f16])).

fof(f15,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:29:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (6252)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (6232)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (6228)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (6234)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (6235)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (6256)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (6238)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (6230)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (6248)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (6242)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (6236)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (6231)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (6249)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (6246)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (6250)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (6254)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (6246)Refutation not found, incomplete strategy% (6246)------------------------------
% 0.21/0.54  % (6246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (6246)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (6246)Memory used [KB]: 10618
% 0.21/0.54  % (6246)Time elapsed: 0.131 s
% 0.21/0.54  % (6246)------------------------------
% 0.21/0.54  % (6246)------------------------------
% 0.21/0.54  % (6235)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f262,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(resolution,[],[f251,f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ~r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) & (r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.21/0.54    inference(negated_conjecture,[],[f8])).
% 0.21/0.54  fof(f8,conjecture,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 0.21/0.54  fof(f251,plain,(
% 0.21/0.54    ( ! [X10,X11] : (r1_xboole_0(k2_zfmisc_1(sK0,X10),k2_zfmisc_1(sK1,X11))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f241,f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.54  fof(f241,plain,(
% 0.21/0.54    ( ! [X10,X11] : (r1_xboole_0(k4_xboole_0(k2_zfmisc_1(sK0,X10),k1_xboole_0),k2_zfmisc_1(sK1,X11))) )),
% 0.21/0.54    inference(superposition,[],[f24,f184])).
% 0.21/0.54  fof(f184,plain,(
% 0.21/0.54    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,X2),k4_xboole_0(k2_zfmisc_1(sK0,X2),k2_zfmisc_1(sK1,X3)))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f183,f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.54  fof(f183,plain,(
% 0.21/0.54    ( ! [X2,X3] : (k4_xboole_0(k2_zfmisc_1(sK0,X2),k4_xboole_0(k2_zfmisc_1(sK0,X2),k2_zfmisc_1(sK1,X3))) = k2_zfmisc_1(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f178,f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.54    inference(backward_demodulation,[],[f23,f14])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f13,f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.54  fof(f178,plain,(
% 0.21/0.54    ( ! [X2,X3] : (k4_xboole_0(k2_zfmisc_1(sK0,X2),k4_xboole_0(k2_zfmisc_1(sK0,X2),k2_zfmisc_1(sK1,X3))) = k2_zfmisc_1(k4_xboole_0(sK0,sK0),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) )),
% 0.21/0.54    inference(superposition,[],[f25,f173])).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    sK0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f166,f12])).
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    ( ! [X10,X11] : (r1_xboole_0(k2_zfmisc_1(X10,sK2),k2_zfmisc_1(X11,sK3)) | sK0 = k4_xboole_0(sK0,sK1)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f156,f14])).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    ( ! [X10,X11] : (r1_xboole_0(k4_xboole_0(k2_zfmisc_1(X10,sK2),k1_xboole_0),k2_zfmisc_1(X11,sK3)) | sK0 = k4_xboole_0(sK0,sK1)) )),
% 0.21/0.54    inference(superposition,[],[f24,f109])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    ( ! [X14,X13] : (k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(X13,sK2),k4_xboole_0(k2_zfmisc_1(X13,sK2),k2_zfmisc_1(X14,sK3))) | sK0 = k4_xboole_0(sK0,sK1)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f108,f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ( ! [X14,X13] : (k4_xboole_0(k2_zfmisc_1(X13,sK2),k4_xboole_0(k2_zfmisc_1(X13,sK2),k2_zfmisc_1(X14,sK3))) = k2_zfmisc_1(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k1_xboole_0) | sK0 = k4_xboole_0(sK0,sK1)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f81,f28])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ( ! [X14,X13] : (k4_xboole_0(k2_zfmisc_1(X13,sK2),k4_xboole_0(k2_zfmisc_1(X13,sK2),k2_zfmisc_1(X14,sK3))) = k2_zfmisc_1(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(sK2,sK2)) | sK0 = k4_xboole_0(sK0,sK1)) )),
% 0.21/0.54    inference(superposition,[],[f25,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    sK2 = k4_xboole_0(sK2,sK3) | sK0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f30,f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    r1_xboole_0(sK0,sK1) | sK2 = k4_xboole_0(sK2,sK3)),
% 0.21/0.54    inference(resolution,[],[f18,f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    r1_xboole_0(sK2,sK3) | r1_xboole_0(sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f22,f16,f16,f16])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f15,f16])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (6235)------------------------------
% 0.21/0.54  % (6235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (6235)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (6235)Memory used [KB]: 6396
% 0.21/0.54  % (6235)Time elapsed: 0.118 s
% 0.21/0.54  % (6235)------------------------------
% 0.21/0.54  % (6235)------------------------------
% 0.21/0.54  % (6226)Success in time 0.181 s
%------------------------------------------------------------------------------
