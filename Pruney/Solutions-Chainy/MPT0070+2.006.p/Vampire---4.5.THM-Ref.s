%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:26 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 106 expanded)
%              Number of leaves         :   11 (  32 expanded)
%              Depth                    :   16
%              Number of atoms          :   78 ( 170 expanded)
%              Number of equality atoms :   43 (  82 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4894,plain,(
    $false ),
    inference(subsumption_resolution,[],[f47,f4893])).

fof(f4893,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f4886,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f49,f23])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f49,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f29,f24])).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f4886,plain,(
    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f29,f4845])).

fof(f4845,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f4732,f366])).

fof(f366,plain,(
    sK0 = k3_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f233,f43])).

fof(f43,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f30,f20])).

fof(f20,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f233,plain,(
    ! [X2,X1] : k3_xboole_0(X2,X1) = k3_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f106,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f106,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f99,f29])).

fof(f99,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k3_xboole_0(X2,X3)) = k4_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f29,f84])).

fof(f84,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(backward_demodulation,[],[f50,f77])).

fof(f77,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k3_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f44,f28])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f30,f26])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f50,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f29,f29])).

fof(f4732,plain,(
    ! [X19] : k3_xboole_0(sK1,X19) = k4_xboole_0(k3_xboole_0(sK1,X19),sK2) ),
    inference(forward_demodulation,[],[f4632,f29])).

fof(f4632,plain,(
    ! [X19] : k4_xboole_0(sK1,k4_xboole_0(sK1,X19)) = k4_xboole_0(k3_xboole_0(sK1,X19),sK2) ),
    inference(superposition,[],[f468,f662])).

fof(f662,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK2)) ),
    inference(superposition,[],[f476,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f476,plain,(
    ! [X32] : k4_xboole_0(sK1,k2_xboole_0(sK2,X32)) = k4_xboole_0(sK1,X32) ),
    inference(superposition,[],[f33,f105])).

fof(f105,plain,(
    sK1 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f96,f24])).

fof(f96,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f84,f46])).

fof(f46,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f31,f21])).

fof(f21,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f468,plain,(
    ! [X12,X10,X11] : k4_xboole_0(X10,k2_xboole_0(k4_xboole_0(X10,X11),X12)) = k4_xboole_0(k3_xboole_0(X10,X11),X12) ),
    inference(superposition,[],[f33,f29])).

fof(f47,plain,(
    k1_xboole_0 != k3_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f32,f22])).

fof(f22,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:29:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.45  % (4708)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.45  % (4706)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.45  % (4705)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.45  % (4704)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.45  % (4716)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.46  % (4713)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.46  % (4713)Refutation not found, incomplete strategy% (4713)------------------------------
% 0.19/0.46  % (4713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (4713)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.46  
% 0.19/0.46  % (4713)Memory used [KB]: 10618
% 0.19/0.46  % (4713)Time elapsed: 0.060 s
% 0.19/0.46  % (4713)------------------------------
% 0.19/0.46  % (4713)------------------------------
% 0.19/0.46  % (4710)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.47  % (4709)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.47  % (4719)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.48  % (4702)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.48  % (4717)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.48  % (4707)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.48  % (4712)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.48  % (4714)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.49  % (4711)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.49  % (4703)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.49  % (4715)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.50  % (4718)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.80/0.60  % (4718)Refutation found. Thanks to Tanya!
% 1.80/0.60  % SZS status Theorem for theBenchmark
% 1.80/0.60  % SZS output start Proof for theBenchmark
% 1.80/0.60  fof(f4894,plain,(
% 1.80/0.60    $false),
% 1.80/0.60    inference(subsumption_resolution,[],[f47,f4893])).
% 1.80/0.60  fof(f4893,plain,(
% 1.80/0.60    k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 1.80/0.60    inference(forward_demodulation,[],[f4886,f52])).
% 1.80/0.60  fof(f52,plain,(
% 1.80/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.80/0.60    inference(forward_demodulation,[],[f49,f23])).
% 1.80/0.60  fof(f23,plain,(
% 1.80/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f6])).
% 1.80/0.60  fof(f6,axiom,(
% 1.80/0.60    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.80/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.80/0.60  fof(f49,plain,(
% 1.80/0.60    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 1.80/0.60    inference(superposition,[],[f29,f24])).
% 1.80/0.60  fof(f24,plain,(
% 1.80/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.80/0.60    inference(cnf_transformation,[],[f8])).
% 1.80/0.60  fof(f8,axiom,(
% 1.80/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.80/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.80/0.61  fof(f29,plain,(
% 1.80/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.80/0.61    inference(cnf_transformation,[],[f10])).
% 1.80/0.61  fof(f10,axiom,(
% 1.80/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.80/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.80/0.61  fof(f4886,plain,(
% 1.80/0.61    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK0)),
% 1.80/0.61    inference(superposition,[],[f29,f4845])).
% 1.80/0.61  fof(f4845,plain,(
% 1.80/0.61    sK0 = k4_xboole_0(sK0,sK2)),
% 1.80/0.61    inference(superposition,[],[f4732,f366])).
% 1.80/0.61  fof(f366,plain,(
% 1.80/0.61    sK0 = k3_xboole_0(sK1,sK0)),
% 1.80/0.61    inference(superposition,[],[f233,f43])).
% 1.80/0.61  fof(f43,plain,(
% 1.80/0.61    sK0 = k3_xboole_0(sK0,sK1)),
% 1.80/0.61    inference(resolution,[],[f30,f20])).
% 1.80/0.61  fof(f20,plain,(
% 1.80/0.61    r1_tarski(sK0,sK1)),
% 1.80/0.61    inference(cnf_transformation,[],[f18])).
% 1.80/0.61  fof(f18,plain,(
% 1.80/0.61    ~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 1.80/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).
% 1.80/0.61  fof(f17,plain,(
% 1.80/0.61    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 1.80/0.61    introduced(choice_axiom,[])).
% 1.80/0.61  fof(f15,plain,(
% 1.80/0.61    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 1.80/0.61    inference(flattening,[],[f14])).
% 1.80/0.61  fof(f14,plain,(
% 1.80/0.61    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 1.80/0.61    inference(ennf_transformation,[],[f12])).
% 1.80/0.61  fof(f12,negated_conjecture,(
% 1.80/0.61    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.80/0.61    inference(negated_conjecture,[],[f11])).
% 1.80/0.61  fof(f11,conjecture,(
% 1.80/0.61    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.80/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.80/0.61  fof(f30,plain,(
% 1.80/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.80/0.61    inference(cnf_transformation,[],[f16])).
% 1.80/0.61  fof(f16,plain,(
% 1.80/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.80/0.61    inference(ennf_transformation,[],[f5])).
% 1.80/0.61  fof(f5,axiom,(
% 1.80/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.80/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.80/0.61  fof(f233,plain,(
% 1.80/0.61    ( ! [X2,X1] : (k3_xboole_0(X2,X1) = k3_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 1.80/0.61    inference(superposition,[],[f106,f28])).
% 1.80/0.61  fof(f28,plain,(
% 1.80/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.80/0.61    inference(cnf_transformation,[],[f2])).
% 1.80/0.61  fof(f2,axiom,(
% 1.80/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.80/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.80/0.61  fof(f106,plain,(
% 1.80/0.61    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 1.80/0.61    inference(forward_demodulation,[],[f99,f29])).
% 1.80/0.61  fof(f99,plain,(
% 1.80/0.61    ( ! [X2,X3] : (k3_xboole_0(X2,k3_xboole_0(X2,X3)) = k4_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 1.80/0.61    inference(superposition,[],[f29,f84])).
% 1.80/0.61  fof(f84,plain,(
% 1.80/0.61    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 1.80/0.61    inference(backward_demodulation,[],[f50,f77])).
% 1.80/0.61  fof(f77,plain,(
% 1.80/0.61    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k3_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 1.80/0.61    inference(superposition,[],[f44,f28])).
% 1.80/0.61  fof(f44,plain,(
% 1.80/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 1.80/0.61    inference(resolution,[],[f30,f26])).
% 1.80/0.61  fof(f26,plain,(
% 1.80/0.61    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.80/0.61    inference(cnf_transformation,[],[f7])).
% 1.80/0.61  fof(f7,axiom,(
% 1.80/0.61    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.80/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.80/0.61  fof(f50,plain,(
% 1.80/0.61    ( ! [X2,X1] : (k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 1.80/0.61    inference(superposition,[],[f29,f29])).
% 1.80/0.61  fof(f4732,plain,(
% 1.80/0.61    ( ! [X19] : (k3_xboole_0(sK1,X19) = k4_xboole_0(k3_xboole_0(sK1,X19),sK2)) )),
% 1.80/0.61    inference(forward_demodulation,[],[f4632,f29])).
% 1.80/0.61  fof(f4632,plain,(
% 1.80/0.61    ( ! [X19] : (k4_xboole_0(sK1,k4_xboole_0(sK1,X19)) = k4_xboole_0(k3_xboole_0(sK1,X19),sK2)) )),
% 1.80/0.61    inference(superposition,[],[f468,f662])).
% 1.80/0.61  fof(f662,plain,(
% 1.80/0.61    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK2))) )),
% 1.80/0.61    inference(superposition,[],[f476,f27])).
% 1.80/0.61  fof(f27,plain,(
% 1.80/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.80/0.61    inference(cnf_transformation,[],[f1])).
% 1.80/0.61  fof(f1,axiom,(
% 1.80/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.80/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.80/0.61  fof(f476,plain,(
% 1.80/0.61    ( ! [X32] : (k4_xboole_0(sK1,k2_xboole_0(sK2,X32)) = k4_xboole_0(sK1,X32)) )),
% 1.80/0.61    inference(superposition,[],[f33,f105])).
% 1.80/0.61  fof(f105,plain,(
% 1.80/0.61    sK1 = k4_xboole_0(sK1,sK2)),
% 1.80/0.61    inference(forward_demodulation,[],[f96,f24])).
% 1.80/0.61  fof(f96,plain,(
% 1.80/0.61    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0)),
% 1.80/0.61    inference(superposition,[],[f84,f46])).
% 1.80/0.61  fof(f46,plain,(
% 1.80/0.61    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 1.80/0.61    inference(resolution,[],[f31,f21])).
% 1.80/0.61  fof(f21,plain,(
% 1.80/0.61    r1_xboole_0(sK1,sK2)),
% 1.80/0.61    inference(cnf_transformation,[],[f18])).
% 1.80/0.61  fof(f31,plain,(
% 1.80/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.80/0.61    inference(cnf_transformation,[],[f19])).
% 1.80/0.61  fof(f19,plain,(
% 1.80/0.61    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.80/0.61    inference(nnf_transformation,[],[f3])).
% 1.80/0.61  fof(f3,axiom,(
% 1.80/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.80/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.80/0.61  fof(f33,plain,(
% 1.80/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.80/0.61    inference(cnf_transformation,[],[f9])).
% 1.80/0.61  fof(f9,axiom,(
% 1.80/0.61    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.80/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.80/0.61  fof(f468,plain,(
% 1.80/0.61    ( ! [X12,X10,X11] : (k4_xboole_0(X10,k2_xboole_0(k4_xboole_0(X10,X11),X12)) = k4_xboole_0(k3_xboole_0(X10,X11),X12)) )),
% 1.80/0.61    inference(superposition,[],[f33,f29])).
% 1.80/0.61  fof(f47,plain,(
% 1.80/0.61    k1_xboole_0 != k3_xboole_0(sK0,sK2)),
% 1.80/0.61    inference(resolution,[],[f32,f22])).
% 1.80/0.61  fof(f22,plain,(
% 1.80/0.61    ~r1_xboole_0(sK0,sK2)),
% 1.80/0.61    inference(cnf_transformation,[],[f18])).
% 1.80/0.61  fof(f32,plain,(
% 1.80/0.61    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.80/0.61    inference(cnf_transformation,[],[f19])).
% 1.80/0.61  % SZS output end Proof for theBenchmark
% 1.80/0.61  % (4718)------------------------------
% 1.80/0.61  % (4718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.80/0.61  % (4718)Termination reason: Refutation
% 1.80/0.61  
% 1.80/0.61  % (4718)Memory used [KB]: 8315
% 1.80/0.61  % (4718)Time elapsed: 0.197 s
% 1.80/0.61  % (4718)------------------------------
% 1.80/0.61  % (4718)------------------------------
% 1.80/0.61  % (4701)Success in time 0.259 s
%------------------------------------------------------------------------------
