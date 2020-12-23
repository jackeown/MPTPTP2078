%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  95 expanded)
%              Number of leaves         :    9 (  28 expanded)
%              Depth                    :   19
%              Number of atoms          :   61 ( 150 expanded)
%              Number of equality atoms :   30 (  79 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72,plain,(
    $false ),
    inference(subsumption_resolution,[],[f70,f21])).

fof(f21,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(f70,plain,(
    sK0 = sK2 ),
    inference(resolution,[],[f63,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f63,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK2)) ),
    inference(superposition,[],[f30,f60])).

fof(f60,plain,(
    k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) ),
    inference(backward_demodulation,[],[f51,f53])).

fof(f53,plain,(
    k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK2)) ),
    inference(resolution,[],[f50,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f50,plain,(
    r1_tarski(k1_tarski(sK2),k1_tarski(sK2)) ),
    inference(resolution,[],[f46,f30])).

fof(f46,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_xboole_0(k1_tarski(sK2),k1_tarski(sK2)))
      | r1_tarski(X0,k1_tarski(sK2)) ) ),
    inference(superposition,[],[f28,f44])).

fof(f44,plain,(
    k1_tarski(sK2) = k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK2))) ),
    inference(forward_demodulation,[],[f43,f32])).

fof(f32,plain,(
    k1_tarski(sK2) = k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(resolution,[],[f20,f23])).

fof(f20,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) = k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK2))) ),
    inference(forward_demodulation,[],[f42,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f42,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK2))) = k2_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1))) ),
    inference(superposition,[],[f25,f40])).

fof(f40,plain,(
    k4_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)) = k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK2)),k2_tarski(sK0,sK1)) ),
    inference(superposition,[],[f24,f37])).

fof(f37,plain,(
    k2_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK2)) ),
    inference(forward_demodulation,[],[f36,f25])).

fof(f36,plain,(
    k2_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)) = k2_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK2))) ),
    inference(superposition,[],[f25,f35])).

fof(f35,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) = k4_xboole_0(k1_tarski(sK2),k1_tarski(sK2)) ),
    inference(superposition,[],[f24,f32])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

% (21068)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% (21044)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% (21049)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f51,plain,(
    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK2)) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK2))) ),
    inference(resolution,[],[f41,f29])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f41,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_tarski(sK0,sK1))
      | k2_xboole_0(k1_tarski(sK2),k1_tarski(sK2)) = k2_xboole_0(X0,k2_xboole_0(k1_tarski(sK2),k1_tarski(sK2))) ) ),
    inference(resolution,[],[f39,f23])).

fof(f39,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_xboole_0(k1_tarski(sK2),k1_tarski(sK2)))
      | ~ r1_tarski(X0,k2_tarski(sK0,sK1)) ) ),
    inference(superposition,[],[f28,f37])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:50:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (21040)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.50  % (21041)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (21041)Refutation not found, incomplete strategy% (21041)------------------------------
% 0.21/0.51  % (21041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21041)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21041)Memory used [KB]: 1663
% 0.21/0.51  % (21041)Time elapsed: 0.095 s
% 0.21/0.51  % (21041)------------------------------
% 0.21/0.51  % (21041)------------------------------
% 0.21/0.51  % (21045)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (21054)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (21055)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (21061)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (21054)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (21046)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f70,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    sK0 != sK2),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) => (sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 0.21/0.52    inference(negated_conjecture,[],[f12])).
% 0.21/0.52  fof(f12,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    sK0 = sK2),
% 0.21/0.52    inference(resolution,[],[f63,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    r1_tarski(k1_tarski(sK0),k1_tarski(sK2))),
% 0.21/0.52    inference(superposition,[],[f30,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))),
% 0.21/0.52    inference(backward_demodulation,[],[f51,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK2))),
% 0.21/0.52    inference(resolution,[],[f50,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    r1_tarski(k1_tarski(sK2),k1_tarski(sK2))),
% 0.21/0.52    inference(resolution,[],[f46,f30])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(k1_tarski(sK2),k1_tarski(sK2))) | r1_tarski(X0,k1_tarski(sK2))) )),
% 0.21/0.52    inference(superposition,[],[f28,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    k1_tarski(sK2) = k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK2)))),
% 0.21/0.52    inference(forward_demodulation,[],[f43,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    k1_tarski(sK2) = k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.21/0.52    inference(resolution,[],[f20,f23])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) = k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK2)))),
% 0.21/0.52    inference(forward_demodulation,[],[f42,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK2))) = k2_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)))),
% 0.21/0.52    inference(superposition,[],[f25,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    k4_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)) = k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK2)),k2_tarski(sK0,sK1))),
% 0.21/0.52    inference(superposition,[],[f24,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    k2_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK2))),
% 0.21/0.52    inference(forward_demodulation,[],[f36,f25])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    k2_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)) = k2_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK2)))),
% 0.21/0.52    inference(superposition,[],[f25,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) = k4_xboole_0(k1_tarski(sK2),k1_tarski(sK2))),
% 0.21/0.52    inference(superposition,[],[f24,f32])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.52  % (21068)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (21044)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (21049)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK2)) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK2)))),
% 0.21/0.53    inference(resolution,[],[f41,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(X0,k2_tarski(sK0,sK1)) | k2_xboole_0(k1_tarski(sK2),k1_tarski(sK2)) = k2_xboole_0(X0,k2_xboole_0(k1_tarski(sK2),k1_tarski(sK2)))) )),
% 0.21/0.53    inference(resolution,[],[f39,f23])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(X0,k2_xboole_0(k1_tarski(sK2),k1_tarski(sK2))) | ~r1_tarski(X0,k2_tarski(sK0,sK1))) )),
% 0.21/0.53    inference(superposition,[],[f28,f37])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (21054)------------------------------
% 0.21/0.53  % (21054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21054)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (21054)Memory used [KB]: 1791
% 0.21/0.53  % (21054)Time elapsed: 0.111 s
% 0.21/0.53  % (21054)------------------------------
% 0.21/0.53  % (21054)------------------------------
% 0.21/0.53  % (21042)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (21039)Success in time 0.165 s
%------------------------------------------------------------------------------
