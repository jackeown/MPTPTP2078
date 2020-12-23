%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:13 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   41 (  50 expanded)
%              Number of leaves         :   12 (  16 expanded)
%              Depth                    :   14
%              Number of atoms          :   51 (  67 expanded)
%              Number of equality atoms :   34 (  50 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f117,plain,(
    $false ),
    inference(subsumption_resolution,[],[f116,f20])).

fof(f20,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & k1_tarski(X0) = k2_tarski(X1,X2) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k2_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & k1_tarski(X0) = k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k2_tarski(X1,X2)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).

fof(f116,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f101,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f101,plain,(
    r1_tarski(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(superposition,[],[f98,f19])).

fof(f19,plain,(
    k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f98,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f86,f23])).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f86,plain,(
    ! [X2,X0,X1] : r1_tarski(k1_tarski(X0),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f79,f27])).

% (15624)Refutation not found, incomplete strategy% (15624)------------------------------
% (15624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f27,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

% (15624)Termination reason: Refutation not found, incomplete strategy

% (15624)Memory used [KB]: 10618
% (15624)Time elapsed: 0.109 s
% (15624)------------------------------
% (15624)------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : r1_tarski(k1_tarski(X0),k2_enumset1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f60,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f60,plain,(
    ! [X6,X4,X8,X7,X5] : r1_tarski(k1_tarski(X4),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(forward_demodulation,[],[f58,f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f58,plain,(
    ! [X6,X4,X8,X7,X5] : r1_tarski(k1_tarski(X4),k4_enumset1(X4,X4,X5,X6,X7,X8)) ),
    inference(superposition,[],[f47,f21])).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : r1_tarski(k2_tarski(X0,X1),k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(forward_demodulation,[],[f45,f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : r1_tarski(k2_tarski(X0,X1),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) ),
    inference(superposition,[],[f39,f23])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : r1_tarski(k1_enumset1(X0,X1,X2),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) ),
    inference(forward_demodulation,[],[f37,f31])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : r1_tarski(k1_enumset1(X0,X1,X2),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) ),
    inference(superposition,[],[f35,f27])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : r1_tarski(k2_enumset1(X0,X1,X2,X3),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(superposition,[],[f22,f32])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f4])).

% (15617)Refutation not found, incomplete strategy% (15617)------------------------------
% (15617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:37:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.45  % (15615)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.49  % (15638)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.49  % (15638)Refutation not found, incomplete strategy% (15638)------------------------------
% 0.22/0.49  % (15638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (15638)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (15638)Memory used [KB]: 6140
% 0.22/0.49  % (15638)Time elapsed: 0.106 s
% 0.22/0.49  % (15638)------------------------------
% 0.22/0.49  % (15638)------------------------------
% 0.22/0.50  % (15630)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.50  % (15630)Refutation not found, incomplete strategy% (15630)------------------------------
% 0.22/0.50  % (15630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (15630)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (15630)Memory used [KB]: 1663
% 0.22/0.51  % (15630)Time elapsed: 0.109 s
% 0.22/0.51  % (15630)------------------------------
% 0.22/0.51  % (15630)------------------------------
% 0.22/0.51  % (15622)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.21/0.52  % (15622)Refutation not found, incomplete strategy% (15622)------------------------------
% 1.21/0.52  % (15622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (15622)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.52  
% 1.21/0.52  % (15622)Memory used [KB]: 10746
% 1.21/0.52  % (15622)Time elapsed: 0.116 s
% 1.21/0.52  % (15622)------------------------------
% 1.21/0.52  % (15622)------------------------------
% 1.21/0.52  % (15621)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.21/0.52  % (15621)Refutation found. Thanks to Tanya!
% 1.21/0.52  % SZS status Theorem for theBenchmark
% 1.32/0.53  % (15613)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.32/0.53  % (15613)Refutation not found, incomplete strategy% (15613)------------------------------
% 1.32/0.53  % (15613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (15613)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (15613)Memory used [KB]: 1663
% 1.32/0.53  % (15613)Time elapsed: 0.121 s
% 1.32/0.53  % (15613)------------------------------
% 1.32/0.53  % (15613)------------------------------
% 1.32/0.53  % (15624)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.32/0.53  % (15617)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.32/0.53  % SZS output start Proof for theBenchmark
% 1.32/0.53  fof(f117,plain,(
% 1.32/0.53    $false),
% 1.32/0.53    inference(subsumption_resolution,[],[f116,f20])).
% 1.32/0.53  fof(f20,plain,(
% 1.32/0.53    sK0 != sK1),
% 1.32/0.53    inference(cnf_transformation,[],[f18])).
% 1.32/0.53  fof(f18,plain,(
% 1.32/0.53    sK0 != sK1 & k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).
% 1.32/0.53  fof(f17,plain,(
% 1.32/0.53    ? [X0,X1,X2] : (X0 != X1 & k1_tarski(X0) = k2_tarski(X1,X2)) => (sK0 != sK1 & k1_tarski(sK0) = k2_tarski(sK1,sK2))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f15,plain,(
% 1.32/0.53    ? [X0,X1,X2] : (X0 != X1 & k1_tarski(X0) = k2_tarski(X1,X2))),
% 1.32/0.53    inference(ennf_transformation,[],[f14])).
% 1.32/0.53  fof(f14,negated_conjecture,(
% 1.32/0.53    ~! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 1.32/0.53    inference(negated_conjecture,[],[f13])).
% 1.32/0.53  fof(f13,conjecture,(
% 1.32/0.53    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).
% 1.32/0.53  fof(f116,plain,(
% 1.32/0.53    sK0 = sK1),
% 1.32/0.53    inference(resolution,[],[f101,f26])).
% 1.32/0.53  fof(f26,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.32/0.53    inference(cnf_transformation,[],[f16])).
% 1.32/0.53  fof(f16,plain,(
% 1.32/0.53    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.32/0.53    inference(ennf_transformation,[],[f12])).
% 1.32/0.53  fof(f12,axiom,(
% 1.32/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 1.32/0.53  fof(f101,plain,(
% 1.32/0.53    r1_tarski(k1_tarski(sK1),k1_tarski(sK0))),
% 1.32/0.53    inference(superposition,[],[f98,f19])).
% 1.32/0.53  fof(f19,plain,(
% 1.32/0.53    k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 1.32/0.53    inference(cnf_transformation,[],[f18])).
% 1.32/0.53  fof(f98,plain,(
% 1.32/0.53    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.32/0.53    inference(superposition,[],[f86,f23])).
% 1.32/0.53  fof(f23,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f6])).
% 1.32/0.53  fof(f6,axiom,(
% 1.32/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.32/0.53  fof(f86,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (r1_tarski(k1_tarski(X0),k1_enumset1(X0,X1,X2))) )),
% 1.32/0.53    inference(superposition,[],[f79,f27])).
% 1.32/0.53  % (15624)Refutation not found, incomplete strategy% (15624)------------------------------
% 1.32/0.53  % (15624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  fof(f27,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f7])).
% 1.32/0.53  % (15624)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (15624)Memory used [KB]: 10618
% 1.32/0.53  % (15624)Time elapsed: 0.109 s
% 1.32/0.53  % (15624)------------------------------
% 1.32/0.53  % (15624)------------------------------
% 1.32/0.53  fof(f7,axiom,(
% 1.32/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.32/0.53  fof(f79,plain,(
% 1.32/0.53    ( ! [X2,X0,X3,X1] : (r1_tarski(k1_tarski(X0),k2_enumset1(X0,X1,X2,X3))) )),
% 1.32/0.53    inference(superposition,[],[f60,f28])).
% 1.32/0.53  fof(f28,plain,(
% 1.32/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f8])).
% 1.32/0.53  fof(f8,axiom,(
% 1.32/0.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.32/0.53  fof(f60,plain,(
% 1.32/0.53    ( ! [X6,X4,X8,X7,X5] : (r1_tarski(k1_tarski(X4),k3_enumset1(X4,X5,X6,X7,X8))) )),
% 1.32/0.53    inference(forward_demodulation,[],[f58,f29])).
% 1.32/0.53  fof(f29,plain,(
% 1.32/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f9])).
% 1.32/0.53  fof(f9,axiom,(
% 1.32/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.32/0.53  fof(f58,plain,(
% 1.32/0.53    ( ! [X6,X4,X8,X7,X5] : (r1_tarski(k1_tarski(X4),k4_enumset1(X4,X4,X5,X6,X7,X8))) )),
% 1.32/0.53    inference(superposition,[],[f47,f21])).
% 1.32/0.53  fof(f21,plain,(
% 1.32/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f5])).
% 1.32/0.53  fof(f5,axiom,(
% 1.32/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.32/0.53  fof(f47,plain,(
% 1.32/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tarski(k2_tarski(X0,X1),k4_enumset1(X0,X1,X2,X3,X4,X5))) )),
% 1.32/0.53    inference(forward_demodulation,[],[f45,f30])).
% 1.32/0.53  fof(f30,plain,(
% 1.32/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f10])).
% 1.32/0.53  fof(f10,axiom,(
% 1.32/0.53    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.32/0.53  fof(f45,plain,(
% 1.32/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tarski(k2_tarski(X0,X1),k5_enumset1(X0,X0,X1,X2,X3,X4,X5))) )),
% 1.32/0.53    inference(superposition,[],[f39,f23])).
% 1.32/0.53  fof(f39,plain,(
% 1.32/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tarski(k1_enumset1(X0,X1,X2),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))) )),
% 1.32/0.53    inference(forward_demodulation,[],[f37,f31])).
% 1.32/0.53  fof(f31,plain,(
% 1.32/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f11])).
% 1.32/0.53  fof(f11,axiom,(
% 1.32/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.32/0.53  fof(f37,plain,(
% 1.32/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tarski(k1_enumset1(X0,X1,X2),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) )),
% 1.32/0.53    inference(superposition,[],[f35,f27])).
% 1.32/0.53  fof(f35,plain,(
% 1.32/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tarski(k2_enumset1(X0,X1,X2,X3),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 1.32/0.53    inference(superposition,[],[f22,f32])).
% 1.32/0.53  fof(f32,plain,(
% 1.32/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f4])).
% 1.32/0.53  % (15617)Refutation not found, incomplete strategy% (15617)------------------------------
% 1.32/0.53  % (15617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  fof(f4,axiom,(
% 1.32/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).
% 1.32/0.53  fof(f22,plain,(
% 1.32/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f2])).
% 1.32/0.53  fof(f2,axiom,(
% 1.32/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.32/0.53  % SZS output end Proof for theBenchmark
% 1.32/0.53  % (15621)------------------------------
% 1.32/0.53  % (15621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (15621)Termination reason: Refutation
% 1.32/0.53  
% 1.32/0.53  % (15621)Memory used [KB]: 1791
% 1.32/0.53  % (15621)Time elapsed: 0.115 s
% 1.32/0.53  % (15621)------------------------------
% 1.32/0.53  % (15621)------------------------------
% 1.32/0.53  % (15610)Success in time 0.172 s
%------------------------------------------------------------------------------
