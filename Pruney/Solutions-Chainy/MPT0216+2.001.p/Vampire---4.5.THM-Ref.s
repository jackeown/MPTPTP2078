%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:13 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   43 (  87 expanded)
%              Number of leaves         :   10 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :   53 ( 128 expanded)
%              Number of equality atoms :   43 ( 113 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f497,plain,(
    $false ),
    inference(subsumption_resolution,[],[f496,f221])).

fof(f221,plain,(
    sK0 != sK1 ),
    inference(backward_demodulation,[],[f23,f219])).

fof(f219,plain,(
    sK0 = sK2 ),
    inference(resolution,[],[f196,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f196,plain,(
    r1_tarski(k1_tarski(sK2),k1_tarski(sK0)) ),
    inference(superposition,[],[f26,f166])).

fof(f166,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f165,f22])).

fof(f22,plain,(
    k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK1 != sK2
    & k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( X1 != X2
        & k1_tarski(X0) = k2_tarski(X1,X2) )
   => ( sK1 != sK2
      & k1_tarski(sK0) = k2_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( X1 != X2
      & k1_tarski(X0) = k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k2_tarski(X1,X2)
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_zfmisc_1)).

fof(f165,plain,(
    k2_tarski(sK1,sK2) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f164,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f164,plain,(
    k2_tarski(sK2,sK1) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f152,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f152,plain,(
    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)) = k1_enumset1(sK2,sK2,sK1) ),
    inference(superposition,[],[f97,f57])).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(superposition,[],[f30,f24])).

fof(f24,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f97,plain,(
    ! [X0] : k1_enumset1(sK2,X0,sK1) = k2_xboole_0(k2_tarski(X0,sK2),k1_tarski(sK0)) ),
    inference(superposition,[],[f32,f22])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f23,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f21])).

fof(f496,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f494,f31])).

fof(f494,plain,(
    r1_tarski(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f486,f57])).

fof(f486,plain,(
    r1_tarski(k2_tarski(sK1,sK1),k1_tarski(sK0)) ),
    inference(superposition,[],[f139,f190])).

fof(f190,plain,(
    k1_tarski(sK0) = k2_enumset1(sK1,sK1,sK0,sK0) ),
    inference(forward_demodulation,[],[f178,f22])).

fof(f178,plain,(
    k2_tarski(sK1,sK2) = k2_enumset1(sK1,sK1,sK0,sK0) ),
    inference(superposition,[],[f148,f30])).

fof(f148,plain,(
    ! [X0,X1] : k2_enumset1(X0,X1,sK1,sK2) = k2_enumset1(X0,X1,sK0,sK0) ),
    inference(backward_demodulation,[],[f129,f132])).

fof(f132,plain,(
    ! [X12,X10,X11] : k2_enumset1(X11,X12,X10,X10) = k2_xboole_0(k2_tarski(X11,X12),k1_tarski(X10)) ),
    inference(superposition,[],[f36,f57])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f129,plain,(
    ! [X0,X1] : k2_enumset1(X0,X1,sK1,sK2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(sK0)) ),
    inference(superposition,[],[f36,f22])).

fof(f139,plain,(
    ! [X6,X8,X7,X5] : r1_tarski(k2_tarski(X5,X6),k2_enumset1(X5,X6,X7,X8)) ),
    inference(superposition,[],[f26,f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:32:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.18/0.51  % (21231)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.18/0.52  % (21233)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.18/0.52  % (21245)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.18/0.52  % (21230)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.18/0.52  % (21242)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.18/0.53  % (21239)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.18/0.53  % (21237)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.18/0.53  % (21228)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.31/0.53  % (21247)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.31/0.53  % (21256)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.31/0.53  % (21232)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.31/0.53  % (21251)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.31/0.54  % (21258)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.31/0.54  % (21258)Refutation not found, incomplete strategy% (21258)------------------------------
% 1.31/0.54  % (21258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (21258)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (21258)Memory used [KB]: 1663
% 1.31/0.54  % (21258)Time elapsed: 0.119 s
% 1.31/0.54  % (21258)------------------------------
% 1.31/0.54  % (21258)------------------------------
% 1.31/0.54  % (21243)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.31/0.54  % (21254)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.31/0.54  % (21244)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.31/0.54  % (21229)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.31/0.54  % (21250)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.31/0.54  % (21234)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.54  % (21235)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.31/0.54  % (21249)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.31/0.54  % (21246)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.31/0.55  % (21257)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.31/0.55  % (21253)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.31/0.55  % (21241)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.31/0.55  % (21248)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.31/0.55  % (21238)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.31/0.55  % (21236)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.31/0.55  % (21240)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.31/0.56  % (21237)Refutation found. Thanks to Tanya!
% 1.31/0.56  % SZS status Theorem for theBenchmark
% 1.31/0.56  % SZS output start Proof for theBenchmark
% 1.31/0.56  fof(f497,plain,(
% 1.31/0.56    $false),
% 1.31/0.56    inference(subsumption_resolution,[],[f496,f221])).
% 1.31/0.56  fof(f221,plain,(
% 1.31/0.56    sK0 != sK1),
% 1.31/0.56    inference(backward_demodulation,[],[f23,f219])).
% 1.31/0.56  fof(f219,plain,(
% 1.31/0.56    sK0 = sK2),
% 1.31/0.56    inference(resolution,[],[f196,f31])).
% 1.31/0.56  fof(f31,plain,(
% 1.31/0.56    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.31/0.56    inference(cnf_transformation,[],[f18])).
% 1.31/0.56  fof(f18,plain,(
% 1.31/0.56    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.31/0.56    inference(ennf_transformation,[],[f13])).
% 1.31/0.56  fof(f13,axiom,(
% 1.31/0.56    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 1.31/0.56  fof(f196,plain,(
% 1.31/0.56    r1_tarski(k1_tarski(sK2),k1_tarski(sK0))),
% 1.31/0.56    inference(superposition,[],[f26,f166])).
% 1.31/0.56  fof(f166,plain,(
% 1.31/0.56    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0))),
% 1.31/0.56    inference(forward_demodulation,[],[f165,f22])).
% 1.31/0.56  fof(f22,plain,(
% 1.31/0.56    k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 1.31/0.56    inference(cnf_transformation,[],[f21])).
% 1.31/0.56  fof(f21,plain,(
% 1.31/0.56    sK1 != sK2 & k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 1.31/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f20])).
% 1.31/0.56  fof(f20,plain,(
% 1.31/0.56    ? [X0,X1,X2] : (X1 != X2 & k1_tarski(X0) = k2_tarski(X1,X2)) => (sK1 != sK2 & k1_tarski(sK0) = k2_tarski(sK1,sK2))),
% 1.31/0.56    introduced(choice_axiom,[])).
% 1.31/0.56  fof(f17,plain,(
% 1.31/0.56    ? [X0,X1,X2] : (X1 != X2 & k1_tarski(X0) = k2_tarski(X1,X2))),
% 1.31/0.56    inference(ennf_transformation,[],[f15])).
% 1.31/0.56  fof(f15,negated_conjecture,(
% 1.31/0.56    ~! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X1 = X2)),
% 1.31/0.56    inference(negated_conjecture,[],[f14])).
% 1.31/0.56  fof(f14,conjecture,(
% 1.31/0.56    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X1 = X2)),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_zfmisc_1)).
% 1.31/0.56  fof(f165,plain,(
% 1.31/0.56    k2_tarski(sK1,sK2) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0))),
% 1.31/0.56    inference(forward_demodulation,[],[f164,f28])).
% 1.31/0.56  fof(f28,plain,(
% 1.31/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f5])).
% 1.31/0.56  fof(f5,axiom,(
% 1.31/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.31/0.56  fof(f164,plain,(
% 1.31/0.56    k2_tarski(sK2,sK1) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0))),
% 1.31/0.56    inference(forward_demodulation,[],[f152,f29])).
% 1.31/0.56  fof(f29,plain,(
% 1.31/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f10])).
% 1.31/0.56  fof(f10,axiom,(
% 1.31/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.31/0.56  fof(f152,plain,(
% 1.31/0.56    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)) = k1_enumset1(sK2,sK2,sK1)),
% 1.31/0.56    inference(superposition,[],[f97,f57])).
% 1.31/0.56  fof(f57,plain,(
% 1.31/0.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.31/0.56    inference(superposition,[],[f30,f24])).
% 1.31/0.56  fof(f24,plain,(
% 1.31/0.56    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f12])).
% 1.31/0.56  fof(f12,axiom,(
% 1.31/0.56    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).
% 1.31/0.56  fof(f30,plain,(
% 1.31/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f11])).
% 1.31/0.56  fof(f11,axiom,(
% 1.31/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 1.31/0.56  fof(f97,plain,(
% 1.31/0.56    ( ! [X0] : (k1_enumset1(sK2,X0,sK1) = k2_xboole_0(k2_tarski(X0,sK2),k1_tarski(sK0))) )),
% 1.31/0.56    inference(superposition,[],[f32,f22])).
% 1.31/0.56  fof(f32,plain,(
% 1.31/0.56    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)) )),
% 1.31/0.56    inference(cnf_transformation,[],[f9])).
% 1.31/0.56  fof(f9,axiom,(
% 1.31/0.56    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
% 1.31/0.56  fof(f26,plain,(
% 1.31/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.31/0.56    inference(cnf_transformation,[],[f4])).
% 1.31/0.56  fof(f4,axiom,(
% 1.31/0.56    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.31/0.56  fof(f23,plain,(
% 1.31/0.56    sK1 != sK2),
% 1.31/0.56    inference(cnf_transformation,[],[f21])).
% 1.31/0.56  fof(f496,plain,(
% 1.31/0.56    sK0 = sK1),
% 1.31/0.56    inference(resolution,[],[f494,f31])).
% 1.31/0.56  fof(f494,plain,(
% 1.31/0.56    r1_tarski(k1_tarski(sK1),k1_tarski(sK0))),
% 1.31/0.56    inference(forward_demodulation,[],[f486,f57])).
% 1.31/0.56  fof(f486,plain,(
% 1.31/0.56    r1_tarski(k2_tarski(sK1,sK1),k1_tarski(sK0))),
% 1.31/0.56    inference(superposition,[],[f139,f190])).
% 1.31/0.56  fof(f190,plain,(
% 1.31/0.56    k1_tarski(sK0) = k2_enumset1(sK1,sK1,sK0,sK0)),
% 1.31/0.56    inference(forward_demodulation,[],[f178,f22])).
% 1.31/0.56  fof(f178,plain,(
% 1.31/0.56    k2_tarski(sK1,sK2) = k2_enumset1(sK1,sK1,sK0,sK0)),
% 1.31/0.56    inference(superposition,[],[f148,f30])).
% 1.31/0.56  fof(f148,plain,(
% 1.31/0.56    ( ! [X0,X1] : (k2_enumset1(X0,X1,sK1,sK2) = k2_enumset1(X0,X1,sK0,sK0)) )),
% 1.31/0.56    inference(backward_demodulation,[],[f129,f132])).
% 1.31/0.56  fof(f132,plain,(
% 1.31/0.56    ( ! [X12,X10,X11] : (k2_enumset1(X11,X12,X10,X10) = k2_xboole_0(k2_tarski(X11,X12),k1_tarski(X10))) )),
% 1.31/0.56    inference(superposition,[],[f36,f57])).
% 1.31/0.56  fof(f36,plain,(
% 1.31/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 1.31/0.56    inference(cnf_transformation,[],[f6])).
% 1.31/0.56  fof(f6,axiom,(
% 1.31/0.56    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 1.31/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 1.31/0.56  fof(f129,plain,(
% 1.31/0.56    ( ! [X0,X1] : (k2_enumset1(X0,X1,sK1,sK2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(sK0))) )),
% 1.31/0.56    inference(superposition,[],[f36,f22])).
% 1.31/0.56  fof(f139,plain,(
% 1.31/0.56    ( ! [X6,X8,X7,X5] : (r1_tarski(k2_tarski(X5,X6),k2_enumset1(X5,X6,X7,X8))) )),
% 1.31/0.56    inference(superposition,[],[f26,f36])).
% 1.31/0.56  % SZS output end Proof for theBenchmark
% 1.31/0.56  % (21237)------------------------------
% 1.31/0.56  % (21237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (21237)Termination reason: Refutation
% 1.31/0.56  
% 1.31/0.56  % (21237)Memory used [KB]: 2046
% 1.31/0.56  % (21237)Time elapsed: 0.145 s
% 1.31/0.56  % (21237)------------------------------
% 1.31/0.56  % (21237)------------------------------
% 1.31/0.56  % (21244)Refutation not found, incomplete strategy% (21244)------------------------------
% 1.31/0.56  % (21244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (21244)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.56  
% 1.31/0.56  % (21244)Memory used [KB]: 10618
% 1.31/0.56  % (21244)Time elapsed: 0.146 s
% 1.31/0.56  % (21244)------------------------------
% 1.31/0.56  % (21244)------------------------------
% 1.31/0.56  % (21255)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.31/0.57  % (21227)Success in time 0.207 s
%------------------------------------------------------------------------------
