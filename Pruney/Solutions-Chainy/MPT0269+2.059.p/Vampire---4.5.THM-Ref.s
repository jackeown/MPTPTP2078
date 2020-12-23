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
% DateTime   : Thu Dec  3 12:40:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   31 (  64 expanded)
%              Number of leaves         :    7 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :   71 ( 175 expanded)
%              Number of equality atoms :   35 ( 133 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f61,plain,(
    $false ),
    inference(subsumption_resolution,[],[f60,f47])).

fof(f47,plain,(
    r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f42,f24])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK0 != k1_tarski(sK1)
    & k1_xboole_0 != sK0
    & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) )
   => ( sK0 != k1_tarski(sK1)
      & k1_xboole_0 != sK0
      & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f42,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK1,sK0) ),
    inference(superposition,[],[f23,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f23,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f59,f49])).

fof(f49,plain,(
    ~ r1_tarski(k1_tarski(sK1),sK0) ),
    inference(subsumption_resolution,[],[f48,f25])).

fof(f25,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,
    ( sK0 = k1_tarski(sK1)
    | ~ r1_tarski(k1_tarski(sK1),sK0) ),
    inference(forward_demodulation,[],[f45,f28])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f45,plain,
    ( sK0 = k2_xboole_0(k1_tarski(sK1),k1_xboole_0)
    | ~ r1_tarski(k1_tarski(sK1),sK0) ),
    inference(superposition,[],[f35,f23])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f59,plain,
    ( r1_tarski(k1_tarski(sK1),sK0)
    | ~ r2_hidden(sK1,sK0) ),
    inference(superposition,[],[f50,f30])).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f50,plain,(
    ! [X0] :
      ( r1_tarski(k2_tarski(sK1,X0),sK0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f47,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:00:27 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.53  % (29146)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (29150)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (29146)Refutation not found, incomplete strategy% (29146)------------------------------
% 0.22/0.54  % (29146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (29146)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (29146)Memory used [KB]: 1663
% 0.22/0.54  % (29146)Time elapsed: 0.111 s
% 0.22/0.54  % (29146)------------------------------
% 0.22/0.54  % (29146)------------------------------
% 0.22/0.55  % (29150)Refutation not found, incomplete strategy% (29150)------------------------------
% 0.22/0.55  % (29150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (29150)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (29150)Memory used [KB]: 6140
% 0.22/0.55  % (29150)Time elapsed: 0.124 s
% 0.22/0.55  % (29150)------------------------------
% 0.22/0.55  % (29150)------------------------------
% 0.22/0.55  % (29154)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (29166)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (29154)Refutation not found, incomplete strategy% (29154)------------------------------
% 0.22/0.56  % (29154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (29154)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (29154)Memory used [KB]: 10618
% 0.22/0.56  % (29154)Time elapsed: 0.131 s
% 0.22/0.56  % (29154)------------------------------
% 0.22/0.56  % (29154)------------------------------
% 0.22/0.56  % (29158)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (29174)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.57  % (29155)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.57  % (29151)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.57  % (29155)Refutation not found, incomplete strategy% (29155)------------------------------
% 0.22/0.57  % (29155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (29155)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (29155)Memory used [KB]: 10618
% 0.22/0.57  % (29155)Time elapsed: 0.143 s
% 0.22/0.57  % (29155)------------------------------
% 0.22/0.57  % (29155)------------------------------
% 0.22/0.57  % (29166)Refutation not found, incomplete strategy% (29166)------------------------------
% 0.22/0.57  % (29166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (29149)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.58  % (29166)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (29166)Memory used [KB]: 10746
% 0.22/0.58  % (29156)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.58  % (29166)Time elapsed: 0.145 s
% 0.22/0.58  % (29166)------------------------------
% 0.22/0.58  % (29166)------------------------------
% 0.22/0.58  % (29153)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.58  % (29156)Refutation not found, incomplete strategy% (29156)------------------------------
% 0.22/0.58  % (29156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (29156)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (29156)Memory used [KB]: 10618
% 0.22/0.58  % (29156)Time elapsed: 0.151 s
% 0.22/0.58  % (29156)------------------------------
% 0.22/0.58  % (29156)------------------------------
% 0.22/0.58  % (29152)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.58  % (29170)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.59  % (29169)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.59  % (29169)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 0.22/0.59  % SZS output start Proof for theBenchmark
% 0.22/0.59  fof(f61,plain,(
% 0.22/0.59    $false),
% 0.22/0.59    inference(subsumption_resolution,[],[f60,f47])).
% 0.22/0.59  fof(f47,plain,(
% 0.22/0.59    r2_hidden(sK1,sK0)),
% 0.22/0.59    inference(subsumption_resolution,[],[f42,f24])).
% 0.22/0.59  fof(f24,plain,(
% 0.22/0.59    k1_xboole_0 != sK0),
% 0.22/0.59    inference(cnf_transformation,[],[f19])).
% 0.22/0.59  fof(f19,plain,(
% 0.22/0.59    sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.22/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18])).
% 0.22/0.59  fof(f18,plain,(
% 0.22/0.59    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1))) => (sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f16,plain,(
% 0.22/0.59    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.22/0.59    inference(ennf_transformation,[],[f15])).
% 0.22/0.59  fof(f15,negated_conjecture,(
% 0.22/0.59    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.22/0.59    inference(negated_conjecture,[],[f14])).
% 0.22/0.59  fof(f14,conjecture,(
% 0.22/0.59    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 0.22/0.59  fof(f42,plain,(
% 0.22/0.59    k1_xboole_0 = sK0 | r2_hidden(sK1,sK0)),
% 0.22/0.59    inference(superposition,[],[f23,f37])).
% 0.22/0.59  fof(f37,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f20])).
% 0.22/0.59  fof(f20,plain,(
% 0.22/0.59    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.22/0.59    inference(nnf_transformation,[],[f13])).
% 0.22/0.59  fof(f13,axiom,(
% 0.22/0.59    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.22/0.59  fof(f23,plain,(
% 0.22/0.59    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.22/0.59    inference(cnf_transformation,[],[f19])).
% 0.22/0.59  fof(f60,plain,(
% 0.22/0.59    ~r2_hidden(sK1,sK0)),
% 0.22/0.59    inference(subsumption_resolution,[],[f59,f49])).
% 0.22/0.59  fof(f49,plain,(
% 0.22/0.59    ~r1_tarski(k1_tarski(sK1),sK0)),
% 0.22/0.59    inference(subsumption_resolution,[],[f48,f25])).
% 0.22/0.59  fof(f25,plain,(
% 0.22/0.59    sK0 != k1_tarski(sK1)),
% 0.22/0.59    inference(cnf_transformation,[],[f19])).
% 0.22/0.59  fof(f48,plain,(
% 0.22/0.59    sK0 = k1_tarski(sK1) | ~r1_tarski(k1_tarski(sK1),sK0)),
% 0.22/0.59    inference(forward_demodulation,[],[f45,f28])).
% 0.22/0.59  fof(f28,plain,(
% 0.22/0.59    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f2])).
% 0.22/0.59  fof(f2,axiom,(
% 0.22/0.59    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.59  fof(f45,plain,(
% 0.22/0.59    sK0 = k2_xboole_0(k1_tarski(sK1),k1_xboole_0) | ~r1_tarski(k1_tarski(sK1),sK0)),
% 0.22/0.59    inference(superposition,[],[f35,f23])).
% 0.22/0.59  fof(f35,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f17])).
% 0.22/0.59  fof(f17,plain,(
% 0.22/0.59    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.59    inference(ennf_transformation,[],[f4])).
% 0.22/0.59  fof(f4,axiom,(
% 0.22/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 0.22/0.59  fof(f59,plain,(
% 0.22/0.59    r1_tarski(k1_tarski(sK1),sK0) | ~r2_hidden(sK1,sK0)),
% 0.22/0.59    inference(superposition,[],[f50,f30])).
% 0.22/0.59  fof(f30,plain,(
% 0.22/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f8])).
% 0.22/0.59  fof(f8,axiom,(
% 0.22/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.59  fof(f50,plain,(
% 0.22/0.59    ( ! [X0] : (r1_tarski(k2_tarski(sK1,X0),sK0) | ~r2_hidden(X0,sK0)) )),
% 0.22/0.59    inference(resolution,[],[f47,f41])).
% 0.22/0.59  fof(f41,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f22])).
% 0.22/0.59  fof(f22,plain,(
% 0.22/0.59    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.22/0.59    inference(flattening,[],[f21])).
% 0.22/0.59  fof(f21,plain,(
% 0.22/0.59    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.22/0.59    inference(nnf_transformation,[],[f12])).
% 0.22/0.59  fof(f12,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.22/0.59  % SZS output end Proof for theBenchmark
% 0.22/0.59  % (29169)------------------------------
% 0.22/0.59  % (29169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (29169)Termination reason: Refutation
% 0.22/0.59  
% 0.22/0.59  % (29169)Memory used [KB]: 1663
% 0.22/0.59  % (29169)Time elapsed: 0.120 s
% 0.22/0.59  % (29169)------------------------------
% 0.22/0.59  % (29169)------------------------------
% 0.22/0.59  % (29145)Success in time 0.224 s
%------------------------------------------------------------------------------
