%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:59 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   23 (  28 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 (  56 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f42,plain,(
    $false ),
    inference(subsumption_resolution,[],[f39,f20])).

fof(f20,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(f39,plain,(
    sK0 = sK2 ),
    inference(resolution,[],[f36,f19])).

fof(f19,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
      | X0 = X2 ) ),
    inference(resolution,[],[f34,f22])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_tarski(X2),X0)
      | ~ r1_tarski(X0,k1_tarski(X1))
      | X1 = X2 ) ),
    inference(resolution,[],[f33,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f27,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:02:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (4747)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (4743)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.19/0.51  % (4742)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.19/0.52  % (4770)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.19/0.52  % (4745)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.19/0.52  % (4746)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.19/0.52  % (4756)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.19/0.52  % (4751)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.19/0.52  % (4763)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.19/0.52  % (4744)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.19/0.52  % (4762)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.19/0.52  % (4760)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.19/0.52  % (4759)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.19/0.52  % (4759)Refutation not found, incomplete strategy% (4759)------------------------------
% 1.19/0.52  % (4759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.52  % (4759)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.52  
% 1.19/0.52  % (4759)Memory used [KB]: 1663
% 1.19/0.52  % (4759)Time elapsed: 0.124 s
% 1.19/0.52  % (4759)------------------------------
% 1.19/0.52  % (4759)------------------------------
% 1.19/0.52  % (4752)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.19/0.52  % (4760)Refutation not found, incomplete strategy% (4760)------------------------------
% 1.19/0.52  % (4760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.52  % (4751)Refutation found. Thanks to Tanya!
% 1.19/0.52  % SZS status Theorem for theBenchmark
% 1.19/0.52  % (4760)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.52  
% 1.19/0.52  % (4760)Memory used [KB]: 1663
% 1.19/0.52  % (4760)Time elapsed: 0.123 s
% 1.19/0.52  % (4760)------------------------------
% 1.19/0.52  % (4760)------------------------------
% 1.19/0.53  % (4756)Refutation not found, incomplete strategy% (4756)------------------------------
% 1.19/0.53  % (4756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.53  % (4756)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.53  
% 1.19/0.53  % (4756)Memory used [KB]: 1663
% 1.19/0.53  % (4756)Time elapsed: 0.123 s
% 1.19/0.53  % (4756)------------------------------
% 1.19/0.53  % (4756)------------------------------
% 1.19/0.53  % (4771)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.19/0.53  % (4771)Refutation not found, incomplete strategy% (4771)------------------------------
% 1.19/0.53  % (4771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.53  % (4771)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.53  
% 1.19/0.53  % (4771)Memory used [KB]: 1663
% 1.19/0.53  % (4771)Time elapsed: 0.134 s
% 1.19/0.53  % (4771)------------------------------
% 1.19/0.53  % (4771)------------------------------
% 1.19/0.53  % SZS output start Proof for theBenchmark
% 1.19/0.53  fof(f42,plain,(
% 1.19/0.53    $false),
% 1.19/0.53    inference(subsumption_resolution,[],[f39,f20])).
% 1.19/0.53  fof(f20,plain,(
% 1.19/0.53    sK0 != sK2),
% 1.19/0.53    inference(cnf_transformation,[],[f18])).
% 1.19/0.53  fof(f18,plain,(
% 1.19/0.53    sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 1.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f17])).
% 1.19/0.53  fof(f17,plain,(
% 1.19/0.53    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) => (sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)))),
% 1.19/0.53    introduced(choice_axiom,[])).
% 1.19/0.53  fof(f13,plain,(
% 1.19/0.53    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 1.19/0.53    inference(ennf_transformation,[],[f12])).
% 1.19/0.53  fof(f12,negated_conjecture,(
% 1.19/0.53    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 1.19/0.53    inference(negated_conjecture,[],[f11])).
% 1.19/0.53  fof(f11,conjecture,(
% 1.19/0.53    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).
% 1.19/0.53  fof(f39,plain,(
% 1.19/0.53    sK0 = sK2),
% 1.19/0.53    inference(resolution,[],[f36,f19])).
% 1.19/0.53  fof(f19,plain,(
% 1.19/0.53    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 1.19/0.53    inference(cnf_transformation,[],[f18])).
% 1.19/0.53  fof(f36,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) | X0 = X2) )),
% 1.19/0.53    inference(resolution,[],[f34,f22])).
% 1.19/0.53  fof(f22,plain,(
% 1.19/0.53    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.19/0.53    inference(cnf_transformation,[],[f9])).
% 1.19/0.53  fof(f9,axiom,(
% 1.19/0.53    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 1.19/0.53  fof(f34,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k1_tarski(X2),X0) | ~r1_tarski(X0,k1_tarski(X1)) | X1 = X2) )),
% 1.19/0.53    inference(resolution,[],[f33,f25])).
% 1.19/0.53  fof(f25,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.19/0.53    inference(cnf_transformation,[],[f15])).
% 1.19/0.53  fof(f15,plain,(
% 1.19/0.53    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.19/0.53    inference(ennf_transformation,[],[f10])).
% 1.19/0.53  fof(f10,axiom,(
% 1.19/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 1.19/0.53  fof(f33,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.19/0.53    inference(superposition,[],[f27,f24])).
% 1.19/0.53  fof(f24,plain,(
% 1.19/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f14])).
% 1.19/0.53  fof(f14,plain,(
% 1.19/0.53    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.19/0.53    inference(ennf_transformation,[],[f2])).
% 1.19/0.53  fof(f2,axiom,(
% 1.19/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.19/0.53  fof(f27,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f16])).
% 1.19/0.53  fof(f16,plain,(
% 1.19/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.19/0.53    inference(ennf_transformation,[],[f1])).
% 1.19/0.53  fof(f1,axiom,(
% 1.19/0.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.19/0.53  % SZS output end Proof for theBenchmark
% 1.19/0.53  % (4751)------------------------------
% 1.19/0.53  % (4751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.53  % (4751)Termination reason: Refutation
% 1.19/0.53  
% 1.19/0.53  % (4751)Memory used [KB]: 1663
% 1.19/0.53  % (4751)Time elapsed: 0.125 s
% 1.19/0.53  % (4751)------------------------------
% 1.19/0.53  % (4751)------------------------------
% 1.19/0.53  % (4764)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.19/0.53  % (4748)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.19/0.53  % (4754)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.30/0.53  % (4741)Success in time 0.168 s
%------------------------------------------------------------------------------
