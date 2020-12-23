%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:18 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   43 (  79 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :   74 ( 131 expanded)
%              Number of equality atoms :   37 (  79 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f183,plain,(
    $false ),
    inference(resolution,[],[f154,f54])).

fof(f54,plain,(
    ! [X2] : r2_hidden(X2,k1_enumset1(X2,X2,X2)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_enumset1(X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f29,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f39])).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f154,plain,(
    ! [X0] : ~ r2_hidden(sK0,X0) ),
    inference(forward_demodulation,[],[f153,f34])).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f153,plain,(
    ! [X0] : ~ r2_hidden(sK0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f149,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f149,plain,(
    ! [X0] : ~ r2_hidden(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f129,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f25,f28])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f129,plain,(
    ! [X0] : ~ sP3(sK0,k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f118,f23])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f118,plain,(
    r2_hidden(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f113,f41])).

fof(f41,plain,(
    k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f19,f28,f40,f40])).

fof(f19,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(f113,plain,(
    r2_hidden(sK0,k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)))) ),
    inference(unit_resulting_resolution,[],[f73,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f24,f28])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f73,plain,(
    sP3(sK0,k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f54,f65,f21])).

fof(f21,plain,(
    ! [X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f65,plain,(
    ~ r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f20,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_enumset1(X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f30,f40])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f20,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:09:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.53  % (22761)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.45/0.55  % (22758)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.45/0.55  % (22756)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.45/0.56  % (22774)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.63/0.56  % (22777)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.63/0.57  % (22766)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.63/0.57  % (22757)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.63/0.57  % (22759)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.63/0.57  % (22769)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.63/0.58  % (22756)Refutation not found, incomplete strategy% (22756)------------------------------
% 1.63/0.58  % (22756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (22756)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.58  
% 1.63/0.58  % (22756)Memory used [KB]: 1663
% 1.63/0.58  % (22756)Time elapsed: 0.156 s
% 1.63/0.58  % (22756)------------------------------
% 1.63/0.58  % (22756)------------------------------
% 1.63/0.58  % (22772)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.63/0.58  % (22771)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.63/0.58  % (22781)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.63/0.58  % (22764)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.63/0.58  % (22760)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.63/0.58  % (22774)Refutation found. Thanks to Tanya!
% 1.63/0.58  % SZS status Theorem for theBenchmark
% 1.63/0.59  % (22783)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.63/0.59  % (22763)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.63/0.59  % SZS output start Proof for theBenchmark
% 1.63/0.59  fof(f183,plain,(
% 1.63/0.59    $false),
% 1.63/0.59    inference(resolution,[],[f154,f54])).
% 1.63/0.59  fof(f54,plain,(
% 1.63/0.59    ( ! [X2] : (r2_hidden(X2,k1_enumset1(X2,X2,X2))) )),
% 1.63/0.59    inference(equality_resolution,[],[f53])).
% 1.63/0.59  fof(f53,plain,(
% 1.63/0.59    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_enumset1(X2,X2,X2) != X1) )),
% 1.63/0.59    inference(equality_resolution,[],[f49])).
% 1.63/0.59  fof(f49,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 1.63/0.59    inference(definition_unfolding,[],[f29,f40])).
% 1.63/0.59  fof(f40,plain,(
% 1.63/0.59    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.63/0.59    inference(definition_unfolding,[],[f33,f39])).
% 1.63/0.59  fof(f39,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f10])).
% 1.63/0.59  fof(f10,axiom,(
% 1.63/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.63/0.59  fof(f33,plain,(
% 1.63/0.59    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f9])).
% 1.63/0.59  fof(f9,axiom,(
% 1.63/0.59    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.63/0.59  fof(f29,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.63/0.59    inference(cnf_transformation,[],[f8])).
% 1.63/0.59  fof(f8,axiom,(
% 1.63/0.59    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.63/0.59  fof(f154,plain,(
% 1.63/0.59    ( ! [X0] : (~r2_hidden(sK0,X0)) )),
% 1.63/0.59    inference(forward_demodulation,[],[f153,f34])).
% 1.63/0.59  fof(f34,plain,(
% 1.63/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.63/0.59    inference(cnf_transformation,[],[f5])).
% 1.63/0.59  fof(f5,axiom,(
% 1.63/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.63/0.59  fof(f153,plain,(
% 1.63/0.59    ( ! [X0] : (~r2_hidden(sK0,k5_xboole_0(X0,k1_xboole_0))) )),
% 1.63/0.59    inference(forward_demodulation,[],[f149,f36])).
% 1.63/0.59  fof(f36,plain,(
% 1.63/0.59    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f4])).
% 1.63/0.59  fof(f4,axiom,(
% 1.63/0.59    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.63/0.59  fof(f149,plain,(
% 1.63/0.59    ( ! [X0] : (~r2_hidden(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))) )),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f129,f50])).
% 1.63/0.59  fof(f50,plain,(
% 1.63/0.59    ( ! [X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.63/0.59    inference(equality_resolution,[],[f44])).
% 1.63/0.59  fof(f44,plain,(
% 1.63/0.59    ( ! [X2,X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.63/0.59    inference(definition_unfolding,[],[f25,f28])).
% 1.63/0.59  fof(f28,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.63/0.59    inference(cnf_transformation,[],[f3])).
% 1.63/0.59  fof(f3,axiom,(
% 1.63/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.63/0.59  fof(f25,plain,(
% 1.63/0.59    ( ! [X2,X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.63/0.59    inference(cnf_transformation,[],[f2])).
% 1.63/0.59  fof(f2,axiom,(
% 1.63/0.59    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.63/0.59  fof(f129,plain,(
% 1.63/0.59    ( ! [X0] : (~sP3(sK0,k1_xboole_0,X0)) )),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f118,f23])).
% 1.63/0.59  fof(f23,plain,(
% 1.63/0.59    ( ! [X0,X3,X1] : (~sP3(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f2])).
% 1.63/0.59  fof(f118,plain,(
% 1.63/0.59    r2_hidden(sK0,k1_xboole_0)),
% 1.63/0.59    inference(forward_demodulation,[],[f113,f41])).
% 1.63/0.59  fof(f41,plain,(
% 1.63/0.59    k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)))),
% 1.63/0.59    inference(definition_unfolding,[],[f19,f28,f40,f40])).
% 1.63/0.59  fof(f19,plain,(
% 1.63/0.59    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.63/0.59    inference(cnf_transformation,[],[f18])).
% 1.63/0.59  fof(f18,plain,(
% 1.63/0.59    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.63/0.59    inference(ennf_transformation,[],[f17])).
% 1.63/0.59  fof(f17,negated_conjecture,(
% 1.63/0.59    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.63/0.59    inference(negated_conjecture,[],[f16])).
% 1.63/0.59  fof(f16,conjecture,(
% 1.63/0.59    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).
% 1.63/0.59  fof(f113,plain,(
% 1.63/0.59    r2_hidden(sK0,k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))))),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f73,f51])).
% 1.63/0.59  fof(f51,plain,(
% 1.63/0.59    ( ! [X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.63/0.59    inference(equality_resolution,[],[f45])).
% 1.63/0.59  fof(f45,plain,(
% 1.63/0.59    ( ! [X2,X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.63/0.59    inference(definition_unfolding,[],[f24,f28])).
% 1.63/0.59  fof(f24,plain,(
% 1.63/0.59    ( ! [X2,X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.63/0.59    inference(cnf_transformation,[],[f2])).
% 1.63/0.59  fof(f73,plain,(
% 1.63/0.59    sP3(sK0,k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK0,sK0,sK0))),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f54,f65,f21])).
% 1.63/0.59  fof(f21,plain,(
% 1.63/0.59    ( ! [X0,X3,X1] : (sP3(X3,X1,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f2])).
% 1.63/0.59  fof(f65,plain,(
% 1.63/0.59    ~r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1))),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f20,f52])).
% 1.63/0.59  fof(f52,plain,(
% 1.63/0.59    ( ! [X2,X0] : (~r2_hidden(X2,k1_enumset1(X0,X0,X0)) | X0 = X2) )),
% 1.63/0.59    inference(equality_resolution,[],[f48])).
% 1.63/0.59  fof(f48,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 1.63/0.59    inference(definition_unfolding,[],[f30,f40])).
% 1.63/0.59  fof(f30,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.63/0.59    inference(cnf_transformation,[],[f8])).
% 1.63/0.59  fof(f20,plain,(
% 1.63/0.59    sK0 != sK1),
% 1.63/0.59    inference(cnf_transformation,[],[f18])).
% 1.63/0.59  % SZS output end Proof for theBenchmark
% 1.63/0.59  % (22774)------------------------------
% 1.63/0.59  % (22774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.59  % (22774)Termination reason: Refutation
% 1.63/0.59  
% 1.63/0.59  % (22774)Memory used [KB]: 1791
% 1.63/0.59  % (22774)Time elapsed: 0.161 s
% 1.63/0.59  % (22774)------------------------------
% 1.63/0.59  % (22774)------------------------------
% 1.63/0.59  % (22778)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.63/0.59  % (22755)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.63/0.59  % (22754)Success in time 0.239 s
%------------------------------------------------------------------------------
