%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:39 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   39 (  52 expanded)
%              Number of leaves         :   10 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :   66 (  92 expanded)
%              Number of equality atoms :   23 (  31 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(resolution,[],[f120,f99])).

fof(f99,plain,(
    r2_hidden(sK1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f49,f98])).

fof(f98,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | ~ sP4(X0,sK1,sK0) ) ),
    inference(superposition,[],[f48,f79])).

fof(f79,plain,(
    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f36,f53,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f53,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f34,f42])).

fof(f42,plain,(
    k1_xboole_0 = k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f20,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f14])).

% (17401)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_enumset1(X0,X0,X0,X1))
      | ~ sP4(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f24,f41])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f49,plain,(
    ! [X0,X3] : sP4(X3,X3,X0) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( X1 != X3
      | sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f120,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f69,f116])).

fof(f116,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f69,f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f69,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f37,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f37,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:28:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.55  % (17393)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.57  % (17393)Refutation not found, incomplete strategy% (17393)------------------------------
% 0.22/0.57  % (17393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (17393)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (17393)Memory used [KB]: 1663
% 0.22/0.57  % (17393)Time elapsed: 0.135 s
% 0.22/0.57  % (17393)------------------------------
% 0.22/0.57  % (17393)------------------------------
% 0.22/0.57  % (17403)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.57  % (17411)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.58  % (17412)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.58  % (17400)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.58  % (17402)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.68/0.58  % (17420)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.68/0.58  % (17397)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.68/0.58  % (17392)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.68/0.59  % (17412)Refutation found. Thanks to Tanya!
% 1.68/0.59  % SZS status Theorem for theBenchmark
% 1.68/0.59  % SZS output start Proof for theBenchmark
% 1.68/0.59  fof(f129,plain,(
% 1.68/0.59    $false),
% 1.68/0.59    inference(resolution,[],[f120,f99])).
% 1.68/0.59  fof(f99,plain,(
% 1.68/0.59    r2_hidden(sK1,k1_xboole_0)),
% 1.68/0.59    inference(unit_resulting_resolution,[],[f49,f98])).
% 1.68/0.59  fof(f98,plain,(
% 1.68/0.59    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~sP4(X0,sK1,sK0)) )),
% 1.68/0.59    inference(superposition,[],[f48,f79])).
% 1.68/0.59  fof(f79,plain,(
% 1.68/0.59    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1)),
% 1.68/0.59    inference(unit_resulting_resolution,[],[f36,f53,f30])).
% 1.68/0.59  fof(f30,plain,(
% 1.68/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.68/0.59    inference(cnf_transformation,[],[f4])).
% 1.68/0.59  fof(f4,axiom,(
% 1.68/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.68/0.59  fof(f53,plain,(
% 1.68/0.59    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k1_xboole_0)),
% 1.68/0.59    inference(superposition,[],[f34,f42])).
% 1.68/0.59  fof(f42,plain,(
% 1.68/0.59    k1_xboole_0 = k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),
% 1.68/0.59    inference(definition_unfolding,[],[f20,f41])).
% 1.68/0.59  fof(f41,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.68/0.59    inference(definition_unfolding,[],[f35,f40])).
% 1.68/0.59  fof(f40,plain,(
% 1.68/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f11])).
% 1.68/0.59  fof(f11,axiom,(
% 1.68/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.68/0.59  fof(f35,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f10])).
% 1.68/0.59  fof(f10,axiom,(
% 1.68/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.68/0.59  fof(f20,plain,(
% 1.68/0.59    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.68/0.59    inference(cnf_transformation,[],[f16])).
% 1.68/0.59  fof(f16,plain,(
% 1.68/0.59    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.68/0.59    inference(ennf_transformation,[],[f14])).
% 1.68/0.59  % (17401)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.68/0.59  fof(f14,negated_conjecture,(
% 1.68/0.59    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.68/0.59    inference(negated_conjecture,[],[f13])).
% 1.68/0.59  fof(f13,conjecture,(
% 1.68/0.59    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 1.68/0.59  fof(f34,plain,(
% 1.68/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.68/0.59    inference(cnf_transformation,[],[f8])).
% 1.68/0.59  fof(f8,axiom,(
% 1.68/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.68/0.59  fof(f36,plain,(
% 1.68/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f6])).
% 1.68/0.59  fof(f6,axiom,(
% 1.68/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.68/0.59  fof(f48,plain,(
% 1.68/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_enumset1(X0,X0,X0,X1)) | ~sP4(X3,X1,X0)) )),
% 1.68/0.59    inference(equality_resolution,[],[f46])).
% 1.68/0.59  fof(f46,plain,(
% 1.68/0.59    ( ! [X2,X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.68/0.59    inference(definition_unfolding,[],[f24,f41])).
% 1.68/0.59  fof(f24,plain,(
% 1.68/0.59    ( ! [X2,X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.68/0.59    inference(cnf_transformation,[],[f9])).
% 1.68/0.59  fof(f9,axiom,(
% 1.68/0.59    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.68/0.59  fof(f49,plain,(
% 1.68/0.59    ( ! [X0,X3] : (sP4(X3,X3,X0)) )),
% 1.68/0.59    inference(equality_resolution,[],[f22])).
% 1.68/0.59  fof(f22,plain,(
% 1.68/0.59    ( ! [X0,X3,X1] : (X1 != X3 | sP4(X3,X1,X0)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f9])).
% 1.68/0.59  fof(f120,plain,(
% 1.68/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.68/0.59    inference(backward_demodulation,[],[f69,f116])).
% 1.68/0.59  fof(f116,plain,(
% 1.68/0.59    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.68/0.59    inference(unit_resulting_resolution,[],[f69,f33])).
% 1.68/0.59  fof(f33,plain,(
% 1.68/0.59    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 1.68/0.59    inference(cnf_transformation,[],[f18])).
% 1.68/0.59  fof(f18,plain,(
% 1.68/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.68/0.59    inference(ennf_transformation,[],[f3])).
% 1.68/0.59  fof(f3,axiom,(
% 1.68/0.59    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.68/0.59  fof(f69,plain,(
% 1.68/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 1.68/0.59    inference(unit_resulting_resolution,[],[f37,f38])).
% 1.68/0.59  fof(f38,plain,(
% 1.68/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f19])).
% 1.68/0.59  fof(f19,plain,(
% 1.68/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.68/0.59    inference(ennf_transformation,[],[f15])).
% 1.68/0.59  fof(f15,plain,(
% 1.68/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.68/0.59    inference(rectify,[],[f2])).
% 1.68/0.59  fof(f2,axiom,(
% 1.68/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.68/0.59  fof(f37,plain,(
% 1.68/0.59    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f7])).
% 1.68/0.59  fof(f7,axiom,(
% 1.68/0.59    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.68/0.59  % SZS output end Proof for theBenchmark
% 1.68/0.59  % (17412)------------------------------
% 1.68/0.59  % (17412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.59  % (17412)Termination reason: Refutation
% 1.68/0.59  
% 1.68/0.59  % (17412)Memory used [KB]: 1791
% 1.68/0.59  % (17412)Time elapsed: 0.157 s
% 1.68/0.59  % (17412)------------------------------
% 1.68/0.59  % (17412)------------------------------
% 1.68/0.59  % (17391)Success in time 0.229 s
%------------------------------------------------------------------------------
