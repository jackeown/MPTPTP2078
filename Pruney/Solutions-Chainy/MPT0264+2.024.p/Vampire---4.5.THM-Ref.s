%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   24 (  31 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :   10
%              Number of atoms          :   57 (  79 expanded)
%              Number of equality atoms :   29 (  44 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58,plain,(
    $false ),
    inference(subsumption_resolution,[],[f57,f12])).

fof(f12,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r2_hidden(X1,X2)
      & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X1
          & r2_hidden(X1,X2)
          & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X1
        & r2_hidden(X1,X2)
        & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).

fof(f57,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f53,f32])).

fof(f32,plain,(
    ! [X0,X3] : r2_hidden(X3,k2_tarski(X0,X3)) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k2_tarski(X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f53,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | sK0 = sK1 ),
    inference(resolution,[],[f48,f11])).

fof(f11,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X6,k2_tarski(sK0,sK1))
      | sK0 = X6 ) ),
    inference(duplicate_literal_removal,[],[f45])).

fof(f45,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X6,k2_tarski(sK0,sK1))
      | sK0 = X6
      | sK0 = X6 ) ),
    inference(resolution,[],[f40,f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

% (17240)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_tarski(sK0,sK0))
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,k2_tarski(sK0,sK1)) ) ),
    inference(superposition,[],[f28,f27])).

fof(f27,plain,(
    k3_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f10,f26])).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f10,plain,(
    k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:15:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.56  % (17243)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.57  % (17223)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (17244)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.57  % (17227)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.57  % (17236)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.57  % (17228)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.57  % (17244)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.58  % (17225)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.58  % (17235)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.58  % (17221)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.58  % (17239)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f58,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(subsumption_resolution,[],[f57,f12])).
% 0.22/0.58  fof(f12,plain,(
% 0.22/0.58    sK0 != sK1),
% 0.22/0.58    inference(cnf_transformation,[],[f9])).
% 0.22/0.59  fof(f9,plain,(
% 0.22/0.59    ? [X0,X1,X2] : (X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 0.22/0.59    inference(ennf_transformation,[],[f8])).
% 0.22/0.59  fof(f8,negated_conjecture,(
% 0.22/0.59    ~! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 0.22/0.59    inference(negated_conjecture,[],[f7])).
% 0.22/0.59  fof(f7,conjecture,(
% 0.22/0.59    ! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).
% 0.22/0.59  fof(f57,plain,(
% 0.22/0.59    sK0 = sK1),
% 0.22/0.59    inference(subsumption_resolution,[],[f53,f32])).
% 0.22/0.59  fof(f32,plain,(
% 0.22/0.59    ( ! [X0,X3] : (r2_hidden(X3,k2_tarski(X0,X3))) )),
% 0.22/0.59    inference(equality_resolution,[],[f31])).
% 0.22/0.59  fof(f31,plain,(
% 0.22/0.59    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k2_tarski(X0,X3) != X2) )),
% 0.22/0.59    inference(equality_resolution,[],[f24])).
% 0.22/0.59  fof(f24,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.59    inference(cnf_transformation,[],[f4])).
% 0.22/0.59  fof(f4,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.59  fof(f53,plain,(
% 0.22/0.59    ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | sK0 = sK1),
% 0.22/0.59    inference(resolution,[],[f48,f11])).
% 0.22/0.59  fof(f11,plain,(
% 0.22/0.59    r2_hidden(sK1,sK2)),
% 0.22/0.59    inference(cnf_transformation,[],[f9])).
% 0.22/0.59  fof(f48,plain,(
% 0.22/0.59    ( ! [X6] : (~r2_hidden(X6,sK2) | ~r2_hidden(X6,k2_tarski(sK0,sK1)) | sK0 = X6) )),
% 0.22/0.59    inference(duplicate_literal_removal,[],[f45])).
% 0.22/0.59  fof(f45,plain,(
% 0.22/0.59    ( ! [X6] : (~r2_hidden(X6,sK2) | ~r2_hidden(X6,k2_tarski(sK0,sK1)) | sK0 = X6 | sK0 = X6) )),
% 0.22/0.59    inference(resolution,[],[f40,f35])).
% 0.22/0.59  fof(f35,plain,(
% 0.22/0.59    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_tarski(X0,X1)) | X1 = X3 | X0 = X3) )),
% 0.22/0.59    inference(equality_resolution,[],[f22])).
% 0.22/0.59  fof(f22,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.59    inference(cnf_transformation,[],[f4])).
% 0.22/0.59  % (17240)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.59  fof(f40,plain,(
% 0.22/0.59    ( ! [X0] : (r2_hidden(X0,k2_tarski(sK0,sK0)) | ~r2_hidden(X0,sK2) | ~r2_hidden(X0,k2_tarski(sK0,sK1))) )),
% 0.22/0.59    inference(superposition,[],[f28,f27])).
% 0.22/0.59  fof(f27,plain,(
% 0.22/0.59    k3_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK0)),
% 0.22/0.59    inference(definition_unfolding,[],[f10,f26])).
% 0.22/0.59  fof(f26,plain,(
% 0.22/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f5])).
% 0.22/0.59  fof(f5,axiom,(
% 0.22/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.59  fof(f10,plain,(
% 0.22/0.59    k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.22/0.59    inference(cnf_transformation,[],[f9])).
% 0.22/0.59  fof(f28,plain,(
% 0.22/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,k3_xboole_0(X0,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 0.22/0.59    inference(equality_resolution,[],[f18])).
% 0.22/0.59  fof(f18,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.59    inference(cnf_transformation,[],[f2])).
% 0.22/0.59  fof(f2,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.22/0.59  % SZS output end Proof for theBenchmark
% 0.22/0.59  % (17244)------------------------------
% 0.22/0.59  % (17244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (17244)Termination reason: Refutation
% 0.22/0.59  
% 0.22/0.59  % (17244)Memory used [KB]: 6268
% 0.22/0.59  % (17244)Time elapsed: 0.153 s
% 0.22/0.59  % (17244)------------------------------
% 0.22/0.59  % (17244)------------------------------
% 0.22/0.59  % (17219)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.59  % (17232)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.59  % (17218)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.59  % (17216)Success in time 0.223 s
%------------------------------------------------------------------------------
