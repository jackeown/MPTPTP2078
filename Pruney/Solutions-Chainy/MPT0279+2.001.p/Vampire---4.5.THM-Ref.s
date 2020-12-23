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
% DateTime   : Thu Dec  3 12:41:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   27 (  73 expanded)
%              Number of leaves         :    5 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :   47 ( 131 expanded)
%              Number of equality atoms :   15 (  34 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(subsumption_resolution,[],[f114,f113])).

fof(f113,plain,(
    ~ r2_hidden(sK3(sK0,sK0),sK0) ),
    inference(forward_demodulation,[],[f102,f97])).

fof(f97,plain,(
    sK0 = sK3(k2_tarski(sK0,sK0),k1_zfmisc_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,
    ( sK0 = sK3(k2_tarski(sK0,sK0),k1_zfmisc_1(sK0))
    | sK0 = sK3(k2_tarski(sK0,sK0),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f40,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f40,plain,(
    r2_hidden(sK3(k2_tarski(sK0,sK0),k1_zfmisc_1(sK0)),k2_tarski(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f30,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f30,plain,(
    ~ r1_tarski(k2_tarski(sK0,sK0),k1_zfmisc_1(sK0)) ),
    inference(definition_unfolding,[],[f12,f20])).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f12,plain,(
    ~ r1_tarski(k1_tarski(sK0),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] : ~ r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

fof(f102,plain,(
    ~ r2_hidden(sK3(sK3(k2_tarski(sK0,sK0),k1_zfmisc_1(sK0)),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f71,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f71,plain,(
    ~ r1_tarski(sK3(k2_tarski(sK0,sK0),k1_zfmisc_1(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f41,f34])).

% (9648)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f34,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f41,plain,(
    ~ r2_hidden(sK3(k2_tarski(sK0,sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f30,f29])).

fof(f114,plain,(
    r2_hidden(sK3(sK0,sK0),sK0) ),
    inference(forward_demodulation,[],[f101,f97])).

fof(f101,plain,(
    r2_hidden(sK3(sK3(k2_tarski(sK0,sK0),k1_zfmisc_1(sK0)),sK0),sK3(k2_tarski(sK0,sK0),k1_zfmisc_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f71,f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:37:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (9658)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.50  % (9645)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (9650)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (9662)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.51  % (9642)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (9654)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (9637)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (9649)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (9645)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f114,f113])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    ~r2_hidden(sK3(sK0,sK0),sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f102,f97])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    sK0 = sK3(k2_tarski(sK0,sK0),k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f89])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    sK0 = sK3(k2_tarski(sK0,sK0),k1_zfmisc_1(sK0)) | sK0 = sK3(k2_tarski(sK0,sK0),k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(resolution,[],[f40,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,k2_tarski(X0,X1))) )),
% 0.22/0.52    inference(equality_resolution,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    r2_hidden(sK3(k2_tarski(sK0,sK0),k1_zfmisc_1(sK0)),k2_tarski(sK0,sK0))),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f30,f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ~r1_tarski(k2_tarski(sK0,sK0),k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(definition_unfolding,[],[f12,f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ~r1_tarski(k1_tarski(sK0),k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ? [X0] : ~r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,negated_conjecture,(
% 0.22/0.52    ~! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 0.22/0.52    inference(negated_conjecture,[],[f8])).
% 0.22/0.52  fof(f8,conjecture,(
% 0.22/0.52    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    ~r2_hidden(sK3(sK3(k2_tarski(sK0,sK0),k1_zfmisc_1(sK0)),sK0),sK0)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f71,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ~r1_tarski(sK3(k2_tarski(sK0,sK0),k1_zfmisc_1(sK0)),sK0)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f41,f34])).
% 0.22/0.52  % (9648)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(equality_resolution,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ~r2_hidden(sK3(k2_tarski(sK0,sK0),k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f30,f29])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    r2_hidden(sK3(sK0,sK0),sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f101,f97])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    r2_hidden(sK3(sK3(k2_tarski(sK0,sK0),k1_zfmisc_1(sK0)),sK0),sK3(k2_tarski(sK0,sK0),k1_zfmisc_1(sK0)))),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f71,f28])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (9645)------------------------------
% 0.22/0.52  % (9645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (9645)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (9645)Memory used [KB]: 10746
% 0.22/0.52  % (9645)Time elapsed: 0.106 s
% 0.22/0.52  % (9645)------------------------------
% 0.22/0.52  % (9645)------------------------------
% 0.22/0.52  % (9647)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (9635)Success in time 0.16 s
%------------------------------------------------------------------------------
