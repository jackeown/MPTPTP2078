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
% DateTime   : Thu Dec  3 12:49:34 EST 2020

% Result     : Theorem 1.17s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :   37 (  91 expanded)
%              Number of leaves         :    9 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   70 ( 175 expanded)
%              Number of equality atoms :   33 (  77 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f266,plain,(
    $false ),
    inference(subsumption_resolution,[],[f261,f76])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[],[f14,f69])).

fof(f69,plain,(
    ! [X4,X5] : k9_relat_1(k1_xboole_0,X5) = k9_relat_1(k1_xboole_0,X4) ),
    inference(resolution,[],[f53,f52])).

fof(f52,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) ),
    inference(subsumption_resolution,[],[f51,f17])).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))
      | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(sK2(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0))) ) ),
    inference(resolution,[],[f50,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_tarski(X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f26,f18])).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) ) ),
    inference(subsumption_resolution,[],[f49,f35])).

fof(f35,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f19,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

% (18880)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f19,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,k1_xboole_0),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) ) ),
    inference(superposition,[],[f27,f15])).

% (18889)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f15,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(k9_relat_1(k1_xboole_0,X0),X1),X1)
      | k9_relat_1(k1_xboole_0,X0) = X1 ) ),
    inference(resolution,[],[f52,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f14,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f261,plain,(
    ! [X1] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X1) ),
    inference(resolution,[],[f258,f52])).

fof(f258,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0,k1_xboole_0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(trivial_inequality_removal,[],[f255])).

fof(f255,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = X0
      | r2_hidden(sK1(X0,k1_xboole_0),X0) ) ),
    inference(superposition,[],[f40,f17])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,k2_tarski(sK1(X0,X1),sK1(X0,X1))) != X1
      | X0 = X1
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(resolution,[],[f20,f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:30:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (18890)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (18882)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (18890)Refutation not found, incomplete strategy% (18890)------------------------------
% 0.22/0.51  % (18890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (18874)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (18890)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (18890)Memory used [KB]: 10618
% 0.22/0.51  % (18890)Time elapsed: 0.058 s
% 0.22/0.51  % (18890)------------------------------
% 0.22/0.51  % (18890)------------------------------
% 0.22/0.51  % (18872)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (18871)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.17/0.52  % (18874)Refutation found. Thanks to Tanya!
% 1.17/0.52  % SZS status Theorem for theBenchmark
% 1.17/0.52  % SZS output start Proof for theBenchmark
% 1.17/0.52  fof(f266,plain,(
% 1.17/0.52    $false),
% 1.17/0.52    inference(subsumption_resolution,[],[f261,f76])).
% 1.17/0.52  fof(f76,plain,(
% 1.17/0.52    ( ! [X0] : (k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)) )),
% 1.17/0.52    inference(superposition,[],[f14,f69])).
% 1.17/0.52  fof(f69,plain,(
% 1.17/0.52    ( ! [X4,X5] : (k9_relat_1(k1_xboole_0,X5) = k9_relat_1(k1_xboole_0,X4)) )),
% 1.17/0.52    inference(resolution,[],[f53,f52])).
% 1.17/0.52  fof(f52,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))) )),
% 1.17/0.52    inference(subsumption_resolution,[],[f51,f17])).
% 1.17/0.52  fof(f17,plain,(
% 1.17/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f2])).
% 1.17/0.52  fof(f2,axiom,(
% 1.17/0.52    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.17/0.52  fof(f51,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(sK2(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)))) )),
% 1.17/0.52    inference(resolution,[],[f50,f31])).
% 1.17/0.52  fof(f31,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k2_tarski(X1,X1)) != X0) )),
% 1.17/0.52    inference(definition_unfolding,[],[f26,f18])).
% 1.17/0.52  fof(f18,plain,(
% 1.17/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f3])).
% 1.17/0.52  fof(f3,axiom,(
% 1.17/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.17/0.52  fof(f26,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.17/0.52    inference(cnf_transformation,[],[f5])).
% 1.17/0.52  fof(f5,axiom,(
% 1.17/0.52    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.17/0.52  fof(f50,plain,(
% 1.17/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,k1_xboole_0),k1_xboole_0) | ~r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))) )),
% 1.17/0.52    inference(subsumption_resolution,[],[f49,f35])).
% 1.17/0.52  fof(f35,plain,(
% 1.17/0.52    v1_relat_1(k1_xboole_0)),
% 1.17/0.52    inference(superposition,[],[f19,f33])).
% 1.17/0.52  fof(f33,plain,(
% 1.17/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.17/0.52    inference(equality_resolution,[],[f24])).
% 1.17/0.52  fof(f24,plain,(
% 1.17/0.52    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f4])).
% 1.17/0.52  % (18880)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.17/0.52  fof(f4,axiom,(
% 1.17/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.17/0.52  fof(f19,plain,(
% 1.17/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.17/0.52    inference(cnf_transformation,[],[f6])).
% 1.17/0.52  fof(f6,axiom,(
% 1.17/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.17/0.52  fof(f49,plain,(
% 1.17/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,k1_xboole_0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))) )),
% 1.17/0.52    inference(superposition,[],[f27,f15])).
% 1.17/0.52  % (18889)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.17/0.52  fof(f15,plain,(
% 1.17/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.17/0.52    inference(cnf_transformation,[],[f8])).
% 1.17/0.52  fof(f8,axiom,(
% 1.17/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.17/0.52  fof(f27,plain,(
% 1.17/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 1.17/0.52    inference(cnf_transformation,[],[f13])).
% 1.17/0.52  fof(f13,plain,(
% 1.17/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.17/0.52    inference(ennf_transformation,[],[f7])).
% 1.17/0.52  fof(f7,axiom,(
% 1.17/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 1.17/0.52  fof(f53,plain,(
% 1.17/0.52    ( ! [X0,X1] : (r2_hidden(sK1(k9_relat_1(k1_xboole_0,X0),X1),X1) | k9_relat_1(k1_xboole_0,X0) = X1) )),
% 1.17/0.52    inference(resolution,[],[f52,f20])).
% 1.17/0.52  fof(f20,plain,(
% 1.17/0.52    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X0 = X1) )),
% 1.17/0.52    inference(cnf_transformation,[],[f12])).
% 1.17/0.52  fof(f12,plain,(
% 1.17/0.52    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.17/0.52    inference(ennf_transformation,[],[f1])).
% 1.17/0.52  fof(f1,axiom,(
% 1.17/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 1.17/0.52  fof(f14,plain,(
% 1.17/0.52    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 1.17/0.52    inference(cnf_transformation,[],[f11])).
% 1.17/0.52  fof(f11,plain,(
% 1.17/0.52    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 1.17/0.52    inference(ennf_transformation,[],[f10])).
% 1.17/0.52  fof(f10,negated_conjecture,(
% 1.17/0.52    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 1.17/0.52    inference(negated_conjecture,[],[f9])).
% 1.17/0.52  fof(f9,conjecture,(
% 1.17/0.52    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 1.17/0.52  fof(f261,plain,(
% 1.17/0.52    ( ! [X1] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X1)) )),
% 1.17/0.52    inference(resolution,[],[f258,f52])).
% 1.17/0.52  fof(f258,plain,(
% 1.17/0.52    ( ! [X0] : (r2_hidden(sK1(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) )),
% 1.17/0.52    inference(trivial_inequality_removal,[],[f255])).
% 1.17/0.52  fof(f255,plain,(
% 1.17/0.52    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = X0 | r2_hidden(sK1(X0,k1_xboole_0),X0)) )),
% 1.17/0.52    inference(superposition,[],[f40,f17])).
% 1.17/0.52  fof(f40,plain,(
% 1.17/0.52    ( ! [X0,X1] : (k4_xboole_0(X1,k2_tarski(sK1(X0,X1),sK1(X0,X1))) != X1 | X0 = X1 | r2_hidden(sK1(X0,X1),X0)) )),
% 1.17/0.52    inference(resolution,[],[f20,f31])).
% 1.17/0.52  % SZS output end Proof for theBenchmark
% 1.17/0.52  % (18874)------------------------------
% 1.17/0.52  % (18874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.52  % (18874)Termination reason: Refutation
% 1.17/0.52  
% 1.17/0.52  % (18874)Memory used [KB]: 6396
% 1.17/0.52  % (18874)Time elapsed: 0.070 s
% 1.17/0.52  % (18874)------------------------------
% 1.17/0.52  % (18874)------------------------------
% 1.17/0.53  % (18866)Success in time 0.159 s
%------------------------------------------------------------------------------
