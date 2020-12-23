%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:07 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   55 (  96 expanded)
%              Number of leaves         :   11 (  23 expanded)
%              Depth                    :   15
%              Number of atoms          :  107 ( 204 expanded)
%              Number of equality atoms :   40 (  73 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(subsumption_resolution,[],[f80,f65])).

fof(f65,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f64])).

fof(f64,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f19,f63])).

fof(f63,plain,(
    k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f61])).

fof(f61,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(resolution,[],[f59,f20])).

fof(f20,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f59,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(sK1))
      | k1_xboole_0 = k11_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f58,f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k11_relat_1(sK1,X1))
      | r2_hidden(X1,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f56,f42])).

fof(f42,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,X0),sK1)
      | ~ r2_hidden(X0,k11_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f35,f21])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f19,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | k1_xboole_0 != k11_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f80,plain,(
    ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f79,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X1,X0),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(superposition,[],[f37,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

% (28333)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f79,plain,(
    r1_xboole_0(k2_tarski(sK0,sK0),k1_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f76])).

% (28335)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f76,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_tarski(sK0,sK0),k1_relat_1(sK1)) ),
    inference(superposition,[],[f48,f70])).

fof(f70,plain,(
    k1_xboole_0 = k1_setfam_1(k2_tarski(k1_relat_1(sK1),k2_tarski(sK0,sK0))) ),
    inference(resolution,[],[f68,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f30,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f68,plain,(
    r1_xboole_0(k1_relat_1(sK1),k2_tarski(sK0,sK0)) ),
    inference(trivial_inequality_removal,[],[f67])).

fof(f67,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),k2_tarski(sK0,sK0)) ),
    inference(superposition,[],[f54,f63])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 != k11_relat_1(sK1,X0)
      | r1_xboole_0(k1_relat_1(sK1),k2_tarski(X0,X0)) ) ),
    inference(subsumption_resolution,[],[f53,f21])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 != k11_relat_1(sK1,X0)
      | r1_xboole_0(k1_relat_1(sK1),k2_tarski(X0,X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f28,f52])).

fof(f52,plain,(
    ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k2_tarski(X0,X0)) ),
    inference(resolution,[],[f38,f21])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_tarski(X1,X1)) ) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_setfam_1(k2_tarski(X1,X0))
      | r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f40,f25])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f26])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : run_vampire %s %d
% 0.08/0.28  % Computer   : n003.cluster.edu
% 0.08/0.28  % Model      : x86_64 x86_64
% 0.08/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.28  % Memory     : 8042.1875MB
% 0.08/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.28  % CPULimit   : 60
% 0.08/0.28  % WCLimit    : 600
% 0.08/0.28  % DateTime   : Tue Dec  1 09:28:12 EST 2020
% 0.08/0.28  % CPUTime    : 
% 0.13/0.36  % (28334)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.13/0.37  % (28331)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.13/0.38  % (28331)Refutation found. Thanks to Tanya!
% 0.13/0.38  % SZS status Theorem for theBenchmark
% 0.13/0.38  % (28325)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.13/0.38  % (28334)Refutation not found, incomplete strategy% (28334)------------------------------
% 0.13/0.38  % (28334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.38  % (28334)Termination reason: Refutation not found, incomplete strategy
% 0.13/0.38  
% 0.13/0.38  % (28334)Memory used [KB]: 10618
% 0.13/0.38  % (28334)Time elapsed: 0.067 s
% 0.13/0.38  % (28334)------------------------------
% 0.13/0.38  % (28334)------------------------------
% 0.13/0.38  % (28328)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.13/0.38  % (28348)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.13/0.39  % (28339)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.13/0.39  % SZS output start Proof for theBenchmark
% 0.13/0.39  fof(f83,plain,(
% 0.13/0.39    $false),
% 0.13/0.39    inference(subsumption_resolution,[],[f80,f65])).
% 0.13/0.39  fof(f65,plain,(
% 0.13/0.39    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.13/0.39    inference(trivial_inequality_removal,[],[f64])).
% 0.13/0.39  fof(f64,plain,(
% 0.13/0.39    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.13/0.39    inference(backward_demodulation,[],[f19,f63])).
% 0.13/0.39  fof(f63,plain,(
% 0.13/0.39    k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.13/0.39    inference(duplicate_literal_removal,[],[f61])).
% 0.13/0.39  fof(f61,plain,(
% 0.13/0.39    k1_xboole_0 = k11_relat_1(sK1,sK0) | k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.13/0.39    inference(resolution,[],[f59,f20])).
% 0.13/0.39  fof(f20,plain,(
% 0.13/0.39    ~r2_hidden(sK0,k1_relat_1(sK1)) | k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.13/0.39    inference(cnf_transformation,[],[f13])).
% 0.13/0.39  fof(f13,plain,(
% 0.13/0.39    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.13/0.39    inference(ennf_transformation,[],[f12])).
% 0.13/0.39  fof(f12,negated_conjecture,(
% 0.13/0.39    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.13/0.39    inference(negated_conjecture,[],[f11])).
% 0.13/0.39  fof(f11,conjecture,(
% 0.13/0.39    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.13/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 0.13/0.39  fof(f59,plain,(
% 0.13/0.39    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK1)) | k1_xboole_0 = k11_relat_1(sK1,X0)) )),
% 0.13/0.39    inference(resolution,[],[f58,f24])).
% 0.13/0.39  fof(f24,plain,(
% 0.13/0.39    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.13/0.39    inference(cnf_transformation,[],[f15])).
% 0.13/0.39  fof(f15,plain,(
% 0.13/0.39    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.13/0.39    inference(ennf_transformation,[],[f2])).
% 0.13/0.39  fof(f2,axiom,(
% 0.13/0.39    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.13/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.13/0.39  fof(f58,plain,(
% 0.13/0.39    ( ! [X0,X1] : (~r2_hidden(X0,k11_relat_1(sK1,X1)) | r2_hidden(X1,k1_relat_1(sK1))) )),
% 0.13/0.39    inference(resolution,[],[f56,f42])).
% 0.13/0.39  fof(f42,plain,(
% 0.13/0.39    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 0.13/0.39    inference(equality_resolution,[],[f31])).
% 0.13/0.39  fof(f31,plain,(
% 0.13/0.39    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.13/0.39    inference(cnf_transformation,[],[f8])).
% 0.13/0.39  fof(f8,axiom,(
% 0.13/0.39    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.13/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.13/0.39  fof(f56,plain,(
% 0.13/0.39    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,X0),sK1) | ~r2_hidden(X0,k11_relat_1(sK1,X1))) )),
% 0.13/0.39    inference(resolution,[],[f35,f21])).
% 0.13/0.39  fof(f21,plain,(
% 0.13/0.39    v1_relat_1(sK1)),
% 0.13/0.39    inference(cnf_transformation,[],[f13])).
% 0.13/0.39  fof(f35,plain,(
% 0.13/0.39    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.13/0.39    inference(cnf_transformation,[],[f17])).
% 0.13/0.39  fof(f17,plain,(
% 0.13/0.39    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.13/0.39    inference(ennf_transformation,[],[f10])).
% 0.13/0.39  fof(f10,axiom,(
% 0.13/0.39    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.13/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 0.13/0.39  fof(f19,plain,(
% 0.13/0.39    r2_hidden(sK0,k1_relat_1(sK1)) | k1_xboole_0 != k11_relat_1(sK1,sK0)),
% 0.13/0.39    inference(cnf_transformation,[],[f13])).
% 0.13/0.39  fof(f80,plain,(
% 0.13/0.39    ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.13/0.39    inference(resolution,[],[f79,f44])).
% 0.13/0.39  fof(f44,plain,(
% 0.13/0.39    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X1,X0),X2) | ~r2_hidden(X0,X2)) )),
% 0.13/0.39    inference(superposition,[],[f37,f25])).
% 0.13/0.39  fof(f25,plain,(
% 0.13/0.39    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.13/0.39    inference(cnf_transformation,[],[f3])).
% 0.13/0.39  fof(f3,axiom,(
% 0.13/0.39    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.13/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.13/0.39  fof(f37,plain,(
% 0.13/0.39    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.13/0.39    inference(cnf_transformation,[],[f18])).
% 0.13/0.39  fof(f18,plain,(
% 0.13/0.39    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.13/0.39    inference(ennf_transformation,[],[f5])).
% 0.13/0.39  % (28333)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.13/0.39  fof(f5,axiom,(
% 0.13/0.39    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.13/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.13/0.39  fof(f79,plain,(
% 0.13/0.39    r1_xboole_0(k2_tarski(sK0,sK0),k1_relat_1(sK1))),
% 0.13/0.39    inference(trivial_inequality_removal,[],[f76])).
% 0.13/0.39  % (28335)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.13/0.39  fof(f76,plain,(
% 0.13/0.39    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_tarski(sK0,sK0),k1_relat_1(sK1))),
% 0.13/0.39    inference(superposition,[],[f48,f70])).
% 0.13/0.39  fof(f70,plain,(
% 0.13/0.39    k1_xboole_0 = k1_setfam_1(k2_tarski(k1_relat_1(sK1),k2_tarski(sK0,sK0)))),
% 0.13/0.39    inference(resolution,[],[f68,f39])).
% 0.13/0.39  fof(f39,plain,(
% 0.13/0.39    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.13/0.39    inference(definition_unfolding,[],[f30,f26])).
% 0.13/0.39  fof(f26,plain,(
% 0.13/0.39    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.13/0.39    inference(cnf_transformation,[],[f6])).
% 0.13/0.39  fof(f6,axiom,(
% 0.13/0.39    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.13/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.13/0.39  fof(f30,plain,(
% 0.13/0.39    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.13/0.39    inference(cnf_transformation,[],[f1])).
% 0.13/0.39  fof(f1,axiom,(
% 0.13/0.39    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.13/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.13/0.39  fof(f68,plain,(
% 0.13/0.39    r1_xboole_0(k1_relat_1(sK1),k2_tarski(sK0,sK0))),
% 0.13/0.39    inference(trivial_inequality_removal,[],[f67])).
% 0.13/0.39  fof(f67,plain,(
% 0.13/0.39    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK1),k2_tarski(sK0,sK0))),
% 0.13/0.39    inference(superposition,[],[f54,f63])).
% 0.13/0.39  fof(f54,plain,(
% 0.13/0.39    ( ! [X0] : (k1_xboole_0 != k11_relat_1(sK1,X0) | r1_xboole_0(k1_relat_1(sK1),k2_tarski(X0,X0))) )),
% 0.13/0.39    inference(subsumption_resolution,[],[f53,f21])).
% 0.13/0.39  fof(f53,plain,(
% 0.13/0.39    ( ! [X0] : (k1_xboole_0 != k11_relat_1(sK1,X0) | r1_xboole_0(k1_relat_1(sK1),k2_tarski(X0,X0)) | ~v1_relat_1(sK1)) )),
% 0.13/0.39    inference(superposition,[],[f28,f52])).
% 0.13/0.39  fof(f52,plain,(
% 0.13/0.39    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k2_tarski(X0,X0))) )),
% 0.13/0.39    inference(resolution,[],[f38,f21])).
% 0.13/0.39  fof(f38,plain,(
% 0.13/0.39    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_tarski(X1,X1))) )),
% 0.13/0.39    inference(definition_unfolding,[],[f23,f22])).
% 0.13/0.39  fof(f22,plain,(
% 0.13/0.39    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.13/0.39    inference(cnf_transformation,[],[f4])).
% 0.13/0.39  fof(f4,axiom,(
% 0.13/0.39    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.13/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.13/0.39  fof(f23,plain,(
% 0.13/0.39    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.13/0.39    inference(cnf_transformation,[],[f14])).
% 0.13/0.39  fof(f14,plain,(
% 0.13/0.39    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.13/0.39    inference(ennf_transformation,[],[f7])).
% 0.13/0.39  fof(f7,axiom,(
% 0.13/0.39    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.13/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 0.13/0.39  fof(f28,plain,(
% 0.13/0.39    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.13/0.39    inference(cnf_transformation,[],[f16])).
% 0.13/0.39  fof(f16,plain,(
% 0.13/0.39    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.13/0.39    inference(ennf_transformation,[],[f9])).
% 0.13/0.39  fof(f9,axiom,(
% 0.13/0.39    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.13/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 0.13/0.39  fof(f48,plain,(
% 0.13/0.39    ( ! [X0,X1] : (k1_xboole_0 != k1_setfam_1(k2_tarski(X1,X0)) | r1_xboole_0(X0,X1)) )),
% 0.13/0.39    inference(superposition,[],[f40,f25])).
% 0.13/0.39  fof(f40,plain,(
% 0.13/0.39    ( ! [X0,X1] : (k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.13/0.39    inference(definition_unfolding,[],[f29,f26])).
% 0.13/0.39  fof(f29,plain,(
% 0.13/0.39    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.13/0.39    inference(cnf_transformation,[],[f1])).
% 0.13/0.39  % SZS output end Proof for theBenchmark
% 0.13/0.39  % (28331)------------------------------
% 0.13/0.39  % (28331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.39  % (28331)Termination reason: Refutation
% 0.13/0.39  
% 0.13/0.39  % (28331)Memory used [KB]: 6268
% 0.13/0.39  % (28331)Time elapsed: 0.066 s
% 0.13/0.39  % (28331)------------------------------
% 0.13/0.39  % (28331)------------------------------
% 0.13/0.39  % (28322)Success in time 0.099 s
%------------------------------------------------------------------------------
