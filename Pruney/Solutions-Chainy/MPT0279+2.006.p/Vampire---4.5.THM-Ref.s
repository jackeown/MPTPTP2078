%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   29 (  52 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 (  87 expanded)
%              Number of equality atoms :   16 (  26 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    $false ),
    inference(subsumption_resolution,[],[f59,f25])).

fof(f25,plain,(
    ~ r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_zfmisc_1(sK0)) ),
    inference(definition_unfolding,[],[f10,f24])).

fof(f24,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f11,f12])).

fof(f12,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f11,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f10,plain,(
    ~ r1_tarski(k1_tarski(sK0),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] : ~ r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

fof(f59,plain,(
    r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f57,f39])).

fof(f39,plain,(
    ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f38,f31])).

fof(f31,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f38,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f15,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK0))
    | r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f15,f54])).

fof(f54,plain,(
    sK0 = sK1(k1_enumset1(sK0,sK0,sK0),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f43,f25])).

fof(f43,plain,(
    ! [X2,X1] :
      ( r1_tarski(k1_enumset1(X1,X1,X1),X2)
      | sK1(k1_enumset1(X1,X1,X1),X2) = X1 ) ),
    inference(resolution,[],[f32,f14])).

fof(f32,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_enumset1(X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f21,f24])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:55:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (7820)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (7831)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (7820)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 1.39/0.56  % (7823)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.39/0.56  % SZS output start Proof for theBenchmark
% 1.39/0.56  fof(f60,plain,(
% 1.39/0.56    $false),
% 1.39/0.56    inference(subsumption_resolution,[],[f59,f25])).
% 1.39/0.56  fof(f25,plain,(
% 1.39/0.56    ~r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_zfmisc_1(sK0))),
% 1.39/0.56    inference(definition_unfolding,[],[f10,f24])).
% 1.39/0.56  fof(f24,plain,(
% 1.39/0.56    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.39/0.56    inference(definition_unfolding,[],[f11,f12])).
% 1.39/0.56  fof(f12,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f4])).
% 1.39/0.56  fof(f4,axiom,(
% 1.39/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.39/0.56  fof(f11,plain,(
% 1.39/0.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f3])).
% 1.39/0.56  fof(f3,axiom,(
% 1.39/0.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.39/0.56  fof(f10,plain,(
% 1.39/0.56    ~r1_tarski(k1_tarski(sK0),k1_zfmisc_1(sK0))),
% 1.39/0.56    inference(cnf_transformation,[],[f8])).
% 1.39/0.56  fof(f8,plain,(
% 1.39/0.56    ? [X0] : ~r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 1.39/0.56    inference(ennf_transformation,[],[f7])).
% 1.39/0.56  fof(f7,negated_conjecture,(
% 1.39/0.56    ~! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 1.39/0.56    inference(negated_conjecture,[],[f6])).
% 1.39/0.56  fof(f6,conjecture,(
% 1.39/0.56    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).
% 1.39/0.56  fof(f59,plain,(
% 1.39/0.56    r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_zfmisc_1(sK0))),
% 1.39/0.56    inference(subsumption_resolution,[],[f57,f39])).
% 1.39/0.56  fof(f39,plain,(
% 1.39/0.56    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(X0))) )),
% 1.39/0.56    inference(resolution,[],[f38,f31])).
% 1.39/0.56  fof(f31,plain,(
% 1.39/0.56    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 1.39/0.56    inference(equality_resolution,[],[f16])).
% 1.39/0.56  fof(f16,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.39/0.56    inference(cnf_transformation,[],[f5])).
% 1.39/0.56  fof(f5,axiom,(
% 1.39/0.56    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.39/0.56  fof(f38,plain,(
% 1.39/0.56    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.39/0.56    inference(duplicate_literal_removal,[],[f37])).
% 1.39/0.56  fof(f37,plain,(
% 1.39/0.56    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.39/0.56    inference(resolution,[],[f15,f14])).
% 1.39/0.56  fof(f14,plain,(
% 1.39/0.56    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f9])).
% 1.39/0.56  fof(f9,plain,(
% 1.39/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f1])).
% 1.39/0.56  fof(f1,axiom,(
% 1.39/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.39/0.56  fof(f15,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~r2_hidden(sK1(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f9])).
% 1.39/0.56  fof(f57,plain,(
% 1.39/0.56    ~r2_hidden(sK0,k1_zfmisc_1(sK0)) | r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_zfmisc_1(sK0))),
% 1.39/0.56    inference(superposition,[],[f15,f54])).
% 1.39/0.56  fof(f54,plain,(
% 1.39/0.56    sK0 = sK1(k1_enumset1(sK0,sK0,sK0),k1_zfmisc_1(sK0))),
% 1.39/0.56    inference(resolution,[],[f43,f25])).
% 1.39/0.56  fof(f43,plain,(
% 1.39/0.56    ( ! [X2,X1] : (r1_tarski(k1_enumset1(X1,X1,X1),X2) | sK1(k1_enumset1(X1,X1,X1),X2) = X1) )),
% 1.39/0.56    inference(resolution,[],[f32,f14])).
% 1.39/0.56  fof(f32,plain,(
% 1.39/0.56    ( ! [X2,X0] : (~r2_hidden(X2,k1_enumset1(X0,X0,X0)) | X0 = X2) )),
% 1.39/0.56    inference(equality_resolution,[],[f28])).
% 1.39/0.56  fof(f28,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 1.39/0.56    inference(definition_unfolding,[],[f21,f24])).
% 1.39/0.56  fof(f21,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.39/0.56    inference(cnf_transformation,[],[f2])).
% 1.39/0.56  fof(f2,axiom,(
% 1.39/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.39/0.56  % SZS output end Proof for theBenchmark
% 1.39/0.56  % (7820)------------------------------
% 1.39/0.56  % (7820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (7820)Termination reason: Refutation
% 1.39/0.56  
% 1.39/0.56  % (7820)Memory used [KB]: 6268
% 1.39/0.56  % (7820)Time elapsed: 0.126 s
% 1.39/0.56  % (7820)------------------------------
% 1.39/0.56  % (7820)------------------------------
% 1.39/0.56  % (7813)Success in time 0.196 s
%------------------------------------------------------------------------------
