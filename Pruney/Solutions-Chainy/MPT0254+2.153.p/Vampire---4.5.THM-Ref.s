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
% DateTime   : Thu Dec  3 12:39:33 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   22 (  22 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    8
%              Number of atoms          :   32 (  32 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(resolution,[],[f26,f19])).

% (27947)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
fof(f19,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f17,f13])).

fof(f13,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f26,plain,(
    ! [X1] : r2_hidden(sK0,X1) ),
    inference(subsumption_resolution,[],[f24,f12])).

fof(f12,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f24,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | r2_hidden(sK0,X1) ) ),
    inference(superposition,[],[f16,f21])).

fof(f21,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(trivial_inequality_removal,[],[f20])).

fof(f20,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(superposition,[],[f14,f11])).

fof(f11,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k2_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = k1_xboole_0
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:36:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.40  % (27946)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.12/0.40  % (27948)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.12/0.41  % (27946)Refutation found. Thanks to Tanya!
% 0.12/0.41  % SZS status Theorem for theBenchmark
% 0.12/0.41  % SZS output start Proof for theBenchmark
% 0.12/0.41  fof(f27,plain,(
% 0.12/0.41    $false),
% 0.12/0.41    inference(resolution,[],[f26,f19])).
% 0.12/0.41  % (27947)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.12/0.41  fof(f19,plain,(
% 0.12/0.41    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.12/0.41    inference(resolution,[],[f17,f13])).
% 0.12/0.41  fof(f13,plain,(
% 0.12/0.41    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.12/0.41    inference(cnf_transformation,[],[f3])).
% 0.12/0.41  fof(f3,axiom,(
% 0.12/0.41    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.12/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.12/0.41  fof(f17,plain,(
% 0.12/0.41    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.12/0.41    inference(cnf_transformation,[],[f10])).
% 0.12/0.41  fof(f10,plain,(
% 0.12/0.41    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.12/0.41    inference(ennf_transformation,[],[f5])).
% 0.12/0.41  fof(f5,axiom,(
% 0.12/0.41    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.12/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.12/0.41  fof(f26,plain,(
% 0.12/0.41    ( ! [X1] : (r2_hidden(sK0,X1)) )),
% 0.12/0.41    inference(subsumption_resolution,[],[f24,f12])).
% 0.12/0.41  fof(f12,plain,(
% 0.12/0.41    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.12/0.41    inference(cnf_transformation,[],[f2])).
% 0.12/0.41  fof(f2,axiom,(
% 0.12/0.41    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.12/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.12/0.41  fof(f24,plain,(
% 0.12/0.41    ( ! [X1] : (~r1_tarski(k1_xboole_0,X1) | r2_hidden(sK0,X1)) )),
% 0.12/0.41    inference(superposition,[],[f16,f21])).
% 0.12/0.41  fof(f21,plain,(
% 0.12/0.41    k1_xboole_0 = k1_tarski(sK0)),
% 0.12/0.41    inference(trivial_inequality_removal,[],[f20])).
% 0.12/0.41  fof(f20,plain,(
% 0.12/0.41    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_tarski(sK0)),
% 0.12/0.41    inference(superposition,[],[f14,f11])).
% 0.12/0.41  fof(f11,plain,(
% 0.12/0.41    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.12/0.41    inference(cnf_transformation,[],[f8])).
% 0.12/0.41  fof(f8,plain,(
% 0.12/0.41    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 0.12/0.41    inference(ennf_transformation,[],[f7])).
% 0.12/0.41  fof(f7,negated_conjecture,(
% 0.12/0.41    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.12/0.41    inference(negated_conjecture,[],[f6])).
% 0.12/0.41  fof(f6,conjecture,(
% 0.12/0.41    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.12/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.12/0.41  fof(f14,plain,(
% 0.12/0.41    ( ! [X0,X1] : (k2_xboole_0(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0) )),
% 0.12/0.41    inference(cnf_transformation,[],[f9])).
% 0.12/0.41  fof(f9,plain,(
% 0.12/0.41    ! [X0,X1] : (k1_xboole_0 = X0 | k2_xboole_0(X0,X1) != k1_xboole_0)),
% 0.12/0.41    inference(ennf_transformation,[],[f1])).
% 0.12/0.41  fof(f1,axiom,(
% 0.12/0.41    ! [X0,X1] : (k2_xboole_0(X0,X1) = k1_xboole_0 => k1_xboole_0 = X0)),
% 0.12/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).
% 0.12/0.41  fof(f16,plain,(
% 0.12/0.41    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.12/0.41    inference(cnf_transformation,[],[f4])).
% 0.12/0.41  fof(f4,axiom,(
% 0.12/0.41    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.12/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.12/0.41  % SZS output end Proof for theBenchmark
% 0.12/0.41  % (27946)------------------------------
% 0.12/0.41  % (27946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.41  % (27946)Termination reason: Refutation
% 0.12/0.41  
% 0.12/0.41  % (27946)Memory used [KB]: 10490
% 0.12/0.41  % (27946)Time elapsed: 0.004 s
% 0.12/0.41  % (27946)------------------------------
% 0.12/0.41  % (27946)------------------------------
% 0.19/0.41  % (27940)Success in time 0.062 s
%------------------------------------------------------------------------------
