%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  57 expanded)
%              Number of leaves         :    3 (  13 expanded)
%              Depth                    :   11
%              Number of atoms          :   60 ( 141 expanded)
%              Number of equality atoms :   25 (  62 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f339,plain,(
    $false ),
    inference(subsumption_resolution,[],[f330,f323])).

fof(f323,plain,(
    r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f7,f322])).

fof(f322,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(subsumption_resolution,[],[f316,f20])).

fof(f20,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f8])).

fof(f8,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f316,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X0))
      | r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f313])).

fof(f313,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X0))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_tarski(X0))
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(superposition,[],[f12,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( sK3(k1_tarski(X0),X1,k1_tarski(X0)) = X0
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(resolution,[],[f37,f18])).

fof(f18,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f9])).

fof(f9,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f330,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f329,f20])).

fof(f329,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_tarski(sK0))
      | ~ r2_hidden(X4,sK1) ) ),
    inference(superposition,[],[f22,f324])).

fof(f324,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(subsumption_resolution,[],[f6,f323])).

fof(f6,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (9860)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.46  % (9852)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (9843)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.49  % (9851)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  % (9850)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.49  % (9858)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (9858)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f339,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f330,f323])).
% 0.20/0.50  fof(f323,plain,(
% 0.20/0.50    r2_hidden(sK0,sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f7,f322])).
% 0.20/0.50  fof(f322,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f316,f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 0.20/0.50    inference(equality_resolution,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 0.20/0.50    inference(equality_resolution,[],[f8])).
% 0.20/0.50  fof(f8,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.50  fof(f316,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k1_tarski(X0)) | r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f313])).
% 0.20/0.50  fof(f313,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k1_tarski(X0)) | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_tarski(X0)) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.50    inference(superposition,[],[f12,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sK3(k1_tarski(X0),X1,k1_tarski(X0)) = X0 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.50    inference(resolution,[],[f37,f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 0.20/0.50    inference(equality_resolution,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 0.20/0.50    inference(factoring,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f7,plain,(
% 0.20/0.50    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,plain,(
% 0.20/0.50    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <~> ~r2_hidden(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.20/0.50    inference(negated_conjecture,[],[f3])).
% 0.20/0.50  fof(f3,conjecture,(
% 0.20/0.50    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 0.20/0.50  fof(f330,plain,(
% 0.20/0.50    ~r2_hidden(sK0,sK1)),
% 0.20/0.50    inference(resolution,[],[f329,f20])).
% 0.20/0.50  fof(f329,plain,(
% 0.20/0.50    ( ! [X4] : (~r2_hidden(X4,k1_tarski(sK0)) | ~r2_hidden(X4,sK1)) )),
% 0.20/0.50    inference(superposition,[],[f22,f324])).
% 0.20/0.50  fof(f324,plain,(
% 0.20/0.50    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f6,f323])).
% 0.20/0.50  fof(f6,plain,(
% 0.20/0.50    ~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (9858)------------------------------
% 0.20/0.50  % (9858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (9858)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (9858)Memory used [KB]: 1791
% 0.20/0.50  % (9858)Time elapsed: 0.096 s
% 0.20/0.50  % (9858)------------------------------
% 0.20/0.50  % (9858)------------------------------
% 0.20/0.50  % (9838)Success in time 0.143 s
%------------------------------------------------------------------------------
