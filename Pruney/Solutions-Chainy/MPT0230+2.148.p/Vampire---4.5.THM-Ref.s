%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:54 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   22 (  28 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  54 expanded)
%              Number of equality atoms :   18 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,plain,(
    $false ),
    inference(subsumption_resolution,[],[f36,f21])).

fof(f21,plain,(
    ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK2)) ),
    inference(unit_resulting_resolution,[],[f12,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f12,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f36,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK2)) ),
    inference(backward_demodulation,[],[f26,f27])).

fof(f27,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f11,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f11,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f7])).

fof(f26,plain,(
    r1_tarski(k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)) ),
    inference(unit_resulting_resolution,[],[f18,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f18,plain,(
    r1_tarski(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(definition_unfolding,[],[f10,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f10,plain,(
    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:03:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.50  % (6146)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.23/0.53  % (6145)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.23/0.53  % (6170)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.23/0.53  % (6157)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.23/0.53  % (6154)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.23/0.53  % (6170)Refutation not found, incomplete strategy% (6170)------------------------------
% 0.23/0.53  % (6170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (6157)Refutation not found, incomplete strategy% (6157)------------------------------
% 0.23/0.53  % (6157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (6147)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.23/0.53  % (6157)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (6157)Memory used [KB]: 1663
% 0.23/0.53  % (6157)Time elapsed: 0.088 s
% 0.23/0.53  % (6157)------------------------------
% 0.23/0.53  % (6157)------------------------------
% 0.23/0.53  % (6170)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (6170)Memory used [KB]: 6140
% 0.23/0.53  % (6170)Time elapsed: 0.089 s
% 0.23/0.53  % (6170)------------------------------
% 0.23/0.53  % (6170)------------------------------
% 0.23/0.53  % (6148)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.53  % (6143)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.23/0.54  % (6162)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.23/0.54  % (6149)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.54  % (6162)Refutation found. Thanks to Tanya!
% 0.23/0.54  % SZS status Theorem for theBenchmark
% 0.23/0.54  % SZS output start Proof for theBenchmark
% 0.23/0.54  fof(f37,plain,(
% 0.23/0.54    $false),
% 0.23/0.54    inference(subsumption_resolution,[],[f36,f21])).
% 0.23/0.54  fof(f21,plain,(
% 0.23/0.54    ~r1_tarski(k1_tarski(sK0),k1_tarski(sK2))),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f12,f15])).
% 0.23/0.54  fof(f15,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.23/0.54    inference(cnf_transformation,[],[f8])).
% 0.23/0.54  fof(f8,plain,(
% 0.23/0.54    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.23/0.54    inference(ennf_transformation,[],[f4])).
% 0.23/0.54  fof(f4,axiom,(
% 0.23/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 0.23/0.54  fof(f12,plain,(
% 0.23/0.54    sK0 != sK2),
% 0.23/0.54    inference(cnf_transformation,[],[f7])).
% 0.23/0.54  fof(f7,plain,(
% 0.23/0.54    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.23/0.54    inference(ennf_transformation,[],[f6])).
% 0.23/0.54  fof(f6,negated_conjecture,(
% 0.23/0.54    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.23/0.54    inference(negated_conjecture,[],[f5])).
% 0.23/0.54  fof(f5,conjecture,(
% 0.23/0.54    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 0.23/0.54  fof(f36,plain,(
% 0.23/0.54    r1_tarski(k1_tarski(sK0),k1_tarski(sK2))),
% 0.23/0.54    inference(backward_demodulation,[],[f26,f27])).
% 0.23/0.54  fof(f27,plain,(
% 0.23/0.54    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f11,f13])).
% 0.23/0.54  fof(f13,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.23/0.54    inference(cnf_transformation,[],[f3])).
% 0.23/0.54  fof(f3,axiom,(
% 0.23/0.54    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.23/0.54  fof(f11,plain,(
% 0.23/0.54    sK0 != sK1),
% 0.23/0.54    inference(cnf_transformation,[],[f7])).
% 0.23/0.54  fof(f26,plain,(
% 0.23/0.54    r1_tarski(k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2))),
% 0.23/0.54    inference(unit_resulting_resolution,[],[f18,f17])).
% 0.23/0.54  fof(f17,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f9])).
% 0.23/0.54  fof(f9,plain,(
% 0.23/0.54    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.23/0.54    inference(ennf_transformation,[],[f1])).
% 0.23/0.54  fof(f1,axiom,(
% 0.23/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.23/0.54  fof(f18,plain,(
% 0.23/0.54    r1_tarski(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),
% 0.23/0.54    inference(definition_unfolding,[],[f10,f16])).
% 0.23/0.54  fof(f16,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f2])).
% 0.23/0.54  fof(f2,axiom,(
% 0.23/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.23/0.54  fof(f10,plain,(
% 0.23/0.54    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 0.23/0.54    inference(cnf_transformation,[],[f7])).
% 0.23/0.54  % SZS output end Proof for theBenchmark
% 0.23/0.54  % (6162)------------------------------
% 0.23/0.54  % (6162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (6162)Termination reason: Refutation
% 0.23/0.54  
% 0.23/0.54  % (6162)Memory used [KB]: 1663
% 0.23/0.54  % (6162)Time elapsed: 0.127 s
% 0.23/0.54  % (6162)------------------------------
% 0.23/0.54  % (6162)------------------------------
% 0.23/0.54  % (6142)Success in time 0.172 s
%------------------------------------------------------------------------------
