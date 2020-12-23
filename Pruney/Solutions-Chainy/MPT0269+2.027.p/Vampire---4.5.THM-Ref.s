%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:50 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   35 (  63 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 ( 125 expanded)
%              Number of equality atoms :   31 (  81 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f219,plain,(
    $false ),
    inference(subsumption_resolution,[],[f217,f126])).

fof(f126,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f93,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f93,plain,(
    ~ r1_tarski(k2_tarski(sK1,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f36,f62,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f62,plain,(
    r1_tarski(sK0,k2_tarski(sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f37,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f37,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK1)) ),
    inference(definition_unfolding,[],[f16,f25])).

fof(f25,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f16,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f36,plain,(
    sK0 != k2_tarski(sK1,sK1) ),
    inference(definition_unfolding,[],[f18,f25])).

fof(f18,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f217,plain,(
    r2_hidden(sK1,sK0) ),
    inference(superposition,[],[f47,f191])).

fof(f191,plain,(
    sK1 = sK3(sK0) ),
    inference(unit_resulting_resolution,[],[f94,f42])).

fof(f42,plain,(
    ! [X2,X0] :
      ( X0 = X2
      | ~ r2_hidden(X2,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f22,f25])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f94,plain,(
    r2_hidden(sK3(sK0),k2_tarski(sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f47,f62,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f47,plain,(
    r2_hidden(sK3(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f17,f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f17,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:48:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (5948)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.49  % (5941)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.49  % (5949)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.49  % (5941)Refutation not found, incomplete strategy% (5941)------------------------------
% 0.22/0.49  % (5941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (5941)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (5941)Memory used [KB]: 10618
% 0.22/0.49  % (5941)Time elapsed: 0.083 s
% 0.22/0.49  % (5941)------------------------------
% 0.22/0.49  % (5941)------------------------------
% 0.22/0.49  % (5949)Refutation not found, incomplete strategy% (5949)------------------------------
% 0.22/0.49  % (5949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (5949)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (5949)Memory used [KB]: 10618
% 0.22/0.49  % (5949)Time elapsed: 0.085 s
% 0.22/0.49  % (5949)------------------------------
% 0.22/0.49  % (5949)------------------------------
% 0.22/0.50  % (5961)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.50  % (5957)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.18/0.51  % (5953)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.18/0.51  % (5948)Refutation found. Thanks to Tanya!
% 1.18/0.51  % SZS status Theorem for theBenchmark
% 1.18/0.51  % SZS output start Proof for theBenchmark
% 1.18/0.51  fof(f219,plain,(
% 1.18/0.51    $false),
% 1.18/0.51    inference(subsumption_resolution,[],[f217,f126])).
% 1.18/0.51  fof(f126,plain,(
% 1.18/0.51    ~r2_hidden(sK1,sK0)),
% 1.18/0.51    inference(duplicate_literal_removal,[],[f120])).
% 1.18/0.51  fof(f120,plain,(
% 1.18/0.51    ~r2_hidden(sK1,sK0) | ~r2_hidden(sK1,sK0)),
% 1.18/0.51    inference(resolution,[],[f93,f35])).
% 1.18/0.51  fof(f35,plain,(
% 1.18/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.18/0.51    inference(cnf_transformation,[],[f10])).
% 1.18/0.51  fof(f10,axiom,(
% 1.18/0.51    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.18/0.51  fof(f93,plain,(
% 1.18/0.51    ~r1_tarski(k2_tarski(sK1,sK1),sK0)),
% 1.18/0.51    inference(unit_resulting_resolution,[],[f36,f62,f32])).
% 1.18/0.51  fof(f32,plain,(
% 1.18/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.18/0.51    inference(cnf_transformation,[],[f3])).
% 1.18/0.51  fof(f3,axiom,(
% 1.18/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.18/0.51  fof(f62,plain,(
% 1.18/0.51    r1_tarski(sK0,k2_tarski(sK1,sK1))),
% 1.18/0.51    inference(unit_resulting_resolution,[],[f37,f20])).
% 1.18/0.51  fof(f20,plain,(
% 1.18/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 1.18/0.51    inference(cnf_transformation,[],[f4])).
% 1.18/0.51  fof(f4,axiom,(
% 1.18/0.51    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.18/0.51  fof(f37,plain,(
% 1.18/0.51    k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK1))),
% 1.18/0.51    inference(definition_unfolding,[],[f16,f25])).
% 1.18/0.51  fof(f25,plain,(
% 1.18/0.51    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.18/0.51    inference(cnf_transformation,[],[f7])).
% 1.18/0.51  fof(f7,axiom,(
% 1.18/0.51    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.18/0.51  fof(f16,plain,(
% 1.18/0.51    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.18/0.51    inference(cnf_transformation,[],[f13])).
% 1.18/0.51  fof(f13,plain,(
% 1.18/0.51    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.18/0.51    inference(ennf_transformation,[],[f12])).
% 1.18/0.51  fof(f12,negated_conjecture,(
% 1.18/0.51    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.18/0.51    inference(negated_conjecture,[],[f11])).
% 1.18/0.51  fof(f11,conjecture,(
% 1.18/0.51    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 1.18/0.51  fof(f36,plain,(
% 1.18/0.51    sK0 != k2_tarski(sK1,sK1)),
% 1.18/0.51    inference(definition_unfolding,[],[f18,f25])).
% 1.18/0.51  fof(f18,plain,(
% 1.18/0.51    sK0 != k1_tarski(sK1)),
% 1.18/0.51    inference(cnf_transformation,[],[f13])).
% 1.18/0.51  fof(f217,plain,(
% 1.18/0.51    r2_hidden(sK1,sK0)),
% 1.18/0.51    inference(superposition,[],[f47,f191])).
% 1.18/0.51  fof(f191,plain,(
% 1.18/0.51    sK1 = sK3(sK0)),
% 1.18/0.51    inference(unit_resulting_resolution,[],[f94,f42])).
% 1.18/0.51  fof(f42,plain,(
% 1.18/0.51    ( ! [X2,X0] : (X0 = X2 | ~r2_hidden(X2,k2_tarski(X0,X0))) )),
% 1.18/0.51    inference(equality_resolution,[],[f40])).
% 1.18/0.51  fof(f40,plain,(
% 1.18/0.51    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_tarski(X0,X0) != X1) )),
% 1.18/0.51    inference(definition_unfolding,[],[f22,f25])).
% 1.18/0.51  fof(f22,plain,(
% 1.18/0.51    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.18/0.51    inference(cnf_transformation,[],[f6])).
% 1.18/0.51  fof(f6,axiom,(
% 1.18/0.51    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.18/0.51  fof(f94,plain,(
% 1.18/0.51    r2_hidden(sK3(sK0),k2_tarski(sK1,sK1))),
% 1.18/0.51    inference(unit_resulting_resolution,[],[f47,f62,f27])).
% 1.18/0.51  fof(f27,plain,(
% 1.18/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.18/0.51    inference(cnf_transformation,[],[f15])).
% 1.18/0.51  fof(f15,plain,(
% 1.18/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.18/0.51    inference(ennf_transformation,[],[f1])).
% 1.18/0.51  fof(f1,axiom,(
% 1.18/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.18/0.51  fof(f47,plain,(
% 1.18/0.51    r2_hidden(sK3(sK0),sK0)),
% 1.18/0.51    inference(unit_resulting_resolution,[],[f17,f26])).
% 1.18/0.51  fof(f26,plain,(
% 1.18/0.51    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0)) )),
% 1.18/0.51    inference(cnf_transformation,[],[f14])).
% 1.18/0.51  fof(f14,plain,(
% 1.18/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.18/0.51    inference(ennf_transformation,[],[f2])).
% 1.18/0.51  fof(f2,axiom,(
% 1.18/0.51    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.18/0.51  fof(f17,plain,(
% 1.18/0.51    k1_xboole_0 != sK0),
% 1.18/0.51    inference(cnf_transformation,[],[f13])).
% 1.18/0.51  % SZS output end Proof for theBenchmark
% 1.18/0.51  % (5948)------------------------------
% 1.18/0.51  % (5948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.51  % (5948)Termination reason: Refutation
% 1.18/0.51  
% 1.18/0.51  % (5948)Memory used [KB]: 10746
% 1.18/0.51  % (5948)Time elapsed: 0.093 s
% 1.18/0.51  % (5948)------------------------------
% 1.18/0.51  % (5948)------------------------------
% 1.18/0.51  % (5938)Success in time 0.145 s
%------------------------------------------------------------------------------
