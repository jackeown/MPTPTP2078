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
% DateTime   : Thu Dec  3 12:46:00 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   32 (  47 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :   10
%              Number of atoms          :   50 (  72 expanded)
%              Number of equality atoms :   41 (  55 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f93,plain,(
    $false ),
    inference(subsumption_resolution,[],[f22,f92])).

fof(f92,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(forward_demodulation,[],[f91,f23])).

fof(f23,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f91,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,k1_setfam_1(k1_tarski(X1))) ),
    inference(subsumption_resolution,[],[f79,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f36,f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 != k3_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(resolution,[],[f29,f34])).

fof(f34,plain,(
    ! [X1] : ~ r1_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,k1_setfam_1(k1_tarski(X1)))
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(superposition,[],[f72,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1)) = k3_xboole_0(X0,k1_setfam_1(X1))
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f66,f37])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1)) = k3_xboole_0(X0,k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(superposition,[],[f30,f23])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f22,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f20])).

fof(f20,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))
   => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:36:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.48  % (28845)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.48  % (28836)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.48  % (28836)Refutation not found, incomplete strategy% (28836)------------------------------
% 0.19/0.48  % (28836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (28836)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.48  
% 0.19/0.48  % (28836)Memory used [KB]: 1663
% 0.19/0.48  % (28836)Time elapsed: 0.092 s
% 0.19/0.48  % (28836)------------------------------
% 0.19/0.48  % (28836)------------------------------
% 0.19/0.49  % (28846)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.49  % (28843)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.50  % (28845)Refutation not found, incomplete strategy% (28845)------------------------------
% 0.19/0.50  % (28845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (28845)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (28845)Memory used [KB]: 10618
% 0.19/0.50  % (28845)Time elapsed: 0.096 s
% 0.19/0.50  % (28845)------------------------------
% 0.19/0.50  % (28845)------------------------------
% 0.19/0.50  % (28847)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.50  % (28859)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.50  % (28847)Refutation not found, incomplete strategy% (28847)------------------------------
% 0.19/0.50  % (28847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (28846)Refutation not found, incomplete strategy% (28846)------------------------------
% 0.19/0.50  % (28846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (28846)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (28846)Memory used [KB]: 10618
% 0.19/0.50  % (28846)Time elapsed: 0.092 s
% 0.19/0.50  % (28846)------------------------------
% 0.19/0.50  % (28846)------------------------------
% 0.19/0.50  % (28838)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.50  % (28851)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.50  % (28838)Refutation not found, incomplete strategy% (28838)------------------------------
% 0.19/0.50  % (28838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (28838)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (28838)Memory used [KB]: 10618
% 0.19/0.50  % (28838)Time elapsed: 0.095 s
% 0.19/0.50  % (28838)------------------------------
% 0.19/0.50  % (28838)------------------------------
% 0.19/0.50  % (28851)Refutation not found, incomplete strategy% (28851)------------------------------
% 0.19/0.50  % (28851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (28851)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (28851)Memory used [KB]: 6140
% 0.19/0.50  % (28851)Time elapsed: 0.001 s
% 0.19/0.50  % (28851)------------------------------
% 0.19/0.50  % (28851)------------------------------
% 0.19/0.50  % (28843)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f93,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(subsumption_resolution,[],[f22,f92])).
% 0.19/0.50  fof(f92,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.19/0.50    inference(forward_demodulation,[],[f91,f23])).
% 0.19/0.50  fof(f23,plain,(
% 0.19/0.50    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f11])).
% 0.19/0.50  fof(f11,axiom,(
% 0.19/0.50    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.19/0.50  fof(f91,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,k1_setfam_1(k1_tarski(X1)))) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f79,f37])).
% 0.19/0.50  fof(f37,plain,(
% 0.19/0.50    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) )),
% 0.19/0.50    inference(superposition,[],[f36,f25])).
% 0.19/0.50  fof(f25,plain,(
% 0.19/0.50    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f14])).
% 0.19/0.50  fof(f14,plain,(
% 0.19/0.50    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.19/0.50    inference(rectify,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.19/0.50  fof(f36,plain,(
% 0.19/0.50    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 0.19/0.50    inference(resolution,[],[f29,f34])).
% 0.19/0.50  fof(f34,plain,(
% 0.19/0.50    ( ! [X1] : (~r1_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.19/0.50    inference(equality_resolution,[],[f31])).
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f19])).
% 0.19/0.50  fof(f19,plain,(
% 0.19/0.50    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.19/0.50    inference(ennf_transformation,[],[f9])).
% 0.19/0.50  fof(f9,axiom,(
% 0.19/0.50    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 0.19/0.50  fof(f29,plain,(
% 0.19/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f17])).
% 0.19/0.50  fof(f17,plain,(
% 0.19/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 0.19/0.50    inference(ennf_transformation,[],[f15])).
% 0.19/0.50  fof(f15,plain,(
% 0.19/0.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 => r1_xboole_0(X0,X1))),
% 0.19/0.50    inference(unused_predicate_definition_removal,[],[f1])).
% 0.19/0.50  fof(f1,axiom,(
% 0.19/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.19/0.50  fof(f79,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,k1_setfam_1(k1_tarski(X1))) | k1_xboole_0 = k1_tarski(X1)) )),
% 0.19/0.50    inference(superposition,[],[f72,f28])).
% 0.19/0.50  fof(f28,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.19/0.50  fof(f72,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1)) = k3_xboole_0(X0,k1_setfam_1(X1)) | k1_xboole_0 = X1) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f66,f37])).
% 0.19/0.50  fof(f66,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1)) = k3_xboole_0(X0,k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = k1_tarski(X0)) )),
% 0.19/0.50    inference(superposition,[],[f30,f23])).
% 0.19/0.50  fof(f30,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f18])).
% 0.19/0.50  fof(f18,plain,(
% 0.19/0.50    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.19/0.50    inference(ennf_transformation,[],[f10])).
% 0.19/0.50  fof(f10,axiom,(
% 0.19/0.50    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).
% 0.19/0.50  fof(f22,plain,(
% 0.19/0.50    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.19/0.50    inference(cnf_transformation,[],[f21])).
% 0.19/0.50  fof(f21,plain,(
% 0.19/0.50    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f20])).
% 0.19/0.50  fof(f20,plain,(
% 0.19/0.50    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f16,plain,(
% 0.19/0.50    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 0.19/0.50    inference(ennf_transformation,[],[f13])).
% 0.19/0.50  fof(f13,negated_conjecture,(
% 0.19/0.50    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.19/0.50    inference(negated_conjecture,[],[f12])).
% 0.19/0.50  fof(f12,conjecture,(
% 0.19/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.19/0.50  % SZS output end Proof for theBenchmark
% 0.19/0.50  % (28843)------------------------------
% 0.19/0.50  % (28843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (28843)Termination reason: Refutation
% 0.19/0.50  
% 0.19/0.50  % (28843)Memory used [KB]: 6268
% 0.19/0.50  % (28843)Time elapsed: 0.111 s
% 0.19/0.50  % (28843)------------------------------
% 0.19/0.50  % (28843)------------------------------
% 0.19/0.50  % (28864)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.50  % (28865)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.50  % (28835)Success in time 0.153 s
%------------------------------------------------------------------------------
