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
% DateTime   : Thu Dec  3 12:33:35 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 291 expanded)
%              Number of leaves         :    6 (  90 expanded)
%              Depth                    :   16
%              Number of atoms          :  108 ( 564 expanded)
%              Number of equality atoms :   55 ( 410 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f211,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f58,f33,f190])).

fof(f190,plain,
    ( ~ sP3(sK0,sK1,sK0,sK0)
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK1)) ),
    inference(forward_demodulation,[],[f187,f173])).

fof(f173,plain,(
    sK0 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f32,f57,f160])).

fof(f160,plain,
    ( sK0 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | ~ sP3(sK1,sK1,sK0,sK0) ),
    inference(superposition,[],[f74,f156])).

fof(f156,plain,
    ( sK1 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1))
    | sK0 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f154])).

fof(f154,plain,
    ( sK1 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1))
    | sK0 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1))
    | sK1 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1))
    | sK1 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1))
    | sK0 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)) ),
    inference(resolution,[],[f153,f18])).

fof(f18,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP3(X4,X2,X1,X0)
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f153,plain,
    ( sP3(sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)),sK1,sK1,sK0)
    | sK1 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1))
    | sK0 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)) ),
    inference(resolution,[],[f88,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_tarski(X0,X1))
      | sP3(X2,X1,X1,X0) ) ),
    inference(superposition,[],[f30,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f13,f12,f11,f11])).

fof(f11,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f12,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f13,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))
      | sP3(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP3(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) != X3 ) ),
    inference(definition_unfolding,[],[f20,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f14,f12,f11])).

fof(f14,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP3(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f88,plain,
    ( r2_hidden(sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    | sK0 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1))
    | sK1 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,
    ( r2_hidden(sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    | sK0 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1))
    | sK1 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1))
    | sK0 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)) ),
    inference(resolution,[],[f85,f18])).

fof(f85,plain,
    ( sP3(sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)),sK1,sK0,sK0)
    | r2_hidden(sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2] :
      ( k2_tarski(sK0,sK1) != X2
      | r2_hidden(sK2(sK0,sK0,sK1,X2),X2)
      | sP3(sK2(sK0,sK0,sK1,X2),sK1,sK0,sK0) ) ),
    inference(superposition,[],[f25,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) = X3
      | r2_hidden(sK2(X0,X1,X2,X3),X3)
      | sP3(sK2(X0,X1,X2,X3),X2,X1,X0) ) ),
    inference(definition_unfolding,[],[f21,f23])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(sK2(X0,X1,X2,X3),X2,X1,X0)
      | r2_hidden(sK2(X0,X1,X2,X3),X3)
      | k1_enumset1(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f25,plain,(
    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))) ),
    inference(definition_unfolding,[],[f10,f23])).

fof(f10,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f74,plain,
    ( ~ sP3(sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)),sK1,sK0,sK0)
    | ~ r2_hidden(sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2] :
      ( k2_tarski(sK0,sK1) != X2
      | ~ r2_hidden(sK2(sK0,sK0,sK1,X2),X2)
      | ~ sP3(sK2(sK0,sK0,sK1,X2),sK1,sK0,sK0) ) ),
    inference(superposition,[],[f25,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) = X3
      | ~ r2_hidden(sK2(X0,X1,X2,X3),X3)
      | ~ sP3(sK2(X0,X1,X2,X3),X2,X1,X0) ) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(sK2(X0,X1,X2,X3),X2,X1,X0)
      | ~ r2_hidden(sK2(X0,X1,X2,X3),X3)
      | k1_enumset1(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(unit_resulting_resolution,[],[f33,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X2,X1,X1,X0)
      | r2_hidden(X2,k2_tarski(X0,X1)) ) ),
    inference(superposition,[],[f31,f24])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))
      | ~ sP3(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP3(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) != X3 ) ),
    inference(definition_unfolding,[],[f19,f23])).

fof(f19,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP3(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X4,X0,X1] : sP3(X4,X4,X1,X0) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X4,X2,X0,X1] :
      ( X2 != X4
      | sP3(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f187,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ sP3(sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)),sK1,sK0,sK0) ),
    inference(backward_demodulation,[],[f74,f173])).

fof(f33,plain,(
    ! [X4,X2,X0] : sP3(X4,X2,X4,X0) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | sP3(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f34,f53])).

fof(f34,plain,(
    ! [X4,X2,X1] : sP3(X4,X2,X1,X4) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X4,X2,X0,X1] :
      ( X0 != X4
      | sP3(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.27/0.53  % (22358)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.27/0.53  % (22357)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.27/0.54  % (22366)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.27/0.54  % (22373)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.27/0.54  % (22356)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.27/0.55  % (22358)Refutation not found, incomplete strategy% (22358)------------------------------
% 1.27/0.55  % (22358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.55  % (22374)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.27/0.55  % (22358)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.55  
% 1.27/0.55  % (22358)Memory used [KB]: 10618
% 1.27/0.55  % (22358)Time elapsed: 0.115 s
% 1.27/0.55  % (22358)------------------------------
% 1.27/0.55  % (22358)------------------------------
% 1.27/0.55  % (22365)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.27/0.55  % (22365)Refutation not found, incomplete strategy% (22365)------------------------------
% 1.27/0.55  % (22365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.55  % (22365)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.55  
% 1.27/0.55  % (22365)Memory used [KB]: 6140
% 1.27/0.55  % (22365)Time elapsed: 0.124 s
% 1.27/0.55  % (22365)------------------------------
% 1.27/0.55  % (22365)------------------------------
% 1.49/0.55  % (22353)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.49/0.56  % (22352)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.49/0.56  % (22374)Refutation found. Thanks to Tanya!
% 1.49/0.56  % SZS status Theorem for theBenchmark
% 1.49/0.56  % (22372)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.49/0.56  % (22352)Refutation not found, incomplete strategy% (22352)------------------------------
% 1.49/0.56  % (22352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (22352)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (22352)Memory used [KB]: 10618
% 1.49/0.56  % (22352)Time elapsed: 0.137 s
% 1.49/0.56  % (22352)------------------------------
% 1.49/0.56  % (22352)------------------------------
% 1.49/0.56  % SZS output start Proof for theBenchmark
% 1.49/0.56  fof(f211,plain,(
% 1.49/0.56    $false),
% 1.49/0.56    inference(unit_resulting_resolution,[],[f58,f33,f190])).
% 1.49/0.56  fof(f190,plain,(
% 1.49/0.56    ~sP3(sK0,sK1,sK0,sK0) | ~r2_hidden(sK0,k2_tarski(sK0,sK1))),
% 1.49/0.56    inference(forward_demodulation,[],[f187,f173])).
% 1.49/0.56  fof(f173,plain,(
% 1.49/0.56    sK0 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1))),
% 1.49/0.56    inference(unit_resulting_resolution,[],[f32,f57,f160])).
% 1.49/0.56  fof(f160,plain,(
% 1.49/0.56    sK0 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)) | ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | ~sP3(sK1,sK1,sK0,sK0)),
% 1.49/0.56    inference(superposition,[],[f74,f156])).
% 1.49/0.56  fof(f156,plain,(
% 1.49/0.56    sK1 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)) | sK0 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1))),
% 1.49/0.56    inference(duplicate_literal_removal,[],[f154])).
% 1.49/0.56  fof(f154,plain,(
% 1.49/0.56    sK1 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)) | sK0 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)) | sK1 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)) | sK1 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)) | sK0 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1))),
% 1.49/0.56    inference(resolution,[],[f153,f18])).
% 1.49/0.56  fof(f18,plain,(
% 1.49/0.56    ( ! [X4,X2,X0,X1] : (~sP3(X4,X2,X1,X0) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 1.49/0.56    inference(cnf_transformation,[],[f9])).
% 1.49/0.56  fof(f9,plain,(
% 1.49/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.49/0.56    inference(ennf_transformation,[],[f2])).
% 1.49/0.56  fof(f2,axiom,(
% 1.49/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.49/0.56  fof(f153,plain,(
% 1.49/0.56    sP3(sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)),sK1,sK1,sK0) | sK1 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)) | sK0 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1))),
% 1.49/0.56    inference(resolution,[],[f88,f47])).
% 1.49/0.56  fof(f47,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_tarski(X0,X1)) | sP3(X2,X1,X1,X0)) )),
% 1.49/0.56    inference(superposition,[],[f30,f24])).
% 1.49/0.56  fof(f24,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0)))) )),
% 1.49/0.56    inference(definition_unfolding,[],[f13,f12,f11,f11])).
% 1.49/0.56  fof(f11,plain,(
% 1.49/0.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f5])).
% 1.49/0.56  fof(f5,axiom,(
% 1.49/0.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.49/0.56  fof(f12,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f1])).
% 1.49/0.56  fof(f1,axiom,(
% 1.49/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.49/0.56  fof(f13,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f3])).
% 1.49/0.56  fof(f3,axiom,(
% 1.49/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 1.49/0.56  fof(f30,plain,(
% 1.49/0.56    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) | sP3(X4,X2,X1,X0)) )),
% 1.49/0.56    inference(equality_resolution,[],[f28])).
% 1.49/0.56  fof(f28,plain,(
% 1.49/0.56    ( ! [X4,X2,X0,X3,X1] : (sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) != X3) )),
% 1.49/0.56    inference(definition_unfolding,[],[f20,f23])).
% 1.49/0.56  fof(f23,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) )),
% 1.49/0.56    inference(definition_unfolding,[],[f14,f12,f11])).
% 1.49/0.56  fof(f14,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f4])).
% 1.49/0.56  fof(f4,axiom,(
% 1.49/0.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 1.49/0.56  fof(f20,plain,(
% 1.49/0.56    ( ! [X4,X2,X0,X3,X1] : (sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.49/0.56    inference(cnf_transformation,[],[f9])).
% 1.49/0.56  fof(f88,plain,(
% 1.49/0.56    r2_hidden(sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) | sK0 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)) | sK1 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1))),
% 1.49/0.56    inference(duplicate_literal_removal,[],[f87])).
% 1.49/0.56  fof(f87,plain,(
% 1.49/0.56    r2_hidden(sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) | sK0 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)) | sK1 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)) | sK0 = sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1))),
% 1.49/0.56    inference(resolution,[],[f85,f18])).
% 1.49/0.56  fof(f85,plain,(
% 1.49/0.56    sP3(sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)),sK1,sK0,sK0) | r2_hidden(sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))),
% 1.49/0.56    inference(equality_resolution,[],[f80])).
% 1.49/0.56  fof(f80,plain,(
% 1.49/0.56    ( ! [X2] : (k2_tarski(sK0,sK1) != X2 | r2_hidden(sK2(sK0,sK0,sK1,X2),X2) | sP3(sK2(sK0,sK0,sK1,X2),sK1,sK0,sK0)) )),
% 1.49/0.56    inference(superposition,[],[f25,f27])).
% 1.49/0.56  fof(f27,plain,(
% 1.49/0.56    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) = X3 | r2_hidden(sK2(X0,X1,X2,X3),X3) | sP3(sK2(X0,X1,X2,X3),X2,X1,X0)) )),
% 1.49/0.56    inference(definition_unfolding,[],[f21,f23])).
% 1.49/0.56  fof(f21,plain,(
% 1.49/0.56    ( ! [X2,X0,X3,X1] : (sP3(sK2(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3),X3) | k1_enumset1(X0,X1,X2) = X3) )),
% 1.49/0.56    inference(cnf_transformation,[],[f9])).
% 1.49/0.56  fof(f25,plain,(
% 1.49/0.56    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)))),
% 1.49/0.56    inference(definition_unfolding,[],[f10,f23])).
% 1.49/0.56  fof(f10,plain,(
% 1.49/0.56    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 1.49/0.56    inference(cnf_transformation,[],[f8])).
% 1.49/0.56  fof(f8,plain,(
% 1.49/0.56    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 1.49/0.56    inference(ennf_transformation,[],[f7])).
% 1.49/0.56  fof(f7,negated_conjecture,(
% 1.49/0.56    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.49/0.56    inference(negated_conjecture,[],[f6])).
% 1.49/0.56  fof(f6,conjecture,(
% 1.49/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.49/0.56  fof(f74,plain,(
% 1.49/0.56    ~sP3(sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)),sK1,sK0,sK0) | ~r2_hidden(sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))),
% 1.49/0.56    inference(equality_resolution,[],[f68])).
% 1.49/0.56  fof(f68,plain,(
% 1.49/0.56    ( ! [X2] : (k2_tarski(sK0,sK1) != X2 | ~r2_hidden(sK2(sK0,sK0,sK1,X2),X2) | ~sP3(sK2(sK0,sK0,sK1,X2),sK1,sK0,sK0)) )),
% 1.49/0.56    inference(superposition,[],[f25,f26])).
% 1.49/0.56  fof(f26,plain,(
% 1.49/0.56    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) = X3 | ~r2_hidden(sK2(X0,X1,X2,X3),X3) | ~sP3(sK2(X0,X1,X2,X3),X2,X1,X0)) )),
% 1.49/0.56    inference(definition_unfolding,[],[f22,f23])).
% 1.49/0.56  fof(f22,plain,(
% 1.49/0.56    ( ! [X2,X0,X3,X1] : (~sP3(sK2(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3) | k1_enumset1(X0,X1,X2) = X3) )),
% 1.49/0.56    inference(cnf_transformation,[],[f9])).
% 1.49/0.56  fof(f57,plain,(
% 1.49/0.56    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X1,X0))) )),
% 1.49/0.56    inference(unit_resulting_resolution,[],[f33,f53])).
% 1.49/0.56  fof(f53,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (~sP3(X2,X1,X1,X0) | r2_hidden(X2,k2_tarski(X0,X1))) )),
% 1.49/0.56    inference(superposition,[],[f31,f24])).
% 1.49/0.56  fof(f31,plain,(
% 1.49/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) | ~sP3(X4,X2,X1,X0)) )),
% 1.49/0.56    inference(equality_resolution,[],[f29])).
% 1.49/0.56  fof(f29,plain,(
% 1.49/0.56    ( ! [X4,X2,X0,X3,X1] : (~sP3(X4,X2,X1,X0) | r2_hidden(X4,X3) | k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) != X3) )),
% 1.49/0.56    inference(definition_unfolding,[],[f19,f23])).
% 1.49/0.56  fof(f19,plain,(
% 1.49/0.56    ( ! [X4,X2,X0,X3,X1] : (~sP3(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.49/0.56    inference(cnf_transformation,[],[f9])).
% 1.49/0.56  fof(f32,plain,(
% 1.49/0.56    ( ! [X4,X0,X1] : (sP3(X4,X4,X1,X0)) )),
% 1.49/0.56    inference(equality_resolution,[],[f17])).
% 1.49/0.56  fof(f17,plain,(
% 1.49/0.56    ( ! [X4,X2,X0,X1] : (X2 != X4 | sP3(X4,X2,X1,X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f9])).
% 1.49/0.56  fof(f187,plain,(
% 1.49/0.56    ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | ~sP3(sK2(sK0,sK0,sK1,k2_tarski(sK0,sK1)),sK1,sK0,sK0)),
% 1.49/0.56    inference(backward_demodulation,[],[f74,f173])).
% 1.49/0.56  fof(f33,plain,(
% 1.49/0.56    ( ! [X4,X2,X0] : (sP3(X4,X2,X4,X0)) )),
% 1.49/0.56    inference(equality_resolution,[],[f16])).
% 1.49/0.56  fof(f16,plain,(
% 1.49/0.56    ( ! [X4,X2,X0,X1] : (X1 != X4 | sP3(X4,X2,X1,X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f9])).
% 1.49/0.56  fof(f58,plain,(
% 1.49/0.56    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 1.49/0.56    inference(unit_resulting_resolution,[],[f34,f53])).
% 1.49/0.56  fof(f34,plain,(
% 1.49/0.56    ( ! [X4,X2,X1] : (sP3(X4,X2,X1,X4)) )),
% 1.49/0.56    inference(equality_resolution,[],[f15])).
% 1.49/0.56  fof(f15,plain,(
% 1.49/0.56    ( ! [X4,X2,X0,X1] : (X0 != X4 | sP3(X4,X2,X1,X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f9])).
% 1.49/0.56  % SZS output end Proof for theBenchmark
% 1.49/0.56  % (22374)------------------------------
% 1.49/0.56  % (22374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (22374)Termination reason: Refutation
% 1.49/0.56  
% 1.49/0.56  % (22374)Memory used [KB]: 6268
% 1.49/0.56  % (22374)Time elapsed: 0.126 s
% 1.49/0.56  % (22374)------------------------------
% 1.49/0.56  % (22374)------------------------------
% 1.49/0.56  % (22349)Success in time 0.194 s
%------------------------------------------------------------------------------
