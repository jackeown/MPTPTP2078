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
% DateTime   : Thu Dec  3 12:41:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  94 expanded)
%              Number of leaves         :    9 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :   62 ( 146 expanded)
%              Number of equality atoms :   52 ( 136 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f34,f31,f32,f33,f59,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k1_enumset1(X1,X1,X2))
      | k1_enumset1(X1,X1,X1) = X0
      | k1_enumset1(X2,X2,X2) = X0
      | k1_enumset1(X1,X1,X2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f24,f30,f30,f21,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f17,f21])).

fof(f17,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_tarski(X1,X2) = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(superposition,[],[f47,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f23,f29,f22])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f20,f21])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0))) ),
    inference(superposition,[],[f35,f36])).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f19,f21,f21])).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f18,f29])).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f33,plain,(
    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) != k1_enumset1(sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f14,f22,f21,f30])).

fof(f14,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_zfmisc_1)).

fof(f32,plain,(
    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) != k1_enumset1(sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f15,f22,f21,f30])).

fof(f15,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f31,plain,(
    k1_enumset1(sK0,sK0,sK1) != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f16,f21,f22,f21])).

fof(f16,plain,(
    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    k1_xboole_0 != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f13,f22,f21])).

fof(f13,plain,(
    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:24:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (1907)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (1907)Refutation not found, incomplete strategy% (1907)------------------------------
% 0.21/0.51  % (1907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1914)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (1908)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (1905)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (1906)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (1910)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (1929)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (1905)Refutation not found, incomplete strategy% (1905)------------------------------
% 0.21/0.51  % (1905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1905)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (1905)Memory used [KB]: 10618
% 0.21/0.51  % (1905)Time elapsed: 0.109 s
% 0.21/0.51  % (1905)------------------------------
% 0.21/0.51  % (1905)------------------------------
% 0.21/0.51  % (1925)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (1907)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (1907)Memory used [KB]: 6140
% 0.21/0.52  % (1904)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (1919)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (1924)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (1909)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (1927)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (1930)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (1914)Refutation not found, incomplete strategy% (1914)------------------------------
% 0.21/0.52  % (1914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1911)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (1914)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1914)Memory used [KB]: 10746
% 0.21/0.52  % (1914)Time elapsed: 0.103 s
% 0.21/0.52  % (1914)------------------------------
% 0.21/0.52  % (1914)------------------------------
% 0.21/0.52  % (1927)Refutation not found, incomplete strategy% (1927)------------------------------
% 0.21/0.52  % (1927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1927)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1927)Memory used [KB]: 10618
% 0.21/0.52  % (1927)Time elapsed: 0.116 s
% 0.21/0.52  % (1927)------------------------------
% 0.21/0.52  % (1927)------------------------------
% 0.21/0.52  % (1930)Refutation not found, incomplete strategy% (1930)------------------------------
% 0.21/0.52  % (1930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1930)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1930)Memory used [KB]: 6268
% 0.21/0.52  % (1930)Time elapsed: 0.110 s
% 0.21/0.52  % (1930)------------------------------
% 0.21/0.52  % (1930)------------------------------
% 0.21/0.52  % (1911)Refutation not found, incomplete strategy% (1911)------------------------------
% 0.21/0.52  % (1911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1911)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1911)Memory used [KB]: 10618
% 0.21/0.52  % (1911)Time elapsed: 0.123 s
% 0.21/0.52  % (1911)------------------------------
% 0.21/0.52  % (1911)------------------------------
% 0.21/0.52  % (1935)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (1907)Time elapsed: 0.105 s
% 0.21/0.52  % (1907)------------------------------
% 0.21/0.52  % (1907)------------------------------
% 0.21/0.52  % (1903)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (1934)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (1929)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f34,f31,f32,f33,f59,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,k1_enumset1(X1,X1,X2)) | k1_enumset1(X1,X1,X1) = X0 | k1_enumset1(X2,X2,X2) = X0 | k1_enumset1(X1,X1,X2) = X0 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f24,f30,f30,f21,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f17,f21])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | k1_tarski(X2) = X0 | k2_tarski(X1,X2) = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.21/0.52    inference(superposition,[],[f47,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f23,f29,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f20,f21])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0)))) )),
% 0.21/0.52    inference(superposition,[],[f35,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f19,f21,f21])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f18,f29])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) != k1_enumset1(sK0,sK0,sK0)),
% 0.21/0.52    inference(definition_unfolding,[],[f14,f22,f21,f30])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : ~(k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 0.21/0.52    inference(negated_conjecture,[],[f9])).
% 0.21/0.52  fof(f9,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : ~(k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_tarski(X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_zfmisc_1)).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) != k1_enumset1(sK1,sK1,sK1)),
% 0.21/0.52    inference(definition_unfolding,[],[f15,f22,f21,f30])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    k1_enumset1(sK0,sK0,sK1) != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2))),
% 0.21/0.52    inference(definition_unfolding,[],[f16,f21,f22,f21])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    k1_xboole_0 != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2))),
% 0.21/0.52    inference(definition_unfolding,[],[f13,f22,f21])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (1929)------------------------------
% 0.21/0.52  % (1929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1929)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (1929)Memory used [KB]: 6268
% 0.21/0.52  % (1929)Time elapsed: 0.123 s
% 0.21/0.52  % (1929)------------------------------
% 0.21/0.52  % (1929)------------------------------
% 0.21/0.52  % (1928)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (1902)Success in time 0.16 s
%------------------------------------------------------------------------------
