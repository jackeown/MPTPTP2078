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
% DateTime   : Thu Dec  3 12:38:10 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 423 expanded)
%              Number of leaves         :   11 ( 119 expanded)
%              Depth                    :   18
%              Number of atoms          :  116 ( 856 expanded)
%              Number of equality atoms :   59 ( 597 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f712,plain,(
    $false ),
    inference(resolution,[],[f702,f77])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f702,plain,(
    ~ r1_tarski(sK1,sK1) ),
    inference(superposition,[],[f684,f474])).

fof(f474,plain,(
    sK1 = k2_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f36,f435,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f435,plain,(
    r1_tarski(k2_xboole_0(sK1,sK2),sK1) ),
    inference(forward_demodulation,[],[f429,f59])).

fof(f59,plain,(
    k2_xboole_0(sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f28,f58])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f429,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(backward_demodulation,[],[f165,f419])).

fof(f419,plain,(
    sK0 = sK3(sK1) ),
    inference(unit_resulting_resolution,[],[f162,f187])).

fof(f187,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_xboole_0(sK1,sK2))
      | sK0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_xboole_0(sK1,sK2))
      | sK0 = X1
      | sK0 = X1
      | sK0 = X1 ) ),
    inference(superposition,[],[f76,f59])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f44,f56])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f162,plain,(
    ! [X0] : r2_hidden(sK3(sK1),k2_xboole_0(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f36,f97,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f97,plain,(
    r2_hidden(sK3(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f30,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f30,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f165,plain,(
    r1_tarski(k2_enumset1(sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f97,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f58])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f684,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(X0,sK2),sK1) ),
    inference(superposition,[],[f676,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f676,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(sK2,X0),sK1) ),
    inference(unit_resulting_resolution,[],[f506,f562,f48])).

fof(f562,plain,(
    ! [X0] : r2_hidden(sK5(sK2,sK1),k2_xboole_0(sK2,X0)) ),
    inference(unit_resulting_resolution,[],[f36,f505,f48])).

fof(f505,plain,(
    r2_hidden(sK5(sK2,sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f502,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f502,plain,(
    ~ r1_tarski(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f29,f497,f54])).

fof(f497,plain,(
    r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f446,f474])).

fof(f446,plain,(
    r1_tarski(k2_xboole_0(sK1,sK2),sK2) ),
    inference(forward_demodulation,[],[f440,f59])).

fof(f440,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK2) ),
    inference(backward_demodulation,[],[f169,f418])).

fof(f418,plain,(
    sK0 = sK3(sK2) ),
    inference(unit_resulting_resolution,[],[f180,f187])).

fof(f180,plain,(
    ! [X0] : r2_hidden(sK3(sK2),k2_xboole_0(X0,sK2)) ),
    inference(superposition,[],[f166,f35])).

fof(f166,plain,(
    ! [X0] : r2_hidden(sK3(sK2),k2_xboole_0(sK2,X0)) ),
    inference(unit_resulting_resolution,[],[f36,f125,f48])).

fof(f125,plain,(
    r2_hidden(sK3(sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f31,f32])).

fof(f31,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f24])).

fof(f169,plain,(
    r1_tarski(k2_enumset1(sK3(sK2),sK3(sK2),sK3(sK2),sK3(sK2)),sK2) ),
    inference(unit_resulting_resolution,[],[f125,f61])).

fof(f29,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f24])).

fof(f506,plain,(
    ~ r2_hidden(sK5(sK2,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f502,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:18:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.50  % (915)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (931)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.51  % (923)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (915)Refutation not found, incomplete strategy% (915)------------------------------
% 0.22/0.52  % (915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (915)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (915)Memory used [KB]: 10618
% 0.22/0.52  % (915)Time elapsed: 0.102 s
% 0.22/0.52  % (915)------------------------------
% 0.22/0.52  % (915)------------------------------
% 0.22/0.52  % (927)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (911)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (904)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (919)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (909)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (905)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (918)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (925)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (908)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (907)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (913)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (914)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (916)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (914)Refutation not found, incomplete strategy% (914)------------------------------
% 0.22/0.54  % (914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (914)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (914)Memory used [KB]: 10618
% 0.22/0.54  % (914)Time elapsed: 0.131 s
% 0.22/0.54  % (914)------------------------------
% 0.22/0.54  % (914)------------------------------
% 0.22/0.54  % (933)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (926)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (912)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (906)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (910)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (930)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (917)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.51/0.55  % (920)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.51/0.55  % (932)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.51/0.55  % (922)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.51/0.55  % (929)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.51/0.56  % (924)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.51/0.56  % (921)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.51/0.56  % (928)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.60/0.57  % (908)Refutation found. Thanks to Tanya!
% 1.60/0.57  % SZS status Theorem for theBenchmark
% 1.60/0.57  % SZS output start Proof for theBenchmark
% 1.60/0.57  fof(f712,plain,(
% 1.60/0.57    $false),
% 1.60/0.57    inference(resolution,[],[f702,f77])).
% 1.60/0.57  fof(f77,plain,(
% 1.60/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.60/0.57    inference(equality_resolution,[],[f53])).
% 1.60/0.57  fof(f53,plain,(
% 1.60/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.60/0.57    inference(cnf_transformation,[],[f4])).
% 1.60/0.57  fof(f4,axiom,(
% 1.60/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.60/0.57  fof(f702,plain,(
% 1.60/0.57    ~r1_tarski(sK1,sK1)),
% 1.60/0.57    inference(superposition,[],[f684,f474])).
% 1.60/0.57  fof(f474,plain,(
% 1.60/0.57    sK1 = k2_xboole_0(sK1,sK2)),
% 1.60/0.57    inference(unit_resulting_resolution,[],[f36,f435,f54])).
% 1.60/0.57  fof(f54,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.60/0.57    inference(cnf_transformation,[],[f4])).
% 1.60/0.57  fof(f435,plain,(
% 1.60/0.57    r1_tarski(k2_xboole_0(sK1,sK2),sK1)),
% 1.60/0.57    inference(forward_demodulation,[],[f429,f59])).
% 1.60/0.57  fof(f59,plain,(
% 1.60/0.57    k2_xboole_0(sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.60/0.57    inference(definition_unfolding,[],[f28,f58])).
% 1.60/0.57  fof(f58,plain,(
% 1.60/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.60/0.57    inference(definition_unfolding,[],[f39,f57])).
% 1.60/0.57  fof(f57,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.60/0.57    inference(definition_unfolding,[],[f55,f56])).
% 1.60/0.57  fof(f56,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f15])).
% 1.60/0.57  fof(f15,axiom,(
% 1.60/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.60/0.57  fof(f55,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f14])).
% 1.60/0.57  fof(f14,axiom,(
% 1.60/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.60/0.57  fof(f39,plain,(
% 1.60/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f13])).
% 1.60/0.57  fof(f13,axiom,(
% 1.60/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.60/0.57  fof(f28,plain,(
% 1.60/0.57    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.60/0.57    inference(cnf_transformation,[],[f24])).
% 1.60/0.57  fof(f24,plain,(
% 1.60/0.57    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.60/0.57    inference(ennf_transformation,[],[f23])).
% 1.60/0.57  fof(f23,negated_conjecture,(
% 1.60/0.57    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.60/0.57    inference(negated_conjecture,[],[f22])).
% 1.60/0.57  fof(f22,conjecture,(
% 1.60/0.57    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 1.60/0.57  fof(f429,plain,(
% 1.60/0.57    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.60/0.57    inference(backward_demodulation,[],[f165,f419])).
% 1.60/0.57  fof(f419,plain,(
% 1.60/0.57    sK0 = sK3(sK1)),
% 1.60/0.57    inference(unit_resulting_resolution,[],[f162,f187])).
% 1.60/0.57  fof(f187,plain,(
% 1.60/0.57    ( ! [X1] : (~r2_hidden(X1,k2_xboole_0(sK1,sK2)) | sK0 = X1) )),
% 1.60/0.57    inference(duplicate_literal_removal,[],[f183])).
% 1.60/0.57  fof(f183,plain,(
% 1.60/0.57    ( ! [X1] : (~r2_hidden(X1,k2_xboole_0(sK1,sK2)) | sK0 = X1 | sK0 = X1 | sK0 = X1) )),
% 1.60/0.57    inference(superposition,[],[f76,f59])).
% 1.60/0.57  fof(f76,plain,(
% 1.60/0.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 1.60/0.57    inference(equality_resolution,[],[f65])).
% 1.60/0.57  fof(f65,plain,(
% 1.60/0.57    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.60/0.57    inference(definition_unfolding,[],[f44,f56])).
% 1.60/0.57  fof(f44,plain,(
% 1.60/0.57    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.60/0.57    inference(cnf_transformation,[],[f26])).
% 1.60/0.57  fof(f26,plain,(
% 1.60/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.60/0.57    inference(ennf_transformation,[],[f12])).
% 1.60/0.57  fof(f12,axiom,(
% 1.60/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.60/0.57  fof(f162,plain,(
% 1.60/0.57    ( ! [X0] : (r2_hidden(sK3(sK1),k2_xboole_0(sK1,X0))) )),
% 1.60/0.57    inference(unit_resulting_resolution,[],[f36,f97,f48])).
% 1.60/0.57  fof(f48,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f27])).
% 1.60/0.57  fof(f27,plain,(
% 1.60/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.60/0.57    inference(ennf_transformation,[],[f2])).
% 1.60/0.57  fof(f2,axiom,(
% 1.60/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.60/0.57  fof(f97,plain,(
% 1.60/0.57    r2_hidden(sK3(sK1),sK1)),
% 1.60/0.57    inference(unit_resulting_resolution,[],[f30,f32])).
% 1.60/0.57  fof(f32,plain,(
% 1.60/0.57    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.60/0.57    inference(cnf_transformation,[],[f25])).
% 1.60/0.57  fof(f25,plain,(
% 1.60/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.60/0.57    inference(ennf_transformation,[],[f3])).
% 1.60/0.57  fof(f3,axiom,(
% 1.60/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.60/0.57  fof(f30,plain,(
% 1.60/0.57    k1_xboole_0 != sK1),
% 1.60/0.57    inference(cnf_transformation,[],[f24])).
% 1.60/0.57  fof(f165,plain,(
% 1.60/0.57    r1_tarski(k2_enumset1(sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1)),sK1)),
% 1.60/0.57    inference(unit_resulting_resolution,[],[f97,f61])).
% 1.60/0.57  fof(f61,plain,(
% 1.60/0.57    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.60/0.57    inference(definition_unfolding,[],[f37,f58])).
% 1.60/0.57  fof(f37,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f20])).
% 1.60/0.57  fof(f20,axiom,(
% 1.60/0.57    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.60/0.57  fof(f36,plain,(
% 1.60/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f8])).
% 1.60/0.57  fof(f8,axiom,(
% 1.60/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.60/0.57  fof(f684,plain,(
% 1.60/0.57    ( ! [X0] : (~r1_tarski(k2_xboole_0(X0,sK2),sK1)) )),
% 1.60/0.57    inference(superposition,[],[f676,f35])).
% 1.60/0.57  fof(f35,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f1])).
% 1.60/0.57  fof(f1,axiom,(
% 1.60/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.60/0.57  fof(f676,plain,(
% 1.60/0.57    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK2,X0),sK1)) )),
% 1.60/0.57    inference(unit_resulting_resolution,[],[f506,f562,f48])).
% 1.60/0.57  fof(f562,plain,(
% 1.60/0.57    ( ! [X0] : (r2_hidden(sK5(sK2,sK1),k2_xboole_0(sK2,X0))) )),
% 1.60/0.57    inference(unit_resulting_resolution,[],[f36,f505,f48])).
% 1.60/0.57  fof(f505,plain,(
% 1.60/0.57    r2_hidden(sK5(sK2,sK1),sK2)),
% 1.60/0.57    inference(unit_resulting_resolution,[],[f502,f49])).
% 1.60/0.57  fof(f49,plain,(
% 1.60/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f27])).
% 1.60/0.57  fof(f502,plain,(
% 1.60/0.57    ~r1_tarski(sK2,sK1)),
% 1.60/0.57    inference(unit_resulting_resolution,[],[f29,f497,f54])).
% 1.60/0.57  fof(f497,plain,(
% 1.60/0.57    r1_tarski(sK1,sK2)),
% 1.60/0.57    inference(backward_demodulation,[],[f446,f474])).
% 1.60/0.57  fof(f446,plain,(
% 1.60/0.57    r1_tarski(k2_xboole_0(sK1,sK2),sK2)),
% 1.60/0.57    inference(forward_demodulation,[],[f440,f59])).
% 1.60/0.57  fof(f440,plain,(
% 1.60/0.57    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK2)),
% 1.60/0.57    inference(backward_demodulation,[],[f169,f418])).
% 1.60/0.57  fof(f418,plain,(
% 1.60/0.57    sK0 = sK3(sK2)),
% 1.60/0.57    inference(unit_resulting_resolution,[],[f180,f187])).
% 1.60/0.57  fof(f180,plain,(
% 1.60/0.57    ( ! [X0] : (r2_hidden(sK3(sK2),k2_xboole_0(X0,sK2))) )),
% 1.60/0.57    inference(superposition,[],[f166,f35])).
% 1.60/0.57  fof(f166,plain,(
% 1.60/0.57    ( ! [X0] : (r2_hidden(sK3(sK2),k2_xboole_0(sK2,X0))) )),
% 1.60/0.57    inference(unit_resulting_resolution,[],[f36,f125,f48])).
% 1.60/0.57  fof(f125,plain,(
% 1.60/0.57    r2_hidden(sK3(sK2),sK2)),
% 1.60/0.57    inference(unit_resulting_resolution,[],[f31,f32])).
% 1.60/0.57  fof(f31,plain,(
% 1.60/0.57    k1_xboole_0 != sK2),
% 1.60/0.57    inference(cnf_transformation,[],[f24])).
% 1.60/0.57  fof(f169,plain,(
% 1.60/0.57    r1_tarski(k2_enumset1(sK3(sK2),sK3(sK2),sK3(sK2),sK3(sK2)),sK2)),
% 1.60/0.57    inference(unit_resulting_resolution,[],[f125,f61])).
% 1.60/0.57  fof(f29,plain,(
% 1.60/0.57    sK1 != sK2),
% 1.60/0.57    inference(cnf_transformation,[],[f24])).
% 1.60/0.57  fof(f506,plain,(
% 1.60/0.57    ~r2_hidden(sK5(sK2,sK1),sK1)),
% 1.60/0.57    inference(unit_resulting_resolution,[],[f502,f50])).
% 1.60/0.57  fof(f50,plain,(
% 1.60/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK5(X0,X1),X1)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f27])).
% 1.60/0.57  % SZS output end Proof for theBenchmark
% 1.60/0.57  % (908)------------------------------
% 1.60/0.57  % (908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.57  % (908)Termination reason: Refutation
% 1.60/0.57  
% 1.60/0.57  % (908)Memory used [KB]: 6524
% 1.60/0.57  % (908)Time elapsed: 0.165 s
% 1.60/0.57  % (908)------------------------------
% 1.60/0.57  % (908)------------------------------
% 1.60/0.58  % (903)Success in time 0.225 s
%------------------------------------------------------------------------------
