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
% DateTime   : Thu Dec  3 12:40:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 208 expanded)
%              Number of leaves         :   14 (  66 expanded)
%              Depth                    :   15
%              Number of atoms          :   99 ( 297 expanded)
%              Number of equality atoms :   60 ( 241 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f905,plain,(
    $false ),
    inference(resolution,[],[f833,f76])).

fof(f76,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
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

fof(f833,plain,(
    ! [X0] : ~ r1_tarski(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f832,f39])).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f832,plain,(
    ! [X0] : ~ r1_tarski(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f743,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f743,plain,(
    ! [X0] : ~ r1_tarski(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f78,f741])).

fof(f741,plain,(
    k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f740,f129])).

fof(f129,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f60,f128])).

fof(f128,plain,(
    sK0 = k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f127,f39])).

fof(f127,plain,(
    k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f119,f40])).

fof(f119,plain,(
    k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f58,f60])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f51,f49,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f60,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f24,f49,f56])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f740,plain,(
    sK0 = k5_xboole_0(sK0,sK0) ),
    inference(forward_demodulation,[],[f731,f128])).

fof(f731,plain,(
    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(backward_demodulation,[],[f205,f714])).

fof(f714,plain,(
    sK1 = sK3(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f179,f73])).

fof(f73,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f35,f56])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f179,plain,(
    r2_hidden(sK3(k2_enumset1(sK1,sK1,sK1,sK1),sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f152,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f152,plain,(
    ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f59,f116,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f116,plain,(
    r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f60,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f28,f49])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f59,plain,(
    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f26,f56])).

fof(f26,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f205,plain,(
    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK3(k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK3(k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK3(k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK3(k2_enumset1(sK1,sK1,sK1,sK1),sK0)))) ),
    inference(unit_resulting_resolution,[],[f180,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = X0 ) ),
    inference(definition_unfolding,[],[f32,f49,f56])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f180,plain,(
    ~ r2_hidden(sK3(k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f152,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    ! [X0] : ~ r1_tarski(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK0))) ),
    inference(unit_resulting_resolution,[],[f25,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f29,f49])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f25,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:25:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (753)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (751)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.49  % (752)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (767)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.50  % (782)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.50  % (779)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.50  % (759)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (760)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (760)Refutation not found, incomplete strategy% (760)------------------------------
% 0.21/0.51  % (760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (760)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (760)Memory used [KB]: 10618
% 0.21/0.51  % (760)Time elapsed: 0.104 s
% 0.21/0.51  % (760)------------------------------
% 0.21/0.51  % (760)------------------------------
% 0.21/0.51  % (748)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (748)Refutation not found, incomplete strategy% (748)------------------------------
% 0.21/0.51  % (748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (748)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (748)Memory used [KB]: 1663
% 0.21/0.51  % (748)Time elapsed: 0.107 s
% 0.21/0.51  % (748)------------------------------
% 0.21/0.51  % (748)------------------------------
% 0.21/0.51  % (755)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (757)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (754)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (764)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (753)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (766)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (780)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (766)Refutation not found, incomplete strategy% (766)------------------------------
% 0.21/0.52  % (766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (766)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (766)Memory used [KB]: 10618
% 0.21/0.52  % (766)Time elapsed: 0.125 s
% 0.21/0.52  % (766)------------------------------
% 0.21/0.52  % (766)------------------------------
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f905,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(resolution,[],[f833,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f833,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f832,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.52  fof(f832,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f743,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.52  fof(f743,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))) )),
% 0.21/0.52    inference(backward_demodulation,[],[f78,f741])).
% 0.21/0.52  fof(f741,plain,(
% 0.21/0.52    k1_xboole_0 = sK0),
% 0.21/0.52    inference(forward_demodulation,[],[f740,f129])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    k1_xboole_0 = k5_xboole_0(sK0,sK0)),
% 0.21/0.52    inference(backward_demodulation,[],[f60,f128])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    sK0 = k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.52    inference(forward_demodulation,[],[f127,f39])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) = k5_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.52    inference(forward_demodulation,[],[f119,f40])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k1_xboole_0))),
% 0.21/0.52    inference(superposition,[],[f58,f60])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f51,f49,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.21/0.52    inference(definition_unfolding,[],[f24,f49,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f38,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f47,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,axiom,(
% 0.21/0.52    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.21/0.52    inference(negated_conjecture,[],[f19])).
% 0.21/0.52  fof(f19,conjecture,(
% 0.21/0.52    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 0.21/0.52  fof(f740,plain,(
% 0.21/0.52    sK0 = k5_xboole_0(sK0,sK0)),
% 0.21/0.52    inference(forward_demodulation,[],[f731,f128])).
% 0.21/0.52  fof(f731,plain,(
% 0.21/0.52    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.21/0.52    inference(backward_demodulation,[],[f205,f714])).
% 0.21/0.52  fof(f714,plain,(
% 0.21/0.52    sK1 = sK3(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f179,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X2,X0] : (~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) | X0 = X2) )),
% 0.21/0.52    inference(equality_resolution,[],[f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.21/0.52    inference(definition_unfolding,[],[f35,f56])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    r2_hidden(sK3(k2_enumset1(sK1,sK1,sK1,sK1),sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f152,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    ~r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f59,f116,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f60,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f28,f49])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    sK0 != k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.21/0.52    inference(definition_unfolding,[],[f26,f56])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    sK0 != k1_tarski(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f205,plain,(
% 0.21/0.52    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK3(k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK3(k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK3(k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK3(k2_enumset1(sK1,sK1,sK1,sK1),sK0))))),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f180,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X1,X0) | k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f32,f49,f56])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,axiom,(
% 0.21/0.52    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    ~r2_hidden(sK3(k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f152,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK0)))) )),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f25,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f29,f49])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    k1_xboole_0 != sK0),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (753)------------------------------
% 0.21/0.52  % (753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (753)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (753)Memory used [KB]: 6524
% 0.21/0.52  % (753)Time elapsed: 0.101 s
% 0.21/0.52  % (753)------------------------------
% 0.21/0.52  % (753)------------------------------
% 0.21/0.52  % (762)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (747)Success in time 0.167 s
%------------------------------------------------------------------------------
