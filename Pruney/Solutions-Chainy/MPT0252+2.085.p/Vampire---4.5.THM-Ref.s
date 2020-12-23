%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:03 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 151 expanded)
%              Number of leaves         :   13 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  110 ( 228 expanded)
%              Number of equality atoms :   46 ( 143 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f126,plain,(
    $false ),
    inference(subsumption_resolution,[],[f123,f29])).

% (12623)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (12615)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (12628)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (12624)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f29,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

% (12622)Refutation not found, incomplete strategy% (12622)------------------------------
% (12622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12622)Termination reason: Refutation not found, incomplete strategy

% (12622)Memory used [KB]: 10618
% (12622)Time elapsed: 0.113 s
% (12622)------------------------------
% (12622)------------------------------
fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f123,plain,(
    r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f112,f120])).

fof(f120,plain,(
    r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(resolution,[],[f117,f101])).

fof(f101,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f79,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f42,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f79,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X1,X2)) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k6_enumset1(X4,X4,X4,X4,X4,X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f48,f59])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f117,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_tarski(k2_tarski(sK0,sK1),sK2))
      | r1_tarski(X1,sK2) ) ),
    inference(superposition,[],[f33,f114])).

fof(f114,plain,(
    sK2 = k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2)) ),
    inference(resolution,[],[f103,f97])).

fof(f97,plain,
    ( ~ r2_hidden(sK2,k2_tarski(k2_tarski(sK0,sK1),sK2))
    | sK2 = k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2)) ),
    inference(resolution,[],[f89,f62])).

fof(f62,plain,(
    r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f28,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),X1)
      | k3_tarski(X0) = X1
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f86,f33])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(resolution,[],[f34,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f103,plain,(
    ! [X4,X5] : r2_hidden(X5,k2_tarski(X4,X5)) ),
    inference(superposition,[],[f75,f60])).

fof(f75,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X4)) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f50,f59])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X2),X1)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f101,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:33:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.52  % (12617)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.53  % (12636)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.53  % (12625)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.23/0.53  % (12629)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.33/0.54  % (12620)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.33/0.54  % (12641)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.33/0.55  % (12622)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.33/0.55  % (12613)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.33/0.55  % (12620)Refutation found. Thanks to Tanya!
% 1.33/0.55  % SZS status Theorem for theBenchmark
% 1.33/0.55  % SZS output start Proof for theBenchmark
% 1.33/0.55  fof(f126,plain,(
% 1.33/0.55    $false),
% 1.33/0.55    inference(subsumption_resolution,[],[f123,f29])).
% 1.33/0.55  % (12623)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.33/0.55  % (12615)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.33/0.55  % (12628)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.33/0.55  % (12624)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.33/0.55  fof(f29,plain,(
% 1.33/0.55    ~r2_hidden(sK0,sK2)),
% 1.33/0.55    inference(cnf_transformation,[],[f21])).
% 1.33/0.55  % (12622)Refutation not found, incomplete strategy% (12622)------------------------------
% 1.33/0.55  % (12622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (12622)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (12622)Memory used [KB]: 10618
% 1.33/0.55  % (12622)Time elapsed: 0.113 s
% 1.33/0.55  % (12622)------------------------------
% 1.33/0.55  % (12622)------------------------------
% 1.33/0.55  fof(f21,plain,(
% 1.33/0.55    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 1.33/0.55    inference(ennf_transformation,[],[f19])).
% 1.33/0.55  fof(f19,negated_conjecture,(
% 1.33/0.55    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 1.33/0.55    inference(negated_conjecture,[],[f18])).
% 1.33/0.55  fof(f18,conjecture,(
% 1.33/0.55    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 1.33/0.55  fof(f123,plain,(
% 1.33/0.55    r2_hidden(sK0,sK2)),
% 1.33/0.55    inference(resolution,[],[f112,f120])).
% 1.33/0.55  fof(f120,plain,(
% 1.33/0.55    r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 1.33/0.55    inference(resolution,[],[f117,f101])).
% 1.33/0.55  fof(f101,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 1.33/0.55    inference(superposition,[],[f79,f60])).
% 1.33/0.55  fof(f60,plain,(
% 1.33/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.33/0.55    inference(definition_unfolding,[],[f32,f59])).
% 1.33/0.55  fof(f59,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.33/0.55    inference(definition_unfolding,[],[f39,f58])).
% 1.33/0.55  fof(f58,plain,(
% 1.33/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.33/0.55    inference(definition_unfolding,[],[f42,f57])).
% 1.33/0.55  fof(f57,plain,(
% 1.33/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.33/0.55    inference(definition_unfolding,[],[f51,f56])).
% 1.33/0.55  fof(f56,plain,(
% 1.33/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.33/0.55    inference(definition_unfolding,[],[f52,f53])).
% 1.33/0.55  fof(f53,plain,(
% 1.33/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f15])).
% 1.33/0.55  fof(f15,axiom,(
% 1.33/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.33/0.55  fof(f52,plain,(
% 1.33/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f14])).
% 1.33/0.55  fof(f14,axiom,(
% 1.33/0.55    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.33/0.55  fof(f51,plain,(
% 1.33/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f13])).
% 1.33/0.55  fof(f13,axiom,(
% 1.33/0.55    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.33/0.55  fof(f42,plain,(
% 1.33/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f12])).
% 1.33/0.55  fof(f12,axiom,(
% 1.33/0.55    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.33/0.55  fof(f39,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f11])).
% 1.33/0.55  fof(f11,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.33/0.55  fof(f32,plain,(
% 1.33/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f10])).
% 1.33/0.55  fof(f10,axiom,(
% 1.33/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.33/0.55  fof(f79,plain,(
% 1.33/0.55    ( ! [X4,X2,X1] : (r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X1,X2))) )),
% 1.33/0.55    inference(equality_resolution,[],[f78])).
% 1.33/0.55  fof(f78,plain,(
% 1.33/0.55    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k6_enumset1(X4,X4,X4,X4,X4,X4,X1,X2) != X3) )),
% 1.33/0.55    inference(equality_resolution,[],[f67])).
% 1.33/0.55  fof(f67,plain,(
% 1.33/0.55    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.33/0.55    inference(definition_unfolding,[],[f48,f59])).
% 1.33/0.55  fof(f48,plain,(
% 1.33/0.55    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.33/0.55    inference(cnf_transformation,[],[f27])).
% 1.33/0.55  fof(f27,plain,(
% 1.33/0.55    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.33/0.55    inference(ennf_transformation,[],[f4])).
% 1.33/0.55  fof(f4,axiom,(
% 1.33/0.55    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.33/0.55  fof(f117,plain,(
% 1.33/0.55    ( ! [X1] : (~r2_hidden(X1,k2_tarski(k2_tarski(sK0,sK1),sK2)) | r1_tarski(X1,sK2)) )),
% 1.33/0.55    inference(superposition,[],[f33,f114])).
% 1.33/0.55  fof(f114,plain,(
% 1.33/0.55    sK2 = k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2))),
% 1.33/0.55    inference(resolution,[],[f103,f97])).
% 1.33/0.55  fof(f97,plain,(
% 1.33/0.55    ~r2_hidden(sK2,k2_tarski(k2_tarski(sK0,sK1),sK2)) | sK2 = k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2))),
% 1.33/0.55    inference(resolution,[],[f89,f62])).
% 1.33/0.55  fof(f62,plain,(
% 1.33/0.55    r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2)),sK2)),
% 1.33/0.55    inference(definition_unfolding,[],[f28,f31])).
% 1.33/0.55  fof(f31,plain,(
% 1.33/0.55    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f17])).
% 1.33/0.55  fof(f17,axiom,(
% 1.33/0.55    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.33/0.55  fof(f28,plain,(
% 1.33/0.55    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 1.33/0.55    inference(cnf_transformation,[],[f21])).
% 1.33/0.55  fof(f89,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~r1_tarski(k3_tarski(X0),X1) | k3_tarski(X0) = X1 | ~r2_hidden(X1,X0)) )),
% 1.33/0.55    inference(resolution,[],[f86,f33])).
% 1.33/0.55  fof(f86,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.33/0.55    inference(resolution,[],[f34,f38])).
% 1.33/0.55  fof(f38,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f26])).
% 1.33/0.55  fof(f26,plain,(
% 1.33/0.55    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 1.33/0.55    inference(ennf_transformation,[],[f3])).
% 1.33/0.55  fof(f3,axiom,(
% 1.33/0.55    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).
% 1.33/0.55  fof(f34,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f24])).
% 1.33/0.55  fof(f24,plain,(
% 1.33/0.55    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 1.33/0.55    inference(flattening,[],[f23])).
% 1.33/0.55  fof(f23,plain,(
% 1.33/0.55    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 1.33/0.55    inference(ennf_transformation,[],[f20])).
% 1.33/0.55  fof(f20,plain,(
% 1.33/0.55    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 1.33/0.55    inference(unused_predicate_definition_removal,[],[f2])).
% 1.33/0.55  fof(f2,axiom,(
% 1.33/0.55    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.33/0.55  fof(f103,plain,(
% 1.33/0.55    ( ! [X4,X5] : (r2_hidden(X5,k2_tarski(X4,X5))) )),
% 1.33/0.55    inference(superposition,[],[f75,f60])).
% 1.33/0.55  fof(f75,plain,(
% 1.33/0.55    ( ! [X4,X0,X1] : (r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X4))) )),
% 1.33/0.55    inference(equality_resolution,[],[f74])).
% 1.33/0.55  fof(f74,plain,(
% 1.33/0.55    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X4) != X3) )),
% 1.33/0.55    inference(equality_resolution,[],[f65])).
% 1.33/0.55  fof(f65,plain,(
% 1.33/0.55    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.33/0.55    inference(definition_unfolding,[],[f50,f59])).
% 1.33/0.55  fof(f50,plain,(
% 1.33/0.55    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.33/0.55    inference(cnf_transformation,[],[f27])).
% 1.33/0.55  fof(f33,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f22])).
% 1.33/0.55  fof(f22,plain,(
% 1.33/0.55    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 1.33/0.55    inference(ennf_transformation,[],[f16])).
% 1.33/0.55  fof(f16,axiom,(
% 1.33/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 1.33/0.55  fof(f112,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X2),X1) | r2_hidden(X0,X1)) )),
% 1.33/0.55    inference(resolution,[],[f101,f35])).
% 1.33/0.55  fof(f35,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f25])).
% 1.33/0.55  fof(f25,plain,(
% 1.33/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.33/0.55    inference(ennf_transformation,[],[f1])).
% 1.33/0.55  fof(f1,axiom,(
% 1.33/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.33/0.55  % SZS output end Proof for theBenchmark
% 1.33/0.55  % (12620)------------------------------
% 1.33/0.55  % (12620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (12620)Termination reason: Refutation
% 1.33/0.55  
% 1.33/0.55  % (12620)Memory used [KB]: 6268
% 1.33/0.55  % (12620)Time elapsed: 0.079 s
% 1.33/0.55  % (12620)------------------------------
% 1.33/0.55  % (12620)------------------------------
% 1.33/0.55  % (12610)Success in time 0.182 s
%------------------------------------------------------------------------------
