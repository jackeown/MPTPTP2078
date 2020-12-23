%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:53 EST 2020

% Result     : Theorem 1.79s
% Output     : Refutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 153 expanded)
%              Number of leaves         :   10 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 264 expanded)
%              Number of equality atoms :   34 ( 113 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1062,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1058,f20])).

fof(f20,plain,(
    sK0 != k2_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).

fof(f1058,plain,(
    sK0 = k2_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f1054,f338])).

fof(f338,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k2_relat_1(k8_relat_1(X2,sK1)))
      | k2_relat_1(k8_relat_1(X2,sK1)) = X2 ) ),
    inference(resolution,[],[f330,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f330,plain,(
    ! [X1] : r1_tarski(k2_relat_1(k8_relat_1(X1,sK1)),X1) ),
    inference(superposition,[],[f316,f71])).

fof(f71,plain,(
    ! [X0] : k2_relat_1(k8_relat_1(X0,sK1)) = k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),X0)) ),
    inference(resolution,[],[f51,f18])).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(forward_demodulation,[],[f45,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f25,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f23,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f24,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f26,f41])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(f316,plain,(
    ! [X14,X15] : r1_tarski(k4_xboole_0(X15,k4_xboole_0(X15,X14)),X14) ),
    inference(forward_demodulation,[],[f304,f44])).

fof(f304,plain,(
    ! [X14,X15] : r1_tarski(k1_setfam_1(k2_enumset1(X15,X15,X15,X14)),X14) ),
    inference(superposition,[],[f132,f67])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(superposition,[],[f44,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f22,f40,f40])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f132,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X2,X3),X2) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
    ! [X2,X3] :
      ( r1_tarski(k4_xboole_0(X2,X3),X2)
      | r1_tarski(k4_xboole_0(X2,X3),X2) ) ),
    inference(resolution,[],[f55,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(k4_xboole_0(X0,X1),X2),X0)
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f50,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1054,plain,(
    r1_tarski(sK0,k2_relat_1(k8_relat_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f1043])).

fof(f1043,plain,
    ( r1_tarski(sK0,k2_relat_1(k8_relat_1(sK0,sK1)))
    | r1_tarski(sK0,k2_relat_1(k8_relat_1(sK0,sK1))) ),
    inference(resolution,[],[f1000,f31])).

fof(f1000,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK2(sK0,k2_relat_1(k8_relat_1(X4,sK1))),X4)
      | r1_tarski(sK0,k2_relat_1(k8_relat_1(X4,sK1))) ) ),
    inference(resolution,[],[f742,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f742,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK0,k2_relat_1(k8_relat_1(X0,sK1))),k4_xboole_0(k2_relat_1(sK1),X0))
      | r1_tarski(sK0,k2_relat_1(k8_relat_1(X0,sK1))) ) ),
    inference(superposition,[],[f716,f71])).

fof(f716,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK0,k4_xboole_0(k2_relat_1(sK1),X0)),X0)
      | r1_tarski(sK0,k4_xboole_0(k2_relat_1(sK1),X0)) ) ),
    inference(duplicate_literal_removal,[],[f696])).

fof(f696,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK0,k4_xboole_0(k2_relat_1(sK1),X0)),X0)
      | r1_tarski(sK0,k4_xboole_0(k2_relat_1(sK1),X0))
      | r1_tarski(sK0,k4_xboole_0(k2_relat_1(sK1),X0)) ) ),
    inference(resolution,[],[f63,f32])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(sK0,X0),k4_xboole_0(k2_relat_1(sK1),X1))
      | r2_hidden(sK2(sK0,X0),X1)
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f61,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f61,plain,(
    ! [X2] :
      ( r2_hidden(sK2(sK0,X2),k2_relat_1(sK1))
      | r1_tarski(sK0,X2) ) ),
    inference(resolution,[],[f58,f19])).

fof(f19,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK2(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f30,f31])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (11752)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.47  % (11770)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.48  % (11752)Refutation not found, incomplete strategy% (11752)------------------------------
% 0.20/0.48  % (11752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (11752)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (11752)Memory used [KB]: 10618
% 0.20/0.48  % (11752)Time elapsed: 0.075 s
% 0.20/0.48  % (11752)------------------------------
% 0.20/0.48  % (11752)------------------------------
% 0.20/0.50  % (11747)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (11765)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (11765)Refutation not found, incomplete strategy% (11765)------------------------------
% 0.20/0.51  % (11765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (11765)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (11765)Memory used [KB]: 10746
% 0.20/0.51  % (11765)Time elapsed: 0.078 s
% 0.20/0.51  % (11765)------------------------------
% 0.20/0.51  % (11765)------------------------------
% 0.20/0.51  % (11748)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (11762)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (11764)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (11744)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (11757)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (11750)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (11745)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (11755)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (11749)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (11746)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (11769)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (11751)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (11743)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (11759)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (11766)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (11743)Refutation not found, incomplete strategy% (11743)------------------------------
% 0.20/0.53  % (11743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11743)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (11743)Memory used [KB]: 1663
% 0.20/0.53  % (11743)Time elapsed: 0.137 s
% 0.20/0.53  % (11743)------------------------------
% 0.20/0.53  % (11743)------------------------------
% 0.20/0.54  % (11772)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (11771)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (11761)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (11768)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (11767)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (11760)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (11763)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (11760)Refutation not found, incomplete strategy% (11760)------------------------------
% 0.20/0.54  % (11760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (11760)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (11760)Memory used [KB]: 10618
% 0.20/0.54  % (11760)Time elapsed: 0.150 s
% 0.20/0.54  % (11760)------------------------------
% 0.20/0.54  % (11760)------------------------------
% 0.20/0.54  % (11763)Refutation not found, incomplete strategy% (11763)------------------------------
% 0.20/0.54  % (11763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (11763)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (11763)Memory used [KB]: 10746
% 0.20/0.54  % (11763)Time elapsed: 0.151 s
% 0.20/0.54  % (11763)------------------------------
% 0.20/0.54  % (11763)------------------------------
% 0.20/0.55  % (11753)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (11756)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (11753)Refutation not found, incomplete strategy% (11753)------------------------------
% 0.20/0.55  % (11753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (11753)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (11753)Memory used [KB]: 10618
% 0.20/0.55  % (11753)Time elapsed: 0.153 s
% 0.20/0.55  % (11753)------------------------------
% 0.20/0.55  % (11753)------------------------------
% 0.20/0.55  % (11754)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (11754)Refutation not found, incomplete strategy% (11754)------------------------------
% 0.20/0.55  % (11754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (11754)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (11754)Memory used [KB]: 10618
% 0.20/0.55  % (11754)Time elapsed: 0.150 s
% 0.20/0.55  % (11754)------------------------------
% 0.20/0.55  % (11754)------------------------------
% 0.20/0.55  % (11758)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.79/0.59  % (11775)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.79/0.60  % (11749)Refutation found. Thanks to Tanya!
% 1.79/0.60  % SZS status Theorem for theBenchmark
% 1.79/0.60  % SZS output start Proof for theBenchmark
% 1.79/0.60  fof(f1062,plain,(
% 1.79/0.60    $false),
% 1.79/0.60    inference(subsumption_resolution,[],[f1058,f20])).
% 1.79/0.60  fof(f20,plain,(
% 1.79/0.60    sK0 != k2_relat_1(k8_relat_1(sK0,sK1))),
% 1.79/0.60    inference(cnf_transformation,[],[f15])).
% 1.79/0.60  fof(f15,plain,(
% 1.79/0.60    ? [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_relat_1(X1))),
% 1.79/0.60    inference(flattening,[],[f14])).
% 1.79/0.60  fof(f14,plain,(
% 1.79/0.60    ? [X0,X1] : ((k2_relat_1(k8_relat_1(X0,X1)) != X0 & r1_tarski(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 1.79/0.60    inference(ennf_transformation,[],[f12])).
% 1.79/0.60  fof(f12,negated_conjecture,(
% 1.79/0.60    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k2_relat_1(X1)) => k2_relat_1(k8_relat_1(X0,X1)) = X0))),
% 1.79/0.60    inference(negated_conjecture,[],[f11])).
% 1.79/0.60  fof(f11,conjecture,(
% 1.79/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k2_relat_1(X1)) => k2_relat_1(k8_relat_1(X0,X1)) = X0))),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).
% 1.79/0.60  fof(f1058,plain,(
% 1.79/0.60    sK0 = k2_relat_1(k8_relat_1(sK0,sK1))),
% 1.79/0.60    inference(resolution,[],[f1054,f338])).
% 1.79/0.60  fof(f338,plain,(
% 1.79/0.60    ( ! [X2] : (~r1_tarski(X2,k2_relat_1(k8_relat_1(X2,sK1))) | k2_relat_1(k8_relat_1(X2,sK1)) = X2) )),
% 1.79/0.60    inference(resolution,[],[f330,f29])).
% 1.79/0.60  fof(f29,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.79/0.60    inference(cnf_transformation,[],[f4])).
% 1.79/0.60  fof(f4,axiom,(
% 1.79/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.79/0.60  fof(f330,plain,(
% 1.79/0.60    ( ! [X1] : (r1_tarski(k2_relat_1(k8_relat_1(X1,sK1)),X1)) )),
% 1.79/0.60    inference(superposition,[],[f316,f71])).
% 1.79/0.60  fof(f71,plain,(
% 1.79/0.60    ( ! [X0] : (k2_relat_1(k8_relat_1(X0,sK1)) = k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),X0))) )),
% 1.79/0.60    inference(resolution,[],[f51,f18])).
% 1.79/0.60  fof(f18,plain,(
% 1.79/0.60    v1_relat_1(sK1)),
% 1.79/0.60    inference(cnf_transformation,[],[f15])).
% 1.79/0.60  fof(f51,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))) )),
% 1.79/0.60    inference(forward_demodulation,[],[f45,f44])).
% 1.79/0.60  fof(f44,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.79/0.60    inference(definition_unfolding,[],[f25,f41])).
% 1.79/0.60  fof(f41,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.79/0.60    inference(definition_unfolding,[],[f23,f40])).
% 1.79/0.60  fof(f40,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.79/0.60    inference(definition_unfolding,[],[f24,f33])).
% 1.79/0.60  fof(f33,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f8])).
% 1.79/0.60  fof(f8,axiom,(
% 1.79/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.79/0.60  fof(f24,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f7])).
% 1.79/0.60  fof(f7,axiom,(
% 1.79/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.79/0.60  fof(f23,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.79/0.60    inference(cnf_transformation,[],[f9])).
% 1.79/0.60  fof(f9,axiom,(
% 1.79/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.79/0.60  fof(f25,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f5])).
% 1.79/0.60  fof(f5,axiom,(
% 1.79/0.60    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.79/0.60  fof(f45,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0))) )),
% 1.79/0.60    inference(definition_unfolding,[],[f26,f41])).
% 1.79/0.60  fof(f26,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f16])).
% 1.79/0.60  fof(f16,plain,(
% 1.79/0.60    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.94/0.60    inference(ennf_transformation,[],[f10])).
% 1.94/0.60  fof(f10,axiom,(
% 1.94/0.60    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 1.94/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).
% 1.94/0.60  fof(f316,plain,(
% 1.94/0.60    ( ! [X14,X15] : (r1_tarski(k4_xboole_0(X15,k4_xboole_0(X15,X14)),X14)) )),
% 1.94/0.60    inference(forward_demodulation,[],[f304,f44])).
% 1.94/0.60  fof(f304,plain,(
% 1.94/0.60    ( ! [X14,X15] : (r1_tarski(k1_setfam_1(k2_enumset1(X15,X15,X15,X14)),X14)) )),
% 1.94/0.60    inference(superposition,[],[f132,f67])).
% 1.94/0.60  fof(f67,plain,(
% 1.94/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) )),
% 1.94/0.60    inference(superposition,[],[f44,f43])).
% 1.94/0.60  fof(f43,plain,(
% 1.94/0.60    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 1.94/0.60    inference(definition_unfolding,[],[f22,f40,f40])).
% 1.94/0.60  fof(f22,plain,(
% 1.94/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.94/0.60    inference(cnf_transformation,[],[f6])).
% 1.94/0.60  fof(f6,axiom,(
% 1.94/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.94/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.94/0.60  fof(f132,plain,(
% 1.94/0.60    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),X2)) )),
% 1.94/0.60    inference(duplicate_literal_removal,[],[f123])).
% 1.94/0.60  fof(f123,plain,(
% 1.94/0.60    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),X2) | r1_tarski(k4_xboole_0(X2,X3),X2)) )),
% 1.94/0.60    inference(resolution,[],[f55,f32])).
% 1.94/0.60  fof(f32,plain,(
% 1.94/0.60    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.94/0.60    inference(cnf_transformation,[],[f17])).
% 1.94/0.60  fof(f17,plain,(
% 1.94/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.94/0.60    inference(ennf_transformation,[],[f1])).
% 1.94/0.60  fof(f1,axiom,(
% 1.94/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.94/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.94/0.60  fof(f55,plain,(
% 1.94/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK2(k4_xboole_0(X0,X1),X2),X0) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.94/0.60    inference(resolution,[],[f50,f31])).
% 1.94/0.60  fof(f31,plain,(
% 1.94/0.60    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.94/0.60    inference(cnf_transformation,[],[f17])).
% 1.94/0.60  fof(f50,plain,(
% 1.94/0.60    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 1.94/0.60    inference(equality_resolution,[],[f37])).
% 1.94/0.60  fof(f37,plain,(
% 1.94/0.60    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.94/0.60    inference(cnf_transformation,[],[f2])).
% 1.94/0.60  fof(f2,axiom,(
% 1.94/0.60    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.94/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.94/0.60  fof(f1054,plain,(
% 1.94/0.60    r1_tarski(sK0,k2_relat_1(k8_relat_1(sK0,sK1)))),
% 1.94/0.60    inference(duplicate_literal_removal,[],[f1043])).
% 1.94/0.60  fof(f1043,plain,(
% 1.94/0.60    r1_tarski(sK0,k2_relat_1(k8_relat_1(sK0,sK1))) | r1_tarski(sK0,k2_relat_1(k8_relat_1(sK0,sK1)))),
% 1.94/0.60    inference(resolution,[],[f1000,f31])).
% 1.94/0.60  fof(f1000,plain,(
% 1.94/0.60    ( ! [X4] : (~r2_hidden(sK2(sK0,k2_relat_1(k8_relat_1(X4,sK1))),X4) | r1_tarski(sK0,k2_relat_1(k8_relat_1(X4,sK1)))) )),
% 1.94/0.60    inference(resolution,[],[f742,f49])).
% 1.94/0.60  fof(f49,plain,(
% 1.94/0.60    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 1.94/0.60    inference(equality_resolution,[],[f38])).
% 1.94/0.60  fof(f38,plain,(
% 1.94/0.60    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.94/0.60    inference(cnf_transformation,[],[f2])).
% 1.94/0.60  fof(f742,plain,(
% 1.94/0.60    ( ! [X0] : (r2_hidden(sK2(sK0,k2_relat_1(k8_relat_1(X0,sK1))),k4_xboole_0(k2_relat_1(sK1),X0)) | r1_tarski(sK0,k2_relat_1(k8_relat_1(X0,sK1)))) )),
% 1.94/0.60    inference(superposition,[],[f716,f71])).
% 1.94/0.60  fof(f716,plain,(
% 1.94/0.60    ( ! [X0] : (r2_hidden(sK2(sK0,k4_xboole_0(k2_relat_1(sK1),X0)),X0) | r1_tarski(sK0,k4_xboole_0(k2_relat_1(sK1),X0))) )),
% 1.94/0.60    inference(duplicate_literal_removal,[],[f696])).
% 1.94/0.60  fof(f696,plain,(
% 1.94/0.60    ( ! [X0] : (r2_hidden(sK2(sK0,k4_xboole_0(k2_relat_1(sK1),X0)),X0) | r1_tarski(sK0,k4_xboole_0(k2_relat_1(sK1),X0)) | r1_tarski(sK0,k4_xboole_0(k2_relat_1(sK1),X0))) )),
% 1.94/0.60    inference(resolution,[],[f63,f32])).
% 1.94/0.60  fof(f63,plain,(
% 1.94/0.60    ( ! [X0,X1] : (r2_hidden(sK2(sK0,X0),k4_xboole_0(k2_relat_1(sK1),X1)) | r2_hidden(sK2(sK0,X0),X1) | r1_tarski(sK0,X0)) )),
% 1.94/0.60    inference(resolution,[],[f61,f48])).
% 1.94/0.60  fof(f48,plain,(
% 1.94/0.60    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 1.94/0.60    inference(equality_resolution,[],[f39])).
% 1.94/0.60  fof(f39,plain,(
% 1.94/0.60    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.94/0.60    inference(cnf_transformation,[],[f2])).
% 1.94/0.60  fof(f61,plain,(
% 1.94/0.60    ( ! [X2] : (r2_hidden(sK2(sK0,X2),k2_relat_1(sK1)) | r1_tarski(sK0,X2)) )),
% 1.94/0.60    inference(resolution,[],[f58,f19])).
% 1.94/0.60  fof(f19,plain,(
% 1.94/0.60    r1_tarski(sK0,k2_relat_1(sK1))),
% 1.94/0.60    inference(cnf_transformation,[],[f15])).
% 1.94/0.60  fof(f58,plain,(
% 1.94/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r2_hidden(sK2(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 1.94/0.60    inference(resolution,[],[f30,f31])).
% 1.94/0.60  fof(f30,plain,(
% 1.94/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.94/0.60    inference(cnf_transformation,[],[f17])).
% 1.94/0.60  % SZS output end Proof for theBenchmark
% 1.94/0.60  % (11749)------------------------------
% 1.94/0.60  % (11749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.60  % (11749)Termination reason: Refutation
% 1.94/0.60  
% 1.94/0.60  % (11749)Memory used [KB]: 7164
% 1.94/0.60  % (11749)Time elapsed: 0.163 s
% 1.94/0.60  % (11749)------------------------------
% 1.94/0.60  % (11749)------------------------------
% 1.94/0.61  % (11742)Success in time 0.246 s
%------------------------------------------------------------------------------
