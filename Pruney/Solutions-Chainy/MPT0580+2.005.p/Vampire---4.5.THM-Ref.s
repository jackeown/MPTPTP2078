%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   82 (1040 expanded)
%              Number of leaves         :   15 ( 311 expanded)
%              Depth                    :   27
%              Number of atoms          :  155 (1731 expanded)
%              Number of equality atoms :   48 ( 853 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f182,plain,(
    $false ),
    inference(subsumption_resolution,[],[f180,f169])).

fof(f169,plain,(
    k1_xboole_0 != sK1 ),
    inference(resolution,[],[f162,f22])).

% (23556)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (23546)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (23545)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (23568)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (23567)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (23565)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (23543)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% (23541)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (23570)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (23555)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (23569)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (23548)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (23563)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (23563)Refutation not found, incomplete strategy% (23563)------------------------------
% (23563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23563)Termination reason: Refutation not found, incomplete strategy

% (23563)Memory used [KB]: 10618
% (23563)Time elapsed: 0.139 s
% (23563)------------------------------
% (23563)------------------------------
% (23562)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f22,plain,
    ( ~ v3_relat_1(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ( v3_relat_1(X0)
      <~> ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) ) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v3_relat_1(X0)
        <=> ! [X1] :
              ( r2_hidden(X1,k2_relat_1(X0))
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k2_relat_1(X0))
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t184_relat_1)).

fof(f162,plain,(
    v3_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f160,f24])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f160,plain,
    ( ~ v1_relat_1(sK0)
    | v3_relat_1(sK0) ),
    inference(resolution,[],[f159,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_zfmisc_1(k1_xboole_0))
      | ~ v1_relat_1(X0)
      | v3_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f53,f50])).

fof(f50,plain,(
    k1_zfmisc_1(k1_xboole_0) = k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f25,f49])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

% (23561)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f25,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
      | v3_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f30,f49])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
      | v3_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v3_relat_1(X0)
      <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_relat_1)).

fof(f159,plain,(
    r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f157,f120])).

fof(f120,plain,(
    ! [X5] : r2_hidden(X5,k1_zfmisc_1(X5)) ),
    inference(resolution,[],[f55,f90])).

fof(f90,plain,(
    ! [X2] : r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X2),k1_zfmisc_1(X2)) ),
    inference(superposition,[],[f28,f51])).

fof(f51,plain,(
    ! [X0] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f27,f49])).

fof(f27,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f28,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f42,f48])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f157,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f39,f156])).

fof(f156,plain,(
    k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f154,f77])).

fof(f77,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f75,f22])).

fof(f75,plain,
    ( v3_relat_1(sK0)
    | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f74,f24])).

fof(f74,plain,
    ( k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | v3_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,
    ( k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | v3_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | v3_relat_1(sK0) ),
    inference(resolution,[],[f61,f60])).

fof(f61,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK0),X0)
      | k1_xboole_0 = sK2(k2_relat_1(sK0),X0)
      | v3_relat_1(sK0) ) ),
    inference(resolution,[],[f38,f23])).

fof(f23,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK0))
      | k1_xboole_0 = X1
      | v3_relat_1(sK0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f154,plain,
    ( k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f152,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f36,f26])).

fof(f26,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

% (23559)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f152,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f117,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(k1_xboole_0))
      | r1_tarski(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f33,f88])).

fof(f88,plain,(
    k1_xboole_0 = k3_tarski(k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f51,f50])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f117,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f81,f79])).

fof(f79,plain,
    ( r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f78,f24])).

fof(f78,plain,
    ( k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(sK0)
    | r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f75,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f52,f50])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X0),k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
      | ~ v3_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f31,f49])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
      | ~ v3_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),X0)
      | r2_hidden(sK1,X0)
      | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f76,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f76,plain,
    ( r2_hidden(sK1,k2_relat_1(sK0))
    | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f75,f21])).

fof(f21,plain,
    ( ~ v3_relat_1(sK0)
    | r2_hidden(sK1,k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f180,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f178,f64])).

fof(f178,plain,(
    r1_tarski(sK1,k1_xboole_0) ),
    inference(resolution,[],[f176,f91])).

fof(f176,plain,(
    r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f172,f159])).

fof(f172,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),X0)
      | r2_hidden(sK1,X0) ) ),
    inference(resolution,[],[f168,f37])).

fof(f168,plain,(
    r2_hidden(sK1,k2_relat_1(sK0)) ),
    inference(resolution,[],[f162,f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:01:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (23544)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (23560)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (23552)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (23547)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (23564)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (23547)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f182,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f180,f169])).
% 0.22/0.53  fof(f169,plain,(
% 0.22/0.53    k1_xboole_0 != sK1),
% 0.22/0.53    inference(resolution,[],[f162,f22])).
% 0.22/0.53  % (23556)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (23546)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (23545)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (23568)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (23567)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (23565)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (23543)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (23541)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (23570)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (23555)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (23569)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (23548)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (23563)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (23563)Refutation not found, incomplete strategy% (23563)------------------------------
% 0.22/0.55  % (23563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23563)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (23563)Memory used [KB]: 10618
% 0.22/0.55  % (23563)Time elapsed: 0.139 s
% 0.22/0.55  % (23563)------------------------------
% 0.22/0.55  % (23563)------------------------------
% 0.22/0.55  % (23562)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ~v3_relat_1(sK0) | k1_xboole_0 != sK1),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ? [X0] : ((v3_relat_1(X0) <~> ! [X1] : (k1_xboole_0 = X1 | ~r2_hidden(X1,k2_relat_1(X0)))) & v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,negated_conjecture,(
% 0.22/0.55    ~! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> ! [X1] : (r2_hidden(X1,k2_relat_1(X0)) => k1_xboole_0 = X1)))),
% 0.22/0.55    inference(negated_conjecture,[],[f15])).
% 0.22/0.55  fof(f15,conjecture,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> ! [X1] : (r2_hidden(X1,k2_relat_1(X0)) => k1_xboole_0 = X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t184_relat_1)).
% 0.22/0.55  fof(f162,plain,(
% 0.22/0.55    v3_relat_1(sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f160,f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    v1_relat_1(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f160,plain,(
% 0.22/0.55    ~v1_relat_1(sK0) | v3_relat_1(sK0)),
% 0.22/0.55    inference(resolution,[],[f159,f60])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) | ~v1_relat_1(X0) | v3_relat_1(X0)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f53,f50])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    k1_zfmisc_1(k1_xboole_0) = k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.55    inference(definition_unfolding,[],[f25,f49])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f29,f48])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f32,f47])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f40,f46])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f44,f45])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.55  % (23561)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | v3_relat_1(X0)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f30,f49])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) | v3_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0] : ((v3_relat_1(X0) <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_relat_1)).
% 0.22/0.55  fof(f159,plain,(
% 0.22/0.55    r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.55    inference(subsumption_resolution,[],[f157,f120])).
% 0.22/0.55  fof(f120,plain,(
% 0.22/0.55    ( ! [X5] : (r2_hidden(X5,k1_zfmisc_1(X5))) )),
% 0.22/0.55    inference(resolution,[],[f55,f90])).
% 0.22/0.55  fof(f90,plain,(
% 0.22/0.55    ( ! [X2] : (r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X2),k1_zfmisc_1(X2))) )),
% 0.22/0.55    inference(superposition,[],[f28,f51])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    ( ! [X0] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0) )),
% 0.22/0.55    inference(definition_unfolding,[],[f27,f49])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,axiom,(
% 0.22/0.55    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f42,f48])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.22/0.55  fof(f157,plain,(
% 0.22/0.55    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.55    inference(superposition,[],[f39,f156])).
% 0.22/0.55  fof(f156,plain,(
% 0.22/0.55    k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.55    inference(subsumption_resolution,[],[f154,f77])).
% 0.22/0.55  fof(f77,plain,(
% 0.22/0.55    k1_xboole_0 != sK1 | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.55    inference(resolution,[],[f75,f22])).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    v3_relat_1(sK0) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.55    inference(subsumption_resolution,[],[f74,f24])).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | v3_relat_1(sK0) | ~v1_relat_1(sK0)),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f71])).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | v3_relat_1(sK0) | ~v1_relat_1(sK0) | v3_relat_1(sK0)),
% 0.22/0.55    inference(resolution,[],[f61,f60])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(sK0),X0) | k1_xboole_0 = sK2(k2_relat_1(sK0),X0) | v3_relat_1(sK0)) )),
% 0.22/0.55    inference(resolution,[],[f38,f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK0)) | k1_xboole_0 = X1 | v3_relat_1(sK0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.55  fof(f154,plain,(
% 0.22/0.55    k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1),
% 0.22/0.55    inference(resolution,[],[f152,f64])).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(resolution,[],[f36,f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.55  % (23559)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  fof(f152,plain,(
% 0.22/0.55    r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.55    inference(resolution,[],[f117,f91])).
% 0.22/0.55  fof(f91,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) | r1_tarski(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(superposition,[],[f33,f88])).
% 0.22/0.55  fof(f88,plain,(
% 0.22/0.55    k1_xboole_0 = k3_tarski(k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.55    inference(superposition,[],[f51,f50])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.22/0.55  fof(f117,plain,(
% 0.22/0.55    r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f115])).
% 0.22/0.55  fof(f115,plain,(
% 0.22/0.55    r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.55    inference(resolution,[],[f81,f79])).
% 0.22/0.55  fof(f79,plain,(
% 0.22/0.55    r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.55    inference(subsumption_resolution,[],[f78,f24])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | ~v1_relat_1(sK0) | r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.55    inference(resolution,[],[f75,f59])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    ( ! [X0] : (~v3_relat_1(X0) | ~v1_relat_1(X0) | r1_tarski(k2_relat_1(X0),k1_zfmisc_1(k1_xboole_0))) )),
% 0.22/0.55    inference(forward_demodulation,[],[f52,f50])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(k2_relat_1(X0),k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | ~v3_relat_1(X0)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f31,f49])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) | ~v3_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f18])).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | r2_hidden(sK1,X0) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))) )),
% 0.22/0.55    inference(resolution,[],[f76,f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    r2_hidden(sK1,k2_relat_1(sK0)) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.55    inference(resolution,[],[f75,f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ~v3_relat_1(sK0) | r2_hidden(sK1,k2_relat_1(sK0))),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  fof(f180,plain,(
% 0.22/0.55    k1_xboole_0 = sK1),
% 0.22/0.55    inference(resolution,[],[f178,f64])).
% 0.22/0.55  fof(f178,plain,(
% 0.22/0.55    r1_tarski(sK1,k1_xboole_0)),
% 0.22/0.55    inference(resolution,[],[f176,f91])).
% 0.22/0.55  fof(f176,plain,(
% 0.22/0.55    r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.55    inference(resolution,[],[f172,f159])).
% 0.22/0.55  fof(f172,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | r2_hidden(sK1,X0)) )),
% 0.22/0.55    inference(resolution,[],[f168,f37])).
% 0.22/0.55  fof(f168,plain,(
% 0.22/0.55    r2_hidden(sK1,k2_relat_1(sK0))),
% 0.22/0.55    inference(resolution,[],[f162,f21])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (23547)------------------------------
% 0.22/0.55  % (23547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23547)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (23547)Memory used [KB]: 6268
% 0.22/0.55  % (23547)Time elapsed: 0.129 s
% 0.22/0.55  % (23547)------------------------------
% 0.22/0.55  % (23547)------------------------------
% 0.22/0.55  % (23566)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (23540)Success in time 0.188 s
%------------------------------------------------------------------------------
