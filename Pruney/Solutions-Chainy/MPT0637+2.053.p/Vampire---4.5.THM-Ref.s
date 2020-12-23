%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 165 expanded)
%              Number of leaves         :   11 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :   98 ( 280 expanded)
%              Number of equality atoms :   59 ( 140 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f145,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f142])).

fof(f142,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f45,f125])).

fof(f125,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(forward_demodulation,[],[f120,f51])).

fof(f51,plain,(
    ! [X0] : k6_relat_1(X0) = k8_relat_1(X0,k6_relat_1(X0)) ),
    inference(forward_demodulation,[],[f50,f32])).

fof(f32,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f50,plain,(
    ! [X0] : k6_relat_1(X0) = k8_relat_1(k2_relat_1(k6_relat_1(X0)),k6_relat_1(X0)) ),
    inference(resolution,[],[f48,f33])).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    inference(resolution,[],[f34,f38])).

fof(f38,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f120,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X1))) ),
    inference(superposition,[],[f99,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(k3_xboole_0(X0,X1),k6_relat_1(X2)) ),
    inference(resolution,[],[f26,f33])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

fof(f99,plain,(
    ! [X6,X5] : k8_relat_1(k3_xboole_0(X5,X6),k6_relat_1(X6)) = k6_relat_1(k3_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f96,f51])).

fof(f96,plain,(
    ! [X6,X5] : k8_relat_1(k3_xboole_0(X5,X6),k6_relat_1(X6)) = k8_relat_1(k3_xboole_0(X5,X6),k6_relat_1(k3_xboole_0(X5,X6))) ),
    inference(superposition,[],[f61,f88])).

fof(f88,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k3_xboole_0(k3_xboole_0(X1,X0),X0) ),
    inference(forward_demodulation,[],[f84,f56])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(backward_demodulation,[],[f47,f54])).

fof(f54,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f44,f43])).

fof(f43,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(resolution,[],[f29,f33])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

% (12279)Termination reason: Refutation not found, incomplete strategy
fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

% (12279)Memory used [KB]: 1663
fof(f44,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f30,f33])).

% (12279)Time elapsed: 0.004 s
% (12279)------------------------------
% (12279)------------------------------
fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

% (12258)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f46,f31])).

fof(f31,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f28,f33])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f84,plain,(
    ! [X0,X1] : k3_xboole_0(k3_xboole_0(X1,X0),X0) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(superposition,[],[f76,f51])).

fof(f76,plain,(
    ! [X4,X2,X3] : k3_xboole_0(k3_xboole_0(X2,X3),X4) = k1_relat_1(k8_relat_1(X2,k8_relat_1(X3,k6_relat_1(X4)))) ),
    inference(superposition,[],[f56,f55])).

fof(f61,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(k3_xboole_0(X2,X3))) = k8_relat_1(X2,k6_relat_1(X3)) ),
    inference(superposition,[],[f59,f54])).

fof(f59,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f53,f54])).

fof(f53,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f52,f31])).

fof(f52,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) ),
    inference(resolution,[],[f27,f33])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(f45,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(superposition,[],[f25,f43])).

fof(f25,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f21])).

fof(f21,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:55:50 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (12266)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.53  % (12257)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (12274)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.53  % (12274)Refutation not found, incomplete strategy% (12274)------------------------------
% 0.22/0.53  % (12274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12249)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (12266)Refutation not found, incomplete strategy% (12266)------------------------------
% 0.22/0.54  % (12266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12274)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12274)Memory used [KB]: 10618
% 0.22/0.54  % (12274)Time elapsed: 0.112 s
% 0.22/0.54  % (12274)------------------------------
% 0.22/0.54  % (12274)------------------------------
% 0.22/0.54  % (12266)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12266)Memory used [KB]: 10618
% 0.22/0.54  % (12266)Time elapsed: 0.123 s
% 0.22/0.54  % (12266)------------------------------
% 0.22/0.54  % (12266)------------------------------
% 0.22/0.54  % (12278)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (12256)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (12253)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (12252)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (12271)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (12250)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (12250)Refutation not found, incomplete strategy% (12250)------------------------------
% 0.22/0.54  % (12250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12250)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12250)Memory used [KB]: 1663
% 0.22/0.54  % (12250)Time elapsed: 0.122 s
% 0.22/0.54  % (12250)------------------------------
% 0.22/0.54  % (12250)------------------------------
% 0.22/0.54  % (12251)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (12254)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (12261)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (12261)Refutation not found, incomplete strategy% (12261)------------------------------
% 0.22/0.55  % (12261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (12260)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (12254)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % (12260)Refutation not found, incomplete strategy% (12260)------------------------------
% 0.22/0.55  % (12260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (12260)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (12260)Memory used [KB]: 10618
% 0.22/0.55  % (12260)Time elapsed: 0.135 s
% 0.22/0.55  % (12260)------------------------------
% 0.22/0.55  % (12260)------------------------------
% 0.22/0.55  % (12270)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (12279)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (12262)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (12261)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (12261)Memory used [KB]: 6140
% 0.22/0.55  % (12261)Time elapsed: 0.124 s
% 0.22/0.55  % (12261)------------------------------
% 0.22/0.55  % (12261)------------------------------
% 0.22/0.55  % (12276)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (12263)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (12273)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (12265)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.56  % (12268)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (12277)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.56  % (12277)Refutation not found, incomplete strategy% (12277)------------------------------
% 0.22/0.56  % (12277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (12262)Refutation not found, incomplete strategy% (12262)------------------------------
% 0.22/0.56  % (12262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (12278)Refutation not found, incomplete strategy% (12278)------------------------------
% 0.22/0.56  % (12278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (12278)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (12278)Memory used [KB]: 10618
% 0.22/0.56  % (12278)Time elapsed: 0.129 s
% 0.22/0.56  % (12278)------------------------------
% 0.22/0.56  % (12278)------------------------------
% 0.22/0.56  % (12276)Refutation not found, incomplete strategy% (12276)------------------------------
% 0.22/0.56  % (12276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (12275)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.56  % (12275)Refutation not found, incomplete strategy% (12275)------------------------------
% 0.22/0.56  % (12275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (12275)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (12275)Memory used [KB]: 6140
% 0.22/0.56  % (12275)Time elapsed: 0.147 s
% 0.22/0.56  % (12275)------------------------------
% 0.22/0.56  % (12275)------------------------------
% 0.22/0.56  % (12276)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (12276)Memory used [KB]: 6140
% 0.22/0.56  % (12276)Time elapsed: 0.148 s
% 0.22/0.56  % (12276)------------------------------
% 0.22/0.56  % (12276)------------------------------
% 1.56/0.57  % (12268)Refutation not found, incomplete strategy% (12268)------------------------------
% 1.56/0.57  % (12268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (12262)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (12262)Memory used [KB]: 10618
% 1.56/0.57  % (12262)Time elapsed: 0.151 s
% 1.56/0.57  % (12262)------------------------------
% 1.56/0.57  % (12262)------------------------------
% 1.56/0.57  % (12267)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.56/0.57  % (12279)Refutation not found, incomplete strategy% (12279)------------------------------
% 1.56/0.57  % (12279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % SZS output start Proof for theBenchmark
% 1.56/0.57  fof(f145,plain,(
% 1.56/0.57    $false),
% 1.56/0.57    inference(trivial_inequality_removal,[],[f142])).
% 1.56/0.57  fof(f142,plain,(
% 1.56/0.57    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.56/0.57    inference(superposition,[],[f45,f125])).
% 1.56/0.57  fof(f125,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 1.56/0.57    inference(forward_demodulation,[],[f120,f51])).
% 1.56/0.57  fof(f51,plain,(
% 1.56/0.57    ( ! [X0] : (k6_relat_1(X0) = k8_relat_1(X0,k6_relat_1(X0))) )),
% 1.56/0.57    inference(forward_demodulation,[],[f50,f32])).
% 1.56/0.57  fof(f32,plain,(
% 1.56/0.57    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.56/0.57    inference(cnf_transformation,[],[f8])).
% 1.56/0.57  fof(f8,axiom,(
% 1.56/0.57    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.56/0.57  fof(f50,plain,(
% 1.56/0.57    ( ! [X0] : (k6_relat_1(X0) = k8_relat_1(k2_relat_1(k6_relat_1(X0)),k6_relat_1(X0))) )),
% 1.56/0.57    inference(resolution,[],[f48,f33])).
% 1.56/0.57  fof(f33,plain,(
% 1.56/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.56/0.57    inference(cnf_transformation,[],[f3])).
% 1.56/0.57  fof(f3,axiom,(
% 1.56/0.57    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.56/0.57  fof(f48,plain,(
% 1.56/0.57    ( ! [X0] : (~v1_relat_1(X0) | k8_relat_1(k2_relat_1(X0),X0) = X0) )),
% 1.56/0.57    inference(resolution,[],[f34,f38])).
% 1.56/0.57  fof(f38,plain,(
% 1.56/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.56/0.57    inference(equality_resolution,[],[f36])).
% 1.56/0.57  fof(f36,plain,(
% 1.56/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.56/0.57    inference(cnf_transformation,[],[f24])).
% 1.56/0.57  fof(f24,plain,(
% 1.56/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.57    inference(flattening,[],[f23])).
% 1.56/0.57  fof(f23,plain,(
% 1.56/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.57    inference(nnf_transformation,[],[f1])).
% 1.56/0.57  fof(f1,axiom,(
% 1.56/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.56/0.57  fof(f34,plain,(
% 1.56/0.57    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f20])).
% 1.56/0.57  fof(f20,plain,(
% 1.56/0.57    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.56/0.57    inference(flattening,[],[f19])).
% 1.56/0.57  fof(f19,plain,(
% 1.56/0.57    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.56/0.57    inference(ennf_transformation,[],[f5])).
% 1.56/0.57  fof(f5,axiom,(
% 1.56/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 1.56/0.57  fof(f120,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X1)))) )),
% 1.56/0.57    inference(superposition,[],[f99,f55])).
% 1.56/0.57  fof(f55,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(k3_xboole_0(X0,X1),k6_relat_1(X2))) )),
% 1.56/0.57    inference(resolution,[],[f26,f33])).
% 1.56/0.57  fof(f26,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f14])).
% 1.56/0.57  fof(f14,plain,(
% 1.56/0.57    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 1.56/0.57    inference(ennf_transformation,[],[f6])).
% 1.56/0.57  fof(f6,axiom,(
% 1.56/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).
% 1.56/0.57  fof(f99,plain,(
% 1.56/0.57    ( ! [X6,X5] : (k8_relat_1(k3_xboole_0(X5,X6),k6_relat_1(X6)) = k6_relat_1(k3_xboole_0(X5,X6))) )),
% 1.56/0.57    inference(forward_demodulation,[],[f96,f51])).
% 1.56/0.57  fof(f96,plain,(
% 1.56/0.57    ( ! [X6,X5] : (k8_relat_1(k3_xboole_0(X5,X6),k6_relat_1(X6)) = k8_relat_1(k3_xboole_0(X5,X6),k6_relat_1(k3_xboole_0(X5,X6)))) )),
% 1.56/0.57    inference(superposition,[],[f61,f88])).
% 1.56/0.57  fof(f88,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k3_xboole_0(k3_xboole_0(X1,X0),X0)) )),
% 1.56/0.57    inference(forward_demodulation,[],[f84,f56])).
% 1.56/0.57  fof(f56,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) )),
% 1.56/0.57    inference(backward_demodulation,[],[f47,f54])).
% 1.56/0.57  fof(f54,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.56/0.57    inference(forward_demodulation,[],[f44,f43])).
% 1.56/0.57  fof(f43,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 1.56/0.57    inference(resolution,[],[f29,f33])).
% 1.56/0.57  fof(f29,plain,(
% 1.56/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 1.56/0.57    inference(cnf_transformation,[],[f17])).
% 1.56/0.57  fof(f17,plain,(
% 1.56/0.57    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 1.56/0.57    inference(ennf_transformation,[],[f4])).
% 1.56/0.57  % (12279)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  fof(f4,axiom,(
% 1.56/0.57    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 1.56/0.57  
% 1.56/0.57  % (12279)Memory used [KB]: 1663
% 1.56/0.57  fof(f44,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.56/0.57    inference(resolution,[],[f30,f33])).
% 1.56/0.57  % (12279)Time elapsed: 0.004 s
% 1.56/0.57  % (12279)------------------------------
% 1.56/0.57  % (12279)------------------------------
% 1.56/0.57  fof(f30,plain,(
% 1.56/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f18])).
% 1.56/0.57  % (12258)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.56/0.57  fof(f18,plain,(
% 1.56/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.56/0.57    inference(ennf_transformation,[],[f10])).
% 1.56/0.57  fof(f10,axiom,(
% 1.56/0.57    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.56/0.57  fof(f47,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.56/0.57    inference(forward_demodulation,[],[f46,f31])).
% 1.56/0.57  fof(f31,plain,(
% 1.56/0.57    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.56/0.57    inference(cnf_transformation,[],[f8])).
% 1.56/0.57  fof(f46,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.56/0.57    inference(resolution,[],[f28,f33])).
% 1.56/0.57  fof(f28,plain,(
% 1.56/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))) )),
% 1.56/0.57    inference(cnf_transformation,[],[f16])).
% 1.56/0.57  fof(f16,plain,(
% 1.56/0.57    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.56/0.57    inference(ennf_transformation,[],[f9])).
% 1.56/0.57  fof(f9,axiom,(
% 1.56/0.57    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 1.56/0.57  fof(f84,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k3_xboole_0(k3_xboole_0(X1,X0),X0) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) )),
% 1.56/0.57    inference(superposition,[],[f76,f51])).
% 1.56/0.57  fof(f76,plain,(
% 1.56/0.57    ( ! [X4,X2,X3] : (k3_xboole_0(k3_xboole_0(X2,X3),X4) = k1_relat_1(k8_relat_1(X2,k8_relat_1(X3,k6_relat_1(X4))))) )),
% 1.56/0.57    inference(superposition,[],[f56,f55])).
% 1.56/0.57  fof(f61,plain,(
% 1.56/0.57    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(k3_xboole_0(X2,X3))) = k8_relat_1(X2,k6_relat_1(X3))) )),
% 1.56/0.57    inference(superposition,[],[f59,f54])).
% 1.56/0.57  fof(f59,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) )),
% 1.56/0.57    inference(forward_demodulation,[],[f53,f54])).
% 1.56/0.57  fof(f53,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) )),
% 1.56/0.57    inference(forward_demodulation,[],[f52,f31])).
% 1.56/0.57  fof(f52,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) )),
% 1.56/0.57    inference(resolution,[],[f27,f33])).
% 1.56/0.57  fof(f27,plain,(
% 1.56/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))) )),
% 1.56/0.57    inference(cnf_transformation,[],[f15])).
% 1.56/0.57  fof(f15,plain,(
% 1.56/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.56/0.57    inference(ennf_transformation,[],[f7])).
% 1.56/0.57  fof(f7,axiom,(
% 1.56/0.57    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).
% 1.56/0.57  fof(f45,plain,(
% 1.56/0.57    k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 1.56/0.57    inference(superposition,[],[f25,f43])).
% 1.56/0.57  fof(f25,plain,(
% 1.56/0.57    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.56/0.57    inference(cnf_transformation,[],[f22])).
% 1.56/0.57  fof(f22,plain,(
% 1.56/0.57    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.56/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f21])).
% 1.56/0.57  fof(f21,plain,(
% 1.56/0.57    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.56/0.57    introduced(choice_axiom,[])).
% 1.56/0.57  fof(f13,plain,(
% 1.56/0.57    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 1.56/0.57    inference(ennf_transformation,[],[f12])).
% 1.56/0.57  fof(f12,negated_conjecture,(
% 1.56/0.57    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.56/0.57    inference(negated_conjecture,[],[f11])).
% 1.56/0.57  fof(f11,conjecture,(
% 1.56/0.57    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 1.56/0.57  % SZS output end Proof for theBenchmark
% 1.56/0.57  % (12254)------------------------------
% 1.56/0.57  % (12254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (12254)Termination reason: Refutation
% 1.56/0.57  
% 1.56/0.57  % (12254)Memory used [KB]: 1791
% 1.56/0.57  % (12254)Time elapsed: 0.126 s
% 1.56/0.57  % (12254)------------------------------
% 1.56/0.57  % (12254)------------------------------
% 1.56/0.57  % (12248)Success in time 0.199 s
%------------------------------------------------------------------------------
