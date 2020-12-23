%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:53 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 132 expanded)
%              Number of leaves         :   12 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  122 ( 281 expanded)
%              Number of equality atoms :   16 (  28 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f418,plain,(
    $false ),
    inference(subsumption_resolution,[],[f414,f113])).

fof(f113,plain,(
    ! [X4] : r1_tarski(k3_relat_1(k2_wellord1(sK1,X4)),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f112,f30])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        | ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
          & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_wellord1)).

fof(f112,plain,(
    ! [X4] :
      ( ~ v1_relat_1(sK1)
      | r1_tarski(k3_relat_1(k2_wellord1(sK1,X4)),k3_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f111,f88])).

fof(f88,plain,(
    ! [X3] : v1_relat_1(k2_wellord1(sK1,X3)) ),
    inference(subsumption_resolution,[],[f85,f49])).

fof(f49,plain,(
    ! [X7] : v1_relat_1(k7_relat_1(sK1,X7)) ),
    inference(resolution,[],[f30,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f85,plain,(
    ! [X3] :
      ( v1_relat_1(k2_wellord1(sK1,X3))
      | ~ v1_relat_1(k7_relat_1(sK1,X3)) ) ),
    inference(superposition,[],[f36,f45])).

fof(f45,plain,(
    ! [X2] : k2_wellord1(sK1,X2) = k8_relat_1(X2,k7_relat_1(sK1,X2)) ),
    inference(resolution,[],[f30,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k8_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f111,plain,(
    ! [X4] :
      ( ~ v1_relat_1(k2_wellord1(sK1,X4))
      | ~ v1_relat_1(sK1)
      | r1_tarski(k3_relat_1(k2_wellord1(sK1,X4)),k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f89,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f89,plain,(
    ! [X1] : r1_tarski(k2_wellord1(sK1,X1),sK1) ),
    inference(superposition,[],[f41,f46])).

fof(f46,plain,(
    ! [X3] : k2_wellord1(sK1,X3) = k3_xboole_0(sK1,k2_zfmisc_1(X3,X3)) ),
    inference(resolution,[],[f30,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f414,plain,(
    ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) ),
    inference(resolution,[],[f407,f29])).

fof(f29,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0)
    | ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f407,plain,(
    ! [X0] : r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),X0) ),
    inference(subsumption_resolution,[],[f406,f88])).

fof(f406,plain,(
    ! [X0] :
      ( r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),X0)
      | ~ v1_relat_1(k2_wellord1(sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f405,f176])).

fof(f176,plain,(
    ! [X1] : r1_tarski(k1_relat_1(k2_wellord1(sK1,X1)),X1) ),
    inference(superposition,[],[f61,f86])).

fof(f86,plain,(
    ! [X2] : k2_wellord1(sK1,X2) = k7_relat_1(k8_relat_1(X2,sK1),X2) ),
    inference(subsumption_resolution,[],[f82,f30])).

fof(f82,plain,(
    ! [X2] :
      ( k2_wellord1(sK1,X2) = k7_relat_1(k8_relat_1(X2,sK1),X2)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f45,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

fof(f61,plain,(
    ! [X19,X18] : r1_tarski(k1_relat_1(k7_relat_1(k8_relat_1(X18,sK1),X19)),X19) ),
    inference(resolution,[],[f48,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f48,plain,(
    ! [X6] : v1_relat_1(k8_relat_1(X6,sK1)) ),
    inference(resolution,[],[f30,f36])).

fof(f405,plain,(
    ! [X0] :
      ( r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),X0)
      | ~ r1_tarski(k1_relat_1(k2_wellord1(sK1,X0)),X0)
      | ~ v1_relat_1(k2_wellord1(sK1,X0)) ) ),
    inference(superposition,[],[f150,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f150,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,k2_relat_1(k2_wellord1(sK1,X1))),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f87,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f87,plain,(
    ! [X2] : r1_tarski(k2_relat_1(k2_wellord1(sK1,X2)),X2) ),
    inference(subsumption_resolution,[],[f84,f49])).

fof(f84,plain,(
    ! [X2] :
      ( r1_tarski(k2_relat_1(k2_wellord1(sK1,X2)),X2)
      | ~ v1_relat_1(k7_relat_1(sK1,X2)) ) ),
    inference(superposition,[],[f39,f45])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:24:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (21952)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.50  % (21951)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.50  % (21960)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.50  % (21949)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.50  % (21947)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  % (21950)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (21962)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.51  % (21949)Refutation not found, incomplete strategy% (21949)------------------------------
% 0.22/0.51  % (21949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21949)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (21949)Memory used [KB]: 10490
% 0.22/0.51  % (21949)Time elapsed: 0.092 s
% 0.22/0.51  % (21949)------------------------------
% 0.22/0.51  % (21949)------------------------------
% 0.22/0.51  % (21948)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.52  % (21946)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.52  % (21957)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.52  % (21968)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.52  % (21965)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.52  % (21963)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.52  % (21955)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.52  % (21959)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.52  % (21966)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.52  % (21964)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.52  % (21969)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.53  % (21961)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.53  % (21958)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.53  % (21969)Refutation not found, incomplete strategy% (21969)------------------------------
% 0.22/0.53  % (21969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (21954)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.53  % (21969)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (21969)Memory used [KB]: 10618
% 0.22/0.53  % (21969)Time elapsed: 0.050 s
% 0.22/0.53  % (21969)------------------------------
% 0.22/0.53  % (21969)------------------------------
% 0.22/0.53  % (21967)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.53  % (21954)Refutation not found, incomplete strategy% (21954)------------------------------
% 0.22/0.53  % (21954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (21954)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (21954)Memory used [KB]: 10618
% 0.22/0.53  % (21954)Time elapsed: 0.115 s
% 0.22/0.53  % (21954)------------------------------
% 0.22/0.53  % (21954)------------------------------
% 0.22/0.53  % (21956)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.53  % (21956)Refutation not found, incomplete strategy% (21956)------------------------------
% 0.22/0.53  % (21956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (21956)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (21956)Memory used [KB]: 10618
% 0.22/0.53  % (21956)Time elapsed: 0.115 s
% 0.22/0.53  % (21956)------------------------------
% 0.22/0.53  % (21956)------------------------------
% 0.22/0.55  % (21953)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.52/0.56  % (21967)Refutation found. Thanks to Tanya!
% 1.52/0.56  % SZS status Theorem for theBenchmark
% 1.52/0.56  % SZS output start Proof for theBenchmark
% 1.52/0.56  fof(f418,plain,(
% 1.52/0.56    $false),
% 1.52/0.56    inference(subsumption_resolution,[],[f414,f113])).
% 1.66/0.58  fof(f113,plain,(
% 1.66/0.58    ( ! [X4] : (r1_tarski(k3_relat_1(k2_wellord1(sK1,X4)),k3_relat_1(sK1))) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f112,f30])).
% 1.66/0.58  fof(f30,plain,(
% 1.66/0.58    v1_relat_1(sK1)),
% 1.66/0.58    inference(cnf_transformation,[],[f16])).
% 1.66/0.58  fof(f16,plain,(
% 1.66/0.58    ? [X0,X1] : ((~r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) | ~r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))) & v1_relat_1(X1))),
% 1.66/0.58    inference(ennf_transformation,[],[f15])).
% 1.66/0.58  fof(f15,negated_conjecture,(
% 1.66/0.58    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))))),
% 1.66/0.58    inference(negated_conjecture,[],[f14])).
% 1.66/0.58  fof(f14,conjecture,(
% 1.66/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_wellord1)).
% 1.66/0.58  fof(f112,plain,(
% 1.66/0.58    ( ! [X4] : (~v1_relat_1(sK1) | r1_tarski(k3_relat_1(k2_wellord1(sK1,X4)),k3_relat_1(sK1))) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f111,f88])).
% 1.66/0.58  fof(f88,plain,(
% 1.66/0.58    ( ! [X3] : (v1_relat_1(k2_wellord1(sK1,X3))) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f85,f49])).
% 1.66/0.58  fof(f49,plain,(
% 1.66/0.58    ( ! [X7] : (v1_relat_1(k7_relat_1(sK1,X7))) )),
% 1.66/0.58    inference(resolution,[],[f30,f37])).
% 1.66/0.58  fof(f37,plain,(
% 1.66/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 1.66/0.58    inference(cnf_transformation,[],[f24])).
% 1.66/0.58  fof(f24,plain,(
% 1.66/0.58    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.66/0.58    inference(ennf_transformation,[],[f6])).
% 1.66/0.58  fof(f6,axiom,(
% 1.66/0.58    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.66/0.58  fof(f85,plain,(
% 1.66/0.58    ( ! [X3] : (v1_relat_1(k2_wellord1(sK1,X3)) | ~v1_relat_1(k7_relat_1(sK1,X3))) )),
% 1.66/0.58    inference(superposition,[],[f36,f45])).
% 1.66/0.58  fof(f45,plain,(
% 1.66/0.58    ( ! [X2] : (k2_wellord1(sK1,X2) = k8_relat_1(X2,k7_relat_1(sK1,X2))) )),
% 1.66/0.58    inference(resolution,[],[f30,f33])).
% 1.66/0.58  fof(f33,plain,(
% 1.66/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))) )),
% 1.66/0.58    inference(cnf_transformation,[],[f20])).
% 1.66/0.58  fof(f20,plain,(
% 1.66/0.58    ! [X0,X1] : (k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.66/0.58    inference(ennf_transformation,[],[f13])).
% 1.66/0.58  fof(f13,axiom,(
% 1.66/0.58    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).
% 1.66/0.58  fof(f36,plain,(
% 1.66/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | v1_relat_1(k8_relat_1(X0,X1))) )),
% 1.66/0.58    inference(cnf_transformation,[],[f23])).
% 1.66/0.58  fof(f23,plain,(
% 1.66/0.58    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 1.66/0.58    inference(ennf_transformation,[],[f7])).
% 1.66/0.58  fof(f7,axiom,(
% 1.66/0.58    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 1.66/0.58  fof(f111,plain,(
% 1.66/0.58    ( ! [X4] : (~v1_relat_1(k2_wellord1(sK1,X4)) | ~v1_relat_1(sK1) | r1_tarski(k3_relat_1(k2_wellord1(sK1,X4)),k3_relat_1(sK1))) )),
% 1.66/0.58    inference(resolution,[],[f89,f31])).
% 1.66/0.58  fof(f31,plain,(
% 1.66/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | r1_tarski(k3_relat_1(X0),k3_relat_1(X1))) )),
% 1.66/0.58    inference(cnf_transformation,[],[f18])).
% 1.66/0.58  fof(f18,plain,(
% 1.66/0.58    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.66/0.58    inference(flattening,[],[f17])).
% 1.66/0.58  fof(f17,plain,(
% 1.66/0.58    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.66/0.58    inference(ennf_transformation,[],[f10])).
% 1.66/0.58  fof(f10,axiom,(
% 1.66/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 1.66/0.58  fof(f89,plain,(
% 1.66/0.58    ( ! [X1] : (r1_tarski(k2_wellord1(sK1,X1),sK1)) )),
% 1.66/0.58    inference(superposition,[],[f41,f46])).
% 1.66/0.58  fof(f46,plain,(
% 1.66/0.58    ( ! [X3] : (k2_wellord1(sK1,X3) = k3_xboole_0(sK1,k2_zfmisc_1(X3,X3))) )),
% 1.66/0.58    inference(resolution,[],[f30,f34])).
% 1.66/0.58  fof(f34,plain,(
% 1.66/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))) )),
% 1.66/0.58    inference(cnf_transformation,[],[f21])).
% 1.66/0.58  fof(f21,plain,(
% 1.66/0.58    ! [X0] : (! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) | ~v1_relat_1(X0))),
% 1.66/0.58    inference(ennf_transformation,[],[f12])).
% 1.66/0.58  fof(f12,axiom,(
% 1.66/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).
% 1.66/0.58  fof(f41,plain,(
% 1.66/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f1])).
% 1.66/0.58  fof(f1,axiom,(
% 1.66/0.58    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.66/0.58  fof(f414,plain,(
% 1.66/0.58    ~r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))),
% 1.66/0.58    inference(resolution,[],[f407,f29])).
% 1.66/0.58  fof(f29,plain,(
% 1.66/0.58    ~r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0) | ~r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))),
% 1.66/0.58    inference(cnf_transformation,[],[f16])).
% 1.66/0.58  fof(f407,plain,(
% 1.66/0.58    ( ! [X0] : (r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),X0)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f406,f88])).
% 1.66/0.58  fof(f406,plain,(
% 1.66/0.58    ( ! [X0] : (r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),X0) | ~v1_relat_1(k2_wellord1(sK1,X0))) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f405,f176])).
% 1.66/0.58  fof(f176,plain,(
% 1.66/0.58    ( ! [X1] : (r1_tarski(k1_relat_1(k2_wellord1(sK1,X1)),X1)) )),
% 1.66/0.58    inference(superposition,[],[f61,f86])).
% 1.66/0.58  fof(f86,plain,(
% 1.66/0.58    ( ! [X2] : (k2_wellord1(sK1,X2) = k7_relat_1(k8_relat_1(X2,sK1),X2)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f82,f30])).
% 1.66/0.58  fof(f82,plain,(
% 1.66/0.58    ( ! [X2] : (k2_wellord1(sK1,X2) = k7_relat_1(k8_relat_1(X2,sK1),X2) | ~v1_relat_1(sK1)) )),
% 1.66/0.58    inference(superposition,[],[f45,f35])).
% 1.66/0.58  fof(f35,plain,(
% 1.66/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))) )),
% 1.66/0.58    inference(cnf_transformation,[],[f22])).
% 1.66/0.58  fof(f22,plain,(
% 1.66/0.58    ! [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.66/0.58    inference(ennf_transformation,[],[f9])).
% 1.66/0.58  fof(f9,axiom,(
% 1.66/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).
% 1.66/0.58  fof(f61,plain,(
% 1.66/0.58    ( ! [X19,X18] : (r1_tarski(k1_relat_1(k7_relat_1(k8_relat_1(X18,sK1),X19)),X19)) )),
% 1.66/0.58    inference(resolution,[],[f48,f40])).
% 1.66/0.58  fof(f40,plain,(
% 1.66/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f28])).
% 1.66/0.58  fof(f28,plain,(
% 1.66/0.58    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.66/0.58    inference(ennf_transformation,[],[f11])).
% 1.66/0.58  fof(f11,axiom,(
% 1.66/0.58    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 1.66/0.58  fof(f48,plain,(
% 1.66/0.58    ( ! [X6] : (v1_relat_1(k8_relat_1(X6,sK1))) )),
% 1.66/0.58    inference(resolution,[],[f30,f36])).
% 1.66/0.58  fof(f405,plain,(
% 1.66/0.58    ( ! [X0] : (r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),X0) | ~r1_tarski(k1_relat_1(k2_wellord1(sK1,X0)),X0) | ~v1_relat_1(k2_wellord1(sK1,X0))) )),
% 1.66/0.58    inference(superposition,[],[f150,f32])).
% 1.66/0.58  fof(f32,plain,(
% 1.66/0.58    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 1.66/0.58    inference(cnf_transformation,[],[f19])).
% 1.66/0.58  fof(f19,plain,(
% 1.66/0.58    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.66/0.58    inference(ennf_transformation,[],[f5])).
% 1.66/0.58  fof(f5,axiom,(
% 1.66/0.58    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 1.66/0.58  fof(f150,plain,(
% 1.66/0.58    ( ! [X0,X1] : (r1_tarski(k2_xboole_0(X0,k2_relat_1(k2_wellord1(sK1,X1))),X1) | ~r1_tarski(X0,X1)) )),
% 1.66/0.58    inference(resolution,[],[f87,f38])).
% 1.66/0.58  fof(f38,plain,(
% 1.66/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f26])).
% 1.66/0.58  fof(f26,plain,(
% 1.66/0.58    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.66/0.58    inference(flattening,[],[f25])).
% 1.66/0.58  fof(f25,plain,(
% 1.66/0.58    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.66/0.58    inference(ennf_transformation,[],[f2])).
% 1.66/0.58  fof(f2,axiom,(
% 1.66/0.58    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.66/0.58  fof(f87,plain,(
% 1.66/0.58    ( ! [X2] : (r1_tarski(k2_relat_1(k2_wellord1(sK1,X2)),X2)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f84,f49])).
% 1.66/0.58  fof(f84,plain,(
% 1.66/0.58    ( ! [X2] : (r1_tarski(k2_relat_1(k2_wellord1(sK1,X2)),X2) | ~v1_relat_1(k7_relat_1(sK1,X2))) )),
% 1.66/0.58    inference(superposition,[],[f39,f45])).
% 1.66/0.58  fof(f39,plain,(
% 1.66/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f27])).
% 1.66/0.58  fof(f27,plain,(
% 1.66/0.58    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 1.66/0.58    inference(ennf_transformation,[],[f8])).
% 1.66/0.58  fof(f8,axiom,(
% 1.66/0.58    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).
% 1.66/0.58  % SZS output end Proof for theBenchmark
% 1.66/0.58  % (21967)------------------------------
% 1.66/0.58  % (21967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.58  % (21967)Termination reason: Refutation
% 1.66/0.58  
% 1.66/0.58  % (21967)Memory used [KB]: 2174
% 1.66/0.58  % (21967)Time elapsed: 0.150 s
% 1.66/0.58  % (21967)------------------------------
% 1.66/0.58  % (21967)------------------------------
% 1.66/0.58  % (21945)Success in time 0.213 s
%------------------------------------------------------------------------------
