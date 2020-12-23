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
% DateTime   : Thu Dec  3 12:53:47 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 107 expanded)
%              Number of leaves         :   12 (  23 expanded)
%              Depth                    :   13
%              Number of atoms          :  104 ( 219 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f175,plain,(
    $false ),
    inference(subsumption_resolution,[],[f168,f97])).

fof(f97,plain,(
    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f90,f56])).

fof(f56,plain,(
    sK0 = k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f30,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f30,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f90,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(superposition,[],[f82,f54])).

fof(f54,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f29,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f82,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(subsumption_resolution,[],[f81,f53])).

fof(f53,plain,(
    ! [X3] : v1_relat_1(k7_relat_1(sK1,X3)) ),
    inference(resolution,[],[f29,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k1_relat_1(k7_relat_1(sK1,X0)))
      | ~ v1_relat_1(k7_relat_1(sK1,X0)) ) ),
    inference(superposition,[],[f36,f51])).

fof(f51,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
    inference(resolution,[],[f29,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f168,plain,(
    ~ r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f148,f160])).

fof(f160,plain,(
    ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k3_xboole_0(X1,k10_relat_1(sK1,k9_relat_1(sK1,X1))) ),
    inference(superposition,[],[f150,f51])).

fof(f150,plain,(
    ! [X7] : k1_relat_1(k7_relat_1(sK1,X7)) = k10_relat_1(k7_relat_1(sK1,X7),k9_relat_1(sK1,X7)) ),
    inference(forward_demodulation,[],[f60,f52])).

fof(f52,plain,(
    ! [X2] : k2_relat_1(k7_relat_1(sK1,X2)) = k9_relat_1(sK1,X2) ),
    inference(resolution,[],[f29,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f60,plain,(
    ! [X7] : k10_relat_1(k7_relat_1(sK1,X7),k2_relat_1(k7_relat_1(sK1,X7))) = k1_relat_1(k7_relat_1(sK1,X7)) ),
    inference(resolution,[],[f53,f32])).

fof(f148,plain,(
    ! [X0] : ~ r1_tarski(sK0,k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))) ),
    inference(superposition,[],[f146,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f146,plain,(
    ! [X0] : ~ r1_tarski(sK0,k3_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0)) ),
    inference(condensation,[],[f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X1))
      | ~ r1_tarski(sK0,k3_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X1)) ) ),
    inference(resolution,[],[f139,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f139,plain,(
    ! [X6,X5] : ~ r1_tarski(k2_xboole_0(sK0,X5),k3_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X6)) ),
    inference(resolution,[],[f86,f33])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      | ~ r1_tarski(k2_xboole_0(sK0,X1),X0) ) ),
    inference(resolution,[],[f75,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f75,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | ~ r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ) ),
    inference(superposition,[],[f66,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f66,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(sK0,X0),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(resolution,[],[f31,f47])).

fof(f31,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:11:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (3116)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (3113)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (3141)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (3124)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (3117)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (3114)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (3124)Refutation not found, incomplete strategy% (3124)------------------------------
% 0.21/0.51  % (3124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3124)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (3124)Memory used [KB]: 10618
% 0.21/0.51  % (3124)Time elapsed: 0.111 s
% 0.21/0.51  % (3124)------------------------------
% 0.21/0.51  % (3124)------------------------------
% 0.21/0.52  % (3121)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (3123)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (3139)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (3120)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (3128)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (3134)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (3140)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (3118)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (3131)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (3137)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (3125)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (3127)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (3119)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (3131)Refutation not found, incomplete strategy% (3131)------------------------------
% 0.21/0.53  % (3131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3131)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3131)Memory used [KB]: 10618
% 0.21/0.53  % (3131)Time elapsed: 0.118 s
% 0.21/0.53  % (3131)------------------------------
% 0.21/0.53  % (3131)------------------------------
% 0.21/0.53  % (3122)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (3115)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (3138)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (3143)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (3136)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (3136)Refutation not found, incomplete strategy% (3136)------------------------------
% 0.21/0.54  % (3136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3136)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3136)Memory used [KB]: 10746
% 0.21/0.54  % (3136)Time elapsed: 0.106 s
% 0.21/0.54  % (3136)------------------------------
% 0.21/0.54  % (3136)------------------------------
% 0.21/0.54  % (3121)Refutation not found, incomplete strategy% (3121)------------------------------
% 0.21/0.54  % (3121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3121)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3121)Memory used [KB]: 10746
% 0.21/0.54  % (3121)Time elapsed: 0.136 s
% 0.21/0.54  % (3121)------------------------------
% 0.21/0.54  % (3121)------------------------------
% 0.21/0.54  % (3123)Refutation not found, incomplete strategy% (3123)------------------------------
% 0.21/0.54  % (3123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3123)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3123)Memory used [KB]: 10618
% 0.21/0.54  % (3123)Time elapsed: 0.137 s
% 0.21/0.54  % (3123)------------------------------
% 0.21/0.54  % (3123)------------------------------
% 0.21/0.54  % (3142)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (3133)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (3129)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (3135)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (3126)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.52/0.56  % (3132)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.52/0.56  % (3135)Refutation found. Thanks to Tanya!
% 1.52/0.56  % SZS status Theorem for theBenchmark
% 1.52/0.56  % SZS output start Proof for theBenchmark
% 1.52/0.56  fof(f175,plain,(
% 1.52/0.56    $false),
% 1.52/0.56    inference(subsumption_resolution,[],[f168,f97])).
% 1.52/0.56  fof(f97,plain,(
% 1.52/0.56    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 1.52/0.56    inference(superposition,[],[f90,f56])).
% 1.52/0.56  fof(f56,plain,(
% 1.52/0.56    sK0 = k3_xboole_0(sK0,k1_relat_1(sK1))),
% 1.52/0.56    inference(resolution,[],[f30,f39])).
% 1.52/0.56  fof(f39,plain,(
% 1.52/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.52/0.56    inference(cnf_transformation,[],[f23])).
% 1.52/0.56  fof(f23,plain,(
% 1.52/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.52/0.56    inference(ennf_transformation,[],[f7])).
% 1.52/0.56  fof(f7,axiom,(
% 1.52/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.52/0.56  fof(f30,plain,(
% 1.52/0.56    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.52/0.56    inference(cnf_transformation,[],[f17])).
% 1.52/0.56  fof(f17,plain,(
% 1.52/0.56    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.52/0.56    inference(flattening,[],[f16])).
% 1.52/0.56  fof(f16,plain,(
% 1.52/0.56    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.52/0.56    inference(ennf_transformation,[],[f15])).
% 1.52/0.56  fof(f15,negated_conjecture,(
% 1.52/0.56    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.52/0.56    inference(negated_conjecture,[],[f14])).
% 1.52/0.56  fof(f14,conjecture,(
% 1.52/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 1.52/0.56  fof(f90,plain,(
% 1.52/0.56    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 1.52/0.56    inference(superposition,[],[f82,f54])).
% 1.52/0.56  fof(f54,plain,(
% 1.52/0.56    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 1.52/0.56    inference(resolution,[],[f29,f32])).
% 1.52/0.56  fof(f32,plain,(
% 1.52/0.56    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f18])).
% 1.52/0.56  fof(f18,plain,(
% 1.52/0.56    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.52/0.56    inference(ennf_transformation,[],[f12])).
% 1.52/0.56  fof(f12,axiom,(
% 1.52/0.56    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.52/0.56  fof(f29,plain,(
% 1.52/0.56    v1_relat_1(sK1)),
% 1.52/0.56    inference(cnf_transformation,[],[f17])).
% 1.52/0.56  fof(f82,plain,(
% 1.52/0.56    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 1.52/0.56    inference(subsumption_resolution,[],[f81,f53])).
% 1.52/0.56  fof(f53,plain,(
% 1.52/0.56    ( ! [X3] : (v1_relat_1(k7_relat_1(sK1,X3))) )),
% 1.52/0.56    inference(resolution,[],[f29,f35])).
% 1.52/0.56  fof(f35,plain,(
% 1.52/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 1.52/0.56    inference(cnf_transformation,[],[f19])).
% 1.52/0.56  fof(f19,plain,(
% 1.52/0.56    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.52/0.56    inference(ennf_transformation,[],[f9])).
% 1.52/0.56  fof(f9,axiom,(
% 1.52/0.56    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.52/0.56  fof(f81,plain,(
% 1.52/0.56    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k1_relat_1(k7_relat_1(sK1,X0))) | ~v1_relat_1(k7_relat_1(sK1,X0))) )),
% 1.52/0.56    inference(superposition,[],[f36,f51])).
% 1.52/0.56  fof(f51,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1))) )),
% 1.52/0.56    inference(resolution,[],[f29,f46])).
% 1.52/0.56  fof(f46,plain,(
% 1.52/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 1.52/0.56    inference(cnf_transformation,[],[f25])).
% 1.52/0.56  fof(f25,plain,(
% 1.52/0.56    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.52/0.56    inference(ennf_transformation,[],[f13])).
% 1.52/0.56  fof(f13,axiom,(
% 1.52/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 1.52/0.56  fof(f36,plain,(
% 1.52/0.56    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f20])).
% 1.52/0.56  fof(f20,plain,(
% 1.52/0.56    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.52/0.56    inference(ennf_transformation,[],[f11])).
% 1.52/0.56  fof(f11,axiom,(
% 1.52/0.56    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 1.52/0.56  fof(f168,plain,(
% 1.52/0.56    ~r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 1.52/0.56    inference(superposition,[],[f148,f160])).
% 1.52/0.56  fof(f160,plain,(
% 1.52/0.56    ( ! [X1] : (k1_relat_1(k7_relat_1(sK1,X1)) = k3_xboole_0(X1,k10_relat_1(sK1,k9_relat_1(sK1,X1)))) )),
% 1.52/0.56    inference(superposition,[],[f150,f51])).
% 1.52/0.56  fof(f150,plain,(
% 1.52/0.56    ( ! [X7] : (k1_relat_1(k7_relat_1(sK1,X7)) = k10_relat_1(k7_relat_1(sK1,X7),k9_relat_1(sK1,X7))) )),
% 1.52/0.56    inference(forward_demodulation,[],[f60,f52])).
% 1.52/0.56  fof(f52,plain,(
% 1.52/0.56    ( ! [X2] : (k2_relat_1(k7_relat_1(sK1,X2)) = k9_relat_1(sK1,X2)) )),
% 1.52/0.56    inference(resolution,[],[f29,f37])).
% 1.52/0.56  fof(f37,plain,(
% 1.52/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f21])).
% 1.52/0.56  fof(f21,plain,(
% 1.52/0.56    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.52/0.56    inference(ennf_transformation,[],[f10])).
% 1.52/0.56  fof(f10,axiom,(
% 1.52/0.56    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.52/0.56  fof(f60,plain,(
% 1.52/0.56    ( ! [X7] : (k10_relat_1(k7_relat_1(sK1,X7),k2_relat_1(k7_relat_1(sK1,X7))) = k1_relat_1(k7_relat_1(sK1,X7))) )),
% 1.52/0.56    inference(resolution,[],[f53,f32])).
% 1.52/0.56  fof(f148,plain,(
% 1.52/0.56    ( ! [X0] : (~r1_tarski(sK0,k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))))) )),
% 1.52/0.56    inference(superposition,[],[f146,f34])).
% 1.52/0.56  fof(f34,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f1])).
% 1.52/0.56  fof(f1,axiom,(
% 1.52/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.52/0.56  fof(f146,plain,(
% 1.52/0.56    ( ! [X0] : (~r1_tarski(sK0,k3_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0))) )),
% 1.52/0.56    inference(condensation,[],[f141])).
% 1.52/0.56  fof(f141,plain,(
% 1.52/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k3_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X1)) | ~r1_tarski(sK0,k3_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X1))) )),
% 1.52/0.56    inference(resolution,[],[f139,f48])).
% 1.52/0.56  fof(f48,plain,(
% 1.52/0.56    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f28])).
% 1.52/0.56  fof(f28,plain,(
% 1.52/0.56    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.52/0.56    inference(flattening,[],[f27])).
% 1.52/0.56  fof(f27,plain,(
% 1.52/0.56    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.52/0.56    inference(ennf_transformation,[],[f8])).
% 1.52/0.56  fof(f8,axiom,(
% 1.52/0.56    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.52/0.56  fof(f139,plain,(
% 1.52/0.56    ( ! [X6,X5] : (~r1_tarski(k2_xboole_0(sK0,X5),k3_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X6))) )),
% 1.52/0.56    inference(resolution,[],[f86,f33])).
% 1.52/0.56  fof(f33,plain,(
% 1.52/0.56    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f6])).
% 1.52/0.56  fof(f6,axiom,(
% 1.52/0.56    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.52/0.56  fof(f86,plain,(
% 1.52/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | ~r1_tarski(k2_xboole_0(sK0,X1),X0)) )),
% 1.52/0.56    inference(resolution,[],[f75,f47])).
% 1.52/0.56  fof(f47,plain,(
% 1.52/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f26])).
% 1.52/0.56  fof(f26,plain,(
% 1.52/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.52/0.56    inference(ennf_transformation,[],[f4])).
% 1.52/0.56  fof(f4,axiom,(
% 1.52/0.56    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.52/0.56  fof(f75,plain,(
% 1.52/0.56    ( ! [X0] : (~r1_tarski(sK0,X0) | ~r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))) )),
% 1.52/0.56    inference(superposition,[],[f66,f38])).
% 1.52/0.56  fof(f38,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f22])).
% 1.52/0.56  fof(f22,plain,(
% 1.52/0.56    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.52/0.56    inference(ennf_transformation,[],[f5])).
% 1.52/0.56  fof(f5,axiom,(
% 1.52/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.52/0.56  fof(f66,plain,(
% 1.52/0.56    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK0,X0),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))) )),
% 1.52/0.56    inference(resolution,[],[f31,f47])).
% 1.52/0.56  fof(f31,plain,(
% 1.52/0.56    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.52/0.56    inference(cnf_transformation,[],[f17])).
% 1.52/0.56  % SZS output end Proof for theBenchmark
% 1.52/0.56  % (3135)------------------------------
% 1.52/0.56  % (3135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (3135)Termination reason: Refutation
% 1.52/0.56  
% 1.52/0.56  % (3135)Memory used [KB]: 1791
% 1.52/0.56  % (3135)Time elapsed: 0.153 s
% 1.52/0.56  % (3135)------------------------------
% 1.52/0.56  % (3135)------------------------------
% 1.52/0.56  % (3112)Success in time 0.201 s
%------------------------------------------------------------------------------
