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
% DateTime   : Thu Dec  3 12:53:48 EST 2020

% Result     : Theorem 1.85s
% Output     : Refutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 183 expanded)
%              Number of leaves         :   12 (  39 expanded)
%              Depth                    :   16
%              Number of atoms          :  111 ( 377 expanded)
%              Number of equality atoms :   30 (  52 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1088,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1084,f67])).

fof(f67,plain,(
    ! [X8,X7] : r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK1,X7),X8)),X8) ),
    inference(resolution,[],[f60,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f60,plain,(
    ! [X5] : v1_relat_1(k7_relat_1(sK1,X5)) ),
    inference(resolution,[],[f33,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f1084,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(resolution,[],[f544,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | ~ r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ) ),
    inference(superposition,[],[f78,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f78,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(sK0,X0),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(resolution,[],[f35,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f35,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f544,plain,(
    r1_tarski(sK0,k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),k10_relat_1(sK1,k9_relat_1(sK1,sK0))))) ),
    inference(forward_demodulation,[],[f537,f142])).

fof(f142,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f139,f59])).

fof(f59,plain,(
    ! [X4] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X4)),X4) ),
    inference(resolution,[],[f33,f40])).

fof(f139,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0)
    | sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f129,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f129,plain,(
    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f121,f63])).

fof(f63,plain,(
    sK0 = k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f34,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f34,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f121,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(superposition,[],[f118,f61])).

fof(f61,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f33,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f118,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(subsumption_resolution,[],[f117,f60])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k1_relat_1(k7_relat_1(sK1,X0)))
      | ~ v1_relat_1(k7_relat_1(sK1,X0)) ) ),
    inference(superposition,[],[f39,f56])).

fof(f56,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
    inference(resolution,[],[f33,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f537,plain,(
    r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),k10_relat_1(sK1,k9_relat_1(sK1,sK0))))) ),
    inference(superposition,[],[f471,f286])).

fof(f286,plain,(
    ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k3_xboole_0(X1,k10_relat_1(sK1,k9_relat_1(sK1,X1))) ),
    inference(superposition,[],[f285,f56])).

fof(f285,plain,(
    ! [X11] : k1_relat_1(k7_relat_1(sK1,X11)) = k10_relat_1(k7_relat_1(sK1,X11),k9_relat_1(sK1,X11)) ),
    inference(forward_demodulation,[],[f69,f58])).

fof(f58,plain,(
    ! [X3] : k2_relat_1(k7_relat_1(sK1,X3)) = k9_relat_1(sK1,X3) ),
    inference(resolution,[],[f33,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f69,plain,(
    ! [X11] : k10_relat_1(k7_relat_1(sK1,X11),k2_relat_1(k7_relat_1(sK1,X11))) = k1_relat_1(k7_relat_1(sK1,X11)) ),
    inference(resolution,[],[f60,f36])).

fof(f471,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),X0))) ),
    inference(superposition,[],[f457,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f457,plain,(
    ! [X7] : r1_tarski(k3_xboole_0(X7,sK0),k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),X7))) ),
    inference(superposition,[],[f414,f63])).

fof(f414,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,k1_relat_1(sK1))),k1_relat_1(k7_relat_1(k7_relat_1(sK1,X1),X0))) ),
    inference(superposition,[],[f411,f61])).

fof(f411,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,k10_relat_1(sK1,X2))),k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1))) ),
    inference(subsumption_resolution,[],[f410,f68])).

fof(f68,plain,(
    ! [X10,X9] : v1_relat_1(k7_relat_1(k7_relat_1(sK1,X9),X10)) ),
    inference(resolution,[],[f60,f38])).

fof(f410,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,k10_relat_1(sK1,X2))),k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1)))
      | ~ v1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1)) ) ),
    inference(superposition,[],[f39,f358])).

fof(f358,plain,(
    ! [X2,X0,X1] : k10_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1),X2) = k3_xboole_0(X1,k3_xboole_0(X0,k10_relat_1(sK1,X2))) ),
    inference(forward_demodulation,[],[f64,f56])).

fof(f64,plain,(
    ! [X2,X0,X1] : k10_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1),X2) = k3_xboole_0(X1,k10_relat_1(k7_relat_1(sK1,X0),X2)) ),
    inference(resolution,[],[f60,f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:14:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (15412)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.51  % (15402)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (15404)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (15404)Refutation not found, incomplete strategy% (15404)------------------------------
% 0.22/0.52  % (15404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15420)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.52  % (15404)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (15404)Memory used [KB]: 10618
% 0.22/0.52  % (15404)Time elapsed: 0.104 s
% 0.22/0.52  % (15404)------------------------------
% 0.22/0.52  % (15404)------------------------------
% 0.22/0.53  % (15395)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (15408)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (15399)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (15414)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (15410)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (15398)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (15403)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (15397)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (15423)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (15400)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (15401)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (15415)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (15416)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (15413)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (15416)Refutation not found, incomplete strategy% (15416)------------------------------
% 0.22/0.55  % (15416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (15416)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (15416)Memory used [KB]: 10746
% 0.22/0.55  % (15416)Time elapsed: 0.100 s
% 0.22/0.55  % (15416)------------------------------
% 0.22/0.55  % (15416)------------------------------
% 0.22/0.55  % (15406)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (15419)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (15394)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (15407)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (15405)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (15396)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (15405)Refutation not found, incomplete strategy% (15405)------------------------------
% 0.22/0.56  % (15405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (15405)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (15405)Memory used [KB]: 10618
% 0.22/0.56  % (15405)Time elapsed: 0.149 s
% 0.22/0.56  % (15405)------------------------------
% 0.22/0.56  % (15405)------------------------------
% 0.22/0.56  % (15417)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (15421)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (15409)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.57  % (15418)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.57  % (15422)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.58  % (15411)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.58  % (15411)Refutation not found, incomplete strategy% (15411)------------------------------
% 0.22/0.58  % (15411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (15411)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (15411)Memory used [KB]: 10618
% 0.22/0.58  % (15411)Time elapsed: 0.166 s
% 0.22/0.58  % (15411)------------------------------
% 0.22/0.58  % (15411)------------------------------
% 1.85/0.61  % (15415)Refutation found. Thanks to Tanya!
% 1.85/0.61  % SZS status Theorem for theBenchmark
% 1.85/0.61  % SZS output start Proof for theBenchmark
% 1.85/0.61  fof(f1088,plain,(
% 1.85/0.61    $false),
% 1.85/0.61    inference(subsumption_resolution,[],[f1084,f67])).
% 1.85/0.61  fof(f67,plain,(
% 1.85/0.61    ( ! [X8,X7] : (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK1,X7),X8)),X8)) )),
% 1.85/0.61    inference(resolution,[],[f60,f40])).
% 1.85/0.61  fof(f40,plain,(
% 1.85/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f22])).
% 1.85/0.61  fof(f22,plain,(
% 1.85/0.61    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.85/0.61    inference(ennf_transformation,[],[f12])).
% 1.85/0.61  fof(f12,axiom,(
% 1.85/0.61    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 1.85/0.61  fof(f60,plain,(
% 1.85/0.61    ( ! [X5] : (v1_relat_1(k7_relat_1(sK1,X5))) )),
% 1.85/0.61    inference(resolution,[],[f33,f38])).
% 1.85/0.61  fof(f38,plain,(
% 1.85/0.61    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 1.85/0.61    inference(cnf_transformation,[],[f20])).
% 1.85/0.61  fof(f20,plain,(
% 1.85/0.61    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.85/0.61    inference(ennf_transformation,[],[f8])).
% 1.85/0.61  fof(f8,axiom,(
% 1.85/0.61    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.85/0.61  fof(f33,plain,(
% 1.85/0.61    v1_relat_1(sK1)),
% 1.85/0.61    inference(cnf_transformation,[],[f18])).
% 1.85/0.61  fof(f18,plain,(
% 1.85/0.61    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.85/0.61    inference(flattening,[],[f17])).
% 1.85/0.61  fof(f17,plain,(
% 1.85/0.61    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.85/0.61    inference(ennf_transformation,[],[f16])).
% 1.85/0.61  fof(f16,negated_conjecture,(
% 1.85/0.61    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.85/0.61    inference(negated_conjecture,[],[f15])).
% 1.85/0.61  fof(f15,conjecture,(
% 1.85/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 1.85/0.61  fof(f1084,plain,(
% 1.85/0.61    ~r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.85/0.61    inference(resolution,[],[f544,f91])).
% 1.85/0.61  fof(f91,plain,(
% 1.85/0.61    ( ! [X0] : (~r1_tarski(sK0,X0) | ~r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))) )),
% 1.85/0.61    inference(superposition,[],[f78,f43])).
% 1.85/0.61  fof(f43,plain,(
% 1.85/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f26])).
% 1.85/0.61  fof(f26,plain,(
% 1.85/0.61    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.85/0.61    inference(ennf_transformation,[],[f5])).
% 1.85/0.61  fof(f5,axiom,(
% 1.85/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.85/0.61  fof(f78,plain,(
% 1.85/0.61    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK0,X0),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))) )),
% 1.85/0.61    inference(resolution,[],[f35,f52])).
% 1.85/0.61  fof(f52,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f30])).
% 1.85/0.61  fof(f30,plain,(
% 1.85/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.85/0.61    inference(ennf_transformation,[],[f4])).
% 1.85/0.61  fof(f4,axiom,(
% 1.85/0.61    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.85/0.61  fof(f35,plain,(
% 1.85/0.61    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.85/0.61    inference(cnf_transformation,[],[f18])).
% 1.85/0.61  fof(f544,plain,(
% 1.85/0.61    r1_tarski(sK0,k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))))),
% 1.85/0.61    inference(forward_demodulation,[],[f537,f142])).
% 1.85/0.61  fof(f142,plain,(
% 1.85/0.61    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.85/0.61    inference(subsumption_resolution,[],[f139,f59])).
% 1.85/0.61  fof(f59,plain,(
% 1.85/0.61    ( ! [X4] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X4)),X4)) )),
% 1.85/0.61    inference(resolution,[],[f33,f40])).
% 1.85/0.61  fof(f139,plain,(
% 1.85/0.61    ~r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) | sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.85/0.61    inference(resolution,[],[f129,f47])).
% 1.85/0.61  fof(f47,plain,(
% 1.85/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.85/0.61    inference(cnf_transformation,[],[f3])).
% 1.85/0.61  fof(f3,axiom,(
% 1.85/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.85/0.61  fof(f129,plain,(
% 1.85/0.61    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 1.85/0.61    inference(superposition,[],[f121,f63])).
% 1.85/0.61  fof(f63,plain,(
% 1.85/0.61    sK0 = k3_xboole_0(sK0,k1_relat_1(sK1))),
% 1.85/0.61    inference(resolution,[],[f34,f44])).
% 1.85/0.61  fof(f44,plain,(
% 1.85/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.85/0.61    inference(cnf_transformation,[],[f27])).
% 1.85/0.61  fof(f27,plain,(
% 1.85/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.85/0.61    inference(ennf_transformation,[],[f6])).
% 1.85/0.61  fof(f6,axiom,(
% 1.85/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.85/0.61  fof(f34,plain,(
% 1.85/0.61    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.85/0.61    inference(cnf_transformation,[],[f18])).
% 1.85/0.61  fof(f121,plain,(
% 1.85/0.61    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 1.85/0.61    inference(superposition,[],[f118,f61])).
% 1.85/0.61  fof(f61,plain,(
% 1.85/0.61    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 1.85/0.61    inference(resolution,[],[f33,f36])).
% 1.85/0.61  fof(f36,plain,(
% 1.85/0.61    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f19])).
% 1.85/0.61  fof(f19,plain,(
% 1.85/0.61    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.85/0.61    inference(ennf_transformation,[],[f11])).
% 1.85/0.61  fof(f11,axiom,(
% 1.85/0.61    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.85/0.61  fof(f118,plain,(
% 1.85/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 1.85/0.61    inference(subsumption_resolution,[],[f117,f60])).
% 1.85/0.61  fof(f117,plain,(
% 1.85/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k1_relat_1(k7_relat_1(sK1,X0))) | ~v1_relat_1(k7_relat_1(sK1,X0))) )),
% 1.85/0.61    inference(superposition,[],[f39,f56])).
% 1.85/0.61  fof(f56,plain,(
% 1.85/0.61    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1))) )),
% 1.85/0.61    inference(resolution,[],[f33,f51])).
% 1.85/0.61  fof(f51,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 1.85/0.61    inference(cnf_transformation,[],[f29])).
% 1.85/0.61  fof(f29,plain,(
% 1.85/0.61    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.85/0.61    inference(ennf_transformation,[],[f14])).
% 1.85/0.61  fof(f14,axiom,(
% 1.85/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 1.85/0.61  fof(f39,plain,(
% 1.85/0.61    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f21])).
% 1.85/0.61  fof(f21,plain,(
% 1.85/0.61    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.85/0.61    inference(ennf_transformation,[],[f10])).
% 1.85/0.61  fof(f10,axiom,(
% 1.85/0.61    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 1.85/0.61  fof(f537,plain,(
% 1.85/0.61    r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))))),
% 1.85/0.61    inference(superposition,[],[f471,f286])).
% 1.85/0.61  fof(f286,plain,(
% 1.85/0.61    ( ! [X1] : (k1_relat_1(k7_relat_1(sK1,X1)) = k3_xboole_0(X1,k10_relat_1(sK1,k9_relat_1(sK1,X1)))) )),
% 1.85/0.61    inference(superposition,[],[f285,f56])).
% 1.85/0.61  fof(f285,plain,(
% 1.85/0.61    ( ! [X11] : (k1_relat_1(k7_relat_1(sK1,X11)) = k10_relat_1(k7_relat_1(sK1,X11),k9_relat_1(sK1,X11))) )),
% 1.85/0.61    inference(forward_demodulation,[],[f69,f58])).
% 1.85/0.61  fof(f58,plain,(
% 1.85/0.61    ( ! [X3] : (k2_relat_1(k7_relat_1(sK1,X3)) = k9_relat_1(sK1,X3)) )),
% 1.85/0.61    inference(resolution,[],[f33,f41])).
% 1.85/0.61  fof(f41,plain,(
% 1.85/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f23])).
% 1.85/0.61  fof(f23,plain,(
% 1.85/0.61    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.85/0.61    inference(ennf_transformation,[],[f9])).
% 1.85/0.61  fof(f9,axiom,(
% 1.85/0.61    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.85/0.61  fof(f69,plain,(
% 1.85/0.61    ( ! [X11] : (k10_relat_1(k7_relat_1(sK1,X11),k2_relat_1(k7_relat_1(sK1,X11))) = k1_relat_1(k7_relat_1(sK1,X11))) )),
% 1.85/0.61    inference(resolution,[],[f60,f36])).
% 1.85/0.61  fof(f471,plain,(
% 1.85/0.61    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,X0),k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),X0)))) )),
% 1.85/0.61    inference(superposition,[],[f457,f37])).
% 1.85/0.61  fof(f37,plain,(
% 1.85/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.85/0.61    inference(cnf_transformation,[],[f1])).
% 1.85/0.61  fof(f1,axiom,(
% 1.85/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.85/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.85/0.61  fof(f457,plain,(
% 1.85/0.61    ( ! [X7] : (r1_tarski(k3_xboole_0(X7,sK0),k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),X7)))) )),
% 1.85/0.61    inference(superposition,[],[f414,f63])).
% 1.85/0.61  fof(f414,plain,(
% 1.85/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,k1_relat_1(sK1))),k1_relat_1(k7_relat_1(k7_relat_1(sK1,X1),X0)))) )),
% 1.85/0.61    inference(superposition,[],[f411,f61])).
% 1.85/0.61  fof(f411,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,k10_relat_1(sK1,X2))),k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1)))) )),
% 1.85/0.61    inference(subsumption_resolution,[],[f410,f68])).
% 1.85/0.61  fof(f68,plain,(
% 1.85/0.61    ( ! [X10,X9] : (v1_relat_1(k7_relat_1(k7_relat_1(sK1,X9),X10))) )),
% 1.85/0.61    inference(resolution,[],[f60,f38])).
% 1.85/0.61  fof(f410,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,k10_relat_1(sK1,X2))),k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1))) | ~v1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1))) )),
% 1.85/0.61    inference(superposition,[],[f39,f358])).
% 1.85/0.61  fof(f358,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1),X2) = k3_xboole_0(X1,k3_xboole_0(X0,k10_relat_1(sK1,X2)))) )),
% 1.85/0.61    inference(forward_demodulation,[],[f64,f56])).
% 1.85/0.61  fof(f64,plain,(
% 1.85/0.61    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1),X2) = k3_xboole_0(X1,k10_relat_1(k7_relat_1(sK1,X0),X2))) )),
% 1.85/0.61    inference(resolution,[],[f60,f51])).
% 1.85/0.61  % SZS output end Proof for theBenchmark
% 1.85/0.61  % (15415)------------------------------
% 1.85/0.61  % (15415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.61  % (15415)Termination reason: Refutation
% 1.85/0.61  
% 1.85/0.61  % (15415)Memory used [KB]: 2174
% 1.85/0.61  % (15415)Time elapsed: 0.204 s
% 1.85/0.61  % (15415)------------------------------
% 1.85/0.61  % (15415)------------------------------
% 1.85/0.61  % (15393)Success in time 0.241 s
%------------------------------------------------------------------------------
