%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:48 EST 2020

% Result     : Theorem 1.77s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 297 expanded)
%              Number of leaves         :   12 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :  121 ( 602 expanded)
%              Number of equality atoms :   31 ( 106 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1513,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1512,f30])).

fof(f30,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f1512,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f1511,f777])).

fof(f777,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f768,f494])).

fof(f494,plain,(
    sK0 = k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f491,f382])).

fof(f382,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,k1_relat_1(k7_relat_1(sK1,X0))),X0) ),
    inference(superposition,[],[f330,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f330,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X2)),X3),X2) ),
    inference(resolution,[],[f310,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f310,plain,(
    ! [X4] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X4)),X4) ),
    inference(superposition,[],[f41,f155])).

fof(f155,plain,(
    ! [X1] : k3_xboole_0(X1,k10_relat_1(sK1,k9_relat_1(sK1,X1))) = k1_relat_1(k7_relat_1(sK1,X1)) ),
    inference(superposition,[],[f61,f50])).

fof(f50,plain,(
    ! [X4,X3] : k10_relat_1(k7_relat_1(sK1,X3),X4) = k3_xboole_0(X3,k10_relat_1(sK1,X4)) ),
    inference(resolution,[],[f28,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X4] : k1_relat_1(k7_relat_1(sK1,X4)) = k10_relat_1(k7_relat_1(sK1,X4),k9_relat_1(sK1,X4)) ),
    inference(forward_demodulation,[],[f58,f47])).

fof(f47,plain,(
    ! [X1] : k2_relat_1(k7_relat_1(sK1,X1)) = k9_relat_1(sK1,X1) ),
    inference(resolution,[],[f28,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f58,plain,(
    ! [X4] : k10_relat_1(k7_relat_1(sK1,X4),k2_relat_1(k7_relat_1(sK1,X4))) = k1_relat_1(k7_relat_1(sK1,X4)) ),
    inference(resolution,[],[f46,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f46,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f28,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f491,plain,
    ( ~ r1_tarski(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),sK0)
    | sK0 = k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(resolution,[],[f217,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f217,plain,(
    r1_tarski(sK0,k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))) ),
    inference(resolution,[],[f216,f55])).

fof(f55,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK0,X1)
      | r1_tarski(sK0,k3_xboole_0(k1_relat_1(sK1),X1)) ) ),
    inference(resolution,[],[f29,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f29,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f216,plain,(
    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f170,f52])).

fof(f52,plain,(
    sK0 = k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f29,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f170,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(superposition,[],[f157,f48])).

fof(f48,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f28,f33])).

fof(f157,plain,(
    ! [X6,X5] : r1_tarski(k3_xboole_0(X5,k10_relat_1(sK1,X6)),k1_relat_1(k7_relat_1(sK1,X5))) ),
    inference(backward_demodulation,[],[f64,f155])).

fof(f64,plain,(
    ! [X6,X5] : r1_tarski(k3_xboole_0(X5,k10_relat_1(sK1,X6)),k3_xboole_0(X5,k10_relat_1(sK1,k9_relat_1(sK1,X5)))) ),
    inference(forward_demodulation,[],[f63,f50])).

fof(f63,plain,(
    ! [X6,X5] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X5),X6),k3_xboole_0(X5,k10_relat_1(sK1,k9_relat_1(sK1,X5)))) ),
    inference(forward_demodulation,[],[f62,f47])).

fof(f62,plain,(
    ! [X6,X5] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X5),X6),k3_xboole_0(X5,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X5))))) ),
    inference(forward_demodulation,[],[f59,f50])).

fof(f59,plain,(
    ! [X6,X5] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X5),X6),k10_relat_1(k7_relat_1(sK1,X5),k2_relat_1(k7_relat_1(sK1,X5)))) ),
    inference(resolution,[],[f46,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).

fof(f768,plain,(
    k1_relat_1(k7_relat_1(sK1,sK0)) = k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f225,f155])).

fof(f225,plain,(
    ! [X1] : k3_xboole_0(sK0,X1) = k3_xboole_0(k1_relat_1(sK1),k3_xboole_0(sK0,X1)) ),
    inference(superposition,[],[f72,f43])).

fof(f72,plain,(
    ! [X0] : k3_xboole_0(sK0,X0) = k3_xboole_0(k3_xboole_0(sK0,X0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f54,f40])).

fof(f54,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f29,f36])).

fof(f1511,plain,(
    r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f1495,f124])).

fof(f124,plain,(
    ! [X1] : k10_relat_1(sK1,X1) = k3_xboole_0(k1_relat_1(sK1),k10_relat_1(sK1,X1)) ),
    inference(superposition,[],[f66,f43])).

fof(f66,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k3_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f51,f40])).

fof(f51,plain,(
    ! [X2] : r1_tarski(k10_relat_1(sK1,X2),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f49,f48])).

fof(f49,plain,(
    ! [X2] : r1_tarski(k10_relat_1(sK1,X2),k10_relat_1(sK1,k2_relat_1(sK1))) ),
    inference(resolution,[],[f28,f32])).

fof(f1495,plain,(
    r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k3_xboole_0(k1_relat_1(sK1),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))) ),
    inference(superposition,[],[f1447,f155])).

fof(f1447,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(k1_relat_1(sK1),X0)) ),
    inference(superposition,[],[f1379,f43])).

fof(f1379,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,sK0),k3_xboole_0(k1_relat_1(sK1),X0)) ),
    inference(resolution,[],[f92,f41])).

fof(f92,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k3_xboole_0(X4,sK0),X5)
      | r1_tarski(k3_xboole_0(X4,sK0),k3_xboole_0(k1_relat_1(sK1),X5)) ) ),
    inference(resolution,[],[f77,f35])).

fof(f77,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,sK0),k1_relat_1(sK1)) ),
    inference(superposition,[],[f54,f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n006.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 13:04:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (28436)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.46  % (28444)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.48  % (28433)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (28451)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (28429)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (28431)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (28432)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (28449)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (28447)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (28443)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (28437)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (28439)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (28453)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (28446)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (28434)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (28448)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (28440)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (28430)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (28454)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.53  % (28441)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (28442)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (28450)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (28435)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (28452)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % (28438)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.54  % (28445)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.77/0.61  % (28434)Refutation found. Thanks to Tanya!
% 1.77/0.61  % SZS status Theorem for theBenchmark
% 1.77/0.61  % SZS output start Proof for theBenchmark
% 1.77/0.61  fof(f1513,plain,(
% 1.77/0.61    $false),
% 1.77/0.61    inference(subsumption_resolution,[],[f1512,f30])).
% 1.77/0.61  fof(f30,plain,(
% 1.77/0.61    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.77/0.61    inference(cnf_transformation,[],[f18])).
% 1.77/0.61  fof(f18,plain,(
% 1.77/0.61    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.77/0.61    inference(flattening,[],[f17])).
% 1.77/0.61  fof(f17,plain,(
% 1.77/0.61    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.77/0.61    inference(ennf_transformation,[],[f16])).
% 1.77/0.61  fof(f16,negated_conjecture,(
% 1.77/0.61    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.77/0.61    inference(negated_conjecture,[],[f15])).
% 1.77/0.61  fof(f15,conjecture,(
% 1.77/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 1.77/0.61  fof(f1512,plain,(
% 1.77/0.61    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.77/0.61    inference(forward_demodulation,[],[f1511,f777])).
% 1.77/0.61  fof(f777,plain,(
% 1.77/0.61    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.77/0.61    inference(forward_demodulation,[],[f768,f494])).
% 1.77/0.61  fof(f494,plain,(
% 1.77/0.61    sK0 = k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 1.77/0.61    inference(subsumption_resolution,[],[f491,f382])).
% 1.77/0.61  fof(f382,plain,(
% 1.77/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,k1_relat_1(k7_relat_1(sK1,X0))),X0)) )),
% 1.77/0.61    inference(superposition,[],[f330,f43])).
% 1.77/0.61  fof(f43,plain,(
% 1.77/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f1])).
% 1.77/0.61  fof(f1,axiom,(
% 1.77/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.77/0.61  fof(f330,plain,(
% 1.77/0.61    ( ! [X2,X3] : (r1_tarski(k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X2)),X3),X2)) )),
% 1.77/0.61    inference(resolution,[],[f310,f36])).
% 1.77/0.61  fof(f36,plain,(
% 1.77/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X2),X1)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f25])).
% 1.77/0.61  fof(f25,plain,(
% 1.77/0.61    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 1.77/0.61    inference(ennf_transformation,[],[f3])).
% 1.77/0.61  fof(f3,axiom,(
% 1.77/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).
% 1.77/0.61  fof(f310,plain,(
% 1.77/0.61    ( ! [X4] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X4)),X4)) )),
% 1.77/0.61    inference(superposition,[],[f41,f155])).
% 1.77/0.61  fof(f155,plain,(
% 1.77/0.61    ( ! [X1] : (k3_xboole_0(X1,k10_relat_1(sK1,k9_relat_1(sK1,X1))) = k1_relat_1(k7_relat_1(sK1,X1))) )),
% 1.77/0.61    inference(superposition,[],[f61,f50])).
% 1.77/0.61  fof(f50,plain,(
% 1.77/0.61    ( ! [X4,X3] : (k10_relat_1(k7_relat_1(sK1,X3),X4) = k3_xboole_0(X3,k10_relat_1(sK1,X4))) )),
% 1.77/0.61    inference(resolution,[],[f28,f31])).
% 1.77/0.61  fof(f31,plain,(
% 1.77/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 1.77/0.61    inference(cnf_transformation,[],[f19])).
% 1.77/0.61  fof(f19,plain,(
% 1.77/0.61    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.77/0.61    inference(ennf_transformation,[],[f14])).
% 1.77/0.61  fof(f14,axiom,(
% 1.77/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 1.77/0.61  fof(f28,plain,(
% 1.77/0.61    v1_relat_1(sK1)),
% 1.77/0.61    inference(cnf_transformation,[],[f18])).
% 1.77/0.61  fof(f61,plain,(
% 1.77/0.61    ( ! [X4] : (k1_relat_1(k7_relat_1(sK1,X4)) = k10_relat_1(k7_relat_1(sK1,X4),k9_relat_1(sK1,X4))) )),
% 1.77/0.61    inference(forward_demodulation,[],[f58,f47])).
% 1.77/0.61  fof(f47,plain,(
% 1.77/0.61    ( ! [X1] : (k2_relat_1(k7_relat_1(sK1,X1)) = k9_relat_1(sK1,X1)) )),
% 1.77/0.61    inference(resolution,[],[f28,f34])).
% 1.77/0.61  fof(f34,plain,(
% 1.77/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f22])).
% 1.77/0.61  fof(f22,plain,(
% 1.77/0.61    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.77/0.61    inference(ennf_transformation,[],[f11])).
% 1.77/0.61  fof(f11,axiom,(
% 1.77/0.61    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.77/0.61  fof(f58,plain,(
% 1.77/0.61    ( ! [X4] : (k10_relat_1(k7_relat_1(sK1,X4),k2_relat_1(k7_relat_1(sK1,X4))) = k1_relat_1(k7_relat_1(sK1,X4))) )),
% 1.77/0.61    inference(resolution,[],[f46,f33])).
% 1.77/0.61  fof(f33,plain,(
% 1.77/0.61    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f21])).
% 1.77/0.61  fof(f21,plain,(
% 1.77/0.61    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.77/0.61    inference(ennf_transformation,[],[f12])).
% 1.77/0.61  fof(f12,axiom,(
% 1.77/0.61    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.77/0.61  fof(f46,plain,(
% 1.77/0.61    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 1.77/0.61    inference(resolution,[],[f28,f42])).
% 1.77/0.61  fof(f42,plain,(
% 1.77/0.61    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 1.77/0.61    inference(cnf_transformation,[],[f27])).
% 1.77/0.61  fof(f27,plain,(
% 1.77/0.61    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.77/0.61    inference(ennf_transformation,[],[f10])).
% 1.77/0.61  fof(f10,axiom,(
% 1.77/0.61    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.77/0.61  fof(f41,plain,(
% 1.77/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.77/0.61    inference(cnf_transformation,[],[f6])).
% 1.77/0.61  fof(f6,axiom,(
% 1.77/0.61    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.77/0.61  fof(f491,plain,(
% 1.77/0.61    ~r1_tarski(k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),sK0) | sK0 = k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 1.77/0.61    inference(resolution,[],[f217,f39])).
% 1.77/0.61  fof(f39,plain,(
% 1.77/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.77/0.61    inference(cnf_transformation,[],[f2])).
% 1.77/0.61  fof(f2,axiom,(
% 1.77/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.77/0.61  fof(f217,plain,(
% 1.77/0.61    r1_tarski(sK0,k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))))),
% 1.77/0.61    inference(resolution,[],[f216,f55])).
% 1.77/0.61  fof(f55,plain,(
% 1.77/0.61    ( ! [X1] : (~r1_tarski(sK0,X1) | r1_tarski(sK0,k3_xboole_0(k1_relat_1(sK1),X1))) )),
% 1.77/0.61    inference(resolution,[],[f29,f35])).
% 1.77/0.61  fof(f35,plain,(
% 1.77/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 1.77/0.61    inference(cnf_transformation,[],[f24])).
% 1.77/0.61  fof(f24,plain,(
% 1.77/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.77/0.61    inference(flattening,[],[f23])).
% 1.77/0.61  fof(f23,plain,(
% 1.77/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.77/0.61    inference(ennf_transformation,[],[f7])).
% 1.77/0.61  fof(f7,axiom,(
% 1.77/0.61    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.77/0.61  fof(f29,plain,(
% 1.77/0.61    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.77/0.61    inference(cnf_transformation,[],[f18])).
% 1.77/0.61  fof(f216,plain,(
% 1.77/0.61    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 1.77/0.61    inference(superposition,[],[f170,f52])).
% 1.77/0.61  fof(f52,plain,(
% 1.77/0.61    sK0 = k3_xboole_0(sK0,k1_relat_1(sK1))),
% 1.77/0.61    inference(resolution,[],[f29,f40])).
% 1.77/0.61  fof(f40,plain,(
% 1.77/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.77/0.61    inference(cnf_transformation,[],[f26])).
% 1.77/0.61  fof(f26,plain,(
% 1.77/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.77/0.61    inference(ennf_transformation,[],[f8])).
% 1.77/0.61  fof(f8,axiom,(
% 1.77/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.77/0.61  fof(f170,plain,(
% 1.77/0.61    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 1.77/0.61    inference(superposition,[],[f157,f48])).
% 1.77/0.61  fof(f48,plain,(
% 1.77/0.61    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 1.77/0.61    inference(resolution,[],[f28,f33])).
% 1.77/0.61  fof(f157,plain,(
% 1.77/0.61    ( ! [X6,X5] : (r1_tarski(k3_xboole_0(X5,k10_relat_1(sK1,X6)),k1_relat_1(k7_relat_1(sK1,X5)))) )),
% 1.77/0.61    inference(backward_demodulation,[],[f64,f155])).
% 1.77/0.61  fof(f64,plain,(
% 1.77/0.61    ( ! [X6,X5] : (r1_tarski(k3_xboole_0(X5,k10_relat_1(sK1,X6)),k3_xboole_0(X5,k10_relat_1(sK1,k9_relat_1(sK1,X5))))) )),
% 1.77/0.61    inference(forward_demodulation,[],[f63,f50])).
% 1.77/0.61  fof(f63,plain,(
% 1.77/0.61    ( ! [X6,X5] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X5),X6),k3_xboole_0(X5,k10_relat_1(sK1,k9_relat_1(sK1,X5))))) )),
% 1.77/0.61    inference(forward_demodulation,[],[f62,f47])).
% 1.77/0.61  fof(f62,plain,(
% 1.77/0.61    ( ! [X6,X5] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X5),X6),k3_xboole_0(X5,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X5)))))) )),
% 1.77/0.61    inference(forward_demodulation,[],[f59,f50])).
% 1.77/0.61  fof(f59,plain,(
% 1.77/0.61    ( ! [X6,X5] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X5),X6),k10_relat_1(k7_relat_1(sK1,X5),k2_relat_1(k7_relat_1(sK1,X5))))) )),
% 1.77/0.61    inference(resolution,[],[f46,f32])).
% 1.77/0.61  fof(f32,plain,(
% 1.77/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))) )),
% 1.77/0.61    inference(cnf_transformation,[],[f20])).
% 1.77/0.61  fof(f20,plain,(
% 1.77/0.61    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.77/0.61    inference(ennf_transformation,[],[f13])).
% 1.77/0.61  fof(f13,axiom,(
% 1.77/0.61    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 1.77/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).
% 1.77/0.61  fof(f768,plain,(
% 1.77/0.61    k1_relat_1(k7_relat_1(sK1,sK0)) = k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 1.77/0.61    inference(superposition,[],[f225,f155])).
% 1.77/0.61  fof(f225,plain,(
% 1.77/0.61    ( ! [X1] : (k3_xboole_0(sK0,X1) = k3_xboole_0(k1_relat_1(sK1),k3_xboole_0(sK0,X1))) )),
% 1.77/0.61    inference(superposition,[],[f72,f43])).
% 1.77/0.61  fof(f72,plain,(
% 1.77/0.61    ( ! [X0] : (k3_xboole_0(sK0,X0) = k3_xboole_0(k3_xboole_0(sK0,X0),k1_relat_1(sK1))) )),
% 1.77/0.61    inference(resolution,[],[f54,f40])).
% 1.77/0.61  fof(f54,plain,(
% 1.77/0.61    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,X0),k1_relat_1(sK1))) )),
% 1.77/0.61    inference(resolution,[],[f29,f36])).
% 1.77/0.61  fof(f1511,plain,(
% 1.77/0.61    r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.77/0.61    inference(forward_demodulation,[],[f1495,f124])).
% 1.77/0.61  fof(f124,plain,(
% 1.77/0.61    ( ! [X1] : (k10_relat_1(sK1,X1) = k3_xboole_0(k1_relat_1(sK1),k10_relat_1(sK1,X1))) )),
% 1.77/0.61    inference(superposition,[],[f66,f43])).
% 1.77/0.61  fof(f66,plain,(
% 1.77/0.61    ( ! [X0] : (k10_relat_1(sK1,X0) = k3_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 1.77/0.61    inference(resolution,[],[f51,f40])).
% 1.77/0.61  fof(f51,plain,(
% 1.77/0.61    ( ! [X2] : (r1_tarski(k10_relat_1(sK1,X2),k1_relat_1(sK1))) )),
% 1.77/0.61    inference(forward_demodulation,[],[f49,f48])).
% 1.77/0.61  fof(f49,plain,(
% 1.77/0.61    ( ! [X2] : (r1_tarski(k10_relat_1(sK1,X2),k10_relat_1(sK1,k2_relat_1(sK1)))) )),
% 1.77/0.61    inference(resolution,[],[f28,f32])).
% 1.77/0.61  fof(f1495,plain,(
% 1.77/0.61    r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k3_xboole_0(k1_relat_1(sK1),k10_relat_1(sK1,k9_relat_1(sK1,sK0))))),
% 1.77/0.61    inference(superposition,[],[f1447,f155])).
% 1.77/0.61  fof(f1447,plain,(
% 1.77/0.61    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(k1_relat_1(sK1),X0))) )),
% 1.77/0.61    inference(superposition,[],[f1379,f43])).
% 1.77/0.61  fof(f1379,plain,(
% 1.77/0.61    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,sK0),k3_xboole_0(k1_relat_1(sK1),X0))) )),
% 1.77/0.61    inference(resolution,[],[f92,f41])).
% 1.77/0.61  fof(f92,plain,(
% 1.77/0.61    ( ! [X4,X5] : (~r1_tarski(k3_xboole_0(X4,sK0),X5) | r1_tarski(k3_xboole_0(X4,sK0),k3_xboole_0(k1_relat_1(sK1),X5))) )),
% 1.77/0.61    inference(resolution,[],[f77,f35])).
% 1.77/0.61  fof(f77,plain,(
% 1.77/0.61    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,sK0),k1_relat_1(sK1))) )),
% 1.77/0.61    inference(superposition,[],[f54,f43])).
% 1.77/0.61  % SZS output end Proof for theBenchmark
% 1.77/0.61  % (28434)------------------------------
% 1.77/0.61  % (28434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.61  % (28434)Termination reason: Refutation
% 1.77/0.61  
% 1.77/0.61  % (28434)Memory used [KB]: 7164
% 1.77/0.61  % (28434)Time elapsed: 0.197 s
% 1.77/0.61  % (28434)------------------------------
% 1.77/0.61  % (28434)------------------------------
% 1.77/0.61  % (28428)Success in time 0.261 s
%------------------------------------------------------------------------------
