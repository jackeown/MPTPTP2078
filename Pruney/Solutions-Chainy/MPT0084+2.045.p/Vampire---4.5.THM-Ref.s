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
% DateTime   : Thu Dec  3 12:31:20 EST 2020

% Result     : Theorem 2.40s
% Output     : Refutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   60 (  87 expanded)
%              Number of leaves         :   13 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :  107 ( 160 expanded)
%              Number of equality atoms :   13 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1873,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1864,f25])).

fof(f25,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f1864,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f1789,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f1789,plain,(
    ! [X0] : r1_xboole_0(k3_xboole_0(sK0,sK1),X0) ),
    inference(resolution,[],[f1755,f1394])).

fof(f1394,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_xboole_0(sK0,X0),sK1)
      | r1_xboole_0(k3_xboole_0(sK0,X0),X1) ) ),
    inference(forward_demodulation,[],[f1387,f50])).

fof(f50,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k3_xboole_0(k3_xboole_0(X1,X2),X1) ),
    inference(resolution,[],[f33,f30])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1387,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),sK0),X1)
      | ~ r1_tarski(k3_xboole_0(sK0,X0),sK1) ) ),
    inference(superposition,[],[f985,f140])).

fof(f140,plain,(
    ! [X4] : k3_xboole_0(sK0,X4) = k3_xboole_0(k3_xboole_0(sK0,X4),sK2) ),
    inference(resolution,[],[f137,f33])).

fof(f137,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),sK2) ),
    inference(resolution,[],[f131,f30])).

fof(f131,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | r1_tarski(X0,sK2) ) ),
    inference(resolution,[],[f40,f26])).

fof(f26,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f985,plain,(
    ! [X6,X7] :
      ( r1_xboole_0(k3_xboole_0(k3_xboole_0(X6,sK2),sK0),X7)
      | ~ r1_tarski(X6,sK1) ) ),
    inference(subsumption_resolution,[],[f975,f41])).

fof(f41,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f31,f28])).

fof(f28,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f975,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,sK1)
      | ~ r1_xboole_0(k1_xboole_0,X7)
      | r1_xboole_0(k3_xboole_0(k3_xboole_0(X6,sK2),sK0),X7) ) ),
    inference(resolution,[],[f655,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f655,plain,(
    ! [X0] :
      ( r1_tarski(k3_xboole_0(k3_xboole_0(X0,sK2),sK0),k1_xboole_0)
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f376,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).

fof(f376,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k3_xboole_0(sK1,sK2))
      | r1_tarski(k3_xboole_0(X2,sK0),k1_xboole_0) ) ),
    inference(superposition,[],[f38,f66])).

fof(f66,plain,(
    k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0) ),
    inference(resolution,[],[f35,f42])).

fof(f42,plain,(
    r1_xboole_0(k3_xboole_0(sK1,sK2),sK0) ),
    inference(resolution,[],[f31,f27])).

fof(f27,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f1755,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(forward_demodulation,[],[f1754,f46])).

fof(f46,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f32,f29])).

fof(f29,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1754,plain,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)),X1) ),
    inference(forward_demodulation,[],[f1715,f46])).

fof(f1715,plain,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)),k2_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f37,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f35,f28])).

fof(f37,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:58:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (5763)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.49  % (5771)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.53  % (5757)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.44/0.55  % (5760)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.44/0.55  % (5753)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.44/0.55  % (5755)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.44/0.55  % (5761)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.44/0.55  % (5766)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.44/0.55  % (5756)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.44/0.55  % (5754)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 1.44/0.56  % (5775)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.44/0.56  % (5762)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.57/0.56  % (5758)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.57/0.56  % (5774)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.57/0.56  % (5752)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.57/0.56  % (5772)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.57/0.57  % (5769)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.57/0.57  % (5770)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.57/0.58  % (5764)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.57/0.58  % (5765)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.57/0.58  % (5773)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.57/0.58  % (5759)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.57/0.59  % (5768)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.57/0.59  % (5767)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 2.40/0.68  % (5765)Refutation found. Thanks to Tanya!
% 2.40/0.68  % SZS status Theorem for theBenchmark
% 2.40/0.68  % SZS output start Proof for theBenchmark
% 2.40/0.68  fof(f1873,plain,(
% 2.40/0.68    $false),
% 2.40/0.68    inference(subsumption_resolution,[],[f1864,f25])).
% 2.40/0.68  fof(f25,plain,(
% 2.40/0.68    ~r1_xboole_0(sK0,sK1)),
% 2.40/0.68    inference(cnf_transformation,[],[f15])).
% 2.40/0.68  fof(f15,plain,(
% 2.40/0.68    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 2.40/0.68    inference(ennf_transformation,[],[f14])).
% 2.40/0.68  fof(f14,negated_conjecture,(
% 2.40/0.68    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 2.40/0.68    inference(negated_conjecture,[],[f13])).
% 2.40/0.68  fof(f13,conjecture,(
% 2.40/0.68    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 2.40/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 2.40/0.68  fof(f1864,plain,(
% 2.40/0.68    r1_xboole_0(sK0,sK1)),
% 2.40/0.68    inference(resolution,[],[f1789,f36])).
% 2.40/0.68  fof(f36,plain,(
% 2.40/0.68    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.40/0.68    inference(cnf_transformation,[],[f19])).
% 2.40/0.68  fof(f19,plain,(
% 2.40/0.68    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 2.40/0.68    inference(ennf_transformation,[],[f12])).
% 2.40/0.68  fof(f12,axiom,(
% 2.40/0.68    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 2.40/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).
% 2.40/0.68  fof(f1789,plain,(
% 2.40/0.68    ( ! [X0] : (r1_xboole_0(k3_xboole_0(sK0,sK1),X0)) )),
% 2.40/0.68    inference(resolution,[],[f1755,f1394])).
% 2.40/0.68  fof(f1394,plain,(
% 2.40/0.68    ( ! [X0,X1] : (~r1_tarski(k3_xboole_0(sK0,X0),sK1) | r1_xboole_0(k3_xboole_0(sK0,X0),X1)) )),
% 2.40/0.68    inference(forward_demodulation,[],[f1387,f50])).
% 2.40/0.68  fof(f50,plain,(
% 2.40/0.68    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k3_xboole_0(k3_xboole_0(X1,X2),X1)) )),
% 2.40/0.68    inference(resolution,[],[f33,f30])).
% 2.40/0.68  fof(f30,plain,(
% 2.40/0.68    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.40/0.68    inference(cnf_transformation,[],[f4])).
% 2.40/0.68  fof(f4,axiom,(
% 2.40/0.68    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.40/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.40/0.68  fof(f33,plain,(
% 2.40/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.40/0.68    inference(cnf_transformation,[],[f18])).
% 2.40/0.68  fof(f18,plain,(
% 2.40/0.68    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.40/0.68    inference(ennf_transformation,[],[f7])).
% 2.40/0.68  fof(f7,axiom,(
% 2.40/0.68    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.40/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.40/0.68  fof(f1387,plain,(
% 2.40/0.68    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),sK0),X1) | ~r1_tarski(k3_xboole_0(sK0,X0),sK1)) )),
% 2.40/0.68    inference(superposition,[],[f985,f140])).
% 2.40/0.68  fof(f140,plain,(
% 2.40/0.68    ( ! [X4] : (k3_xboole_0(sK0,X4) = k3_xboole_0(k3_xboole_0(sK0,X4),sK2)) )),
% 2.40/0.68    inference(resolution,[],[f137,f33])).
% 2.40/0.68  fof(f137,plain,(
% 2.40/0.68    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,X0),sK2)) )),
% 2.40/0.68    inference(resolution,[],[f131,f30])).
% 2.40/0.68  fof(f131,plain,(
% 2.40/0.68    ( ! [X0] : (~r1_tarski(X0,sK0) | r1_tarski(X0,sK2)) )),
% 2.40/0.68    inference(resolution,[],[f40,f26])).
% 2.40/0.68  fof(f26,plain,(
% 2.40/0.68    r1_tarski(sK0,sK2)),
% 2.40/0.68    inference(cnf_transformation,[],[f15])).
% 2.40/0.68  fof(f40,plain,(
% 2.40/0.68    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 2.40/0.68    inference(cnf_transformation,[],[f24])).
% 2.40/0.68  fof(f24,plain,(
% 2.40/0.68    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.40/0.68    inference(flattening,[],[f23])).
% 2.40/0.68  fof(f23,plain,(
% 2.40/0.68    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.40/0.68    inference(ennf_transformation,[],[f5])).
% 2.40/0.68  fof(f5,axiom,(
% 2.40/0.68    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.40/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.40/0.68  fof(f985,plain,(
% 2.40/0.68    ( ! [X6,X7] : (r1_xboole_0(k3_xboole_0(k3_xboole_0(X6,sK2),sK0),X7) | ~r1_tarski(X6,sK1)) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f975,f41])).
% 2.40/0.68  fof(f41,plain,(
% 2.40/0.68    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 2.40/0.68    inference(resolution,[],[f31,f28])).
% 2.40/0.68  fof(f28,plain,(
% 2.40/0.68    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.40/0.68    inference(cnf_transformation,[],[f11])).
% 2.40/0.68  fof(f11,axiom,(
% 2.40/0.68    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.40/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.40/0.68  fof(f31,plain,(
% 2.40/0.68    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 2.40/0.68    inference(cnf_transformation,[],[f16])).
% 2.40/0.68  fof(f16,plain,(
% 2.40/0.68    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.40/0.68    inference(ennf_transformation,[],[f2])).
% 2.40/0.68  fof(f2,axiom,(
% 2.40/0.68    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.40/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.40/0.68  fof(f975,plain,(
% 2.40/0.68    ( ! [X6,X7] : (~r1_tarski(X6,sK1) | ~r1_xboole_0(k1_xboole_0,X7) | r1_xboole_0(k3_xboole_0(k3_xboole_0(X6,sK2),sK0),X7)) )),
% 2.40/0.68    inference(resolution,[],[f655,f39])).
% 2.40/0.68  fof(f39,plain,(
% 2.40/0.68    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 2.40/0.68    inference(cnf_transformation,[],[f22])).
% 2.40/0.68  fof(f22,plain,(
% 2.40/0.68    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.40/0.68    inference(flattening,[],[f21])).
% 2.40/0.68  fof(f21,plain,(
% 2.40/0.68    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.40/0.68    inference(ennf_transformation,[],[f10])).
% 2.40/0.68  fof(f10,axiom,(
% 2.40/0.68    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.40/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 2.40/0.68  fof(f655,plain,(
% 2.40/0.68    ( ! [X0] : (r1_tarski(k3_xboole_0(k3_xboole_0(X0,sK2),sK0),k1_xboole_0) | ~r1_tarski(X0,sK1)) )),
% 2.40/0.68    inference(resolution,[],[f376,f38])).
% 2.40/0.68  fof(f38,plain,(
% 2.40/0.68    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 2.40/0.68    inference(cnf_transformation,[],[f20])).
% 2.40/0.68  fof(f20,plain,(
% 2.40/0.68    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 2.40/0.68    inference(ennf_transformation,[],[f6])).
% 2.40/0.68  fof(f6,axiom,(
% 2.40/0.68    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)))),
% 2.40/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).
% 2.40/0.68  fof(f376,plain,(
% 2.40/0.68    ( ! [X2] : (~r1_tarski(X2,k3_xboole_0(sK1,sK2)) | r1_tarski(k3_xboole_0(X2,sK0),k1_xboole_0)) )),
% 2.40/0.68    inference(superposition,[],[f38,f66])).
% 2.40/0.68  fof(f66,plain,(
% 2.40/0.68    k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)),
% 2.40/0.68    inference(resolution,[],[f35,f42])).
% 2.40/0.68  fof(f42,plain,(
% 2.40/0.68    r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)),
% 2.40/0.68    inference(resolution,[],[f31,f27])).
% 2.40/0.68  fof(f27,plain,(
% 2.40/0.68    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 2.40/0.68    inference(cnf_transformation,[],[f15])).
% 2.40/0.68  fof(f35,plain,(
% 2.40/0.68    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.40/0.68    inference(cnf_transformation,[],[f1])).
% 2.40/0.68  fof(f1,axiom,(
% 2.40/0.68    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.40/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.40/0.68  fof(f1755,plain,(
% 2.40/0.68    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 2.40/0.68    inference(forward_demodulation,[],[f1754,f46])).
% 2.40/0.68  fof(f46,plain,(
% 2.40/0.68    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.40/0.68    inference(resolution,[],[f32,f29])).
% 2.40/0.68  fof(f29,plain,(
% 2.40/0.68    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.40/0.68    inference(cnf_transformation,[],[f8])).
% 2.40/0.68  fof(f8,axiom,(
% 2.40/0.68    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.40/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.40/0.68  fof(f32,plain,(
% 2.40/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.40/0.68    inference(cnf_transformation,[],[f17])).
% 2.40/0.68  fof(f17,plain,(
% 2.40/0.68    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.40/0.68    inference(ennf_transformation,[],[f3])).
% 2.40/0.68  fof(f3,axiom,(
% 2.40/0.68    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.40/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.40/0.68  fof(f1754,plain,(
% 2.40/0.68    ( ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)),X1)) )),
% 2.40/0.68    inference(forward_demodulation,[],[f1715,f46])).
% 2.40/0.68  fof(f1715,plain,(
% 2.40/0.68    ( ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)),k2_xboole_0(k1_xboole_0,X1))) )),
% 2.40/0.68    inference(superposition,[],[f37,f65])).
% 2.40/0.68  fof(f65,plain,(
% 2.40/0.68    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.40/0.68    inference(resolution,[],[f35,f28])).
% 2.40/0.68  fof(f37,plain,(
% 2.40/0.68    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 2.40/0.68    inference(cnf_transformation,[],[f9])).
% 2.40/0.68  fof(f9,axiom,(
% 2.40/0.68    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 2.40/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
% 2.40/0.68  % SZS output end Proof for theBenchmark
% 2.40/0.68  % (5765)------------------------------
% 2.40/0.68  % (5765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.40/0.68  % (5765)Termination reason: Refutation
% 2.40/0.68  
% 2.40/0.68  % (5765)Memory used [KB]: 7164
% 2.40/0.68  % (5765)Time elapsed: 0.261 s
% 2.40/0.68  % (5765)------------------------------
% 2.40/0.68  % (5765)------------------------------
% 2.40/0.68  % (5751)Success in time 0.323 s
%------------------------------------------------------------------------------
