%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 (  78 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :   17
%              Number of atoms          :   74 ( 123 expanded)
%              Number of equality atoms :   33 (  50 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1103,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1090,f23])).

fof(f23,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f1090,plain,(
    r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f42,f999])).

fof(f999,plain,(
    sK1 = k2_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f990,f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f990,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f31,f935])).

fof(f935,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f932,f27])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f932,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f869,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | ~ r1_tarski(X0,sK0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f35,f22])).

fof(f22,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f869,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(superposition,[],[f42,f563])).

fof(f563,plain,(
    sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f531,f24])).

fof(f531,plain,(
    k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f87,f186])).

fof(f186,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f185,f142])).

fof(f142,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f62,f24])).

fof(f62,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),X5) = X5 ),
    inference(resolution,[],[f33,f27])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f185,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f181,f68])).

fof(f68,plain,(
    ! [X5] : k4_xboole_0(k1_xboole_0,X5) = k4_xboole_0(X5,X5) ),
    inference(superposition,[],[f30,f39])).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f29,f24])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f181,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f30,f58])).

fof(f58,plain,(
    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f33,f21])).

fof(f21,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f87,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f31,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f42,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f25,f29])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.39  % (8042)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.20/0.41  % (8038)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.41  % (8037)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.42  % (8034)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.42  % (8039)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.43  % (8040)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.43  % (8030)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.44  % (8032)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.44  % (8036)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.44  % (8031)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.45  % (8035)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.46  % (8034)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f1103,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(subsumption_resolution,[],[f1090,f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ~r1_tarski(sK0,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.20/0.46    inference(flattening,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.46    inference(ennf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.20/0.46    inference(negated_conjecture,[],[f13])).
% 0.20/0.46  fof(f13,conjecture,(
% 0.20/0.46    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
% 0.20/0.46  fof(f1090,plain,(
% 0.20/0.46    r1_tarski(sK0,sK1)),
% 0.20/0.46    inference(superposition,[],[f42,f999])).
% 0.20/0.46  fof(f999,plain,(
% 0.20/0.46    sK1 = k2_xboole_0(sK1,sK0)),
% 0.20/0.46    inference(forward_demodulation,[],[f990,f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.46  fof(f990,plain,(
% 0.20/0.46    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0)),
% 0.20/0.46    inference(superposition,[],[f31,f935])).
% 0.20/0.46  fof(f935,plain,(
% 0.20/0.46    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f932,f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.46  fof(f932,plain,(
% 0.20/0.46    ~r1_tarski(k4_xboole_0(sK0,sK1),sK0) | k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.46    inference(resolution,[],[f869,f94])).
% 0.20/0.46  fof(f94,plain,(
% 0.20/0.46    ( ! [X0] : (~r1_tarski(X0,sK2) | ~r1_tarski(X0,sK0) | k1_xboole_0 = X0) )),
% 0.20/0.46    inference(resolution,[],[f35,f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    r1_xboole_0(sK0,sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | k1_xboole_0 = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.46    inference(flattening,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).
% 0.20/0.46  fof(f869,plain,(
% 0.20/0.46    r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 0.20/0.46    inference(superposition,[],[f42,f563])).
% 0.20/0.46  fof(f563,plain,(
% 0.20/0.46    sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 0.20/0.46    inference(forward_demodulation,[],[f531,f24])).
% 0.20/0.46  fof(f531,plain,(
% 0.20/0.46    k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK2,k1_xboole_0)),
% 0.20/0.46    inference(superposition,[],[f87,f186])).
% 0.20/0.46  fof(f186,plain,(
% 0.20/0.46    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.46    inference(forward_demodulation,[],[f185,f142])).
% 0.20/0.46  fof(f142,plain,(
% 0.20/0.46    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6)) )),
% 0.20/0.46    inference(superposition,[],[f62,f24])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),X5) = X5) )),
% 0.20/0.46    inference(resolution,[],[f33,f27])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.46  fof(f185,plain,(
% 0.20/0.46    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2))),
% 0.20/0.46    inference(forward_demodulation,[],[f181,f68])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    ( ! [X5] : (k4_xboole_0(k1_xboole_0,X5) = k4_xboole_0(X5,X5)) )),
% 0.20/0.46    inference(superposition,[],[f30,f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.20/0.46    inference(superposition,[],[f29,f24])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,axiom,(
% 0.20/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.20/0.46  fof(f181,plain,(
% 0.20/0.46    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2))),
% 0.20/0.46    inference(superposition,[],[f30,f58])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.46    inference(resolution,[],[f33,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 0.20/0.46    inference(superposition,[],[f31,f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) )),
% 0.20/0.46    inference(superposition,[],[f25,f29])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,axiom,(
% 0.20/0.46    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (8034)------------------------------
% 0.20/0.46  % (8034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (8034)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (8034)Memory used [KB]: 11257
% 0.20/0.46  % (8034)Time elapsed: 0.057 s
% 0.20/0.46  % (8034)------------------------------
% 0.20/0.46  % (8034)------------------------------
% 0.20/0.46  % (8027)Success in time 0.109 s
%------------------------------------------------------------------------------
