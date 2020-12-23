%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:52 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 440 expanded)
%              Number of leaves         :   10 ( 121 expanded)
%              Depth                    :   25
%              Number of atoms          :  117 ( 767 expanded)
%              Number of equality atoms :   63 ( 413 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f542,plain,(
    $false ),
    inference(subsumption_resolution,[],[f541,f22])).

fof(f22,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f541,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f539,f255])).

fof(f255,plain,(
    sK1 = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f247,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f247,plain,(
    sK1 = k2_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f236,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f236,plain,(
    r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f223,f38])).

fof(f38,plain,(
    r1_tarski(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f23,f19])).

fof(f19,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f223,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,k2_xboole_0(sK0,X0))
      | r1_tarski(sK2,X0) ) ),
    inference(superposition,[],[f33,f218])).

fof(f218,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f210,f54])).

fof(f54,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f46,f26])).

fof(f46,plain,(
    ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,X5),X4) = X4 ),
    inference(resolution,[],[f28,f24])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f210,plain,(
    k4_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(trivial_inequality_removal,[],[f207])).

fof(f207,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k4_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f139,f187])).

fof(f187,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f36,f20])).

fof(f20,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f30,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f139,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k4_xboole_0(X2,X3)
      | k2_xboole_0(X2,X3) = X3 ) ),
    inference(resolution,[],[f32,f28])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f539,plain,(
    sK2 = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f537,f28])).

fof(f537,plain,(
    r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f529,f39])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f23,f26])).

fof(f529,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(superposition,[],[f440,f465])).

fof(f465,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f427,f26])).

fof(f427,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK0) ),
    inference(backward_demodulation,[],[f19,f426])).

fof(f426,plain,(
    sK0 = sK3 ),
    inference(forward_demodulation,[],[f424,f386])).

fof(f386,plain,(
    sK0 = k2_xboole_0(sK0,sK3) ),
    inference(superposition,[],[f376,f26])).

fof(f376,plain,(
    sK0 = k2_xboole_0(sK3,sK0) ),
    inference(resolution,[],[f366,f28])).

fof(f366,plain,(
    r1_tarski(sK3,sK0) ),
    inference(resolution,[],[f278,f41])).

fof(f41,plain,(
    r1_tarski(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f39,f19])).

fof(f278,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK3,k2_xboole_0(X0,sK1))
      | r1_tarski(sK3,X0) ) ),
    inference(superposition,[],[f230,f26])).

fof(f230,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK3,k2_xboole_0(sK1,X0))
      | r1_tarski(sK3,X0) ) ),
    inference(superposition,[],[f33,f220])).

fof(f220,plain,(
    sK3 = k4_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f209,f54])).

fof(f209,plain,(
    k4_xboole_0(sK3,sK1) = k2_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(trivial_inequality_removal,[],[f208])).

fof(f208,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k4_xboole_0(sK3,sK1) = k2_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f139,f188])).

fof(f188,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f36,f21])).

fof(f21,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f424,plain,(
    sK3 = k2_xboole_0(sK0,sK3) ),
    inference(resolution,[],[f422,f28])).

fof(f422,plain,(
    r1_tarski(sK0,sK3) ),
    inference(subsumption_resolution,[],[f412,f23])).

fof(f412,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK0,sK1))
    | r1_tarski(sK0,sK3) ),
    inference(superposition,[],[f344,f19])).

fof(f344,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,k2_xboole_0(sK2,X0))
      | r1_tarski(sK0,X0) ) ),
    inference(superposition,[],[f33,f341])).

fof(f341,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f340,f54])).

fof(f340,plain,(
    k4_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(trivial_inequality_removal,[],[f339])).

fof(f339,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k4_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f139,f327])).

fof(f327,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f302,f67])).

fof(f67,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(X4,X4) ),
    inference(resolution,[],[f31,f56])).

fof(f56,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f39,f46])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f302,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[],[f35,f218])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f25,f27,f27])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f440,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,k2_xboole_0(sK0,X0))
      | r1_tarski(sK1,X0) ) ),
    inference(backward_demodulation,[],[f360,f426])).

fof(f360,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | ~ r1_tarski(sK1,k2_xboole_0(sK3,X0)) ) ),
    inference(superposition,[],[f33,f357])).

fof(f357,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f356,f54])).

fof(f356,plain,(
    k4_xboole_0(sK1,sK3) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(trivial_inequality_removal,[],[f355])).

fof(f355,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k4_xboole_0(sK1,sK3) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f139,f328])).

fof(f328,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f303,f67])).

fof(f303,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[],[f35,f220])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:15:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (6558)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (6571)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (6579)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (6563)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (6576)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (6556)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (6581)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (6569)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (6573)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (6580)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (6577)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (6555)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.56  % (6568)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (6564)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (6578)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (6565)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (6560)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.56  % (6561)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (6572)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (6557)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.51/0.56  % (6574)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.51/0.57  % (6562)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.51/0.57  % (6576)Refutation not found, incomplete strategy% (6576)------------------------------
% 1.51/0.57  % (6576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (6576)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.57  
% 1.51/0.57  % (6576)Memory used [KB]: 10746
% 1.51/0.57  % (6576)Time elapsed: 0.140 s
% 1.51/0.57  % (6576)------------------------------
% 1.51/0.57  % (6576)------------------------------
% 1.51/0.57  % (6575)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.51/0.57  % (6566)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.51/0.57  % (6559)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.51/0.57  % (6567)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.51/0.57  % (6554)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.51/0.57  % (6583)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.51/0.58  % (6570)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.51/0.58  % (6582)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.62/0.58  % (6560)Refutation found. Thanks to Tanya!
% 1.62/0.58  % SZS status Theorem for theBenchmark
% 1.62/0.58  % SZS output start Proof for theBenchmark
% 1.62/0.58  fof(f542,plain,(
% 1.62/0.58    $false),
% 1.62/0.58    inference(subsumption_resolution,[],[f541,f22])).
% 1.62/0.58  fof(f22,plain,(
% 1.62/0.58    sK1 != sK2),
% 1.62/0.58    inference(cnf_transformation,[],[f14])).
% 1.62/0.58  fof(f14,plain,(
% 1.62/0.58    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 1.62/0.58    inference(flattening,[],[f13])).
% 1.62/0.58  fof(f13,plain,(
% 1.62/0.58    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 1.62/0.58    inference(ennf_transformation,[],[f12])).
% 1.62/0.58  fof(f12,negated_conjecture,(
% 1.62/0.58    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.62/0.58    inference(negated_conjecture,[],[f11])).
% 1.62/0.58  fof(f11,conjecture,(
% 1.62/0.58    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 1.62/0.58  fof(f541,plain,(
% 1.62/0.58    sK1 = sK2),
% 1.62/0.58    inference(forward_demodulation,[],[f539,f255])).
% 1.62/0.58  fof(f255,plain,(
% 1.62/0.58    sK1 = k2_xboole_0(sK1,sK2)),
% 1.62/0.58    inference(superposition,[],[f247,f26])).
% 1.62/0.58  fof(f26,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f1])).
% 1.62/0.58  fof(f1,axiom,(
% 1.62/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.62/0.58  fof(f247,plain,(
% 1.62/0.58    sK1 = k2_xboole_0(sK2,sK1)),
% 1.62/0.58    inference(resolution,[],[f236,f28])).
% 1.62/0.58  fof(f28,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.62/0.58    inference(cnf_transformation,[],[f15])).
% 1.62/0.58  fof(f15,plain,(
% 1.62/0.58    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.62/0.58    inference(ennf_transformation,[],[f5])).
% 1.62/0.58  fof(f5,axiom,(
% 1.62/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.62/0.58  fof(f236,plain,(
% 1.62/0.58    r1_tarski(sK2,sK1)),
% 1.62/0.58    inference(resolution,[],[f223,f38])).
% 1.62/0.58  fof(f38,plain,(
% 1.62/0.58    r1_tarski(sK2,k2_xboole_0(sK0,sK1))),
% 1.62/0.58    inference(superposition,[],[f23,f19])).
% 1.62/0.58  fof(f19,plain,(
% 1.62/0.58    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.62/0.58    inference(cnf_transformation,[],[f14])).
% 1.62/0.58  fof(f23,plain,(
% 1.62/0.58    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f10])).
% 1.62/0.58  fof(f10,axiom,(
% 1.62/0.58    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.62/0.58  fof(f223,plain,(
% 1.62/0.58    ( ! [X0] : (~r1_tarski(sK2,k2_xboole_0(sK0,X0)) | r1_tarski(sK2,X0)) )),
% 1.62/0.58    inference(superposition,[],[f33,f218])).
% 1.62/0.58  fof(f218,plain,(
% 1.62/0.58    sK2 = k4_xboole_0(sK2,sK0)),
% 1.62/0.58    inference(forward_demodulation,[],[f210,f54])).
% 1.62/0.58  fof(f54,plain,(
% 1.62/0.58    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 1.62/0.58    inference(superposition,[],[f46,f26])).
% 1.62/0.58  fof(f46,plain,(
% 1.62/0.58    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,X5),X4) = X4) )),
% 1.62/0.58    inference(resolution,[],[f28,f24])).
% 1.62/0.58  fof(f24,plain,(
% 1.62/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f6])).
% 1.62/0.58  fof(f6,axiom,(
% 1.62/0.58    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.62/0.58  fof(f210,plain,(
% 1.62/0.58    k4_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 1.62/0.58    inference(trivial_inequality_removal,[],[f207])).
% 1.62/0.58  fof(f207,plain,(
% 1.62/0.58    k1_xboole_0 != k1_xboole_0 | k4_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 1.62/0.58    inference(superposition,[],[f139,f187])).
% 1.62/0.58  fof(f187,plain,(
% 1.62/0.58    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 1.62/0.58    inference(resolution,[],[f36,f20])).
% 1.62/0.58  fof(f20,plain,(
% 1.62/0.58    r1_xboole_0(sK2,sK0)),
% 1.62/0.58    inference(cnf_transformation,[],[f14])).
% 1.62/0.58  fof(f36,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.62/0.58    inference(definition_unfolding,[],[f30,f27])).
% 1.62/0.58  fof(f27,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f8])).
% 1.62/0.58  fof(f8,axiom,(
% 1.62/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.62/0.58  fof(f30,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f3])).
% 1.62/0.58  fof(f3,axiom,(
% 1.62/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.62/0.58  fof(f139,plain,(
% 1.62/0.58    ( ! [X2,X3] : (k1_xboole_0 != k4_xboole_0(X2,X3) | k2_xboole_0(X2,X3) = X3) )),
% 1.62/0.58    inference(resolution,[],[f32,f28])).
% 1.62/0.58  fof(f32,plain,(
% 1.62/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f4])).
% 1.62/0.58  fof(f4,axiom,(
% 1.62/0.58    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.62/0.58  fof(f33,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f16])).
% 1.62/0.58  fof(f16,plain,(
% 1.62/0.58    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.62/0.58    inference(ennf_transformation,[],[f7])).
% 1.62/0.58  fof(f7,axiom,(
% 1.62/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.62/0.58  fof(f539,plain,(
% 1.62/0.58    sK2 = k2_xboole_0(sK1,sK2)),
% 1.62/0.58    inference(resolution,[],[f537,f28])).
% 1.62/0.58  fof(f537,plain,(
% 1.62/0.58    r1_tarski(sK1,sK2)),
% 1.62/0.58    inference(subsumption_resolution,[],[f529,f39])).
% 1.62/0.58  fof(f39,plain,(
% 1.62/0.58    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 1.62/0.58    inference(superposition,[],[f23,f26])).
% 1.62/0.58  fof(f529,plain,(
% 1.62/0.58    ~r1_tarski(sK1,k2_xboole_0(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 1.62/0.58    inference(superposition,[],[f440,f465])).
% 1.62/0.58  fof(f465,plain,(
% 1.62/0.58    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,sK2)),
% 1.62/0.58    inference(superposition,[],[f427,f26])).
% 1.62/0.58  fof(f427,plain,(
% 1.62/0.58    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK0)),
% 1.62/0.58    inference(backward_demodulation,[],[f19,f426])).
% 1.62/0.58  fof(f426,plain,(
% 1.62/0.58    sK0 = sK3),
% 1.62/0.58    inference(forward_demodulation,[],[f424,f386])).
% 1.62/0.58  fof(f386,plain,(
% 1.62/0.58    sK0 = k2_xboole_0(sK0,sK3)),
% 1.62/0.58    inference(superposition,[],[f376,f26])).
% 1.62/0.58  fof(f376,plain,(
% 1.62/0.58    sK0 = k2_xboole_0(sK3,sK0)),
% 1.62/0.58    inference(resolution,[],[f366,f28])).
% 1.62/0.58  fof(f366,plain,(
% 1.62/0.58    r1_tarski(sK3,sK0)),
% 1.62/0.58    inference(resolution,[],[f278,f41])).
% 1.62/0.58  fof(f41,plain,(
% 1.62/0.58    r1_tarski(sK3,k2_xboole_0(sK0,sK1))),
% 1.62/0.58    inference(superposition,[],[f39,f19])).
% 1.62/0.58  fof(f278,plain,(
% 1.62/0.58    ( ! [X0] : (~r1_tarski(sK3,k2_xboole_0(X0,sK1)) | r1_tarski(sK3,X0)) )),
% 1.62/0.58    inference(superposition,[],[f230,f26])).
% 1.62/0.58  fof(f230,plain,(
% 1.62/0.58    ( ! [X0] : (~r1_tarski(sK3,k2_xboole_0(sK1,X0)) | r1_tarski(sK3,X0)) )),
% 1.62/0.58    inference(superposition,[],[f33,f220])).
% 1.62/0.58  fof(f220,plain,(
% 1.62/0.58    sK3 = k4_xboole_0(sK3,sK1)),
% 1.62/0.58    inference(forward_demodulation,[],[f209,f54])).
% 1.62/0.58  fof(f209,plain,(
% 1.62/0.58    k4_xboole_0(sK3,sK1) = k2_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 1.62/0.58    inference(trivial_inequality_removal,[],[f208])).
% 1.62/0.58  fof(f208,plain,(
% 1.62/0.58    k1_xboole_0 != k1_xboole_0 | k4_xboole_0(sK3,sK1) = k2_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 1.62/0.58    inference(superposition,[],[f139,f188])).
% 1.62/0.58  fof(f188,plain,(
% 1.62/0.58    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 1.62/0.58    inference(resolution,[],[f36,f21])).
% 1.62/0.58  fof(f21,plain,(
% 1.62/0.58    r1_xboole_0(sK3,sK1)),
% 1.62/0.58    inference(cnf_transformation,[],[f14])).
% 1.62/0.58  fof(f424,plain,(
% 1.62/0.58    sK3 = k2_xboole_0(sK0,sK3)),
% 1.62/0.58    inference(resolution,[],[f422,f28])).
% 1.62/0.58  fof(f422,plain,(
% 1.62/0.58    r1_tarski(sK0,sK3)),
% 1.62/0.58    inference(subsumption_resolution,[],[f412,f23])).
% 1.62/0.58  fof(f412,plain,(
% 1.62/0.58    ~r1_tarski(sK0,k2_xboole_0(sK0,sK1)) | r1_tarski(sK0,sK3)),
% 1.62/0.58    inference(superposition,[],[f344,f19])).
% 1.62/0.58  fof(f344,plain,(
% 1.62/0.58    ( ! [X0] : (~r1_tarski(sK0,k2_xboole_0(sK2,X0)) | r1_tarski(sK0,X0)) )),
% 1.62/0.58    inference(superposition,[],[f33,f341])).
% 1.62/0.58  fof(f341,plain,(
% 1.62/0.58    sK0 = k4_xboole_0(sK0,sK2)),
% 1.62/0.58    inference(forward_demodulation,[],[f340,f54])).
% 1.62/0.58  fof(f340,plain,(
% 1.62/0.58    k4_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.62/0.58    inference(trivial_inequality_removal,[],[f339])).
% 1.62/0.58  fof(f339,plain,(
% 1.62/0.58    k1_xboole_0 != k1_xboole_0 | k4_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.62/0.58    inference(superposition,[],[f139,f327])).
% 1.62/0.58  fof(f327,plain,(
% 1.62/0.58    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.62/0.58    inference(forward_demodulation,[],[f302,f67])).
% 1.62/0.58  fof(f67,plain,(
% 1.62/0.58    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(X4,X4)) )),
% 1.62/0.58    inference(resolution,[],[f31,f56])).
% 1.62/0.58  fof(f56,plain,(
% 1.62/0.58    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.62/0.58    inference(superposition,[],[f39,f46])).
% 1.62/0.58  fof(f31,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f4])).
% 1.62/0.58  fof(f302,plain,(
% 1.62/0.58    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,sK2)),
% 1.62/0.58    inference(superposition,[],[f35,f218])).
% 1.62/0.58  fof(f35,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.62/0.58    inference(definition_unfolding,[],[f25,f27,f27])).
% 1.62/0.58  fof(f25,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f2])).
% 1.62/0.58  fof(f2,axiom,(
% 1.62/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.62/0.58  fof(f440,plain,(
% 1.62/0.58    ( ! [X0] : (~r1_tarski(sK1,k2_xboole_0(sK0,X0)) | r1_tarski(sK1,X0)) )),
% 1.62/0.58    inference(backward_demodulation,[],[f360,f426])).
% 1.62/0.58  fof(f360,plain,(
% 1.62/0.58    ( ! [X0] : (r1_tarski(sK1,X0) | ~r1_tarski(sK1,k2_xboole_0(sK3,X0))) )),
% 1.62/0.58    inference(superposition,[],[f33,f357])).
% 1.62/0.58  fof(f357,plain,(
% 1.62/0.58    sK1 = k4_xboole_0(sK1,sK3)),
% 1.62/0.58    inference(forward_demodulation,[],[f356,f54])).
% 1.62/0.58  fof(f356,plain,(
% 1.62/0.58    k4_xboole_0(sK1,sK3) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 1.62/0.58    inference(trivial_inequality_removal,[],[f355])).
% 1.62/0.58  fof(f355,plain,(
% 1.62/0.58    k1_xboole_0 != k1_xboole_0 | k4_xboole_0(sK1,sK3) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 1.62/0.58    inference(superposition,[],[f139,f328])).
% 1.62/0.58  fof(f328,plain,(
% 1.62/0.58    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 1.62/0.58    inference(forward_demodulation,[],[f303,f67])).
% 1.62/0.58  fof(f303,plain,(
% 1.62/0.58    k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k4_xboole_0(sK3,sK3)),
% 1.62/0.58    inference(superposition,[],[f35,f220])).
% 1.62/0.58  % SZS output end Proof for theBenchmark
% 1.62/0.58  % (6560)------------------------------
% 1.62/0.58  % (6560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.58  % (6560)Termination reason: Refutation
% 1.62/0.58  
% 1.62/0.58  % (6560)Memory used [KB]: 6396
% 1.62/0.58  % (6560)Time elapsed: 0.141 s
% 1.62/0.58  % (6560)------------------------------
% 1.62/0.58  % (6560)------------------------------
% 1.62/0.59  % (6553)Success in time 0.22 s
%------------------------------------------------------------------------------
