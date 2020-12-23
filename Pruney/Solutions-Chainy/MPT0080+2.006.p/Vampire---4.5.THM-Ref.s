%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:59 EST 2020

% Result     : Theorem 4.05s
% Output     : Refutation 4.05s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 457 expanded)
%              Number of leaves         :   14 ( 142 expanded)
%              Depth                    :   18
%              Number of atoms          :  104 ( 634 expanded)
%              Number of equality atoms :   52 ( 360 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10644,plain,(
    $false ),
    inference(resolution,[],[f10493,f24])).

fof(f24,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f10493,plain,(
    r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f383,f10454])).

fof(f10454,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f10393,f7625])).

fof(f7625,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(backward_demodulation,[],[f3015,f7589])).

fof(f7589,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f7544,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f7544,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f7487,f89])).

fof(f89,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(backward_demodulation,[],[f57,f88])).

fof(f88,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f86,f26])).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[],[f41,f25])).

fof(f25,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f34,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f57,plain,(
    ! [X1] : k2_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(superposition,[],[f55,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f55,plain,(
    ! [X7] : k2_xboole_0(k4_xboole_0(X7,X7),X7) = X7 ),
    inference(resolution,[],[f33,f48])).

fof(f48,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(X0,X0),X0) ),
    inference(superposition,[],[f38,f26])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f29,f32])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f7487,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X2,k2_xboole_0(X3,k1_xboole_0)),X2) ),
    inference(superposition,[],[f464,f200])).

fof(f200,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(forward_demodulation,[],[f180,f195])).

fof(f195,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f179,f88])).

fof(f179,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f120,f27])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f120,plain,(
    ! [X2,X3] : k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f36,f88])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f180,plain,(
    ! [X2,X1] : k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f120,f31])).

fof(f464,plain,(
    ! [X12,X13,X11] : r1_tarski(k4_xboole_0(X11,k2_xboole_0(X12,k4_xboole_0(X11,k2_xboole_0(X12,X13)))),X13) ),
    inference(forward_demodulation,[],[f451,f36])).

fof(f451,plain,(
    ! [X12,X13,X11] : r1_tarski(k4_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,k2_xboole_0(X12,X13))),X13) ),
    inference(superposition,[],[f383,f36])).

fof(f3015,plain,(
    k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) ),
    inference(forward_demodulation,[],[f2915,f27])).

fof(f2915,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f914,f468])).

fof(f468,plain,(
    k4_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f465,f33])).

fof(f465,plain,(
    r1_tarski(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f452,f26])).

fof(f452,plain,(
    r1_tarski(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f383,f85])).

fof(f85,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f41,f23])).

fof(f23,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f914,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f242,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f33,f28])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f242,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f37,f31])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f10393,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f7796,f8037])).

fof(f8037,plain,(
    sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f7588,f31])).

fof(f7588,plain,(
    sK2 = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    inference(resolution,[],[f7567,f33])).

fof(f7567,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(forward_demodulation,[],[f7566,f90])).

fof(f90,plain,(
    ! [X7] : k2_xboole_0(k1_xboole_0,X7) = X7 ),
    inference(backward_demodulation,[],[f55,f88])).

fof(f7566,plain,(
    r1_tarski(k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK1)),sK2) ),
    inference(forward_demodulation,[],[f7502,f31])).

fof(f7502,plain,(
    r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,k1_xboole_0)),sK2) ),
    inference(superposition,[],[f464,f207])).

fof(f207,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f187,f195])).

fof(f187,plain,(
    k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f120,f50])).

fof(f50,plain,(
    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f33,f22])).

fof(f22,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f7796,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[],[f36,f7625])).

fof(f383,plain,(
    ! [X4,X5] : r1_tarski(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4) ),
    inference(superposition,[],[f38,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f30,f32,f32])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.45  % (21746)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.45  % (21760)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.45  % (21757)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.45  % (21753)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.45  % (21752)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.46  % (21749)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.46  % (21759)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.46  % (21745)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.46  % (21751)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.46  % (21748)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.47  % (21747)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.47  % (21756)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.47  % (21750)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.48  % (21754)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.48  % (21762)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.48  % (21758)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.49  % (21755)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.50  % (21761)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 4.05/0.88  % (21746)Refutation found. Thanks to Tanya!
% 4.05/0.88  % SZS status Theorem for theBenchmark
% 4.05/0.88  % SZS output start Proof for theBenchmark
% 4.05/0.88  fof(f10644,plain,(
% 4.05/0.88    $false),
% 4.05/0.88    inference(resolution,[],[f10493,f24])).
% 4.05/0.88  fof(f24,plain,(
% 4.05/0.88    ~r1_tarski(sK0,sK1)),
% 4.05/0.88    inference(cnf_transformation,[],[f20])).
% 4.05/0.88  fof(f20,plain,(
% 4.05/0.88    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 4.05/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19])).
% 4.05/0.88  fof(f19,plain,(
% 4.05/0.88    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 4.05/0.88    introduced(choice_axiom,[])).
% 4.05/0.88  fof(f17,plain,(
% 4.05/0.88    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 4.05/0.88    inference(flattening,[],[f16])).
% 4.05/0.88  fof(f16,plain,(
% 4.05/0.88    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 4.05/0.88    inference(ennf_transformation,[],[f14])).
% 4.05/0.88  fof(f14,negated_conjecture,(
% 4.05/0.88    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 4.05/0.88    inference(negated_conjecture,[],[f13])).
% 4.05/0.88  fof(f13,conjecture,(
% 4.05/0.88    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 4.05/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
% 4.05/0.88  fof(f10493,plain,(
% 4.05/0.88    r1_tarski(sK0,sK1)),
% 4.05/0.88    inference(superposition,[],[f383,f10454])).
% 4.05/0.88  fof(f10454,plain,(
% 4.05/0.88    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 4.05/0.88    inference(forward_demodulation,[],[f10393,f7625])).
% 4.05/0.88  fof(f7625,plain,(
% 4.05/0.88    sK0 = k4_xboole_0(sK0,sK2)),
% 4.05/0.88    inference(backward_demodulation,[],[f3015,f7589])).
% 4.05/0.88  fof(f7589,plain,(
% 4.05/0.88    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 4.05/0.88    inference(resolution,[],[f7544,f33])).
% 4.05/0.88  fof(f33,plain,(
% 4.05/0.88    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 4.05/0.88    inference(cnf_transformation,[],[f18])).
% 4.05/0.88  fof(f18,plain,(
% 4.05/0.88    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.05/0.88    inference(ennf_transformation,[],[f5])).
% 4.05/0.88  fof(f5,axiom,(
% 4.05/0.88    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.05/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 4.05/0.88  fof(f7544,plain,(
% 4.05/0.88    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),X2)) )),
% 4.05/0.88    inference(forward_demodulation,[],[f7487,f89])).
% 4.05/0.88  fof(f89,plain,(
% 4.05/0.88    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 4.05/0.88    inference(backward_demodulation,[],[f57,f88])).
% 4.05/0.88  fof(f88,plain,(
% 4.05/0.88    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 4.05/0.88    inference(forward_demodulation,[],[f86,f26])).
% 4.05/0.88  fof(f26,plain,(
% 4.05/0.88    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.05/0.88    inference(cnf_transformation,[],[f7])).
% 4.05/0.88  fof(f7,axiom,(
% 4.05/0.88    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 4.05/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 4.05/0.88  fof(f86,plain,(
% 4.05/0.88    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 4.05/0.88    inference(resolution,[],[f41,f25])).
% 4.05/0.88  fof(f25,plain,(
% 4.05/0.88    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 4.05/0.88    inference(cnf_transformation,[],[f11])).
% 4.05/0.88  fof(f11,axiom,(
% 4.05/0.88    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 4.05/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 4.05/0.88  fof(f41,plain,(
% 4.05/0.88    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.05/0.88    inference(definition_unfolding,[],[f34,f32])).
% 4.05/0.88  fof(f32,plain,(
% 4.05/0.88    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.05/0.88    inference(cnf_transformation,[],[f9])).
% 4.05/0.88  fof(f9,axiom,(
% 4.05/0.88    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.05/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 4.05/0.88  fof(f34,plain,(
% 4.05/0.88    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 4.05/0.88    inference(cnf_transformation,[],[f21])).
% 4.05/0.88  fof(f21,plain,(
% 4.05/0.88    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 4.05/0.88    inference(nnf_transformation,[],[f3])).
% 4.05/0.88  fof(f3,axiom,(
% 4.05/0.88    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 4.05/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 4.05/0.88  fof(f57,plain,(
% 4.05/0.88    ( ! [X1] : (k2_xboole_0(X1,k4_xboole_0(X1,X1)) = X1) )),
% 4.05/0.88    inference(superposition,[],[f55,f31])).
% 4.05/0.88  fof(f31,plain,(
% 4.05/0.88    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.05/0.88    inference(cnf_transformation,[],[f1])).
% 4.05/0.88  fof(f1,axiom,(
% 4.05/0.88    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.05/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 4.05/0.88  fof(f55,plain,(
% 4.05/0.88    ( ! [X7] : (k2_xboole_0(k4_xboole_0(X7,X7),X7) = X7) )),
% 4.05/0.88    inference(resolution,[],[f33,f48])).
% 4.05/0.88  fof(f48,plain,(
% 4.05/0.88    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,X0),X0)) )),
% 4.05/0.88    inference(superposition,[],[f38,f26])).
% 4.05/0.88  fof(f38,plain,(
% 4.05/0.88    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 4.05/0.88    inference(definition_unfolding,[],[f29,f32])).
% 4.05/0.88  fof(f29,plain,(
% 4.05/0.88    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 4.05/0.88    inference(cnf_transformation,[],[f6])).
% 4.05/0.88  fof(f6,axiom,(
% 4.05/0.88    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 4.05/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 4.05/0.88  fof(f7487,plain,(
% 4.05/0.88    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,k2_xboole_0(X3,k1_xboole_0)),X2)) )),
% 4.05/0.88    inference(superposition,[],[f464,f200])).
% 4.05/0.88  fof(f200,plain,(
% 4.05/0.88    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 4.05/0.88    inference(forward_demodulation,[],[f180,f195])).
% 4.05/0.88  fof(f195,plain,(
% 4.05/0.88    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 4.05/0.88    inference(forward_demodulation,[],[f179,f88])).
% 4.05/0.88  fof(f179,plain,(
% 4.05/0.88    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0)) )),
% 4.05/0.88    inference(superposition,[],[f120,f27])).
% 4.05/0.88  fof(f27,plain,(
% 4.05/0.88    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 4.05/0.88    inference(cnf_transformation,[],[f15])).
% 4.05/0.88  fof(f15,plain,(
% 4.05/0.88    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 4.05/0.88    inference(rectify,[],[f4])).
% 4.05/0.88  fof(f4,axiom,(
% 4.05/0.88    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 4.05/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 4.05/0.88  fof(f120,plain,(
% 4.05/0.88    ( ! [X2,X3] : (k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 4.05/0.88    inference(superposition,[],[f36,f88])).
% 4.05/0.88  fof(f36,plain,(
% 4.05/0.88    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.05/0.88    inference(cnf_transformation,[],[f8])).
% 4.05/0.88  fof(f8,axiom,(
% 4.05/0.88    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.05/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 4.05/0.88  fof(f180,plain,(
% 4.05/0.88    ( ! [X2,X1] : (k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 4.05/0.88    inference(superposition,[],[f120,f31])).
% 4.05/0.88  fof(f464,plain,(
% 4.05/0.88    ( ! [X12,X13,X11] : (r1_tarski(k4_xboole_0(X11,k2_xboole_0(X12,k4_xboole_0(X11,k2_xboole_0(X12,X13)))),X13)) )),
% 4.05/0.88    inference(forward_demodulation,[],[f451,f36])).
% 4.05/0.88  fof(f451,plain,(
% 4.05/0.88    ( ! [X12,X13,X11] : (r1_tarski(k4_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,k2_xboole_0(X12,X13))),X13)) )),
% 4.05/0.88    inference(superposition,[],[f383,f36])).
% 4.05/0.88  fof(f3015,plain,(
% 4.05/0.88    k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0)),
% 4.05/0.88    inference(forward_demodulation,[],[f2915,f27])).
% 4.05/0.88  fof(f2915,plain,(
% 4.05/0.88    k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK2))),
% 4.05/0.88    inference(superposition,[],[f914,f468])).
% 4.05/0.88  fof(f468,plain,(
% 4.05/0.88    k4_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 4.05/0.88    inference(resolution,[],[f465,f33])).
% 4.05/0.88  fof(f465,plain,(
% 4.05/0.88    r1_tarski(sK0,k4_xboole_0(sK0,sK2))),
% 4.05/0.88    inference(forward_demodulation,[],[f452,f26])).
% 4.05/0.88  fof(f452,plain,(
% 4.05/0.88    r1_tarski(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,sK2))),
% 4.05/0.88    inference(superposition,[],[f383,f85])).
% 4.05/0.88  fof(f85,plain,(
% 4.05/0.88    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 4.05/0.88    inference(resolution,[],[f41,f23])).
% 4.05/0.88  fof(f23,plain,(
% 4.05/0.88    r1_xboole_0(sK0,sK2)),
% 4.05/0.88    inference(cnf_transformation,[],[f20])).
% 4.05/0.88  fof(f914,plain,(
% 4.05/0.88    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 4.05/0.88    inference(superposition,[],[f242,f51])).
% 4.05/0.88  fof(f51,plain,(
% 4.05/0.88    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 4.05/0.88    inference(resolution,[],[f33,f28])).
% 4.05/0.88  fof(f28,plain,(
% 4.05/0.88    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.05/0.88    inference(cnf_transformation,[],[f12])).
% 4.05/0.88  fof(f12,axiom,(
% 4.05/0.88    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.05/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 4.05/0.88  fof(f242,plain,(
% 4.05/0.88    ( ! [X6,X7,X5] : (k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6))) )),
% 4.05/0.88    inference(superposition,[],[f37,f31])).
% 4.05/0.88  fof(f37,plain,(
% 4.05/0.88    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.05/0.88    inference(cnf_transformation,[],[f10])).
% 4.05/0.88  fof(f10,axiom,(
% 4.05/0.88    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.05/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 4.05/0.88  fof(f10393,plain,(
% 4.05/0.88    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 4.05/0.88    inference(superposition,[],[f7796,f8037])).
% 4.05/0.88  fof(f8037,plain,(
% 4.05/0.88    sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 4.05/0.88    inference(superposition,[],[f7588,f31])).
% 4.05/0.88  fof(f7588,plain,(
% 4.05/0.88    sK2 = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)),
% 4.05/0.88    inference(resolution,[],[f7567,f33])).
% 4.05/0.88  fof(f7567,plain,(
% 4.05/0.88    r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 4.05/0.88    inference(forward_demodulation,[],[f7566,f90])).
% 4.05/0.88  fof(f90,plain,(
% 4.05/0.88    ( ! [X7] : (k2_xboole_0(k1_xboole_0,X7) = X7) )),
% 4.05/0.88    inference(backward_demodulation,[],[f55,f88])).
% 4.05/0.88  fof(f7566,plain,(
% 4.05/0.88    r1_tarski(k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK1)),sK2)),
% 4.05/0.88    inference(forward_demodulation,[],[f7502,f31])).
% 4.05/0.88  fof(f7502,plain,(
% 4.05/0.88    r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,k1_xboole_0)),sK2)),
% 4.05/0.88    inference(superposition,[],[f464,f207])).
% 4.05/0.88  fof(f207,plain,(
% 4.05/0.88    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 4.05/0.88    inference(forward_demodulation,[],[f187,f195])).
% 4.05/0.88  fof(f187,plain,(
% 4.05/0.88    k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 4.05/0.88    inference(superposition,[],[f120,f50])).
% 4.05/0.88  fof(f50,plain,(
% 4.05/0.88    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 4.05/0.88    inference(resolution,[],[f33,f22])).
% 4.05/0.88  fof(f22,plain,(
% 4.05/0.88    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 4.05/0.88    inference(cnf_transformation,[],[f20])).
% 4.05/0.88  fof(f7796,plain,(
% 4.05/0.88    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)) )),
% 4.05/0.88    inference(superposition,[],[f36,f7625])).
% 4.05/0.88  fof(f383,plain,(
% 4.05/0.88    ( ! [X4,X5] : (r1_tarski(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4)) )),
% 4.05/0.88    inference(superposition,[],[f38,f39])).
% 4.05/0.88  fof(f39,plain,(
% 4.05/0.88    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 4.05/0.88    inference(definition_unfolding,[],[f30,f32,f32])).
% 4.05/0.88  fof(f30,plain,(
% 4.05/0.88    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.05/0.88    inference(cnf_transformation,[],[f2])).
% 4.05/0.88  fof(f2,axiom,(
% 4.05/0.88    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.05/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 4.05/0.88  % SZS output end Proof for theBenchmark
% 4.05/0.88  % (21746)------------------------------
% 4.05/0.88  % (21746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.05/0.88  % (21746)Termination reason: Refutation
% 4.05/0.88  
% 4.05/0.88  % (21746)Memory used [KB]: 10490
% 4.05/0.88  % (21746)Time elapsed: 0.470 s
% 4.05/0.88  % (21746)------------------------------
% 4.05/0.88  % (21746)------------------------------
% 4.05/0.88  % (21744)Success in time 0.527 s
%------------------------------------------------------------------------------
