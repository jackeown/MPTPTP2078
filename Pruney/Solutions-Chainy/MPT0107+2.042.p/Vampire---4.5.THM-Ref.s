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
% DateTime   : Thu Dec  3 12:32:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 379 expanded)
%              Number of leaves         :   14 ( 108 expanded)
%              Depth                    :   21
%              Number of atoms          :   78 ( 492 expanded)
%              Number of equality atoms :   69 ( 321 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f844,plain,(
    $false ),
    inference(subsumption_resolution,[],[f21,f830])).

fof(f830,plain,(
    ! [X17,X18] : k4_xboole_0(X17,X18) = k5_xboole_0(X17,k3_xboole_0(X17,X18)) ),
    inference(superposition,[],[f804,f399])).

fof(f399,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = X2 ),
    inference(forward_demodulation,[],[f395,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f57,f23])).

fof(f23,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f26,f42])).

fof(f42,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f31,f24])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

% (4308)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f395,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = k2_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f78,f393])).

fof(f393,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(X7,X6) ),
    inference(subsumption_resolution,[],[f379,f256])).

fof(f256,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2)) ),
    inference(backward_demodulation,[],[f232,f255])).

fof(f255,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(backward_demodulation,[],[f254,f247])).

fof(f247,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f79,f134])).

fof(f134,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(backward_demodulation,[],[f84,f133])).

fof(f133,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f126,f23])).

fof(f126,plain,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f26,f121])).

fof(f121,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f111,f47])).

fof(f47,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f46,f31])).

fof(f46,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f44,f42])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f24,f42])).

fof(f111,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f28,f76])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f27,f43])).

fof(f43,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f42,f42])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f84,plain,(
    ! [X0,X1] : k3_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f72,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[],[f27,f42])).

fof(f79,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X4,X5),X4) ),
    inference(superposition,[],[f42,f27])).

fof(f254,plain,(
    ! [X2,X1] : k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(forward_demodulation,[],[f245,f33])).

fof(f245,plain,(
    ! [X2,X1] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f28,f134])).

fof(f232,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f29,f149])).

fof(f149,plain,(
    ! [X2,X3] : k2_xboole_0(X3,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,X2) ),
    inference(forward_demodulation,[],[f143,f26])).

fof(f143,plain,(
    ! [X2,X3] : k2_xboole_0(X3,k2_xboole_0(X2,X3)) = k5_xboole_0(X3,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f26,f29])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f379,plain,(
    ! [X6,X7] :
      ( k1_xboole_0 != k4_xboole_0(k2_xboole_0(X7,X6),k2_xboole_0(X6,X7))
      | k2_xboole_0(X6,X7) = k2_xboole_0(X7,X6) ) ),
    inference(superposition,[],[f30,f256])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f78,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f26,f27])).

fof(f804,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5 ),
    inference(superposition,[],[f784,f780])).

fof(f780,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f761,f34])).

fof(f34,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f25,f23])).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f761,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f32,f22])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f784,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f780,f25])).

fof(f21,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f19])).

fof(f19,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:17:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (4307)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (4321)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (4313)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (4319)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (4314)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (4307)Refutation not found, incomplete strategy% (4307)------------------------------
% 0.22/0.53  % (4307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (4307)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (4307)Memory used [KB]: 1663
% 0.22/0.53  % (4307)Time elapsed: 0.111 s
% 0.22/0.53  % (4307)------------------------------
% 0.22/0.53  % (4307)------------------------------
% 0.22/0.54  % (4322)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (4335)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (4312)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (4316)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (4336)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (4327)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (4310)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (4327)Refutation not found, incomplete strategy% (4327)------------------------------
% 0.22/0.55  % (4327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4327)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (4327)Memory used [KB]: 10618
% 0.22/0.55  % (4327)Time elapsed: 0.126 s
% 0.22/0.55  % (4327)------------------------------
% 0.22/0.55  % (4327)------------------------------
% 0.22/0.55  % (4315)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (4330)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (4330)Refutation not found, incomplete strategy% (4330)------------------------------
% 0.22/0.55  % (4330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4330)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (4330)Memory used [KB]: 1663
% 0.22/0.55  % (4330)Time elapsed: 0.139 s
% 0.22/0.55  % (4330)------------------------------
% 0.22/0.55  % (4330)------------------------------
% 0.22/0.55  % (4315)Refutation not found, incomplete strategy% (4315)------------------------------
% 0.22/0.55  % (4315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4315)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (4315)Memory used [KB]: 10618
% 0.22/0.55  % (4315)Time elapsed: 0.130 s
% 0.22/0.55  % (4315)------------------------------
% 0.22/0.55  % (4315)------------------------------
% 0.22/0.55  % (4311)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (4309)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (4326)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (4309)Refutation not found, incomplete strategy% (4309)------------------------------
% 0.22/0.55  % (4309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4309)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (4309)Memory used [KB]: 10618
% 0.22/0.55  % (4309)Time elapsed: 0.136 s
% 0.22/0.55  % (4309)------------------------------
% 0.22/0.55  % (4309)------------------------------
% 0.22/0.56  % (4331)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (4314)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % (4324)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (4328)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (4328)Refutation not found, incomplete strategy% (4328)------------------------------
% 0.22/0.56  % (4328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (4328)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (4328)Memory used [KB]: 1663
% 0.22/0.56  % (4328)Time elapsed: 0.110 s
% 0.22/0.56  % (4328)------------------------------
% 0.22/0.56  % (4328)------------------------------
% 0.22/0.56  % (4324)Refutation not found, incomplete strategy% (4324)------------------------------
% 0.22/0.56  % (4324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (4324)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (4324)Memory used [KB]: 10618
% 0.22/0.56  % (4324)Time elapsed: 0.151 s
% 0.22/0.56  % (4324)------------------------------
% 0.22/0.56  % (4324)------------------------------
% 0.22/0.56  % (4323)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (4333)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.56  % (4334)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f844,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(subsumption_resolution,[],[f21,f830])).
% 0.22/0.57  fof(f830,plain,(
% 0.22/0.57    ( ! [X17,X18] : (k4_xboole_0(X17,X18) = k5_xboole_0(X17,k3_xboole_0(X17,X18))) )),
% 0.22/0.57    inference(superposition,[],[f804,f399])).
% 0.22/0.57  fof(f399,plain,(
% 0.22/0.57    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = X2) )),
% 0.22/0.57    inference(forward_demodulation,[],[f395,f62])).
% 0.22/0.57  fof(f62,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.57    inference(forward_demodulation,[],[f57,f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,axiom,(
% 0.22/0.57    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.57  fof(f57,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(superposition,[],[f26,f42])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.57    inference(resolution,[],[f31,f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f15])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.57    inference(unused_predicate_definition_removal,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f12])).
% 0.22/0.57  % (4308)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.57  fof(f12,axiom,(
% 0.22/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.57  fof(f395,plain,(
% 0.22/0.57    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = k2_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 0.22/0.57    inference(backward_demodulation,[],[f78,f393])).
% 0.22/0.57  fof(f393,plain,(
% 0.22/0.57    ( ! [X6,X7] : (k2_xboole_0(X6,X7) = k2_xboole_0(X7,X6)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f379,f256])).
% 0.22/0.57  fof(f256,plain,(
% 0.22/0.57    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2))) )),
% 0.22/0.57    inference(backward_demodulation,[],[f232,f255])).
% 0.22/0.57  fof(f255,plain,(
% 0.22/0.57    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 0.22/0.57    inference(backward_demodulation,[],[f254,f247])).
% 0.22/0.57  fof(f247,plain,(
% 0.22/0.57    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6))) )),
% 0.22/0.57    inference(superposition,[],[f79,f134])).
% 0.22/0.57  fof(f134,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.57    inference(backward_demodulation,[],[f84,f133])).
% 0.22/0.57  fof(f133,plain,(
% 0.22/0.57    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 0.22/0.57    inference(forward_demodulation,[],[f126,f23])).
% 0.22/0.57  fof(f126,plain,(
% 0.22/0.57    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,k1_xboole_0)) )),
% 0.22/0.57    inference(superposition,[],[f26,f121])).
% 0.22/0.57  fof(f121,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.57    inference(forward_demodulation,[],[f111,f47])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.57    inference(resolution,[],[f46,f31])).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.22/0.57    inference(superposition,[],[f44,f42])).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k1_xboole_0,k4_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(superposition,[],[f24,f42])).
% 0.22/0.57  fof(f111,plain,(
% 0.22/0.57    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.57    inference(superposition,[],[f28,f76])).
% 0.22/0.57  fof(f76,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.57    inference(superposition,[],[f27,f43])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(superposition,[],[f42,f42])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.57  fof(f84,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k3_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0))) )),
% 0.22/0.57    inference(forward_demodulation,[],[f72,f33])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.57  fof(f72,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k3_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) )),
% 0.22/0.57    inference(superposition,[],[f27,f42])).
% 0.22/0.57  fof(f79,plain,(
% 0.22/0.57    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X4,X5),X4)) )),
% 0.22/0.57    inference(superposition,[],[f42,f27])).
% 0.22/0.57  fof(f254,plain,(
% 0.22/0.57    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 0.22/0.57    inference(forward_demodulation,[],[f245,f33])).
% 0.22/0.57  fof(f245,plain,(
% 0.22/0.57    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))) )),
% 0.22/0.57    inference(superposition,[],[f28,f134])).
% 0.22/0.57  fof(f232,plain,(
% 0.22/0.57    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2))) )),
% 0.22/0.57    inference(superposition,[],[f29,f149])).
% 0.22/0.57  fof(f149,plain,(
% 0.22/0.57    ( ! [X2,X3] : (k2_xboole_0(X3,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,X2)) )),
% 0.22/0.57    inference(forward_demodulation,[],[f143,f26])).
% 0.22/0.57  fof(f143,plain,(
% 0.22/0.57    ( ! [X2,X3] : (k2_xboole_0(X3,k2_xboole_0(X2,X3)) = k5_xboole_0(X3,k4_xboole_0(X2,X3))) )),
% 0.22/0.57    inference(superposition,[],[f26,f29])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.22/0.57  fof(f379,plain,(
% 0.22/0.57    ( ! [X6,X7] : (k1_xboole_0 != k4_xboole_0(k2_xboole_0(X7,X6),k2_xboole_0(X6,X7)) | k2_xboole_0(X6,X7) = k2_xboole_0(X7,X6)) )),
% 0.22/0.57    inference(superposition,[],[f30,f256])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f17])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).
% 0.22/0.57  fof(f78,plain,(
% 0.22/0.57    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3))) )),
% 0.22/0.57    inference(superposition,[],[f26,f27])).
% 0.22/0.57  fof(f804,plain,(
% 0.22/0.57    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5) )),
% 0.22/0.57    inference(superposition,[],[f784,f780])).
% 0.22/0.57  fof(f780,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.22/0.57    inference(forward_demodulation,[],[f761,f34])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.22/0.57    inference(superposition,[],[f25,f23])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.22/0.57  fof(f761,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(superposition,[],[f32,f22])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f11])).
% 0.22/0.57  fof(f11,axiom,(
% 0.22/0.57    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.22/0.57  fof(f784,plain,(
% 0.22/0.57    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 0.22/0.57    inference(superposition,[],[f780,f25])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.57    inference(cnf_transformation,[],[f20])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.57    inference(negated_conjecture,[],[f13])).
% 0.22/0.57  fof(f13,conjecture,(
% 0.22/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (4314)------------------------------
% 0.22/0.57  % (4314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (4314)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (4314)Memory used [KB]: 6780
% 0.22/0.57  % (4314)Time elapsed: 0.141 s
% 0.22/0.57  % (4314)------------------------------
% 0.22/0.57  % (4314)------------------------------
% 0.22/0.57  % (4306)Success in time 0.2 s
%------------------------------------------------------------------------------
