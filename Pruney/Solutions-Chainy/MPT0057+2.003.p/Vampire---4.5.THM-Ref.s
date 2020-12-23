%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:09 EST 2020

% Result     : Theorem 2.58s
% Output     : Refutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 192 expanded)
%              Number of leaves         :   14 (  66 expanded)
%              Depth                    :   17
%              Number of atoms          :   77 ( 199 expanded)
%              Number of equality atoms :   64 ( 185 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f916,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f915])).

fof(f915,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f890,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f890,plain,(
    k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f844,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(backward_demodulation,[],[f43,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f34,f27,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f844,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f243,f843])).

fof(f843,plain,(
    ! [X35,X33,X34] : k2_xboole_0(k4_xboole_0(X33,X34),k4_xboole_0(X33,k4_xboole_0(X33,X35))) = k4_xboole_0(X33,k4_xboole_0(X34,X35)) ),
    inference(forward_demodulation,[],[f834,f607])).

fof(f607,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4))) ),
    inference(forward_demodulation,[],[f606,f51])).

fof(f51,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f25,f23])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f606,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(X2,k2_xboole_0(k1_xboole_0,k4_xboole_0(X3,X4))) ),
    inference(forward_demodulation,[],[f563,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f40,f45])).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f41,f24])).

fof(f24,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f22,f27])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f563,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X2),k4_xboole_0(X3,X4))) = k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4))) ),
    inference(superposition,[],[f47,f47])).

fof(f834,plain,(
    ! [X35,X33,X34] : k2_xboole_0(k4_xboole_0(X33,X34),k4_xboole_0(X33,k4_xboole_0(X33,X35))) = k4_xboole_0(X33,k4_xboole_0(X33,k2_xboole_0(k4_xboole_0(X33,X34),X35))) ),
    inference(superposition,[],[f483,f784])).

fof(f784,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(unit_resulting_resolution,[],[f720,f374])).

fof(f374,plain,(
    ! [X4,X3] :
      ( k2_xboole_0(X4,X3) = X3
      | ~ r1_tarski(X4,X3) ) ),
    inference(superposition,[],[f92,f25])).

fof(f92,plain,(
    ! [X2,X1] :
      ( k2_xboole_0(X2,X1) = X2
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f86,f23])).

fof(f86,plain,(
    ! [X2,X1] :
      ( k2_xboole_0(X2,X1) = k2_xboole_0(X2,k1_xboole_0)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f29,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f720,plain,(
    ! [X14,X13] : r1_tarski(k4_xboole_0(X13,X14),X13) ),
    inference(backward_demodulation,[],[f438,f719])).

fof(f719,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(forward_demodulation,[],[f718,f45])).

fof(f718,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f677,f24])).

fof(f677,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[],[f483,f91])).

fof(f91,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f85,f23])).

fof(f85,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,X0) ),
    inference(superposition,[],[f29,f46])).

fof(f438,plain,(
    ! [X14,X13] : r1_tarski(k4_xboole_0(X13,X14),k2_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X13,X14)))) ),
    inference(forward_demodulation,[],[f421,f25])).

fof(f421,plain,(
    ! [X14,X13] : r1_tarski(k4_xboole_0(X13,X14),k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X13)) ),
    inference(superposition,[],[f109,f42])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f109,plain,(
    ! [X6,X7] : r1_tarski(k4_xboole_0(X7,X6),k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f98,f29])).

fof(f98,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f65,f25])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f24,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f483,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(backward_demodulation,[],[f44,f482])).

fof(f482,plain,(
    ! [X6,X7,X5] : k4_xboole_0(k2_xboole_0(X5,X7),k2_xboole_0(X5,X6)) = k4_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f447,f51])).

fof(f447,plain,(
    ! [X6,X7,X5] : k4_xboole_0(k2_xboole_0(X5,X7),k2_xboole_0(X5,X6)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X7,k2_xboole_0(X5,X6))) ),
    inference(superposition,[],[f37,f24])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f38,f27,f27])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f243,plain,(
    k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) != k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f49,f35])).

fof(f49,plain,(
    k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) != k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f48,f25])).

fof(f48,plain,(
    k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) != k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) ),
    inference(backward_demodulation,[],[f39,f47])).

fof(f39,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(definition_unfolding,[],[f21,f27,f27,f27])).

fof(f21,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:25:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (21339)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.48  % (21346)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (21337)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (21333)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.57  % (21334)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.57  % (21353)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.57  % (21353)Refutation not found, incomplete strategy% (21353)------------------------------
% 0.21/0.57  % (21353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (21353)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (21353)Memory used [KB]: 1663
% 0.21/0.57  % (21353)Time elapsed: 0.132 s
% 0.21/0.57  % (21353)------------------------------
% 0.21/0.57  % (21353)------------------------------
% 0.21/0.57  % (21328)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.57  % (21340)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.57  % (21328)Refutation not found, incomplete strategy% (21328)------------------------------
% 0.21/0.57  % (21328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (21328)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (21328)Memory used [KB]: 1663
% 0.21/0.57  % (21328)Time elapsed: 0.157 s
% 0.21/0.57  % (21328)------------------------------
% 0.21/0.57  % (21328)------------------------------
% 0.21/0.57  % (21357)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.58  % (21345)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.58  % (21358)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.58  % (21355)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.58  % (21329)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.58  % (21348)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.58  % (21350)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.59  % (21351)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.59  % (21350)Refutation not found, incomplete strategy% (21350)------------------------------
% 0.21/0.59  % (21350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (21350)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (21350)Memory used [KB]: 10746
% 0.21/0.59  % (21350)Time elapsed: 0.179 s
% 0.21/0.59  % (21350)------------------------------
% 0.21/0.59  % (21350)------------------------------
% 0.21/0.59  % (21351)Refutation not found, incomplete strategy% (21351)------------------------------
% 0.21/0.59  % (21351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (21351)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (21351)Memory used [KB]: 1663
% 0.21/0.59  % (21351)Time elapsed: 0.181 s
% 0.21/0.59  % (21351)------------------------------
% 0.21/0.59  % (21351)------------------------------
% 0.21/0.59  % (21342)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.59  % (21343)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.60  % (21338)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.60  % (21338)Refutation not found, incomplete strategy% (21338)------------------------------
% 0.21/0.60  % (21338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (21338)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (21338)Memory used [KB]: 10618
% 0.21/0.60  % (21338)Time elapsed: 0.177 s
% 0.21/0.60  % (21338)------------------------------
% 0.21/0.60  % (21338)------------------------------
% 0.21/0.61  % (21354)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.61  % (21335)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.93/0.62  % (21347)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.93/0.62  % (21330)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.93/0.62  % (21331)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.93/0.62  % (21330)Refutation not found, incomplete strategy% (21330)------------------------------
% 1.93/0.62  % (21330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.62  % (21330)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.62  
% 1.93/0.62  % (21330)Memory used [KB]: 10618
% 1.93/0.62  % (21330)Time elapsed: 0.197 s
% 1.93/0.62  % (21330)------------------------------
% 1.93/0.62  % (21330)------------------------------
% 1.93/0.62  % (21349)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.93/0.62  % (21352)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.93/0.63  % (21341)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.93/0.63  % (21356)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.93/0.63  % (21352)Refutation not found, incomplete strategy% (21352)------------------------------
% 1.93/0.63  % (21352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.63  % (21352)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.63  
% 1.93/0.63  % (21352)Memory used [KB]: 10746
% 1.93/0.63  % (21352)Time elapsed: 0.196 s
% 1.93/0.63  % (21352)------------------------------
% 1.93/0.63  % (21352)------------------------------
% 1.93/0.63  % (21360)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 2.10/0.64  % (21347)Refutation not found, incomplete strategy% (21347)------------------------------
% 2.10/0.64  % (21347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.64  % (21347)Termination reason: Refutation not found, incomplete strategy
% 2.10/0.64  
% 2.10/0.64  % (21347)Memory used [KB]: 10618
% 2.10/0.64  % (21347)Time elapsed: 0.208 s
% 2.10/0.64  % (21347)------------------------------
% 2.10/0.64  % (21347)------------------------------
% 2.13/0.64  % (21344)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 2.58/0.71  % (21354)Refutation found. Thanks to Tanya!
% 2.58/0.71  % SZS status Theorem for theBenchmark
% 2.58/0.71  % SZS output start Proof for theBenchmark
% 2.58/0.71  fof(f916,plain,(
% 2.58/0.71    $false),
% 2.58/0.71    inference(trivial_inequality_removal,[],[f915])).
% 2.58/0.71  fof(f915,plain,(
% 2.58/0.71    k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)))),
% 2.58/0.71    inference(forward_demodulation,[],[f890,f25])).
% 2.58/0.71  fof(f25,plain,(
% 2.58/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.58/0.71    inference(cnf_transformation,[],[f1])).
% 2.58/0.71  fof(f1,axiom,(
% 2.58/0.71    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.58/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.58/0.71  fof(f890,plain,(
% 2.58/0.71    k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)))),
% 2.58/0.71    inference(superposition,[],[f844,f47])).
% 2.58/0.71  fof(f47,plain,(
% 2.58/0.71    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 2.58/0.71    inference(backward_demodulation,[],[f43,f35])).
% 2.58/0.71  fof(f35,plain,(
% 2.58/0.71    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.58/0.71    inference(cnf_transformation,[],[f9])).
% 2.58/0.71  fof(f9,axiom,(
% 2.58/0.71    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.58/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.58/0.71  fof(f43,plain,(
% 2.58/0.71    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 2.58/0.71    inference(definition_unfolding,[],[f34,f27,f27])).
% 2.58/0.71  fof(f27,plain,(
% 2.58/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.58/0.71    inference(cnf_transformation,[],[f13])).
% 2.58/0.71  fof(f13,axiom,(
% 2.58/0.71    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.58/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.58/0.71  fof(f34,plain,(
% 2.58/0.71    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.58/0.71    inference(cnf_transformation,[],[f14])).
% 2.58/0.71  fof(f14,axiom,(
% 2.58/0.71    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.58/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 2.58/0.71  fof(f844,plain,(
% 2.58/0.71    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)))),
% 2.58/0.71    inference(backward_demodulation,[],[f243,f843])).
% 2.58/0.71  fof(f843,plain,(
% 2.58/0.71    ( ! [X35,X33,X34] : (k2_xboole_0(k4_xboole_0(X33,X34),k4_xboole_0(X33,k4_xboole_0(X33,X35))) = k4_xboole_0(X33,k4_xboole_0(X34,X35))) )),
% 2.58/0.71    inference(forward_demodulation,[],[f834,f607])).
% 2.58/0.71  fof(f607,plain,(
% 2.58/0.71    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4)))) )),
% 2.58/0.71    inference(forward_demodulation,[],[f606,f51])).
% 2.58/0.71  fof(f51,plain,(
% 2.58/0.71    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.58/0.71    inference(superposition,[],[f25,f23])).
% 2.58/0.71  fof(f23,plain,(
% 2.58/0.71    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.58/0.71    inference(cnf_transformation,[],[f2])).
% 2.58/0.71  fof(f2,axiom,(
% 2.58/0.71    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.58/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 2.58/0.71  fof(f606,plain,(
% 2.58/0.71    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(X2,k2_xboole_0(k1_xboole_0,k4_xboole_0(X3,X4)))) )),
% 2.58/0.71    inference(forward_demodulation,[],[f563,f46])).
% 2.58/0.71  fof(f46,plain,(
% 2.58/0.71    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.58/0.71    inference(backward_demodulation,[],[f40,f45])).
% 2.58/0.71  fof(f45,plain,(
% 2.58/0.71    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.58/0.71    inference(forward_demodulation,[],[f41,f24])).
% 2.58/0.71  fof(f24,plain,(
% 2.58/0.71    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.58/0.71    inference(cnf_transformation,[],[f11])).
% 2.58/0.71  fof(f11,axiom,(
% 2.58/0.71    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.58/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.58/0.71  fof(f41,plain,(
% 2.58/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 2.58/0.71    inference(definition_unfolding,[],[f26,f27])).
% 2.58/0.71  fof(f26,plain,(
% 2.58/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 2.58/0.71    inference(cnf_transformation,[],[f3])).
% 2.58/0.71  fof(f3,axiom,(
% 2.58/0.71    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.58/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 2.58/0.71  fof(f40,plain,(
% 2.58/0.71    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.58/0.71    inference(definition_unfolding,[],[f22,f27])).
% 2.58/0.71  fof(f22,plain,(
% 2.58/0.71    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.58/0.71    inference(cnf_transformation,[],[f5])).
% 2.58/0.71  fof(f5,axiom,(
% 2.58/0.71    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.58/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 2.58/0.71  fof(f563,plain,(
% 2.58/0.71    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X2),k4_xboole_0(X3,X4))) = k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4)))) )),
% 2.58/0.71    inference(superposition,[],[f47,f47])).
% 2.58/0.71  fof(f834,plain,(
% 2.58/0.71    ( ! [X35,X33,X34] : (k2_xboole_0(k4_xboole_0(X33,X34),k4_xboole_0(X33,k4_xboole_0(X33,X35))) = k4_xboole_0(X33,k4_xboole_0(X33,k2_xboole_0(k4_xboole_0(X33,X34),X35)))) )),
% 2.58/0.71    inference(superposition,[],[f483,f784])).
% 2.58/0.71  fof(f784,plain,(
% 2.58/0.71    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 2.58/0.71    inference(unit_resulting_resolution,[],[f720,f374])).
% 2.58/0.71  fof(f374,plain,(
% 2.58/0.71    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = X3 | ~r1_tarski(X4,X3)) )),
% 2.58/0.71    inference(superposition,[],[f92,f25])).
% 2.58/0.71  fof(f92,plain,(
% 2.58/0.71    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = X2 | ~r1_tarski(X1,X2)) )),
% 2.58/0.71    inference(forward_demodulation,[],[f86,f23])).
% 2.58/0.71  fof(f86,plain,(
% 2.58/0.71    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X2,k1_xboole_0) | ~r1_tarski(X1,X2)) )),
% 2.58/0.71    inference(superposition,[],[f29,f32])).
% 2.58/0.71  fof(f32,plain,(
% 2.58/0.71    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.58/0.71    inference(cnf_transformation,[],[f7])).
% 2.58/0.71  fof(f7,axiom,(
% 2.58/0.71    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.58/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).
% 2.58/0.71  fof(f29,plain,(
% 2.58/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.58/0.71    inference(cnf_transformation,[],[f8])).
% 2.58/0.71  fof(f8,axiom,(
% 2.58/0.71    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.58/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.58/0.71  fof(f720,plain,(
% 2.58/0.71    ( ! [X14,X13] : (r1_tarski(k4_xboole_0(X13,X14),X13)) )),
% 2.58/0.71    inference(backward_demodulation,[],[f438,f719])).
% 2.58/0.71  fof(f719,plain,(
% 2.58/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 2.58/0.71    inference(forward_demodulation,[],[f718,f45])).
% 2.58/0.71  fof(f718,plain,(
% 2.58/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.58/0.71    inference(forward_demodulation,[],[f677,f24])).
% 2.58/0.71  fof(f677,plain,(
% 2.58/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.58/0.71    inference(superposition,[],[f483,f91])).
% 2.58/0.71  fof(f91,plain,(
% 2.58/0.71    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.58/0.71    inference(forward_demodulation,[],[f85,f23])).
% 2.58/0.71  fof(f85,plain,(
% 2.58/0.71    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,X0)) )),
% 2.58/0.71    inference(superposition,[],[f29,f46])).
% 2.58/0.71  fof(f438,plain,(
% 2.58/0.71    ( ! [X14,X13] : (r1_tarski(k4_xboole_0(X13,X14),k2_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X13,X14))))) )),
% 2.58/0.71    inference(forward_demodulation,[],[f421,f25])).
% 2.58/0.71  fof(f421,plain,(
% 2.58/0.71    ( ! [X14,X13] : (r1_tarski(k4_xboole_0(X13,X14),k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X13))) )),
% 2.58/0.71    inference(superposition,[],[f109,f42])).
% 2.58/0.71  fof(f42,plain,(
% 2.58/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.58/0.71    inference(definition_unfolding,[],[f28,f27])).
% 2.58/0.71  fof(f28,plain,(
% 2.58/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.58/0.71    inference(cnf_transformation,[],[f12])).
% 2.58/0.71  fof(f12,axiom,(
% 2.58/0.71    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.58/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.58/0.71  fof(f109,plain,(
% 2.58/0.71    ( ! [X6,X7] : (r1_tarski(k4_xboole_0(X7,X6),k2_xboole_0(X6,X7))) )),
% 2.58/0.71    inference(superposition,[],[f98,f29])).
% 2.58/0.71  fof(f98,plain,(
% 2.58/0.71    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) )),
% 2.58/0.71    inference(superposition,[],[f65,f25])).
% 2.58/0.71  fof(f65,plain,(
% 2.58/0.71    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.58/0.71    inference(unit_resulting_resolution,[],[f24,f33])).
% 2.58/0.71  fof(f33,plain,(
% 2.58/0.71    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 2.58/0.71    inference(cnf_transformation,[],[f7])).
% 2.58/0.71  fof(f483,plain,(
% 2.58/0.71    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X0,X2)))) )),
% 2.58/0.71    inference(backward_demodulation,[],[f44,f482])).
% 2.58/0.71  fof(f482,plain,(
% 2.58/0.71    ( ! [X6,X7,X5] : (k4_xboole_0(k2_xboole_0(X5,X7),k2_xboole_0(X5,X6)) = k4_xboole_0(X7,k2_xboole_0(X5,X6))) )),
% 2.58/0.71    inference(forward_demodulation,[],[f447,f51])).
% 2.58/0.71  fof(f447,plain,(
% 2.58/0.71    ( ! [X6,X7,X5] : (k4_xboole_0(k2_xboole_0(X5,X7),k2_xboole_0(X5,X6)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X7,k2_xboole_0(X5,X6)))) )),
% 2.58/0.71    inference(superposition,[],[f37,f24])).
% 2.58/0.71  fof(f37,plain,(
% 2.58/0.71    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 2.58/0.71    inference(cnf_transformation,[],[f10])).
% 2.58/0.71  fof(f10,axiom,(
% 2.58/0.71    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 2.58/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).
% 2.58/0.71  fof(f44,plain,(
% 2.58/0.71    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)))) )),
% 2.58/0.71    inference(definition_unfolding,[],[f38,f27,f27])).
% 2.58/0.71  fof(f38,plain,(
% 2.58/0.71    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 2.58/0.71    inference(cnf_transformation,[],[f4])).
% 2.58/0.71  fof(f4,axiom,(
% 2.58/0.71    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 2.58/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).
% 2.58/0.71  fof(f243,plain,(
% 2.58/0.71    k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) != k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)))),
% 2.58/0.71    inference(superposition,[],[f49,f35])).
% 2.58/0.71  fof(f49,plain,(
% 2.58/0.71    k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) != k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)))),
% 2.58/0.71    inference(forward_demodulation,[],[f48,f25])).
% 2.58/0.71  fof(f48,plain,(
% 2.58/0.71    k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) != k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2))),
% 2.58/0.71    inference(backward_demodulation,[],[f39,f47])).
% 2.58/0.71  fof(f39,plain,(
% 2.58/0.71    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))),
% 2.58/0.71    inference(definition_unfolding,[],[f21,f27,f27,f27])).
% 2.58/0.71  fof(f21,plain,(
% 2.58/0.71    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 2.58/0.71    inference(cnf_transformation,[],[f19])).
% 2.58/0.71  fof(f19,plain,(
% 2.58/0.71    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 2.58/0.71    inference(ennf_transformation,[],[f18])).
% 2.58/0.71  fof(f18,negated_conjecture,(
% 2.58/0.71    ~! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 2.58/0.71    inference(negated_conjecture,[],[f17])).
% 2.58/0.71  fof(f17,conjecture,(
% 2.58/0.71    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 2.58/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).
% 2.58/0.71  % SZS output end Proof for theBenchmark
% 2.58/0.71  % (21354)------------------------------
% 2.58/0.71  % (21354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.58/0.71  % (21354)Termination reason: Refutation
% 2.58/0.71  
% 2.58/0.71  % (21354)Memory used [KB]: 7036
% 2.58/0.71  % (21354)Time elapsed: 0.269 s
% 2.58/0.71  % (21354)------------------------------
% 2.58/0.71  % (21354)------------------------------
% 2.58/0.71  % (21323)Success in time 0.345 s
%------------------------------------------------------------------------------
