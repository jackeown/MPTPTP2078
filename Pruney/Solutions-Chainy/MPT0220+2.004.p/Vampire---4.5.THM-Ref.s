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
% DateTime   : Thu Dec  3 12:35:36 EST 2020

% Result     : Theorem 2.33s
% Output     : Refutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 267 expanded)
%              Number of leaves         :   16 (  85 expanded)
%              Depth                    :   16
%              Number of atoms          :   72 ( 327 expanded)
%              Number of equality atoms :   58 ( 254 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1231,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1230])).

fof(f1230,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(superposition,[],[f1218,f324])).

fof(f324,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X0))) = X1 ),
    inference(superposition,[],[f125,f28])).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f125,plain,(
    ! [X10,X9] : k5_xboole_0(X9,k5_xboole_0(k3_xboole_0(X9,X9),X10)) = X10 ),
    inference(forward_demodulation,[],[f109,f87])).

fof(f87,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f86,f28])).

fof(f86,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f59,f81])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(unit_resulting_resolution,[],[f67,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f31])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f59,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f25,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f109,plain,(
    ! [X10,X9] : k5_xboole_0(X9,k5_xboole_0(k3_xboole_0(X9,X9),X10)) = k5_xboole_0(k1_xboole_0,X10) ),
    inference(superposition,[],[f41,f81])).

fof(f41,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1218,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(backward_demodulation,[],[f71,f1175])).

fof(f1175,plain,(
    ! [X0,X1] : k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ),
    inference(unit_resulting_resolution,[],[f60,f567])).

fof(f567,plain,(
    ! [X4,X5] :
      ( k3_xboole_0(X4,X5) = k3_xboole_0(X4,X4)
      | ~ r1_tarski(X4,X5) ) ),
    inference(forward_demodulation,[],[f566,f87])).

fof(f566,plain,(
    ! [X4,X5] :
      ( k3_xboole_0(X4,X5) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X4,X4))
      | ~ r1_tarski(X4,X5) ) ),
    inference(forward_demodulation,[],[f537,f28])).

fof(f537,plain,(
    ! [X4,X5] :
      ( k3_xboole_0(X4,X5) = k5_xboole_0(k3_xboole_0(X4,X4),k1_xboole_0)
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f397,f62])).

fof(f397,plain,(
    ! [X12,X11] : k5_xboole_0(k3_xboole_0(X11,X11),k5_xboole_0(X11,X12)) = X12 ),
    inference(superposition,[],[f125,f340])).

fof(f340,plain,(
    ! [X6] : k3_xboole_0(k3_xboole_0(X6,X6),k3_xboole_0(X6,X6)) = X6 ),
    inference(forward_demodulation,[],[f327,f86])).

fof(f327,plain,(
    ! [X6] : k5_xboole_0(X6,k1_xboole_0) = k3_xboole_0(k3_xboole_0(X6,X6),k3_xboole_0(X6,X6)) ),
    inference(superposition,[],[f125,f81])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f26,f57,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f56])).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f71,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    inference(backward_demodulation,[],[f58,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f58,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(definition_unfolding,[],[f23,f56,f52,f57,f56])).

fof(f23,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:14:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.40/0.55  % (30629)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.40/0.56  % (30631)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.40/0.56  % (30631)Refutation not found, incomplete strategy% (30631)------------------------------
% 1.40/0.56  % (30631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (30629)Refutation not found, incomplete strategy% (30629)------------------------------
% 1.40/0.56  % (30629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.57  % (30650)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.40/0.57  % (30652)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.40/0.57  % (30629)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.57  
% 1.40/0.57  % (30629)Memory used [KB]: 10618
% 1.40/0.57  % (30629)Time elapsed: 0.122 s
% 1.40/0.57  % (30629)------------------------------
% 1.40/0.57  % (30629)------------------------------
% 1.40/0.57  % (30627)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.40/0.57  % (30652)Refutation not found, incomplete strategy% (30652)------------------------------
% 1.40/0.57  % (30652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.57  % (30631)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.57  
% 1.40/0.57  % (30631)Memory used [KB]: 6140
% 1.40/0.57  % (30631)Time elapsed: 0.122 s
% 1.40/0.57  % (30631)------------------------------
% 1.40/0.57  % (30631)------------------------------
% 1.40/0.57  % (30627)Refutation not found, incomplete strategy% (30627)------------------------------
% 1.40/0.57  % (30627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.57  % (30627)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.57  
% 1.40/0.57  % (30627)Memory used [KB]: 1663
% 1.40/0.57  % (30627)Time elapsed: 0.146 s
% 1.40/0.57  % (30627)------------------------------
% 1.40/0.57  % (30627)------------------------------
% 1.40/0.57  % (30650)Refutation not found, incomplete strategy% (30650)------------------------------
% 1.40/0.57  % (30650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.57  % (30635)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.40/0.57  % (30637)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.40/0.57  % (30650)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.57  
% 1.40/0.57  % (30650)Memory used [KB]: 1663
% 1.40/0.57  % (30650)Time elapsed: 0.136 s
% 1.40/0.57  % (30650)------------------------------
% 1.40/0.57  % (30650)------------------------------
% 1.40/0.57  % (30652)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.57  
% 1.40/0.57  % (30652)Memory used [KB]: 6268
% 1.40/0.57  % (30652)Time elapsed: 0.135 s
% 1.40/0.57  % (30652)------------------------------
% 1.40/0.57  % (30652)------------------------------
% 1.40/0.58  % (30637)Refutation not found, incomplete strategy% (30637)------------------------------
% 1.40/0.58  % (30637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.58  % (30635)Refutation not found, incomplete strategy% (30635)------------------------------
% 1.40/0.58  % (30635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.58  % (30635)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.58  
% 1.40/0.58  % (30635)Memory used [KB]: 10618
% 1.40/0.58  % (30635)Time elapsed: 0.147 s
% 1.40/0.58  % (30635)------------------------------
% 1.40/0.58  % (30635)------------------------------
% 1.40/0.58  % (30637)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.58  
% 1.40/0.58  % (30637)Memory used [KB]: 10618
% 1.40/0.58  % (30637)Time elapsed: 0.148 s
% 1.40/0.58  % (30637)------------------------------
% 1.40/0.58  % (30637)------------------------------
% 1.40/0.58  % (30649)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.40/0.60  % (30634)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.40/0.60  % (30649)Refutation not found, incomplete strategy% (30649)------------------------------
% 1.40/0.60  % (30649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.60  % (30649)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.60  
% 1.40/0.60  % (30649)Memory used [KB]: 10746
% 1.40/0.60  % (30649)Time elapsed: 0.176 s
% 1.40/0.60  % (30649)------------------------------
% 1.40/0.60  % (30649)------------------------------
% 1.40/0.60  % (30643)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.40/0.60  % (30633)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.40/0.60  % (30630)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.40/0.60  % (30638)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.40/0.61  % (30653)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.40/0.61  % (30654)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.40/0.62  % (30645)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.62  % (30644)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.40/0.62  % (30646)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.40/0.62  % (30632)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.40/0.62  % (30636)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.40/0.62  % (30639)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.40/0.63  % (30648)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.40/0.63  % (30638)Refutation not found, incomplete strategy% (30638)------------------------------
% 1.40/0.63  % (30638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.63  % (30638)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.63  
% 1.40/0.63  % (30638)Memory used [KB]: 10618
% 1.40/0.63  % (30638)Time elapsed: 0.197 s
% 1.40/0.63  % (30638)------------------------------
% 1.40/0.63  % (30638)------------------------------
% 1.40/0.63  % (30648)Refutation not found, incomplete strategy% (30648)------------------------------
% 1.40/0.63  % (30648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.63  % (30656)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.40/0.63  % (30642)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.40/0.63  % (30653)Refutation not found, incomplete strategy% (30653)------------------------------
% 1.40/0.63  % (30653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.63  % (30628)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.40/0.63  % (30651)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.40/0.64  % (30644)Refutation not found, incomplete strategy% (30644)------------------------------
% 1.40/0.64  % (30644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.64  % (30644)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.64  
% 1.40/0.64  % (30644)Memory used [KB]: 10618
% 1.40/0.64  % (30644)Time elapsed: 0.208 s
% 1.40/0.64  % (30644)------------------------------
% 1.40/0.64  % (30644)------------------------------
% 1.40/0.64  % (30636)Refutation not found, incomplete strategy% (30636)------------------------------
% 1.40/0.64  % (30636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.64  % (30636)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.64  
% 1.40/0.64  % (30636)Memory used [KB]: 10618
% 1.40/0.64  % (30636)Time elapsed: 0.208 s
% 1.40/0.64  % (30636)------------------------------
% 1.40/0.64  % (30636)------------------------------
% 1.40/0.64  % (30653)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.64  
% 1.40/0.64  % (30653)Memory used [KB]: 10618
% 1.40/0.64  % (30653)Time elapsed: 0.199 s
% 1.40/0.64  % (30653)------------------------------
% 1.40/0.64  % (30653)------------------------------
% 1.40/0.64  % (30647)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.40/0.65  % (30640)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.40/0.65  % (30648)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.65  
% 1.40/0.65  % (30648)Memory used [KB]: 1663
% 1.40/0.65  % (30648)Time elapsed: 0.150 s
% 1.40/0.65  % (30648)------------------------------
% 1.40/0.65  % (30648)------------------------------
% 2.01/0.65  % (30655)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 2.01/0.66  % (30641)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 2.01/0.66  % (30647)Refutation not found, incomplete strategy% (30647)------------------------------
% 2.01/0.66  % (30647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.66  % (30647)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.66  
% 2.01/0.66  % (30647)Memory used [KB]: 10746
% 2.01/0.66  % (30647)Time elapsed: 0.225 s
% 2.01/0.66  % (30647)------------------------------
% 2.01/0.66  % (30647)------------------------------
% 2.33/0.74  % (30651)Refutation found. Thanks to Tanya!
% 2.33/0.74  % SZS status Theorem for theBenchmark
% 2.33/0.74  % SZS output start Proof for theBenchmark
% 2.33/0.74  fof(f1231,plain,(
% 2.33/0.74    $false),
% 2.33/0.74    inference(trivial_inequality_removal,[],[f1230])).
% 2.33/0.74  fof(f1230,plain,(
% 2.33/0.74    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 2.33/0.74    inference(superposition,[],[f1218,f324])).
% 2.33/0.74  fof(f324,plain,(
% 2.33/0.74    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X0))) = X1) )),
% 2.33/0.74    inference(superposition,[],[f125,f28])).
% 2.33/0.74  fof(f28,plain,(
% 2.33/0.74    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.33/0.74    inference(cnf_transformation,[],[f2])).
% 2.33/0.74  fof(f2,axiom,(
% 2.33/0.74    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.33/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.33/0.74  fof(f125,plain,(
% 2.33/0.74    ( ! [X10,X9] : (k5_xboole_0(X9,k5_xboole_0(k3_xboole_0(X9,X9),X10)) = X10) )),
% 2.33/0.74    inference(forward_demodulation,[],[f109,f87])).
% 2.33/0.74  fof(f87,plain,(
% 2.33/0.74    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.33/0.74    inference(superposition,[],[f86,f28])).
% 2.33/0.74  fof(f86,plain,(
% 2.33/0.74    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.33/0.74    inference(backward_demodulation,[],[f59,f81])).
% 2.33/0.74  fof(f81,plain,(
% 2.33/0.74    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 2.33/0.74    inference(unit_resulting_resolution,[],[f67,f62])).
% 2.33/0.74  fof(f62,plain,(
% 2.33/0.74    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 2.33/0.74    inference(definition_unfolding,[],[f38,f31])).
% 2.33/0.74  fof(f31,plain,(
% 2.33/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.33/0.74    inference(cnf_transformation,[],[f8])).
% 2.33/0.74  fof(f8,axiom,(
% 2.33/0.74    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.33/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.33/0.74  fof(f38,plain,(
% 2.33/0.74    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.33/0.74    inference(cnf_transformation,[],[f7])).
% 2.33/0.74  fof(f7,axiom,(
% 2.33/0.74    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.33/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.33/0.74  fof(f67,plain,(
% 2.33/0.74    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.33/0.74    inference(equality_resolution,[],[f33])).
% 2.33/0.74  fof(f33,plain,(
% 2.33/0.74    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.33/0.74    inference(cnf_transformation,[],[f6])).
% 2.33/0.74  fof(f6,axiom,(
% 2.33/0.74    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.33/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.33/0.74  fof(f59,plain,(
% 2.33/0.74    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 2.33/0.74    inference(definition_unfolding,[],[f25,f52])).
% 2.33/0.74  fof(f52,plain,(
% 2.33/0.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.33/0.74    inference(definition_unfolding,[],[f30,f31])).
% 2.33/0.74  fof(f30,plain,(
% 2.33/0.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.33/0.74    inference(cnf_transformation,[],[f10])).
% 2.33/0.74  fof(f10,axiom,(
% 2.33/0.74    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.33/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.33/0.74  fof(f25,plain,(
% 2.33/0.74    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.33/0.74    inference(cnf_transformation,[],[f20])).
% 2.33/0.74  fof(f20,plain,(
% 2.33/0.74    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.33/0.74    inference(rectify,[],[f5])).
% 2.33/0.74  fof(f5,axiom,(
% 2.33/0.74    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.33/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.33/0.74  fof(f109,plain,(
% 2.33/0.74    ( ! [X10,X9] : (k5_xboole_0(X9,k5_xboole_0(k3_xboole_0(X9,X9),X10)) = k5_xboole_0(k1_xboole_0,X10)) )),
% 2.33/0.74    inference(superposition,[],[f41,f81])).
% 2.33/0.74  fof(f41,plain,(
% 2.33/0.74    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.33/0.74    inference(cnf_transformation,[],[f9])).
% 2.33/0.74  fof(f9,axiom,(
% 2.33/0.74    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.33/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.33/0.74  fof(f1218,plain,(
% 2.33/0.74    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 2.33/0.74    inference(backward_demodulation,[],[f71,f1175])).
% 2.33/0.74  fof(f1175,plain,(
% 2.33/0.74    ( ! [X0,X1] : (k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) )),
% 2.33/0.74    inference(unit_resulting_resolution,[],[f60,f567])).
% 2.33/0.74  fof(f567,plain,(
% 2.33/0.74    ( ! [X4,X5] : (k3_xboole_0(X4,X5) = k3_xboole_0(X4,X4) | ~r1_tarski(X4,X5)) )),
% 2.33/0.74    inference(forward_demodulation,[],[f566,f87])).
% 2.33/0.74  fof(f566,plain,(
% 2.33/0.74    ( ! [X4,X5] : (k3_xboole_0(X4,X5) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X4,X4)) | ~r1_tarski(X4,X5)) )),
% 2.33/0.74    inference(forward_demodulation,[],[f537,f28])).
% 2.33/0.74  fof(f537,plain,(
% 2.33/0.74    ( ! [X4,X5] : (k3_xboole_0(X4,X5) = k5_xboole_0(k3_xboole_0(X4,X4),k1_xboole_0) | ~r1_tarski(X4,X5)) )),
% 2.33/0.74    inference(superposition,[],[f397,f62])).
% 2.33/0.74  fof(f397,plain,(
% 2.33/0.74    ( ! [X12,X11] : (k5_xboole_0(k3_xboole_0(X11,X11),k5_xboole_0(X11,X12)) = X12) )),
% 2.33/0.74    inference(superposition,[],[f125,f340])).
% 2.33/0.74  fof(f340,plain,(
% 2.33/0.74    ( ! [X6] : (k3_xboole_0(k3_xboole_0(X6,X6),k3_xboole_0(X6,X6)) = X6) )),
% 2.33/0.74    inference(forward_demodulation,[],[f327,f86])).
% 2.33/0.74  fof(f327,plain,(
% 2.33/0.74    ( ! [X6] : (k5_xboole_0(X6,k1_xboole_0) = k3_xboole_0(k3_xboole_0(X6,X6),k3_xboole_0(X6,X6))) )),
% 2.33/0.74    inference(superposition,[],[f125,f81])).
% 2.33/0.74  fof(f60,plain,(
% 2.33/0.74    ( ! [X0,X1] : (r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 2.33/0.74    inference(definition_unfolding,[],[f26,f57,f56])).
% 2.33/0.74  fof(f56,plain,(
% 2.33/0.74    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 2.33/0.74    inference(definition_unfolding,[],[f29,f55])).
% 2.33/0.74  fof(f55,plain,(
% 2.33/0.74    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 2.33/0.74    inference(definition_unfolding,[],[f40,f54])).
% 2.33/0.74  fof(f54,plain,(
% 2.33/0.74    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 2.33/0.74    inference(definition_unfolding,[],[f49,f53])).
% 2.33/0.74  fof(f53,plain,(
% 2.33/0.74    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 2.33/0.74    inference(definition_unfolding,[],[f50,f51])).
% 2.33/0.74  fof(f51,plain,(
% 2.33/0.74    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.33/0.74    inference(cnf_transformation,[],[f16])).
% 2.33/0.74  fof(f16,axiom,(
% 2.33/0.74    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.33/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.33/0.74  fof(f50,plain,(
% 2.33/0.74    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.33/0.74    inference(cnf_transformation,[],[f15])).
% 2.33/0.74  fof(f15,axiom,(
% 2.33/0.74    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.33/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.33/0.74  fof(f49,plain,(
% 2.33/0.74    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.33/0.74    inference(cnf_transformation,[],[f14])).
% 2.33/0.74  fof(f14,axiom,(
% 2.33/0.74    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.33/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.33/0.74  fof(f40,plain,(
% 2.33/0.74    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.33/0.74    inference(cnf_transformation,[],[f13])).
% 2.33/0.74  fof(f13,axiom,(
% 2.33/0.74    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.33/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.33/0.74  fof(f29,plain,(
% 2.33/0.74    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.33/0.74    inference(cnf_transformation,[],[f12])).
% 2.33/0.74  fof(f12,axiom,(
% 2.33/0.74    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.33/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.33/0.74  fof(f57,plain,(
% 2.33/0.74    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 2.33/0.74    inference(definition_unfolding,[],[f24,f56])).
% 2.33/0.74  fof(f24,plain,(
% 2.33/0.74    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.33/0.74    inference(cnf_transformation,[],[f11])).
% 2.33/0.74  fof(f11,axiom,(
% 2.33/0.74    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.33/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.33/0.74  fof(f26,plain,(
% 2.33/0.74    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 2.33/0.74    inference(cnf_transformation,[],[f17])).
% 2.33/0.74  fof(f17,axiom,(
% 2.33/0.74    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 2.33/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 2.33/0.74  fof(f71,plain,(
% 2.33/0.74    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 2.33/0.74    inference(backward_demodulation,[],[f58,f27])).
% 2.33/0.74  fof(f27,plain,(
% 2.33/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.33/0.74    inference(cnf_transformation,[],[f1])).
% 2.33/0.74  fof(f1,axiom,(
% 2.33/0.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.33/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.33/0.74  fof(f58,plain,(
% 2.33/0.74    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 2.33/0.74    inference(definition_unfolding,[],[f23,f56,f52,f57,f56])).
% 2.33/0.74  fof(f23,plain,(
% 2.33/0.74    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 2.33/0.74    inference(cnf_transformation,[],[f21])).
% 2.33/0.74  fof(f21,plain,(
% 2.33/0.74    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 2.33/0.74    inference(ennf_transformation,[],[f19])).
% 2.33/0.74  fof(f19,negated_conjecture,(
% 2.33/0.74    ~! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 2.33/0.74    inference(negated_conjecture,[],[f18])).
% 2.33/0.74  fof(f18,conjecture,(
% 2.33/0.74    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 2.33/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).
% 2.33/0.74  % SZS output end Proof for theBenchmark
% 2.33/0.74  % (30651)------------------------------
% 2.33/0.74  % (30651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.33/0.74  % (30651)Termination reason: Refutation
% 2.33/0.74  
% 2.33/0.74  % (30651)Memory used [KB]: 7291
% 2.33/0.74  % (30651)Time elapsed: 0.293 s
% 2.33/0.74  % (30651)------------------------------
% 2.33/0.74  % (30651)------------------------------
% 2.33/0.74  % (30623)Success in time 0.369 s
%------------------------------------------------------------------------------
