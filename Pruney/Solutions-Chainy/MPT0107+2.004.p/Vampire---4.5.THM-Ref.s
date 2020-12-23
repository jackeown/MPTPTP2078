%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 437 expanded)
%              Number of leaves         :   11 ( 157 expanded)
%              Depth                    :   15
%              Number of atoms          :   60 ( 438 expanded)
%              Number of equality atoms :   59 ( 437 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f234,plain,(
    $false ),
    inference(subsumption_resolution,[],[f28,f233])).

fof(f233,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f154,f231])).

fof(f231,plain,(
    ! [X19,X18] : k4_xboole_0(X18,X19) = k5_xboole_0(k4_xboole_0(X18,X19),k4_xboole_0(X18,X18)) ),
    inference(forward_demodulation,[],[f213,f183])).

fof(f183,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X4)) ),
    inference(backward_demodulation,[],[f138,f163])).

fof(f163,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f102,f31])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f20,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f102,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X3,X4)),X3) = k4_xboole_0(X5,X3) ),
    inference(backward_demodulation,[],[f62,f100])).

fof(f100,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,k4_xboole_0(X3,X2))) = X2 ),
    inference(forward_demodulation,[],[f93,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f31,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f24,f22,f22])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f93,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))),k4_xboole_0(X3,k4_xboole_0(X3,X2))) = X2 ),
    inference(superposition,[],[f82,f34])).

fof(f82,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f75,f30])).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f19,f26,f22])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f75,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f32,f31])).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(definition_unfolding,[],[f21,f26,f26])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f62,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X3,X4)),X3) = k4_xboole_0(X5,k5_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3)))) ),
    inference(superposition,[],[f29,f34])).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f18,f26])).

fof(f18,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f138,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X4,X5),X4)) ),
    inference(forward_demodulation,[],[f127,f59])).

fof(f59,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f49,f38])).

fof(f49,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))) ),
    inference(superposition,[],[f38,f34])).

fof(f127,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5))) ),
    inference(superposition,[],[f31,f108])).

fof(f108,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X0) = k4_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f29,f104])).

fof(f104,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(backward_demodulation,[],[f84,f102])).

fof(f84,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
    inference(backward_demodulation,[],[f36,f82])).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f33,f31])).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f23,f26,f26])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f213,plain,(
    ! [X19,X18] : k4_xboole_0(X18,X19) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X18,X19),k4_xboole_0(X18,X18)),k4_xboole_0(X18,X18)) ),
    inference(superposition,[],[f82,f163])).

fof(f154,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f142,f102])).

fof(f142,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ),
    inference(superposition,[],[f116,f31])).

fof(f116,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(backward_demodulation,[],[f27,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,X0) = k4_xboole_0(k4_xboole_0(X2,X0),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f29,f103])).

fof(f103,plain,(
    ! [X4,X5] : k5_xboole_0(X4,k4_xboole_0(k4_xboole_0(X4,X5),X4)) = X4 ),
    inference(backward_demodulation,[],[f39,f100])).

fof(f39,plain,(
    ! [X4,X5] : k5_xboole_0(X4,k4_xboole_0(k4_xboole_0(X4,X5),X4)) = k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X5,X4))) ),
    inference(superposition,[],[f33,f34])).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f28,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f17,f22])).

fof(f17,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 19:32:50 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.48  % (22228)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.48  % (22219)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.48  % (22219)Refutation not found, incomplete strategy% (22219)------------------------------
% 0.22/0.48  % (22219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (22219)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (22219)Memory used [KB]: 10618
% 0.22/0.48  % (22219)Time elapsed: 0.056 s
% 0.22/0.48  % (22219)------------------------------
% 0.22/0.48  % (22219)------------------------------
% 0.22/0.52  % (22227)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (22211)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (22211)Refutation not found, incomplete strategy% (22211)------------------------------
% 0.22/0.52  % (22211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22211)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22211)Memory used [KB]: 1663
% 0.22/0.52  % (22211)Time elapsed: 0.096 s
% 0.22/0.52  % (22211)------------------------------
% 0.22/0.52  % (22211)------------------------------
% 0.22/0.52  % (22218)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (22216)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (22240)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (22215)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (22215)Refutation not found, incomplete strategy% (22215)------------------------------
% 0.22/0.53  % (22215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (22215)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (22215)Memory used [KB]: 6140
% 0.22/0.53  % (22215)Time elapsed: 0.110 s
% 0.22/0.53  % (22215)------------------------------
% 0.22/0.53  % (22215)------------------------------
% 0.22/0.53  % (22213)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (22221)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (22213)Refutation not found, incomplete strategy% (22213)------------------------------
% 0.22/0.53  % (22213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (22213)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (22213)Memory used [KB]: 10618
% 0.22/0.53  % (22213)Time elapsed: 0.107 s
% 0.22/0.53  % (22213)------------------------------
% 0.22/0.53  % (22213)------------------------------
% 0.22/0.53  % (22221)Refutation not found, incomplete strategy% (22221)------------------------------
% 0.22/0.53  % (22221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (22221)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (22221)Memory used [KB]: 10618
% 0.22/0.53  % (22221)Time elapsed: 0.108 s
% 0.22/0.53  % (22221)------------------------------
% 0.22/0.53  % (22221)------------------------------
% 0.22/0.53  % (22214)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (22232)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (22224)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (22217)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (22236)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (22238)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (22212)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (22231)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (22226)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (22216)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f234,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(subsumption_resolution,[],[f28,f233])).
% 0.22/0.55  fof(f233,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.55    inference(backward_demodulation,[],[f154,f231])).
% 0.22/0.55  fof(f231,plain,(
% 0.22/0.55    ( ! [X19,X18] : (k4_xboole_0(X18,X19) = k5_xboole_0(k4_xboole_0(X18,X19),k4_xboole_0(X18,X18))) )),
% 0.22/0.55    inference(forward_demodulation,[],[f213,f183])).
% 0.22/0.55  fof(f183,plain,(
% 0.22/0.55    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X4))) )),
% 0.22/0.55    inference(backward_demodulation,[],[f138,f163])).
% 0.22/0.55  fof(f163,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0)) )),
% 0.22/0.55    inference(superposition,[],[f102,f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.55    inference(definition_unfolding,[],[f20,f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.55  fof(f102,plain,(
% 0.22/0.55    ( ! [X4,X5,X3] : (k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X3,X4)),X3) = k4_xboole_0(X5,X3)) )),
% 0.22/0.55    inference(backward_demodulation,[],[f62,f100])).
% 0.22/0.55  fof(f100,plain,(
% 0.22/0.55    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,k4_xboole_0(X3,X2))) = X2) )),
% 0.22/0.55    inference(forward_demodulation,[],[f93,f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.22/0.55    inference(superposition,[],[f31,f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.22/0.55    inference(definition_unfolding,[],[f24,f22,f22])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.55  fof(f93,plain,(
% 0.22/0.55    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))),k4_xboole_0(X3,k4_xboole_0(X3,X2))) = X2) )),
% 0.22/0.55    inference(superposition,[],[f82,f34])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.55    inference(forward_demodulation,[],[f75,f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0) )),
% 0.22/0.55    inference(definition_unfolding,[],[f19,f26,f22])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) )),
% 0.22/0.55    inference(superposition,[],[f32,f31])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0))) )),
% 0.22/0.55    inference(definition_unfolding,[],[f21,f26,f26])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    ( ! [X4,X5,X3] : (k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X3,X4)),X3) = k4_xboole_0(X5,k5_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))))) )),
% 0.22/0.55    inference(superposition,[],[f29,f34])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 0.22/0.55    inference(definition_unfolding,[],[f18,f26])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.55  fof(f138,plain,(
% 0.22/0.55    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X4,X5),X4))) )),
% 0.22/0.55    inference(forward_demodulation,[],[f127,f59])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3))) )),
% 0.22/0.55    inference(forward_demodulation,[],[f49,f38])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))) )),
% 0.22/0.55    inference(superposition,[],[f38,f34])).
% 0.22/0.55  fof(f127,plain,(
% 0.22/0.55    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5)))) )),
% 0.22/0.55    inference(superposition,[],[f31,f108])).
% 0.22/0.55  fof(f108,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k4_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 0.22/0.55    inference(superposition,[],[f29,f104])).
% 0.22/0.55  fof(f104,plain,(
% 0.22/0.55    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.22/0.55    inference(backward_demodulation,[],[f84,f102])).
% 0.22/0.55  fof(f84,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0) )),
% 0.22/0.55    inference(backward_demodulation,[],[f36,f82])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) )),
% 0.22/0.55    inference(superposition,[],[f33,f31])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 0.22/0.55    inference(definition_unfolding,[],[f23,f26,f26])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.55  fof(f213,plain,(
% 0.22/0.55    ( ! [X19,X18] : (k4_xboole_0(X18,X19) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X18,X19),k4_xboole_0(X18,X18)),k4_xboole_0(X18,X18))) )),
% 0.22/0.55    inference(superposition,[],[f82,f163])).
% 0.22/0.55  fof(f154,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0))) )),
% 0.22/0.55    inference(forward_demodulation,[],[f142,f102])).
% 0.22/0.55  fof(f142,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0))) )),
% 0.22/0.55    inference(superposition,[],[f116,f31])).
% 0.22/0.55  fof(f116,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.22/0.55    inference(backward_demodulation,[],[f27,f115])).
% 0.22/0.55  fof(f115,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(X2,X0) = k4_xboole_0(k4_xboole_0(X2,X0),k4_xboole_0(X0,X1))) )),
% 0.22/0.55    inference(superposition,[],[f29,f103])).
% 0.22/0.55  fof(f103,plain,(
% 0.22/0.55    ( ! [X4,X5] : (k5_xboole_0(X4,k4_xboole_0(k4_xboole_0(X4,X5),X4)) = X4) )),
% 0.22/0.55    inference(backward_demodulation,[],[f39,f100])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ( ! [X4,X5] : (k5_xboole_0(X4,k4_xboole_0(k4_xboole_0(X4,X5),X4)) = k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X5,X4)))) )),
% 0.22/0.55    inference(superposition,[],[f33,f34])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1)))) )),
% 0.22/0.55    inference(definition_unfolding,[],[f25,f26])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.22/0.55    inference(definition_unfolding,[],[f17,f22])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.55    inference(negated_conjecture,[],[f12])).
% 0.22/0.55  fof(f12,conjecture,(
% 0.22/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (22216)------------------------------
% 0.22/0.55  % (22216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (22216)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (22216)Memory used [KB]: 6396
% 0.22/0.55  % (22216)Time elapsed: 0.132 s
% 0.22/0.55  % (22216)------------------------------
% 0.22/0.55  % (22216)------------------------------
% 0.22/0.55  % (22210)Success in time 0.179 s
%------------------------------------------------------------------------------
