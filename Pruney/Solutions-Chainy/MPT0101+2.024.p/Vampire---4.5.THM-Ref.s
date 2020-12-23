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
% DateTime   : Thu Dec  3 12:31:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 132 expanded)
%              Number of leaves         :   17 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :   65 ( 133 expanded)
%              Number of equality atoms :   64 ( 132 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f325,plain,(
    $false ),
    inference(subsumption_resolution,[],[f324,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f32,f31,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f324,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f323,f51])).

fof(f51,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f25,f23])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f323,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f322,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f38,f44])).

fof(f44,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f39,f24])).

fof(f24,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f26,f30])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f22,f30])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f322,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f321,f209])).

fof(f209,plain,(
    ! [X17,X15,X16] : k4_xboole_0(X17,k2_xboole_0(k4_xboole_0(X17,X15),X16)) = k4_xboole_0(X17,k2_xboole_0(X16,k4_xboole_0(X17,X15))) ),
    inference(forward_demodulation,[],[f208,f100])).

fof(f100,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X4,k4_xboole_0(X2,X3)) = k2_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(superposition,[],[f27,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f208,plain,(
    ! [X17,X15,X16] : k4_xboole_0(X17,k2_xboole_0(k4_xboole_0(X17,X15),X16)) = k4_xboole_0(X17,k2_xboole_0(X16,k4_xboole_0(X17,k2_xboole_0(X15,X16)))) ),
    inference(forward_demodulation,[],[f207,f25])).

fof(f207,plain,(
    ! [X17,X15,X16] : k4_xboole_0(X17,k2_xboole_0(k4_xboole_0(X17,k2_xboole_0(X15,X16)),X16)) = k4_xboole_0(X17,k2_xboole_0(k4_xboole_0(X17,X15),X16)) ),
    inference(forward_demodulation,[],[f184,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(backward_demodulation,[],[f42,f35])).

fof(f42,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f34,f30,f30])).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f184,plain,(
    ! [X17,X15,X16] : k4_xboole_0(X17,k2_xboole_0(k4_xboole_0(X17,k2_xboole_0(X15,X16)),X16)) = k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X15,X16))) ),
    inference(superposition,[],[f47,f29])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f321,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK0)))) ),
    inference(forward_demodulation,[],[f320,f186])).

fof(f186,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
    inference(superposition,[],[f47,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f36,f30])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_xboole_1)).

fof(f320,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(backward_demodulation,[],[f49,f319])).

fof(f319,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f260,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f30])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

fof(f260,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[],[f29,f40])).

fof(f49,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(forward_demodulation,[],[f48,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f48,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f46,f47])).

fof(f46,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))) ),
    inference(backward_demodulation,[],[f37,f42])).

fof(f37,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f21,f31,f31,f30])).

fof(f21,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:17:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.46  % (28711)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (28710)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.51  % (28709)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.51  % (28723)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.51  % (28712)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (28713)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.52  % (28721)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.52  % (28720)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.52  % (28724)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.53  % (28722)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.53  % (28715)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.53  % (28718)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.53  % (28708)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.53  % (28723)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f325,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f324,f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f32,f31,f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,axiom,(
% 0.20/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 0.20/0.53  fof(f324,plain,(
% 0.20/0.53    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.20/0.53    inference(forward_demodulation,[],[f323,f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.20/0.53    inference(superposition,[],[f25,f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.53  fof(f323,plain,(
% 0.20/0.53    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))))),
% 0.20/0.53    inference(forward_demodulation,[],[f322,f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.53    inference(backward_demodulation,[],[f38,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.53    inference(forward_demodulation,[],[f39,f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 0.20/0.53    inference(definition_unfolding,[],[f26,f30])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f22,f30])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.53  fof(f322,plain,(
% 0.20/0.53    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK1))))),
% 0.20/0.53    inference(forward_demodulation,[],[f321,f209])).
% 0.20/0.53  fof(f209,plain,(
% 0.20/0.53    ( ! [X17,X15,X16] : (k4_xboole_0(X17,k2_xboole_0(k4_xboole_0(X17,X15),X16)) = k4_xboole_0(X17,k2_xboole_0(X16,k4_xboole_0(X17,X15)))) )),
% 0.20/0.53    inference(forward_demodulation,[],[f208,f100])).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    ( ! [X4,X2,X3] : (k2_xboole_0(X4,k4_xboole_0(X2,X3)) = k2_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X4)))) )),
% 0.20/0.53    inference(superposition,[],[f27,f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.53  fof(f208,plain,(
% 0.20/0.53    ( ! [X17,X15,X16] : (k4_xboole_0(X17,k2_xboole_0(k4_xboole_0(X17,X15),X16)) = k4_xboole_0(X17,k2_xboole_0(X16,k4_xboole_0(X17,k2_xboole_0(X15,X16))))) )),
% 0.20/0.53    inference(forward_demodulation,[],[f207,f25])).
% 0.20/0.53  fof(f207,plain,(
% 0.20/0.53    ( ! [X17,X15,X16] : (k4_xboole_0(X17,k2_xboole_0(k4_xboole_0(X17,k2_xboole_0(X15,X16)),X16)) = k4_xboole_0(X17,k2_xboole_0(k4_xboole_0(X17,X15),X16))) )),
% 0.20/0.53    inference(forward_demodulation,[],[f184,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 0.20/0.53    inference(backward_demodulation,[],[f42,f35])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f34,f30,f30])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.20/0.53  fof(f184,plain,(
% 0.20/0.53    ( ! [X17,X15,X16] : (k4_xboole_0(X17,k2_xboole_0(k4_xboole_0(X17,k2_xboole_0(X15,X16)),X16)) = k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X15,X16)))) )),
% 0.20/0.53    inference(superposition,[],[f47,f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.20/0.53  fof(f321,plain,(
% 0.20/0.53    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK0))))),
% 0.20/0.53    inference(forward_demodulation,[],[f320,f186])).
% 0.20/0.53  fof(f186,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) )),
% 0.20/0.53    inference(superposition,[],[f47,f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f36,f30])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_xboole_1)).
% 0.20/0.53  fof(f320,plain,(
% 0.20/0.53    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.20/0.53    inference(backward_demodulation,[],[f49,f319])).
% 0.20/0.53  fof(f319,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.53    inference(forward_demodulation,[],[f260,f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f33,f30])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,axiom,(
% 0.20/0.53    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).
% 0.20/0.53  fof(f260,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.53    inference(superposition,[],[f29,f40])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.20/0.53    inference(forward_demodulation,[],[f48,f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,axiom,(
% 0.20/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 0.20/0.53    inference(backward_demodulation,[],[f46,f47])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))))),
% 0.20/0.53    inference(backward_demodulation,[],[f37,f42])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.20/0.53    inference(definition_unfolding,[],[f21,f31,f31,f30])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.53    inference(negated_conjecture,[],[f16])).
% 0.20/0.53  fof(f16,conjecture,(
% 0.20/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (28723)------------------------------
% 0.20/0.53  % (28723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (28723)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (28723)Memory used [KB]: 10874
% 0.20/0.53  % (28723)Time elapsed: 0.101 s
% 0.20/0.53  % (28723)------------------------------
% 0.20/0.53  % (28723)------------------------------
% 0.20/0.54  % (28707)Success in time 0.17 s
%------------------------------------------------------------------------------
