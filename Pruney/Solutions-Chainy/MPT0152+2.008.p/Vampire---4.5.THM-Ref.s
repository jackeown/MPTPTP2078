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
% DateTime   : Thu Dec  3 12:33:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  80 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   19
%              Number of atoms          :   44 (  81 expanded)
%              Number of equality atoms :   43 (  80 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    9 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f48])).

fof(f48,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) ),
    inference(forward_demodulation,[],[f47,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f47,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))))) ),
    inference(forward_demodulation,[],[f46,f19])).

fof(f46,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))) ),
    inference(forward_demodulation,[],[f45,f19])).

fof(f45,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))) ),
    inference(forward_demodulation,[],[f44,f19])).

fof(f44,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))) ),
    inference(superposition,[],[f40,f19])).

fof(f40,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) ),
    inference(forward_demodulation,[],[f39,f19])).

fof(f39,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) ),
    inference(forward_demodulation,[],[f38,f19])).

fof(f38,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) ),
    inference(forward_demodulation,[],[f37,f19])).

% (463)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f37,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7))))))) ),
    inference(forward_demodulation,[],[f36,f19])).

fof(f36,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7)))))) ),
    inference(forward_demodulation,[],[f35,f19])).

fof(f35,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7))))) ),
    inference(forward_demodulation,[],[f34,f19])).

fof(f34,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7)))) ),
    inference(forward_demodulation,[],[f33,f19])).

fof(f33,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7))) ),
    inference(backward_demodulation,[],[f31,f19])).

fof(f31,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6))),k1_tarski(sK7)) ),
    inference(definition_unfolding,[],[f15,f30,f29])).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k1_tarski(X3))),k1_tarski(X4)),k2_xboole_0(k1_tarski(X5),k1_tarski(X6))) ),
    inference(definition_unfolding,[],[f23,f27,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k1_tarski(X3))),k1_tarski(X4)) ),
    inference(definition_unfolding,[],[f21,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k1_tarski(X3))) ),
    inference(definition_unfolding,[],[f20,f16,f16])).

% (467)Refutation not found, incomplete strategy% (467)------------------------------
% (467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f5])).

% (460)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

% (468)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% (473)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% (462)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
fof(f30,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5)))),k2_xboole_0(k1_tarski(X6),k1_tarski(X7))) ),
    inference(definition_unfolding,[],[f24,f28,f16])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5)))) ),
    inference(definition_unfolding,[],[f22,f25,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) ),
    inference(definition_unfolding,[],[f17,f16])).

fof(f17,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

% (467)Termination reason: Refutation not found, incomplete strategy

% (467)Memory used [KB]: 10618
% (467)Time elapsed: 0.073 s
% (467)------------------------------
% (467)------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_enumset1)).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

fof(f15,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:37:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (461)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (466)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (458)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (470)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (459)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (469)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (467)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.51  % (470)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))))))),
% 0.21/0.51    inference(forward_demodulation,[],[f47,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))),
% 0.21/0.51    inference(forward_demodulation,[],[f46,f19])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))))),
% 0.21/0.51    inference(forward_demodulation,[],[f45,f19])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))),
% 0.21/0.51    inference(forward_demodulation,[],[f44,f19])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))),
% 0.21/0.51    inference(superposition,[],[f40,f19])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))),
% 0.21/0.51    inference(forward_demodulation,[],[f39,f19])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))))))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))),
% 0.21/0.51    inference(forward_demodulation,[],[f38,f19])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))))))))),
% 0.21/0.51    inference(forward_demodulation,[],[f37,f19])).
% 0.21/0.51  % (463)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7)))))))),
% 0.21/0.51    inference(forward_demodulation,[],[f36,f19])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7))))))),
% 0.21/0.51    inference(forward_demodulation,[],[f35,f19])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7)))))),
% 0.21/0.51    inference(forward_demodulation,[],[f34,f19])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7))))),
% 0.21/0.51    inference(forward_demodulation,[],[f33,f19])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7)))),
% 0.21/0.51    inference(backward_demodulation,[],[f31,f19])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)),k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6))),k1_tarski(sK7))),
% 0.21/0.51    inference(definition_unfolding,[],[f15,f30,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k1_tarski(X3))),k1_tarski(X4)),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f23,f27,f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k1_tarski(X3))),k1_tarski(X4))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f21,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k1_tarski(X3)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f20,f16,f16])).
% 0.21/0.51  % (467)Refutation not found, incomplete strategy% (467)------------------------------
% 0.21/0.51  % (467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  % (460)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).
% 0.21/0.51  % (468)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (473)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (462)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5)))),k2_xboole_0(k1_tarski(X6),k1_tarski(X7)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f24,f28,f16])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5))))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f22,f25,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f17,f16])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  % (467)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (467)Memory used [KB]: 10618
% 0.21/0.51  % (467)Time elapsed: 0.073 s
% 0.21/0.51  % (467)------------------------------
% 0.21/0.51  % (467)------------------------------
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_enumset1)).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7))),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f12,f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK7))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 0.21/0.51    inference(negated_conjecture,[],[f10])).
% 0.21/0.51  fof(f10,conjecture,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (470)------------------------------
% 0.21/0.51  % (470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (470)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (470)Memory used [KB]: 6140
% 0.21/0.51  % (470)Time elapsed: 0.010 s
% 0.21/0.51  % (470)------------------------------
% 0.21/0.51  % (470)------------------------------
% 0.21/0.52  % (450)Success in time 0.153 s
%------------------------------------------------------------------------------
