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
% DateTime   : Thu Dec  3 12:33:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   20 (  32 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   21 (  33 expanded)
%              Number of equality atoms :   20 (  32 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f19])).

fof(f19,plain,(
    k5_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1))) != k5_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1))) ),
    inference(forward_demodulation,[],[f18,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k1_tarski(X1),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f11,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k1_tarski(X2),k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f13,f12])).

fof(f12,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f13,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f11,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f18,plain,(
    k5_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1))) != k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k1_tarski(sK1),k2_tarski(sK0,sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k1_tarski(sK1),k2_tarski(sK0,sK0))))) ),
    inference(definition_unfolding,[],[f10,f15,f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k1_tarski(X2),k2_tarski(X0,X1))),k4_xboole_0(k1_tarski(X3),k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k1_tarski(X2),k2_tarski(X0,X1))))) ),
    inference(definition_unfolding,[],[f14,f12,f15])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f10,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:22:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (803012609)
% 0.13/0.37  ipcrm: permission denied for id (803307533)
% 0.13/0.38  ipcrm: permission denied for id (803405843)
% 0.13/0.39  ipcrm: permission denied for id (803471383)
% 0.13/0.39  ipcrm: permission denied for id (803536921)
% 0.13/0.39  ipcrm: permission denied for id (803635226)
% 0.13/0.39  ipcrm: permission denied for id (803602460)
% 0.13/0.39  ipcrm: permission denied for id (803667997)
% 0.13/0.40  ipcrm: permission denied for id (803733535)
% 0.13/0.40  ipcrm: permission denied for id (803799073)
% 0.13/0.40  ipcrm: permission denied for id (803897381)
% 0.20/0.41  ipcrm: permission denied for id (803962920)
% 0.20/0.41  ipcrm: permission denied for id (803995691)
% 0.20/0.41  ipcrm: permission denied for id (804028460)
% 0.20/0.41  ipcrm: permission denied for id (804061229)
% 0.20/0.42  ipcrm: permission denied for id (804093998)
% 0.20/0.42  ipcrm: permission denied for id (804126768)
% 0.20/0.42  ipcrm: permission denied for id (804159537)
% 0.20/0.42  ipcrm: permission denied for id (804192306)
% 0.20/0.42  ipcrm: permission denied for id (804225075)
% 0.20/0.42  ipcrm: permission denied for id (804257844)
% 0.20/0.43  ipcrm: permission denied for id (804323383)
% 0.20/0.43  ipcrm: permission denied for id (804356152)
% 0.20/0.43  ipcrm: permission denied for id (804388921)
% 0.20/0.43  ipcrm: permission denied for id (804454461)
% 0.20/0.44  ipcrm: permission denied for id (804487231)
% 0.20/0.44  ipcrm: permission denied for id (804520001)
% 0.20/0.44  ipcrm: permission denied for id (804552771)
% 0.20/0.45  ipcrm: permission denied for id (804651081)
% 0.20/0.45  ipcrm: permission denied for id (804683852)
% 0.20/0.46  ipcrm: permission denied for id (804716622)
% 0.20/0.46  ipcrm: permission denied for id (804749391)
% 0.20/0.46  ipcrm: permission denied for id (804782160)
% 0.20/0.46  ipcrm: permission denied for id (804814929)
% 0.20/0.46  ipcrm: permission denied for id (804847699)
% 0.20/0.46  ipcrm: permission denied for id (804880469)
% 0.20/0.47  ipcrm: permission denied for id (804913238)
% 0.20/0.47  ipcrm: permission denied for id (804946008)
% 0.20/0.47  ipcrm: permission denied for id (804978777)
% 0.20/0.47  ipcrm: permission denied for id (805011547)
% 0.20/0.48  ipcrm: permission denied for id (805208164)
% 0.20/0.48  ipcrm: permission denied for id (805240933)
% 0.20/0.49  ipcrm: permission denied for id (805273702)
% 0.20/0.49  ipcrm: permission denied for id (805306471)
% 0.20/0.49  ipcrm: permission denied for id (805339240)
% 0.20/0.49  ipcrm: permission denied for id (805404778)
% 0.20/0.50  ipcrm: permission denied for id (805732470)
% 0.20/0.51  ipcrm: permission denied for id (805765239)
% 0.20/0.51  ipcrm: permission denied for id (805798008)
% 0.20/0.51  ipcrm: permission denied for id (805830777)
% 0.20/0.51  ipcrm: permission denied for id (805863546)
% 0.20/0.58  % (27314)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.59  % (27321)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.59  % (27314)Refutation found. Thanks to Tanya!
% 0.20/0.59  % SZS status Theorem for theBenchmark
% 0.20/0.59  % SZS output start Proof for theBenchmark
% 0.20/0.59  fof(f20,plain,(
% 0.20/0.59    $false),
% 0.20/0.59    inference(trivial_inequality_removal,[],[f19])).
% 0.20/0.59  fof(f19,plain,(
% 0.20/0.59    k5_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1))) != k5_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)))),
% 0.20/0.59    inference(forward_demodulation,[],[f18,f17])).
% 0.20/0.59  fof(f17,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k1_tarski(X1),k2_tarski(X0,X0)))) )),
% 0.20/0.59    inference(definition_unfolding,[],[f11,f15])).
% 0.20/0.59  fof(f15,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)))) )),
% 0.20/0.59    inference(definition_unfolding,[],[f13,f12])).
% 0.20/0.59  fof(f12,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f1])).
% 0.20/0.59  fof(f1,axiom,(
% 0.20/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.59  fof(f13,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f2])).
% 0.20/0.59  fof(f2,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 0.20/0.59  fof(f11,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f4])).
% 0.20/0.59  fof(f4,axiom,(
% 0.20/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.59  fof(f18,plain,(
% 0.20/0.59    k5_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1))) != k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k1_tarski(sK1),k2_tarski(sK0,sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k1_tarski(sK1),k2_tarski(sK0,sK0)))))),
% 0.20/0.59    inference(definition_unfolding,[],[f10,f15,f16])).
% 0.20/0.59  fof(f16,plain,(
% 0.20/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k1_tarski(X2),k2_tarski(X0,X1))),k4_xboole_0(k1_tarski(X3),k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)))))) )),
% 0.20/0.59    inference(definition_unfolding,[],[f14,f12,f15])).
% 0.20/0.59  fof(f14,plain,(
% 0.20/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f3])).
% 0.20/0.59  fof(f3,axiom,(
% 0.20/0.59    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 0.20/0.59  fof(f10,plain,(
% 0.20/0.59    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.20/0.59    inference(cnf_transformation,[],[f9])).
% 0.20/0.59  fof(f9,plain,(
% 0.20/0.59    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.20/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).
% 0.20/0.59  fof(f8,plain,(
% 0.20/0.59    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f7,plain,(
% 0.20/0.59    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.59    inference(ennf_transformation,[],[f6])).
% 0.20/0.59  fof(f6,negated_conjecture,(
% 0.20/0.59    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.59    inference(negated_conjecture,[],[f5])).
% 0.20/0.59  fof(f5,conjecture,(
% 0.20/0.59    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.59  % SZS output end Proof for theBenchmark
% 0.20/0.59  % (27314)------------------------------
% 0.20/0.59  % (27314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (27314)Termination reason: Refutation
% 0.20/0.59  
% 0.20/0.59  % (27314)Memory used [KB]: 6012
% 0.20/0.59  % (27314)Time elapsed: 0.027 s
% 0.20/0.59  % (27314)------------------------------
% 0.20/0.59  % (27314)------------------------------
% 0.20/0.59  % (27165)Success in time 0.236 s
%------------------------------------------------------------------------------
