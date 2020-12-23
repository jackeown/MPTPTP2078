%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:36 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   25 (  58 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :   12
%              Number of atoms          :   32 (  86 expanded)
%              Number of equality atoms :   31 (  85 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,plain,(
    $false ),
    inference(subsumption_resolution,[],[f59,f12])).

fof(f12,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( k1_xboole_0 != sK0
    & k1_xboole_0 = k2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 != X0
        & k2_xboole_0(X0,X1) = k1_xboole_0 )
   => ( k1_xboole_0 != sK0
      & k1_xboole_0 = k2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != X0
      & k2_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(X0,X1) = k1_xboole_0
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = k1_xboole_0
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

fof(f59,plain,(
    k1_xboole_0 = sK0 ),
    inference(superposition,[],[f51,f13])).

fof(f13,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f51,plain,(
    ! [X16] : k2_xboole_0(sK0,X16) = X16 ),
    inference(forward_demodulation,[],[f49,f17])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f15,f13])).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f49,plain,(
    ! [X16] : k2_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X16)) = X16 ),
    inference(backward_demodulation,[],[f42,f48])).

fof(f48,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f44,f11])).

fof(f11,plain,(
    k1_xboole_0 = k2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f44,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f42,f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f42,plain,(
    ! [X16] : k2_xboole_0(sK0,k2_xboole_0(sK1,X16)) = X16 ),
    inference(forward_demodulation,[],[f31,f17])).

fof(f31,plain,(
    ! [X16] : k2_xboole_0(sK0,k2_xboole_0(sK1,X16)) = k2_xboole_0(k1_xboole_0,X16) ),
    inference(superposition,[],[f16,f11])).

fof(f16,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n024.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:28:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.44  % (5244)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.19/0.45  % (5244)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.45  % SZS output start Proof for theBenchmark
% 0.19/0.45  fof(f66,plain,(
% 0.19/0.45    $false),
% 0.19/0.45    inference(subsumption_resolution,[],[f59,f12])).
% 0.19/0.45  fof(f12,plain,(
% 0.19/0.45    k1_xboole_0 != sK0),
% 0.19/0.45    inference(cnf_transformation,[],[f10])).
% 0.19/0.45  fof(f10,plain,(
% 0.19/0.45    k1_xboole_0 != sK0 & k1_xboole_0 = k2_xboole_0(sK0,sK1)),
% 0.19/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f9])).
% 0.19/0.45  fof(f9,plain,(
% 0.19/0.45    ? [X0,X1] : (k1_xboole_0 != X0 & k2_xboole_0(X0,X1) = k1_xboole_0) => (k1_xboole_0 != sK0 & k1_xboole_0 = k2_xboole_0(sK0,sK1))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f8,plain,(
% 0.19/0.45    ? [X0,X1] : (k1_xboole_0 != X0 & k2_xboole_0(X0,X1) = k1_xboole_0)),
% 0.19/0.45    inference(ennf_transformation,[],[f6])).
% 0.19/0.45  fof(f6,negated_conjecture,(
% 0.19/0.45    ~! [X0,X1] : (k2_xboole_0(X0,X1) = k1_xboole_0 => k1_xboole_0 = X0)),
% 0.19/0.45    inference(negated_conjecture,[],[f5])).
% 0.19/0.45  fof(f5,conjecture,(
% 0.19/0.45    ! [X0,X1] : (k2_xboole_0(X0,X1) = k1_xboole_0 => k1_xboole_0 = X0)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).
% 0.19/0.45  fof(f59,plain,(
% 0.19/0.45    k1_xboole_0 = sK0),
% 0.19/0.45    inference(superposition,[],[f51,f13])).
% 0.19/0.45  fof(f13,plain,(
% 0.19/0.45    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.45    inference(cnf_transformation,[],[f3])).
% 0.19/0.45  fof(f3,axiom,(
% 0.19/0.45    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.19/0.45  fof(f51,plain,(
% 0.19/0.45    ( ! [X16] : (k2_xboole_0(sK0,X16) = X16) )),
% 0.19/0.45    inference(forward_demodulation,[],[f49,f17])).
% 0.19/0.45  fof(f17,plain,(
% 0.19/0.45    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.19/0.45    inference(superposition,[],[f15,f13])).
% 0.19/0.45  fof(f15,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f1])).
% 0.19/0.45  fof(f1,axiom,(
% 0.19/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.19/0.45  fof(f49,plain,(
% 0.19/0.45    ( ! [X16] : (k2_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X16)) = X16) )),
% 0.19/0.45    inference(backward_demodulation,[],[f42,f48])).
% 0.19/0.45  fof(f48,plain,(
% 0.19/0.45    k1_xboole_0 = sK1),
% 0.19/0.45    inference(forward_demodulation,[],[f44,f11])).
% 0.19/0.45  fof(f11,plain,(
% 0.19/0.45    k1_xboole_0 = k2_xboole_0(sK0,sK1)),
% 0.19/0.45    inference(cnf_transformation,[],[f10])).
% 0.19/0.45  fof(f44,plain,(
% 0.19/0.45    sK1 = k2_xboole_0(sK0,sK1)),
% 0.19/0.45    inference(superposition,[],[f42,f14])).
% 0.19/0.45  fof(f14,plain,(
% 0.19/0.45    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.19/0.45    inference(cnf_transformation,[],[f7])).
% 0.19/0.45  fof(f7,plain,(
% 0.19/0.45    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.19/0.45    inference(rectify,[],[f2])).
% 0.19/0.45  fof(f2,axiom,(
% 0.19/0.45    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.19/0.45  fof(f42,plain,(
% 0.19/0.45    ( ! [X16] : (k2_xboole_0(sK0,k2_xboole_0(sK1,X16)) = X16) )),
% 0.19/0.45    inference(forward_demodulation,[],[f31,f17])).
% 0.19/0.45  fof(f31,plain,(
% 0.19/0.45    ( ! [X16] : (k2_xboole_0(sK0,k2_xboole_0(sK1,X16)) = k2_xboole_0(k1_xboole_0,X16)) )),
% 0.19/0.45    inference(superposition,[],[f16,f11])).
% 0.19/0.45  fof(f16,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f4])).
% 0.19/0.45  fof(f4,axiom,(
% 0.19/0.45    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.19/0.45  % SZS output end Proof for theBenchmark
% 0.19/0.45  % (5244)------------------------------
% 0.19/0.45  % (5244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (5244)Termination reason: Refutation
% 0.19/0.45  
% 0.19/0.45  % (5244)Memory used [KB]: 1663
% 0.19/0.45  % (5244)Time elapsed: 0.005 s
% 0.19/0.45  % (5244)------------------------------
% 0.19/0.45  % (5244)------------------------------
% 0.19/0.45  % (5225)Success in time 0.099 s
%------------------------------------------------------------------------------
