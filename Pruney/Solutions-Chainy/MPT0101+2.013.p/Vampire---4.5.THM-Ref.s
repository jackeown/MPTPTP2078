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
% DateTime   : Thu Dec  3 12:31:53 EST 2020

% Result     : Theorem 2.71s
% Output     : Refutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 289 expanded)
%              Number of leaves         :   15 (  95 expanded)
%              Depth                    :   14
%              Number of atoms          :   95 ( 310 expanded)
%              Number of equality atoms :   74 ( 284 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3075,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f850,f3060,f3074])).

fof(f3074,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f3073])).

fof(f3073,plain,
    ( $false
    | spl2_5 ),
    inference(subsumption_resolution,[],[f3072,f1118])).

fof(f1118,plain,(
    ! [X24,X23] : k2_xboole_0(X23,X24) = k2_xboole_0(k4_xboole_0(X24,X23),X23) ),
    inference(forward_demodulation,[],[f1074,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f26,f20])).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f1074,plain,(
    ! [X24,X23] : k2_xboole_0(k4_xboole_0(X24,X23),X23) = k2_xboole_0(X23,k2_xboole_0(X23,X24)) ),
    inference(superposition,[],[f215,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f215,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f56,f20])).

fof(f56,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f26,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f3072,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)
    | spl2_5 ),
    inference(forward_demodulation,[],[f3071,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f3071,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k1_xboole_0))
    | spl2_5 ),
    inference(forward_demodulation,[],[f3070,f33])).

fof(f33,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f29,f20])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) ),
    inference(definition_unfolding,[],[f18,f24])).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f18,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f3070,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)))
    | spl2_5 ),
    inference(forward_demodulation,[],[f3062,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f27,f23])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f3062,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_5 ),
    inference(superposition,[],[f3059,f51])).

fof(f51,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X2,k2_xboole_0(X3,X4)) = k2_xboole_0(k2_xboole_0(X3,X2),X4) ),
    inference(superposition,[],[f26,f21])).

fof(f3059,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f3057])).

fof(f3057,plain,
    ( spl2_5
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f3060,plain,
    ( ~ spl2_5
    | spl2_3 ),
    inference(avatar_split_clause,[],[f2940,f847,f3057])).

fof(f847,plain,
    ( spl2_3
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f2940,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_3 ),
    inference(backward_demodulation,[],[f849,f2898])).

fof(f2898,plain,(
    ! [X64,X65,X63] : k2_xboole_0(X64,k4_xboole_0(X65,X63)) = k4_xboole_0(k2_xboole_0(X64,k4_xboole_0(X65,X63)),k4_xboole_0(X63,X64)) ),
    inference(superposition,[],[f132,f747])).

fof(f747,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X5,X3))) ),
    inference(forward_demodulation,[],[f746,f123])).

fof(f123,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X2,k2_xboole_0(X3,X4)),k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f102,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f102,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3 ),
    inference(forward_demodulation,[],[f101,f19])).

fof(f101,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f78,f33])).

fof(f78,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k4_xboole_0(X4,X4)) ),
    inference(superposition,[],[f30,f22])).

fof(f746,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X5,X3))) = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(X4,X5)),k4_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f681,f48])).

fof(f48,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f45,f20])).

fof(f45,plain,(
    ! [X2] : k2_xboole_0(X2,X2) = k2_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f22,f33])).

fof(f681,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X5,X3))) = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(X4,X5)),k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0))) ),
    inference(superposition,[],[f326,f33])).

fof(f326,plain,(
    ! [X6,X4,X7,X5] : k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(X6,X7))) = k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,X6)),k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(X4,X7)))) ),
    inference(backward_demodulation,[],[f89,f300])).

fof(f300,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X3,k4_xboole_0(X4,X2)) = k2_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2))) ),
    inference(superposition,[],[f40,f21])).

fof(f40,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X4,k4_xboole_0(X2,X3)) = k2_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(superposition,[],[f22,f25])).

fof(f89,plain,(
    ! [X6,X4,X7,X5] : k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,X6)),k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(X4,k2_xboole_0(X5,X7))))) = k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(X6,X7))) ),
    inference(forward_demodulation,[],[f88,f25])).

fof(f88,plain,(
    ! [X6,X4,X7,X5] : k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X6,X7)) = k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,X6)),k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(X4,k2_xboole_0(X5,X7))))) ),
    inference(forward_demodulation,[],[f87,f25])).

fof(f87,plain,(
    ! [X6,X4,X7,X5] : k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X6,X7)) = k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,X6)),k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(k4_xboole_0(X4,X5),X7)))) ),
    inference(forward_demodulation,[],[f73,f25])).

fof(f73,plain,(
    ! [X6,X4,X7,X5] : k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X6,X7)) = k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,X6)),k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X4,X5),X7))) ),
    inference(superposition,[],[f30,f25])).

fof(f132,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2 ),
    inference(backward_demodulation,[],[f94,f124])).

fof(f124,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f102,f21])).

fof(f94,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f93,f21])).

fof(f93,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f75,f19])).

fof(f75,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f30,f33])).

fof(f849,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f847])).

fof(f850,plain,
    ( ~ spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f749,f108,f847])).

fof(f108,plain,
    ( spl2_1
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f749,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(backward_demodulation,[],[f110,f747])).

fof(f110,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f111,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f63,f108])).

fof(f63,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(backward_demodulation,[],[f31,f50])).

fof(f31,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f28,f25])).

fof(f28,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f17,f24,f24,f23])).

fof(f17,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:03:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (19443)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (19445)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (19446)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (19455)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (19454)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (19451)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (19442)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (19459)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (19456)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (19449)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (19458)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (19448)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (19444)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (19450)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.51  % (19447)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.52  % (19457)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.52  % (19453)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.52  % (19453)Refutation not found, incomplete strategy% (19453)------------------------------
% 0.21/0.52  % (19453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19453)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19453)Memory used [KB]: 10490
% 0.21/0.52  % (19453)Time elapsed: 0.093 s
% 0.21/0.52  % (19453)------------------------------
% 0.21/0.52  % (19453)------------------------------
% 0.21/0.52  % (19452)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 2.71/0.72  % (19457)Refutation found. Thanks to Tanya!
% 2.71/0.72  % SZS status Theorem for theBenchmark
% 2.71/0.72  % SZS output start Proof for theBenchmark
% 2.71/0.72  fof(f3075,plain,(
% 2.71/0.72    $false),
% 2.71/0.72    inference(avatar_sat_refutation,[],[f111,f850,f3060,f3074])).
% 2.71/0.72  fof(f3074,plain,(
% 2.71/0.72    spl2_5),
% 2.71/0.72    inference(avatar_contradiction_clause,[],[f3073])).
% 2.71/0.72  fof(f3073,plain,(
% 2.71/0.72    $false | spl2_5),
% 2.71/0.72    inference(subsumption_resolution,[],[f3072,f1118])).
% 2.71/0.72  fof(f1118,plain,(
% 2.71/0.72    ( ! [X24,X23] : (k2_xboole_0(X23,X24) = k2_xboole_0(k4_xboole_0(X24,X23),X23)) )),
% 2.71/0.72    inference(forward_demodulation,[],[f1074,f50])).
% 2.71/0.72  fof(f50,plain,(
% 2.71/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.71/0.72    inference(superposition,[],[f26,f20])).
% 2.71/0.72  fof(f20,plain,(
% 2.71/0.72    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.71/0.72    inference(cnf_transformation,[],[f13])).
% 2.71/0.72  fof(f13,plain,(
% 2.71/0.72    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.71/0.72    inference(rectify,[],[f3])).
% 2.71/0.72  fof(f3,axiom,(
% 2.71/0.72    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.71/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.71/0.72  fof(f26,plain,(
% 2.71/0.72    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.71/0.72    inference(cnf_transformation,[],[f8])).
% 2.71/0.72  fof(f8,axiom,(
% 2.71/0.72    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.71/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 2.71/0.72  fof(f1074,plain,(
% 2.71/0.72    ( ! [X24,X23] : (k2_xboole_0(k4_xboole_0(X24,X23),X23) = k2_xboole_0(X23,k2_xboole_0(X23,X24))) )),
% 2.71/0.72    inference(superposition,[],[f215,f22])).
% 2.71/0.72  fof(f22,plain,(
% 2.71/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.71/0.72    inference(cnf_transformation,[],[f4])).
% 2.71/0.72  fof(f4,axiom,(
% 2.71/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.71/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.71/0.72  fof(f215,plain,(
% 2.71/0.72    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.71/0.72    inference(superposition,[],[f56,f20])).
% 2.71/0.72  fof(f56,plain,(
% 2.71/0.72    ( ! [X6,X7,X5] : (k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6))) )),
% 2.71/0.72    inference(superposition,[],[f26,f21])).
% 2.71/0.72  fof(f21,plain,(
% 2.71/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.71/0.72    inference(cnf_transformation,[],[f1])).
% 2.71/0.72  fof(f1,axiom,(
% 2.71/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.71/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.71/0.72  fof(f3072,plain,(
% 2.71/0.72    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) | spl2_5),
% 2.71/0.72    inference(forward_demodulation,[],[f3071,f19])).
% 2.71/0.72  fof(f19,plain,(
% 2.71/0.72    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.71/0.72    inference(cnf_transformation,[],[f5])).
% 2.71/0.72  fof(f5,axiom,(
% 2.71/0.72    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.71/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.71/0.72  fof(f3071,plain,(
% 2.71/0.72    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k1_xboole_0)) | spl2_5),
% 2.71/0.72    inference(forward_demodulation,[],[f3070,f33])).
% 2.71/0.72  fof(f33,plain,(
% 2.71/0.72    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 2.71/0.72    inference(superposition,[],[f29,f20])).
% 2.71/0.72  fof(f29,plain,(
% 2.71/0.72    ( ! [X0] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) )),
% 2.71/0.72    inference(definition_unfolding,[],[f18,f24])).
% 2.71/0.72  fof(f24,plain,(
% 2.71/0.72    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 2.71/0.72    inference(cnf_transformation,[],[f2])).
% 2.71/0.72  fof(f2,axiom,(
% 2.71/0.72    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 2.71/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 2.71/0.72  fof(f18,plain,(
% 2.71/0.72    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.71/0.72    inference(cnf_transformation,[],[f10])).
% 2.71/0.72  fof(f10,axiom,(
% 2.71/0.72    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.71/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.71/0.72  fof(f3070,plain,(
% 2.71/0.72    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK1,sK1))) | spl2_5),
% 2.71/0.72    inference(forward_demodulation,[],[f3062,f30])).
% 2.71/0.72  fof(f30,plain,(
% 2.71/0.72    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 2.71/0.72    inference(definition_unfolding,[],[f27,f23])).
% 2.71/0.72  fof(f23,plain,(
% 2.71/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.71/0.72    inference(cnf_transformation,[],[f7])).
% 2.71/0.72  fof(f7,axiom,(
% 2.71/0.72    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.71/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.71/0.72  fof(f27,plain,(
% 2.71/0.72    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 2.71/0.72    inference(cnf_transformation,[],[f9])).
% 2.71/0.72  fof(f9,axiom,(
% 2.71/0.72    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 2.71/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 2.71/0.72  fof(f3062,plain,(
% 2.71/0.72    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_5),
% 2.71/0.72    inference(superposition,[],[f3059,f51])).
% 2.71/0.72  fof(f51,plain,(
% 2.71/0.72    ( ! [X4,X2,X3] : (k2_xboole_0(X2,k2_xboole_0(X3,X4)) = k2_xboole_0(k2_xboole_0(X3,X2),X4)) )),
% 2.71/0.72    inference(superposition,[],[f26,f21])).
% 2.71/0.72  fof(f3059,plain,(
% 2.71/0.72    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_5),
% 2.71/0.72    inference(avatar_component_clause,[],[f3057])).
% 2.71/0.72  fof(f3057,plain,(
% 2.71/0.72    spl2_5 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.71/0.72    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 2.71/0.72  fof(f3060,plain,(
% 2.71/0.72    ~spl2_5 | spl2_3),
% 2.71/0.72    inference(avatar_split_clause,[],[f2940,f847,f3057])).
% 2.71/0.72  fof(f847,plain,(
% 2.71/0.72    spl2_3 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.71/0.72    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.71/0.72  fof(f2940,plain,(
% 2.71/0.72    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_3),
% 2.71/0.72    inference(backward_demodulation,[],[f849,f2898])).
% 2.71/0.72  fof(f2898,plain,(
% 2.71/0.72    ( ! [X64,X65,X63] : (k2_xboole_0(X64,k4_xboole_0(X65,X63)) = k4_xboole_0(k2_xboole_0(X64,k4_xboole_0(X65,X63)),k4_xboole_0(X63,X64))) )),
% 2.71/0.72    inference(superposition,[],[f132,f747])).
% 2.71/0.72  fof(f747,plain,(
% 2.71/0.72    ( ! [X4,X5,X3] : (k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X5,X3)))) )),
% 2.71/0.72    inference(forward_demodulation,[],[f746,f123])).
% 2.71/0.72  fof(f123,plain,(
% 2.71/0.72    ( ! [X4,X2,X3] : (k4_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X2,k2_xboole_0(X3,X4)),k4_xboole_0(X2,X3))) )),
% 2.71/0.72    inference(superposition,[],[f102,f25])).
% 2.71/0.72  fof(f25,plain,(
% 2.71/0.72    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.71/0.72    inference(cnf_transformation,[],[f6])).
% 2.71/0.72  fof(f6,axiom,(
% 2.71/0.72    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.71/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.71/0.72  fof(f102,plain,(
% 2.71/0.72    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3) )),
% 2.71/0.72    inference(forward_demodulation,[],[f101,f19])).
% 2.71/0.72  fof(f101,plain,(
% 2.71/0.72    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k1_xboole_0)) )),
% 2.71/0.72    inference(forward_demodulation,[],[f78,f33])).
% 2.71/0.72  fof(f78,plain,(
% 2.71/0.72    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k4_xboole_0(X4,X4))) )),
% 2.71/0.72    inference(superposition,[],[f30,f22])).
% 2.71/0.72  fof(f746,plain,(
% 2.71/0.72    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X5,X3))) = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(X4,X5)),k4_xboole_0(X3,X4))) )),
% 2.71/0.72    inference(forward_demodulation,[],[f681,f48])).
% 2.71/0.72  fof(f48,plain,(
% 2.71/0.72    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 2.71/0.72    inference(forward_demodulation,[],[f45,f20])).
% 2.71/0.72  fof(f45,plain,(
% 2.71/0.72    ( ! [X2] : (k2_xboole_0(X2,X2) = k2_xboole_0(X2,k1_xboole_0)) )),
% 2.71/0.72    inference(superposition,[],[f22,f33])).
% 2.71/0.72  fof(f681,plain,(
% 2.71/0.72    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X5,X3))) = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(X4,X5)),k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0)))) )),
% 2.71/0.72    inference(superposition,[],[f326,f33])).
% 2.71/0.72  fof(f326,plain,(
% 2.71/0.72    ( ! [X6,X4,X7,X5] : (k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(X6,X7))) = k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,X6)),k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(X4,X7))))) )),
% 2.71/0.72    inference(backward_demodulation,[],[f89,f300])).
% 2.71/0.72  fof(f300,plain,(
% 2.71/0.72    ( ! [X4,X2,X3] : (k2_xboole_0(X3,k4_xboole_0(X4,X2)) = k2_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2)))) )),
% 2.71/0.72    inference(superposition,[],[f40,f21])).
% 2.71/0.72  fof(f40,plain,(
% 2.71/0.72    ( ! [X4,X2,X3] : (k2_xboole_0(X4,k4_xboole_0(X2,X3)) = k2_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X4)))) )),
% 2.71/0.72    inference(superposition,[],[f22,f25])).
% 2.71/0.72  fof(f89,plain,(
% 2.71/0.72    ( ! [X6,X4,X7,X5] : (k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,X6)),k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(X4,k2_xboole_0(X5,X7))))) = k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(X6,X7)))) )),
% 2.71/0.72    inference(forward_demodulation,[],[f88,f25])).
% 2.71/0.72  fof(f88,plain,(
% 2.71/0.72    ( ! [X6,X4,X7,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X6,X7)) = k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,X6)),k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(X4,k2_xboole_0(X5,X7)))))) )),
% 2.71/0.72    inference(forward_demodulation,[],[f87,f25])).
% 2.71/0.72  fof(f87,plain,(
% 2.71/0.72    ( ! [X6,X4,X7,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X6,X7)) = k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,X6)),k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(k4_xboole_0(X4,X5),X7))))) )),
% 2.71/0.72    inference(forward_demodulation,[],[f73,f25])).
% 2.71/0.72  fof(f73,plain,(
% 2.71/0.72    ( ! [X6,X4,X7,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X6,X7)) = k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,X6)),k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X4,X5),X7)))) )),
% 2.71/0.72    inference(superposition,[],[f30,f25])).
% 2.71/0.72  fof(f132,plain,(
% 2.71/0.72    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) )),
% 2.71/0.72    inference(backward_demodulation,[],[f94,f124])).
% 2.71/0.72  fof(f124,plain,(
% 2.71/0.72    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 2.71/0.72    inference(superposition,[],[f102,f21])).
% 2.71/0.72  fof(f94,plain,(
% 2.71/0.72    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 2.71/0.72    inference(forward_demodulation,[],[f93,f21])).
% 2.71/0.72  fof(f93,plain,(
% 2.71/0.72    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),X2)) )),
% 2.71/0.72    inference(forward_demodulation,[],[f75,f19])).
% 2.71/0.72  fof(f75,plain,(
% 2.71/0.72    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k1_xboole_0))) )),
% 2.71/0.72    inference(superposition,[],[f30,f33])).
% 2.71/0.72  fof(f849,plain,(
% 2.71/0.72    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_3),
% 2.71/0.72    inference(avatar_component_clause,[],[f847])).
% 2.71/0.73  fof(f850,plain,(
% 2.71/0.73    ~spl2_3 | spl2_1),
% 2.71/0.73    inference(avatar_split_clause,[],[f749,f108,f847])).
% 2.71/0.73  fof(f108,plain,(
% 2.71/0.73    spl2_1 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 2.71/0.73    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.71/0.73  fof(f749,plain,(
% 2.71/0.73    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_1),
% 2.71/0.73    inference(backward_demodulation,[],[f110,f747])).
% 2.71/0.73  fof(f110,plain,(
% 2.71/0.73    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl2_1),
% 2.71/0.73    inference(avatar_component_clause,[],[f108])).
% 2.71/0.73  fof(f111,plain,(
% 2.71/0.73    ~spl2_1),
% 2.71/0.73    inference(avatar_split_clause,[],[f63,f108])).
% 2.71/0.73  fof(f63,plain,(
% 2.71/0.73    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 2.71/0.73    inference(backward_demodulation,[],[f31,f50])).
% 2.71/0.73  fof(f31,plain,(
% 2.71/0.73    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 2.71/0.73    inference(backward_demodulation,[],[f28,f25])).
% 2.71/0.73  fof(f28,plain,(
% 2.71/0.73    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 2.71/0.73    inference(definition_unfolding,[],[f17,f24,f24,f23])).
% 2.71/0.73  fof(f17,plain,(
% 2.71/0.73    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.71/0.73    inference(cnf_transformation,[],[f16])).
% 2.71/0.73  fof(f16,plain,(
% 2.71/0.73    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.71/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 2.71/0.73  fof(f15,plain,(
% 2.71/0.73    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.71/0.73    introduced(choice_axiom,[])).
% 2.71/0.73  fof(f14,plain,(
% 2.71/0.73    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.71/0.73    inference(ennf_transformation,[],[f12])).
% 2.71/0.73  fof(f12,negated_conjecture,(
% 2.71/0.73    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.71/0.73    inference(negated_conjecture,[],[f11])).
% 2.71/0.73  fof(f11,conjecture,(
% 2.71/0.73    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.71/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 2.71/0.73  % SZS output end Proof for theBenchmark
% 2.71/0.73  % (19457)------------------------------
% 2.71/0.73  % (19457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.71/0.73  % (19457)Termination reason: Refutation
% 2.71/0.73  
% 2.71/0.73  % (19457)Memory used [KB]: 15095
% 2.71/0.73  % (19457)Time elapsed: 0.290 s
% 2.71/0.73  % (19457)------------------------------
% 2.71/0.73  % (19457)------------------------------
% 2.71/0.73  % (19439)Success in time 0.364 s
%------------------------------------------------------------------------------
