%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 423 expanded)
%              Number of leaves         :   14 ( 144 expanded)
%              Depth                    :   19
%              Number of atoms          :   95 ( 443 expanded)
%              Number of equality atoms :   77 ( 416 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1494,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f43,f44,f1489,f1493])).

fof(f1493,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f1492])).

fof(f1492,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f34,f1491])).

fof(f1491,plain,(
    ! [X10,X9] : k2_xboole_0(X9,X10) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f1490,f1052])).

fof(f1052,plain,(
    ! [X14,X15,X13] : k2_xboole_0(X13,X15) = k2_xboole_0(k2_xboole_0(X13,X15),k4_xboole_0(X13,X14)) ),
    inference(forward_demodulation,[],[f1051,f74])).

fof(f74,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(backward_demodulation,[],[f46,f71])).

fof(f71,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = X1 ),
    inference(backward_demodulation,[],[f45,f69])).

fof(f69,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f63,f18])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f63,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f21,f18])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f45,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f20,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f28,f18])).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f17,f22])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f46,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f45,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1051,plain,(
    ! [X14,X15,X13] : k2_xboole_0(k2_xboole_0(X13,X15),k4_xboole_0(X13,X14)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X13,X15)) ),
    inference(forward_demodulation,[],[f1038,f19])).

fof(f1038,plain,(
    ! [X14,X15,X13] : k2_xboole_0(k2_xboole_0(X13,X15),k4_xboole_0(X13,X14)) = k2_xboole_0(k2_xboole_0(X13,X15),k1_xboole_0) ),
    inference(superposition,[],[f20,f837])).

fof(f837,plain,(
    ! [X37,X35,X36] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X35,X36),k2_xboole_0(X35,X37)) ),
    inference(superposition,[],[f264,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f264,plain,(
    ! [X8,X7,X9] : k1_xboole_0 = k4_xboole_0(X7,k2_xboole_0(k2_xboole_0(X8,X7),X9)) ),
    inference(forward_demodulation,[],[f243,f75])).

fof(f75,plain,(
    ! [X9] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X9) ),
    inference(forward_demodulation,[],[f72,f36])).

fof(f72,plain,(
    ! [X9] : k4_xboole_0(k1_xboole_0,X9) = k4_xboole_0(X9,X9) ),
    inference(backward_demodulation,[],[f62,f71])).

fof(f62,plain,(
    ! [X9] : k4_xboole_0(k1_xboole_0,X9) = k4_xboole_0(k2_xboole_0(X9,X9),X9) ),
    inference(superposition,[],[f21,f46])).

fof(f243,plain,(
    ! [X8,X7,X9] : k4_xboole_0(k1_xboole_0,X9) = k4_xboole_0(X7,k2_xboole_0(k2_xboole_0(X8,X7),X9)) ),
    inference(superposition,[],[f26,f140])).

fof(f140,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f138,f19])).

fof(f138,plain,(
    ! [X6,X7] : k1_xboole_0 = k4_xboole_0(X6,k2_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f136,f36])).

fof(f136,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k2_xboole_0(X6,X7)) = k4_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f21,f104])).

fof(f104,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f99,f20])).

fof(f99,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f20,f58])).

fof(f58,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X3,X2),X3) ),
    inference(superposition,[],[f21,f19])).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1490,plain,(
    ! [X10,X9] : k2_xboole_0(k2_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k2_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f1347,f19])).

fof(f1347,plain,(
    ! [X10,X9] : k2_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),k2_xboole_0(X9,X10)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(superposition,[],[f309,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f25,f22])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).

fof(f309,plain,(
    ! [X12,X11] : k2_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(X12,X11),X11) ),
    inference(forward_demodulation,[],[f308,f74])).

fof(f308,plain,(
    ! [X12,X11] : k2_xboole_0(k4_xboole_0(X12,X11),X11) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X11,X12)) ),
    inference(forward_demodulation,[],[f280,f19])).

fof(f280,plain,(
    ! [X12,X11] : k2_xboole_0(k4_xboole_0(X12,X11),X11) = k2_xboole_0(k2_xboole_0(X11,X12),k1_xboole_0) ),
    inference(superposition,[],[f194,f20])).

fof(f194,plain,(
    ! [X4,X3] : k2_xboole_0(X3,X4) = k2_xboole_0(k2_xboole_0(X4,X3),k1_xboole_0) ),
    inference(forward_demodulation,[],[f181,f116])).

fof(f116,plain,(
    ! [X6,X5] : k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f115,f78])).

fof(f78,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X2,k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f65,f20])).

fof(f65,plain,(
    ! [X2,X1] : k2_xboole_0(X2,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f20,f21])).

fof(f115,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X5)) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f108,f19])).

fof(f108,plain,(
    ! [X6,X5] : k2_xboole_0(k2_xboole_0(X6,X5),X5) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f78,f78])).

fof(f181,plain,(
    ! [X4,X3] : k2_xboole_0(k2_xboole_0(X4,X3),k1_xboole_0) = k2_xboole_0(k2_xboole_0(X4,X3),k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f20,f149])).

fof(f149,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X4,X3)) ),
    inference(backward_demodulation,[],[f114,f140])).

fof(f114,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k2_xboole_0(X4,X3)) = k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X4,X3)) ),
    inference(superposition,[],[f21,f78])).

fof(f34,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl2_1
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1489,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f1488])).

fof(f1488,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f42,f1487])).

fof(f1487,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f1486,f1052])).

fof(f1486,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f1343,f19])).

fof(f1343,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f20,f30])).

fof(f42,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl2_2
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f44,plain,
    ( ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f38,f32,f40])).

fof(f38,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | spl2_1 ),
    inference(superposition,[],[f34,f19])).

fof(f43,plain,
    ( ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f37,f32,f40])).

fof(f37,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | spl2_1 ),
    inference(superposition,[],[f34,f19])).

fof(f35,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f27,f32])).

fof(f27,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f16,f24,f22])).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f16,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (21774)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.46  % (21766)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (21765)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (21767)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (21780)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (21775)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (21775)Refutation not found, incomplete strategy% (21775)------------------------------
% 0.21/0.48  % (21775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21775)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (21775)Memory used [KB]: 10490
% 0.21/0.48  % (21775)Time elapsed: 0.063 s
% 0.21/0.48  % (21775)------------------------------
% 0.21/0.48  % (21775)------------------------------
% 0.21/0.48  % (21778)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (21770)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (21773)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (21781)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (21768)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (21764)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (21772)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (21771)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (21769)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (21779)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (21776)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.52  % (21777)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.54  % (21774)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f1494,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f35,f43,f44,f1489,f1493])).
% 0.21/0.54  fof(f1493,plain,(
% 0.21/0.54    spl2_1),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f1492])).
% 0.21/0.54  fof(f1492,plain,(
% 0.21/0.54    $false | spl2_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f34,f1491])).
% 0.21/0.54  fof(f1491,plain,(
% 0.21/0.54    ( ! [X10,X9] : (k2_xboole_0(X9,X10) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f1490,f1052])).
% 0.21/0.54  fof(f1052,plain,(
% 0.21/0.54    ( ! [X14,X15,X13] : (k2_xboole_0(X13,X15) = k2_xboole_0(k2_xboole_0(X13,X15),k4_xboole_0(X13,X14))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f1051,f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.21/0.54    inference(backward_demodulation,[],[f46,f71])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X1] : (k2_xboole_0(X1,X1) = X1) )),
% 0.21/0.54    inference(backward_demodulation,[],[f45,f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 0.21/0.54    inference(forward_demodulation,[],[f63,f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 0.21/0.54    inference(superposition,[],[f21,f18])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X1] : (k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0)) )),
% 0.21/0.54    inference(superposition,[],[f20,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.54    inference(backward_demodulation,[],[f28,f18])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f17,f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X1] : (k2_xboole_0(X1,X1) = k2_xboole_0(k1_xboole_0,X1)) )),
% 0.21/0.54    inference(superposition,[],[f45,f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.54  fof(f1051,plain,(
% 0.21/0.54    ( ! [X14,X15,X13] : (k2_xboole_0(k2_xboole_0(X13,X15),k4_xboole_0(X13,X14)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X13,X15))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f1038,f19])).
% 0.21/0.54  fof(f1038,plain,(
% 0.21/0.54    ( ! [X14,X15,X13] : (k2_xboole_0(k2_xboole_0(X13,X15),k4_xboole_0(X13,X14)) = k2_xboole_0(k2_xboole_0(X13,X15),k1_xboole_0)) )),
% 0.21/0.54    inference(superposition,[],[f20,f837])).
% 0.21/0.54  fof(f837,plain,(
% 0.21/0.54    ( ! [X37,X35,X36] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X35,X36),k2_xboole_0(X35,X37))) )),
% 0.21/0.54    inference(superposition,[],[f264,f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f23,f22])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.54  fof(f264,plain,(
% 0.21/0.54    ( ! [X8,X7,X9] : (k1_xboole_0 = k4_xboole_0(X7,k2_xboole_0(k2_xboole_0(X8,X7),X9))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f243,f75])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X9] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X9)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f72,f36])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X9] : (k4_xboole_0(k1_xboole_0,X9) = k4_xboole_0(X9,X9)) )),
% 0.21/0.54    inference(backward_demodulation,[],[f62,f71])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X9] : (k4_xboole_0(k1_xboole_0,X9) = k4_xboole_0(k2_xboole_0(X9,X9),X9)) )),
% 0.21/0.54    inference(superposition,[],[f21,f46])).
% 0.21/0.54  fof(f243,plain,(
% 0.21/0.54    ( ! [X8,X7,X9] : (k4_xboole_0(k1_xboole_0,X9) = k4_xboole_0(X7,k2_xboole_0(k2_xboole_0(X8,X7),X9))) )),
% 0.21/0.54    inference(superposition,[],[f26,f140])).
% 0.21/0.54  fof(f140,plain,(
% 0.21/0.54    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 0.21/0.54    inference(superposition,[],[f138,f19])).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(X6,k2_xboole_0(X6,X7))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f136,f36])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    ( ! [X6,X7] : (k4_xboole_0(X6,k2_xboole_0(X6,X7)) = k4_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,X7))) )),
% 0.21/0.54    inference(superposition,[],[f21,f104])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f99,f20])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 0.21/0.54    inference(superposition,[],[f20,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X3,X2),X3)) )),
% 0.21/0.54    inference(superposition,[],[f21,f19])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.54  fof(f1490,plain,(
% 0.21/0.54    ( ! [X10,X9] : (k2_xboole_0(k2_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k2_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f1347,f19])).
% 0.21/0.54  fof(f1347,plain,(
% 0.21/0.54    ( ! [X10,X9] : (k2_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),k2_xboole_0(X9,X10)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 0.21/0.54    inference(superposition,[],[f309,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f25,f22])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).
% 0.21/0.54  fof(f309,plain,(
% 0.21/0.54    ( ! [X12,X11] : (k2_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(X12,X11),X11)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f308,f74])).
% 0.21/0.54  fof(f308,plain,(
% 0.21/0.54    ( ! [X12,X11] : (k2_xboole_0(k4_xboole_0(X12,X11),X11) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X11,X12))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f280,f19])).
% 0.21/0.54  fof(f280,plain,(
% 0.21/0.54    ( ! [X12,X11] : (k2_xboole_0(k4_xboole_0(X12,X11),X11) = k2_xboole_0(k2_xboole_0(X11,X12),k1_xboole_0)) )),
% 0.21/0.54    inference(superposition,[],[f194,f20])).
% 0.21/0.54  fof(f194,plain,(
% 0.21/0.54    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k2_xboole_0(k2_xboole_0(X4,X3),k1_xboole_0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f181,f116])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    ( ! [X6,X5] : (k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f115,f78])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X2,k2_xboole_0(X1,X2))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f65,f20])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X2,X1] : (k2_xboole_0(X2,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k4_xboole_0(X1,X2))) )),
% 0.21/0.54    inference(superposition,[],[f20,f21])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    ( ! [X6,X5] : (k2_xboole_0(X5,k2_xboole_0(X6,X5)) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f108,f19])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ( ! [X6,X5] : (k2_xboole_0(k2_xboole_0(X6,X5),X5) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6))) )),
% 0.21/0.54    inference(superposition,[],[f78,f78])).
% 0.21/0.54  fof(f181,plain,(
% 0.21/0.54    ( ! [X4,X3] : (k2_xboole_0(k2_xboole_0(X4,X3),k1_xboole_0) = k2_xboole_0(k2_xboole_0(X4,X3),k2_xboole_0(X3,X4))) )),
% 0.21/0.54    inference(superposition,[],[f20,f149])).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X4,X3))) )),
% 0.21/0.54    inference(backward_demodulation,[],[f114,f140])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    ( ! [X4,X3] : (k4_xboole_0(X3,k2_xboole_0(X4,X3)) = k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X4,X3))) )),
% 0.21/0.54    inference(superposition,[],[f21,f78])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    spl2_1 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.54  fof(f1489,plain,(
% 0.21/0.54    spl2_2),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f1488])).
% 0.21/0.54  fof(f1488,plain,(
% 0.21/0.54    $false | spl2_2),
% 0.21/0.54    inference(subsumption_resolution,[],[f42,f1487])).
% 0.21/0.54  fof(f1487,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f1486,f1052])).
% 0.21/0.54  fof(f1486,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f1343,f19])).
% 0.21/0.54  fof(f1343,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) )),
% 0.21/0.54    inference(superposition,[],[f20,f30])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | spl2_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    spl2_2 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ~spl2_2 | spl2_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f38,f32,f40])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | spl2_1),
% 0.21/0.54    inference(superposition,[],[f34,f19])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ~spl2_2 | spl2_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f37,f32,f40])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | spl2_1),
% 0.21/0.54    inference(superposition,[],[f34,f19])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ~spl2_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f27,f32])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.21/0.54    inference(definition_unfolding,[],[f16,f24,f22])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.54    inference(negated_conjecture,[],[f11])).
% 0.21/0.54  fof(f11,conjecture,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (21774)------------------------------
% 0.21/0.54  % (21774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21774)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (21774)Memory used [KB]: 7036
% 0.21/0.54  % (21774)Time elapsed: 0.084 s
% 0.21/0.54  % (21774)------------------------------
% 0.21/0.54  % (21774)------------------------------
% 0.21/0.54  % (21763)Success in time 0.184 s
%------------------------------------------------------------------------------
