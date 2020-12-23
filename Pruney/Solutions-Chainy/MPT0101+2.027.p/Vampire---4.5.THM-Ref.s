%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:55 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 208 expanded)
%              Number of leaves         :   13 (  73 expanded)
%              Depth                    :   13
%              Number of atoms          :   85 ( 227 expanded)
%              Number of equality atoms :   66 ( 203 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1442,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f481,f1438,f1441])).

fof(f1441,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f1440])).

fof(f1440,plain,
    ( $false
    | spl2_5 ),
    inference(subsumption_resolution,[],[f1439,f71])).

fof(f71,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))) ),
    inference(superposition,[],[f25,f15])).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f20,f19,f17])).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f19,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f1439,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | spl2_5 ),
    inference(superposition,[],[f1437,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1437,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f1435])).

fof(f1435,plain,
    ( spl2_5
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f1438,plain,
    ( ~ spl2_5
    | spl2_3 ),
    inference(avatar_split_clause,[],[f1282,f478,f1435])).

fof(f478,plain,
    ( spl2_3
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f1282,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_3 ),
    inference(backward_demodulation,[],[f480,f1280])).

fof(f1280,plain,(
    ! [X12,X10,X11] : k4_xboole_0(X10,k4_xboole_0(X10,X11)) = k4_xboole_0(X10,k2_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X12,X10))) ),
    inference(forward_demodulation,[],[f1260,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f136,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f136,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),X5) = X5 ),
    inference(backward_demodulation,[],[f44,f129])).

fof(f129,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X1)) = X0 ),
    inference(superposition,[],[f34,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f22,f17])).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f34,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2 ),
    inference(superposition,[],[f24,f15])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f18,f17])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f44,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(X5,k4_xboole_0(X6,X6)) ),
    inference(superposition,[],[f26,f16])).

fof(f1260,plain,(
    ! [X12,X10,X11] : k4_xboole_0(X10,k2_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X12,X10))) = k2_xboole_0(k4_xboole_0(X10,k2_xboole_0(k4_xboole_0(X10,X11),X12)),k4_xboole_0(X10,k4_xboole_0(X10,X11))) ),
    inference(superposition,[],[f167,f244])).

fof(f244,plain,(
    ! [X23,X21] : k4_xboole_0(X21,X23) = k2_xboole_0(k4_xboole_0(X21,X23),k4_xboole_0(X21,X21)) ),
    inference(backward_demodulation,[],[f93,f243])).

fof(f243,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X0))) = X2 ),
    inference(forward_demodulation,[],[f226,f16])).

fof(f226,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1)))) = X2 ),
    inference(superposition,[],[f129,f21])).

fof(f93,plain,(
    ! [X23,X21,X22] : k4_xboole_0(X21,k4_xboole_0(X23,k4_xboole_0(X21,k2_xboole_0(X22,X21)))) = k2_xboole_0(k4_xboole_0(X21,X23),k4_xboole_0(X21,X21)) ),
    inference(superposition,[],[f26,f62])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))) = X0 ),
    inference(forward_demodulation,[],[f61,f16])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1)))) = X0 ),
    inference(forward_demodulation,[],[f60,f15])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1))) = X0 ),
    inference(forward_demodulation,[],[f43,f21])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = X0 ),
    inference(superposition,[],[f26,f24])).

fof(f167,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X3)))) ),
    inference(backward_demodulation,[],[f53,f155])).

fof(f155,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X1,k4_xboole_0(X2,X0)) = k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X0))) ),
    inference(superposition,[],[f29,f15])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f16,f21])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X3))))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f52,f21])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X3))))) ),
    inference(forward_demodulation,[],[f51,f21])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X3)))) ),
    inference(forward_demodulation,[],[f40,f21])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X3))) ),
    inference(superposition,[],[f26,f21])).

fof(f480,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f478])).

fof(f481,plain,
    ( ~ spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f203,f119,f478])).

fof(f119,plain,
    ( spl2_1
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f203,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_1 ),
    inference(backward_demodulation,[],[f123,f176])).

fof(f176,plain,(
    ! [X19,X17,X18] : k4_xboole_0(X18,k2_xboole_0(X17,k2_xboole_0(X17,X19))) = k4_xboole_0(X18,k2_xboole_0(X17,X19)) ),
    inference(superposition,[],[f31,f139])).

fof(f139,plain,(
    ! [X3] : k2_xboole_0(X3,X3) = X3 ),
    inference(superposition,[],[f136,f62])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f30,f21])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(forward_demodulation,[],[f28,f21])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[],[f21,f21])).

fof(f123,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_1 ),
    inference(superposition,[],[f121,f15])).

fof(f121,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f119])).

fof(f122,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f27,f119])).

fof(f27,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f23,f21])).

fof(f23,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f14,f19,f19,f17])).

fof(f14,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:35:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (6989)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (6988)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (6996)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (6987)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (6991)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (6997)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (6997)Refutation not found, incomplete strategy% (6997)------------------------------
% 0.21/0.48  % (6997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (6997)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (6997)Memory used [KB]: 10490
% 0.21/0.48  % (6997)Time elapsed: 0.061 s
% 0.21/0.48  % (6997)------------------------------
% 0.21/0.48  % (6997)------------------------------
% 0.21/0.48  % (6990)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (6998)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (6999)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (6994)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (7002)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (6995)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (7001)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (6986)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.52  % (7003)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.52  % (6993)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.52  % (6992)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (7000)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.74/0.58  % (7001)Refutation found. Thanks to Tanya!
% 1.74/0.58  % SZS status Theorem for theBenchmark
% 1.74/0.58  % SZS output start Proof for theBenchmark
% 1.74/0.58  fof(f1442,plain,(
% 1.74/0.58    $false),
% 1.74/0.58    inference(avatar_sat_refutation,[],[f122,f481,f1438,f1441])).
% 1.74/0.58  fof(f1441,plain,(
% 1.74/0.58    spl2_5),
% 1.74/0.58    inference(avatar_contradiction_clause,[],[f1440])).
% 1.74/0.58  fof(f1440,plain,(
% 1.74/0.58    $false | spl2_5),
% 1.74/0.58    inference(subsumption_resolution,[],[f1439,f71])).
% 1.74/0.58  fof(f71,plain,(
% 1.74/0.58    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2)))) )),
% 1.74/0.58    inference(superposition,[],[f25,f15])).
% 1.74/0.58  fof(f15,plain,(
% 1.74/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f1])).
% 1.74/0.58  fof(f1,axiom,(
% 1.74/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.74/0.58  fof(f25,plain,(
% 1.74/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.74/0.58    inference(definition_unfolding,[],[f20,f19,f17])).
% 1.74/0.58  fof(f17,plain,(
% 1.74/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f5])).
% 1.74/0.58  fof(f5,axiom,(
% 1.74/0.58    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.74/0.58  fof(f19,plain,(
% 1.74/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.74/0.58    inference(cnf_transformation,[],[f2])).
% 1.74/0.58  fof(f2,axiom,(
% 1.74/0.58    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 1.74/0.58  fof(f20,plain,(
% 1.74/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.74/0.58    inference(cnf_transformation,[],[f8])).
% 1.74/0.58  fof(f8,axiom,(
% 1.74/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).
% 1.74/0.58  fof(f1439,plain,(
% 1.74/0.58    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | spl2_5),
% 1.74/0.58    inference(superposition,[],[f1437,f16])).
% 1.74/0.58  fof(f16,plain,(
% 1.74/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.74/0.58    inference(cnf_transformation,[],[f3])).
% 1.74/0.58  fof(f3,axiom,(
% 1.74/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.74/0.58  fof(f1437,plain,(
% 1.74/0.58    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_5),
% 1.74/0.58    inference(avatar_component_clause,[],[f1435])).
% 1.74/0.58  fof(f1435,plain,(
% 1.74/0.58    spl2_5 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 1.74/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.74/0.58  fof(f1438,plain,(
% 1.74/0.58    ~spl2_5 | spl2_3),
% 1.74/0.58    inference(avatar_split_clause,[],[f1282,f478,f1435])).
% 1.74/0.58  fof(f478,plain,(
% 1.74/0.58    spl2_3 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 1.74/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.74/0.58  fof(f1282,plain,(
% 1.74/0.58    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_3),
% 1.74/0.58    inference(backward_demodulation,[],[f480,f1280])).
% 1.74/0.58  fof(f1280,plain,(
% 1.74/0.58    ( ! [X12,X10,X11] : (k4_xboole_0(X10,k4_xboole_0(X10,X11)) = k4_xboole_0(X10,k2_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X12,X10)))) )),
% 1.74/0.58    inference(forward_demodulation,[],[f1260,f138])).
% 1.74/0.58  fof(f138,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1))) )),
% 1.74/0.58    inference(superposition,[],[f136,f21])).
% 1.74/0.58  fof(f21,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.74/0.58    inference(cnf_transformation,[],[f4])).
% 1.74/0.58  fof(f4,axiom,(
% 1.74/0.58    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.74/0.58  fof(f136,plain,(
% 1.74/0.58    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),X5) = X5) )),
% 1.74/0.58    inference(backward_demodulation,[],[f44,f129])).
% 1.74/0.58  fof(f129,plain,(
% 1.74/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X1)) = X0) )),
% 1.74/0.58    inference(superposition,[],[f34,f26])).
% 1.74/0.58  fof(f26,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 1.74/0.58    inference(definition_unfolding,[],[f22,f17])).
% 1.74/0.58  fof(f22,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.74/0.58    inference(cnf_transformation,[],[f7])).
% 1.74/0.58  fof(f7,axiom,(
% 1.74/0.58    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 1.74/0.58  fof(f34,plain,(
% 1.74/0.58    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2) )),
% 1.74/0.58    inference(superposition,[],[f24,f15])).
% 1.74/0.58  fof(f24,plain,(
% 1.74/0.58    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 1.74/0.58    inference(definition_unfolding,[],[f18,f17])).
% 1.74/0.58  fof(f18,plain,(
% 1.74/0.58    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.74/0.58    inference(cnf_transformation,[],[f6])).
% 1.74/0.58  fof(f6,axiom,(
% 1.74/0.58    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.74/0.58  fof(f44,plain,(
% 1.74/0.58    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(X5,k4_xboole_0(X6,X6))) )),
% 1.74/0.58    inference(superposition,[],[f26,f16])).
% 1.74/0.58  fof(f1260,plain,(
% 1.74/0.58    ( ! [X12,X10,X11] : (k4_xboole_0(X10,k2_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X12,X10))) = k2_xboole_0(k4_xboole_0(X10,k2_xboole_0(k4_xboole_0(X10,X11),X12)),k4_xboole_0(X10,k4_xboole_0(X10,X11)))) )),
% 1.74/0.58    inference(superposition,[],[f167,f244])).
% 1.74/0.58  fof(f244,plain,(
% 1.74/0.58    ( ! [X23,X21] : (k4_xboole_0(X21,X23) = k2_xboole_0(k4_xboole_0(X21,X23),k4_xboole_0(X21,X21))) )),
% 1.74/0.58    inference(backward_demodulation,[],[f93,f243])).
% 1.74/0.58  fof(f243,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X0))) = X2) )),
% 1.74/0.58    inference(forward_demodulation,[],[f226,f16])).
% 1.74/0.58  fof(f226,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1)))) = X2) )),
% 1.74/0.58    inference(superposition,[],[f129,f21])).
% 1.74/0.58  fof(f93,plain,(
% 1.74/0.58    ( ! [X23,X21,X22] : (k4_xboole_0(X21,k4_xboole_0(X23,k4_xboole_0(X21,k2_xboole_0(X22,X21)))) = k2_xboole_0(k4_xboole_0(X21,X23),k4_xboole_0(X21,X21))) )),
% 1.74/0.58    inference(superposition,[],[f26,f62])).
% 1.74/0.58  fof(f62,plain,(
% 1.74/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))) = X0) )),
% 1.74/0.58    inference(forward_demodulation,[],[f61,f16])).
% 1.74/0.58  fof(f61,plain,(
% 1.74/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1)))) = X0) )),
% 1.74/0.58    inference(forward_demodulation,[],[f60,f15])).
% 1.74/0.58  fof(f60,plain,(
% 1.74/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1))) = X0) )),
% 1.74/0.58    inference(forward_demodulation,[],[f43,f21])).
% 1.74/0.58  fof(f43,plain,(
% 1.74/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) = X0) )),
% 1.74/0.58    inference(superposition,[],[f26,f24])).
% 1.74/0.58  fof(f167,plain,(
% 1.74/0.58    ( ! [X2,X0,X3,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X3))))) )),
% 1.74/0.58    inference(backward_demodulation,[],[f53,f155])).
% 1.74/0.58  fof(f155,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (k2_xboole_0(X1,k4_xboole_0(X2,X0)) = k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X0)))) )),
% 1.74/0.58    inference(superposition,[],[f29,f15])).
% 1.74/0.58  fof(f29,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 1.74/0.58    inference(superposition,[],[f16,f21])).
% 1.74/0.58  fof(f53,plain,(
% 1.74/0.58    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X3))))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X3)))) )),
% 1.74/0.58    inference(forward_demodulation,[],[f52,f21])).
% 1.74/0.58  fof(f52,plain,(
% 1.74/0.58    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X3)))))) )),
% 1.74/0.58    inference(forward_demodulation,[],[f51,f21])).
% 1.74/0.58  fof(f51,plain,(
% 1.74/0.58    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X3))))) )),
% 1.74/0.58    inference(forward_demodulation,[],[f40,f21])).
% 1.74/0.58  fof(f40,plain,(
% 1.74/0.58    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X3)))) )),
% 1.74/0.58    inference(superposition,[],[f26,f21])).
% 1.74/0.58  fof(f480,plain,(
% 1.74/0.58    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_3),
% 1.74/0.58    inference(avatar_component_clause,[],[f478])).
% 1.74/0.58  fof(f481,plain,(
% 1.74/0.58    ~spl2_3 | spl2_1),
% 1.74/0.58    inference(avatar_split_clause,[],[f203,f119,f478])).
% 1.74/0.58  fof(f119,plain,(
% 1.74/0.58    spl2_1 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 1.74/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.74/0.58  fof(f203,plain,(
% 1.74/0.58    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_1),
% 1.74/0.58    inference(backward_demodulation,[],[f123,f176])).
% 1.74/0.58  fof(f176,plain,(
% 1.74/0.58    ( ! [X19,X17,X18] : (k4_xboole_0(X18,k2_xboole_0(X17,k2_xboole_0(X17,X19))) = k4_xboole_0(X18,k2_xboole_0(X17,X19))) )),
% 1.74/0.58    inference(superposition,[],[f31,f139])).
% 1.74/0.58  fof(f139,plain,(
% 1.74/0.58    ( ! [X3] : (k2_xboole_0(X3,X3) = X3) )),
% 1.74/0.58    inference(superposition,[],[f136,f62])).
% 1.74/0.58  fof(f31,plain,(
% 1.74/0.58    ( ! [X2,X0,X3,X1] : (k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3)))) )),
% 1.74/0.58    inference(forward_demodulation,[],[f30,f21])).
% 1.74/0.58  fof(f30,plain,(
% 1.74/0.58    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3))) )),
% 1.74/0.58    inference(forward_demodulation,[],[f28,f21])).
% 1.74/0.58  fof(f28,plain,(
% 1.74/0.58    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3)) )),
% 1.74/0.58    inference(superposition,[],[f21,f21])).
% 1.74/0.58  fof(f123,plain,(
% 1.74/0.58    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_1),
% 1.74/0.58    inference(superposition,[],[f121,f15])).
% 1.74/0.58  fof(f121,plain,(
% 1.74/0.58    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) | spl2_1),
% 1.74/0.58    inference(avatar_component_clause,[],[f119])).
% 1.74/0.58  fof(f122,plain,(
% 1.74/0.58    ~spl2_1),
% 1.74/0.58    inference(avatar_split_clause,[],[f27,f119])).
% 1.74/0.58  fof(f27,plain,(
% 1.74/0.58    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 1.74/0.58    inference(backward_demodulation,[],[f23,f21])).
% 1.74/0.58  fof(f23,plain,(
% 1.74/0.58    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 1.74/0.58    inference(definition_unfolding,[],[f14,f19,f19,f17])).
% 1.74/0.58  fof(f14,plain,(
% 1.74/0.58    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.74/0.58    inference(cnf_transformation,[],[f13])).
% 1.74/0.58  fof(f13,plain,(
% 1.74/0.58    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.74/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).
% 1.74/0.58  fof(f12,plain,(
% 1.74/0.58    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.74/0.58    introduced(choice_axiom,[])).
% 1.74/0.58  fof(f11,plain,(
% 1.74/0.58    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.74/0.58    inference(ennf_transformation,[],[f10])).
% 1.74/0.58  fof(f10,negated_conjecture,(
% 1.74/0.58    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.74/0.58    inference(negated_conjecture,[],[f9])).
% 1.74/0.58  fof(f9,conjecture,(
% 1.74/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.74/0.58  % SZS output end Proof for theBenchmark
% 1.74/0.58  % (7001)------------------------------
% 1.74/0.58  % (7001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.58  % (7001)Termination reason: Refutation
% 1.74/0.58  
% 1.74/0.58  % (7001)Memory used [KB]: 12409
% 1.74/0.58  % (7001)Time elapsed: 0.078 s
% 1.74/0.58  % (7001)------------------------------
% 1.74/0.58  % (7001)------------------------------
% 1.74/0.58  % (6985)Success in time 0.222 s
%------------------------------------------------------------------------------
