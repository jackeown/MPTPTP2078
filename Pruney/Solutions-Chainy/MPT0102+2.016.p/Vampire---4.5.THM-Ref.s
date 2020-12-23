%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:58 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 223 expanded)
%              Number of leaves         :   19 (  81 expanded)
%              Depth                    :   15
%              Number of atoms          :  100 ( 243 expanded)
%              Number of equality atoms :   80 ( 218 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1249,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f444,f631,f799,f1239])).

fof(f1239,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f1238])).

fof(f1238,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f1237,f62])).

fof(f62,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f31,f28])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1237,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_3 ),
    inference(forward_demodulation,[],[f1232,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f32,f36,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1232,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))
    | spl2_3 ),
    inference(backward_demodulation,[],[f798,f1217])).

fof(f1217,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k4_xboole_0(X8,X9)) = X8 ),
    inference(forward_demodulation,[],[f1187,f277])).

fof(f277,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f276,f62])).

fof(f276,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f246,f57])).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f46,f56])).

fof(f56,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f49,f30])).

fof(f30,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f27,f36])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f246,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),X1)) ),
    inference(superposition,[],[f58,f48])).

fof(f58,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(forward_demodulation,[],[f52,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f52,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f41,f36,f36])).

fof(f41,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f1187,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(X9,X8)))) = X8 ),
    inference(superposition,[],[f219,f48])).

fof(f219,plain,(
    ! [X12,X11] : k2_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,X12))) = X11 ),
    inference(forward_demodulation,[],[f218,f56])).

fof(f218,plain,(
    ! [X12,X11] : k4_xboole_0(X11,k1_xboole_0) = k2_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f196,f98])).

fof(f98,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f86,f30])).

fof(f86,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f40,f57])).

fof(f196,plain,(
    ! [X12,X11] : k4_xboole_0(X11,k4_xboole_0(k1_xboole_0,X12)) = k2_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,X12))) ),
    inference(superposition,[],[f54,f56])).

fof(f54,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f43,f36])).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f798,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f796])).

fof(f796,plain,
    ( spl2_3
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f799,plain,
    ( ~ spl2_3
    | spl2_2 ),
    inference(avatar_split_clause,[],[f785,f628,f796])).

fof(f628,plain,
    ( spl2_2
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f785,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))
    | spl2_2 ),
    inference(backward_demodulation,[],[f630,f783])).

fof(f783,plain,(
    ! [X19,X20,X18] : k4_xboole_0(X18,k4_xboole_0(k2_xboole_0(X19,X18),X20)) = k4_xboole_0(X18,k4_xboole_0(X18,X20)) ),
    inference(forward_demodulation,[],[f758,f62])).

fof(f758,plain,(
    ! [X19,X20,X18] : k4_xboole_0(X18,k4_xboole_0(k2_xboole_0(X19,X18),X20)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X18,k4_xboole_0(X18,X20))) ),
    inference(superposition,[],[f54,f65])).

fof(f65,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f30,f31])).

fof(f630,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f628])).

fof(f631,plain,
    ( ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f498,f441,f628])).

fof(f441,plain,
    ( spl2_1
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f498,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))
    | spl2_1 ),
    inference(forward_demodulation,[],[f497,f31])).

fof(f497,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0))))
    | spl2_1 ),
    inference(backward_demodulation,[],[f443,f496])).

fof(f496,plain,(
    ! [X19,X17,X18] : k4_xboole_0(k2_xboole_0(X17,X18),k2_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(X18,X19))) = k4_xboole_0(X18,k4_xboole_0(k2_xboole_0(X17,X18),k2_xboole_0(k4_xboole_0(X17,X18),X19))) ),
    inference(forward_demodulation,[],[f455,f123])).

fof(f123,plain,(
    ! [X8,X9] : k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X8,X9)) = X9 ),
    inference(forward_demodulation,[],[f122,f56])).

fof(f122,plain,(
    ! [X8,X9] : k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X8,X9)) = k4_xboole_0(X9,k1_xboole_0) ),
    inference(forward_demodulation,[],[f106,f65])).

fof(f106,plain,(
    ! [X8,X9] : k4_xboole_0(X9,k4_xboole_0(X9,k2_xboole_0(X8,X9))) = k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X8,X9)) ),
    inference(superposition,[],[f48,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f455,plain,(
    ! [X19,X17,X18] : k4_xboole_0(k2_xboole_0(X17,X18),k2_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(X18,X19))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X17,X18),k4_xboole_0(X17,X18)),k4_xboole_0(k2_xboole_0(X17,X18),k2_xboole_0(k4_xboole_0(X17,X18),X19))) ),
    inference(superposition,[],[f60,f35])).

fof(f60,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(forward_demodulation,[],[f59,f40])).

fof(f59,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2))) ),
    inference(forward_demodulation,[],[f53,f58])).

fof(f53,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f42,f36,f36,f36,f36])).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f443,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f441])).

fof(f444,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f439,f441])).

fof(f439,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(backward_demodulation,[],[f45,f362])).

fof(f362,plain,(
    ! [X6,X7] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,X6)),k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f30,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f38,f37,f36])).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f45,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f26,f36,f37,f37])).

fof(f26,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24])).

fof(f24,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:54:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.45  % (3716)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.46  % (3718)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.46  % (3718)Refutation not found, incomplete strategy% (3718)------------------------------
% 0.19/0.46  % (3718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (3718)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.46  
% 0.19/0.46  % (3718)Memory used [KB]: 10618
% 0.19/0.46  % (3718)Time elapsed: 0.053 s
% 0.19/0.46  % (3718)------------------------------
% 0.19/0.46  % (3718)------------------------------
% 0.19/0.47  % (3710)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.47  % (3707)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.47  % (3723)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.47  % (3717)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.47  % (3711)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.47  % (3709)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.47  % (3714)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.48  % (3724)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.48  % (3721)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.49  % (3722)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.49  % (3713)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.49  % (3712)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.50  % (3719)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.50  % (3708)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.50  % (3715)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.51  % (3720)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.56  % (3722)Refutation found. Thanks to Tanya!
% 0.19/0.56  % SZS status Theorem for theBenchmark
% 0.19/0.56  % SZS output start Proof for theBenchmark
% 0.19/0.56  fof(f1249,plain,(
% 0.19/0.56    $false),
% 0.19/0.56    inference(avatar_sat_refutation,[],[f444,f631,f799,f1239])).
% 0.19/0.56  fof(f1239,plain,(
% 0.19/0.56    spl2_3),
% 0.19/0.56    inference(avatar_contradiction_clause,[],[f1238])).
% 0.19/0.56  fof(f1238,plain,(
% 0.19/0.56    $false | spl2_3),
% 0.19/0.56    inference(subsumption_resolution,[],[f1237,f62])).
% 0.19/0.56  fof(f62,plain,(
% 0.19/0.56    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.19/0.56    inference(superposition,[],[f31,f28])).
% 0.19/0.56  fof(f28,plain,(
% 0.19/0.56    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.56    inference(cnf_transformation,[],[f8])).
% 0.19/0.56  fof(f8,axiom,(
% 0.19/0.56    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.19/0.56  fof(f31,plain,(
% 0.19/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f1])).
% 0.19/0.56  fof(f1,axiom,(
% 0.19/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.19/0.56  fof(f1237,plain,(
% 0.19/0.56    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_3),
% 0.19/0.56    inference(forward_demodulation,[],[f1232,f48])).
% 0.19/0.56  fof(f48,plain,(
% 0.19/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.19/0.56    inference(definition_unfolding,[],[f32,f36,f36])).
% 0.19/0.56  fof(f36,plain,(
% 0.19/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.19/0.56    inference(cnf_transformation,[],[f14])).
% 0.19/0.56  fof(f14,axiom,(
% 0.19/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.56  fof(f32,plain,(
% 0.19/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f2])).
% 0.19/0.56  fof(f2,axiom,(
% 0.19/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.56  fof(f1232,plain,(
% 0.19/0.56    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) | spl2_3),
% 0.19/0.56    inference(backward_demodulation,[],[f798,f1217])).
% 0.19/0.56  fof(f1217,plain,(
% 0.19/0.56    ( ! [X8,X9] : (k2_xboole_0(X8,k4_xboole_0(X8,X9)) = X8) )),
% 0.19/0.56    inference(forward_demodulation,[],[f1187,f277])).
% 0.19/0.56  fof(f277,plain,(
% 0.19/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.19/0.56    inference(forward_demodulation,[],[f276,f62])).
% 0.19/0.56  fof(f276,plain,(
% 0.19/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.19/0.56    inference(forward_demodulation,[],[f246,f57])).
% 0.19/0.56  fof(f57,plain,(
% 0.19/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.19/0.56    inference(backward_demodulation,[],[f46,f56])).
% 0.19/0.56  fof(f56,plain,(
% 0.19/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.56    inference(forward_demodulation,[],[f49,f30])).
% 0.19/0.56  fof(f30,plain,(
% 0.19/0.56    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.19/0.56    inference(cnf_transformation,[],[f13])).
% 0.19/0.56  fof(f13,axiom,(
% 0.19/0.56    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.19/0.56  fof(f49,plain,(
% 0.19/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 0.19/0.56    inference(definition_unfolding,[],[f33,f36])).
% 0.19/0.56  fof(f33,plain,(
% 0.19/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.19/0.56    inference(cnf_transformation,[],[f9])).
% 0.19/0.56  fof(f9,axiom,(
% 0.19/0.56    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.19/0.56  fof(f46,plain,(
% 0.19/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.19/0.56    inference(definition_unfolding,[],[f27,f36])).
% 0.19/0.56  fof(f27,plain,(
% 0.19/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f10])).
% 0.19/0.56  fof(f10,axiom,(
% 0.19/0.56    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.19/0.56  fof(f246,plain,(
% 0.19/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),X1))) )),
% 0.19/0.56    inference(superposition,[],[f58,f48])).
% 0.19/0.56  fof(f58,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 0.19/0.56    inference(forward_demodulation,[],[f52,f40])).
% 0.19/0.56  fof(f40,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.19/0.56    inference(cnf_transformation,[],[f12])).
% 0.19/0.56  fof(f12,axiom,(
% 0.19/0.56    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.19/0.56  fof(f52,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.19/0.56    inference(definition_unfolding,[],[f41,f36,f36])).
% 0.19/0.56  fof(f41,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f15])).
% 0.19/0.56  fof(f15,axiom,(
% 0.19/0.56    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.19/0.56  fof(f1187,plain,(
% 0.19/0.56    ( ! [X8,X9] : (k2_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(X9,X8)))) = X8) )),
% 0.19/0.56    inference(superposition,[],[f219,f48])).
% 0.19/0.56  fof(f219,plain,(
% 0.19/0.56    ( ! [X12,X11] : (k2_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,X12))) = X11) )),
% 0.19/0.56    inference(forward_demodulation,[],[f218,f56])).
% 0.19/0.56  fof(f218,plain,(
% 0.19/0.56    ( ! [X12,X11] : (k4_xboole_0(X11,k1_xboole_0) = k2_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,X12)))) )),
% 0.19/0.56    inference(forward_demodulation,[],[f196,f98])).
% 0.19/0.56  fof(f98,plain,(
% 0.19/0.56    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3)) )),
% 0.19/0.56    inference(forward_demodulation,[],[f86,f30])).
% 0.19/0.56  fof(f86,plain,(
% 0.19/0.56    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)) )),
% 0.19/0.56    inference(superposition,[],[f40,f57])).
% 0.19/0.56  fof(f196,plain,(
% 0.19/0.56    ( ! [X12,X11] : (k4_xboole_0(X11,k4_xboole_0(k1_xboole_0,X12)) = k2_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,X12)))) )),
% 0.19/0.56    inference(superposition,[],[f54,f56])).
% 0.19/0.56  fof(f54,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.19/0.56    inference(definition_unfolding,[],[f43,f36])).
% 0.19/0.56  fof(f43,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.19/0.56    inference(cnf_transformation,[],[f16])).
% 0.19/0.56  fof(f16,axiom,(
% 0.19/0.56    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.19/0.56  fof(f798,plain,(
% 0.19/0.56    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))))) | spl2_3),
% 0.19/0.56    inference(avatar_component_clause,[],[f796])).
% 0.19/0.56  fof(f796,plain,(
% 0.19/0.56    spl2_3 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))),
% 0.19/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.19/0.56  fof(f799,plain,(
% 0.19/0.56    ~spl2_3 | spl2_2),
% 0.19/0.56    inference(avatar_split_clause,[],[f785,f628,f796])).
% 0.19/0.56  fof(f628,plain,(
% 0.19/0.56    spl2_2 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))),
% 0.19/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.56  fof(f785,plain,(
% 0.19/0.56    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))))) | spl2_2),
% 0.19/0.56    inference(backward_demodulation,[],[f630,f783])).
% 0.19/0.56  fof(f783,plain,(
% 0.19/0.56    ( ! [X19,X20,X18] : (k4_xboole_0(X18,k4_xboole_0(k2_xboole_0(X19,X18),X20)) = k4_xboole_0(X18,k4_xboole_0(X18,X20))) )),
% 0.19/0.56    inference(forward_demodulation,[],[f758,f62])).
% 0.19/0.56  fof(f758,plain,(
% 0.19/0.56    ( ! [X19,X20,X18] : (k4_xboole_0(X18,k4_xboole_0(k2_xboole_0(X19,X18),X20)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X18,k4_xboole_0(X18,X20)))) )),
% 0.19/0.56    inference(superposition,[],[f54,f65])).
% 0.19/0.56  fof(f65,plain,(
% 0.19/0.56    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 0.19/0.56    inference(superposition,[],[f30,f31])).
% 0.19/0.56  fof(f630,plain,(
% 0.19/0.56    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))))) | spl2_2),
% 0.19/0.56    inference(avatar_component_clause,[],[f628])).
% 0.19/0.56  fof(f631,plain,(
% 0.19/0.56    ~spl2_2 | spl2_1),
% 0.19/0.56    inference(avatar_split_clause,[],[f498,f441,f628])).
% 0.19/0.56  fof(f441,plain,(
% 0.19/0.56    spl2_1 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.19/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.56  fof(f498,plain,(
% 0.19/0.56    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))))) | spl2_1),
% 0.19/0.56    inference(forward_demodulation,[],[f497,f31])).
% 0.19/0.56  fof(f497,plain,(
% 0.19/0.56    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)))) | spl2_1),
% 0.19/0.56    inference(backward_demodulation,[],[f443,f496])).
% 0.19/0.56  fof(f496,plain,(
% 0.19/0.56    ( ! [X19,X17,X18] : (k4_xboole_0(k2_xboole_0(X17,X18),k2_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(X18,X19))) = k4_xboole_0(X18,k4_xboole_0(k2_xboole_0(X17,X18),k2_xboole_0(k4_xboole_0(X17,X18),X19)))) )),
% 0.19/0.56    inference(forward_demodulation,[],[f455,f123])).
% 0.19/0.56  fof(f123,plain,(
% 0.19/0.56    ( ! [X8,X9] : (k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X8,X9)) = X9) )),
% 0.19/0.56    inference(forward_demodulation,[],[f122,f56])).
% 0.19/0.56  fof(f122,plain,(
% 0.19/0.56    ( ! [X8,X9] : (k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X8,X9)) = k4_xboole_0(X9,k1_xboole_0)) )),
% 0.19/0.56    inference(forward_demodulation,[],[f106,f65])).
% 0.19/0.56  fof(f106,plain,(
% 0.19/0.56    ( ! [X8,X9] : (k4_xboole_0(X9,k4_xboole_0(X9,k2_xboole_0(X8,X9))) = k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X8,X9))) )),
% 0.19/0.56    inference(superposition,[],[f48,f35])).
% 0.19/0.56  fof(f35,plain,(
% 0.19/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f11])).
% 0.19/0.56  fof(f11,axiom,(
% 0.19/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.19/0.56  fof(f455,plain,(
% 0.19/0.56    ( ! [X19,X17,X18] : (k4_xboole_0(k2_xboole_0(X17,X18),k2_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(X18,X19))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X17,X18),k4_xboole_0(X17,X18)),k4_xboole_0(k2_xboole_0(X17,X18),k2_xboole_0(k4_xboole_0(X17,X18),X19)))) )),
% 0.19/0.56    inference(superposition,[],[f60,f35])).
% 0.19/0.56  fof(f60,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)))) )),
% 0.19/0.56    inference(forward_demodulation,[],[f59,f40])).
% 0.19/0.56  fof(f59,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)))) )),
% 0.19/0.56    inference(forward_demodulation,[],[f53,f58])).
% 0.19/0.56  fof(f53,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 0.19/0.56    inference(definition_unfolding,[],[f42,f36,f36,f36,f36])).
% 0.19/0.56  fof(f42,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.19/0.56    inference(cnf_transformation,[],[f6])).
% 0.19/0.56  fof(f6,axiom,(
% 0.19/0.56    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.19/0.56  fof(f443,plain,(
% 0.19/0.56    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl2_1),
% 0.19/0.56    inference(avatar_component_clause,[],[f441])).
% 0.19/0.56  fof(f444,plain,(
% 0.19/0.56    ~spl2_1),
% 0.19/0.56    inference(avatar_split_clause,[],[f439,f441])).
% 0.19/0.56  fof(f439,plain,(
% 0.19/0.56    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.19/0.56    inference(backward_demodulation,[],[f45,f362])).
% 0.19/0.56  fof(f362,plain,(
% 0.19/0.56    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,X6)),k2_xboole_0(X6,X7))) )),
% 0.19/0.56    inference(superposition,[],[f30,f51])).
% 0.19/0.56  fof(f51,plain,(
% 0.19/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.19/0.56    inference(definition_unfolding,[],[f38,f37,f36])).
% 0.19/0.56  fof(f37,plain,(
% 0.19/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.19/0.56    inference(cnf_transformation,[],[f3])).
% 0.19/0.56  fof(f3,axiom,(
% 0.19/0.56    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.19/0.56  fof(f38,plain,(
% 0.19/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.19/0.56    inference(cnf_transformation,[],[f18])).
% 0.19/0.56  fof(f18,axiom,(
% 0.19/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 0.19/0.56  fof(f45,plain,(
% 0.19/0.56    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.19/0.56    inference(definition_unfolding,[],[f26,f36,f37,f37])).
% 0.19/0.56  fof(f26,plain,(
% 0.19/0.56    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.19/0.56    inference(cnf_transformation,[],[f25])).
% 0.19/0.56  fof(f25,plain,(
% 0.19/0.56    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.19/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24])).
% 0.19/0.56  fof(f24,plain,(
% 0.19/0.56    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.19/0.56    introduced(choice_axiom,[])).
% 0.19/0.56  fof(f21,plain,(
% 0.19/0.56    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.19/0.56    inference(ennf_transformation,[],[f20])).
% 0.19/0.56  fof(f20,negated_conjecture,(
% 0.19/0.56    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.19/0.56    inference(negated_conjecture,[],[f19])).
% 0.19/0.56  fof(f19,conjecture,(
% 0.19/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.19/0.56  % SZS output end Proof for theBenchmark
% 0.19/0.56  % (3722)------------------------------
% 0.19/0.56  % (3722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.56  % (3722)Termination reason: Refutation
% 0.19/0.56  
% 0.19/0.56  % (3722)Memory used [KB]: 11641
% 0.19/0.56  % (3722)Time elapsed: 0.149 s
% 0.19/0.56  % (3722)------------------------------
% 0.19/0.56  % (3722)------------------------------
% 0.19/0.57  % (3706)Success in time 0.216 s
%------------------------------------------------------------------------------
