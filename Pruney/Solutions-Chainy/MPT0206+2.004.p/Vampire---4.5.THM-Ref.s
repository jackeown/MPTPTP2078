%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 224 expanded)
%              Number of leaves         :   17 (  84 expanded)
%              Depth                    :   15
%              Number of atoms          :   79 ( 243 expanded)
%              Number of equality atoms :   60 ( 219 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f519,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f74,f93,f507])).

fof(f507,plain,(
    spl9_4 ),
    inference(avatar_contradiction_clause,[],[f506])).

fof(f506,plain,
    ( $false
    | spl9_4 ),
    inference(trivial_inequality_removal,[],[f505])).

fof(f505,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl9_4 ),
    inference(forward_demodulation,[],[f464,f118])).

fof(f118,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k1_tarski(X0))) ),
    inference(backward_demodulation,[],[f42,f115])).

fof(f115,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(forward_demodulation,[],[f100,f42])).

fof(f100,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))),k1_tarski(X0))) ),
    inference(superposition,[],[f38,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X5,X0,X0,X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X5),k4_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) ),
    inference(superposition,[],[f42,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f25,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f26,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f28,f35])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f30,f20])).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f29,f20,f33])).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

fof(f464,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_enumset1(sK3,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl9_4 ),
    inference(backward_demodulation,[],[f92,f186])).

fof(f186,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(superposition,[],[f132,f38])).

fof(f132,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_enumset1(X0,X1,X2,X3,X3,X4,X5),k1_tarski(X0))) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(forward_demodulation,[],[f128,f38])).

fof(f128,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_enumset1(X0,X1,X2,X3,X3,X4,X5),k1_tarski(X0))),k1_tarski(X0))) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(superposition,[],[f117,f43])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1))),k1_tarski(X0))) = k5_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k4_xboole_0(k3_enumset1(X5,X5,X6,X7,X8),k3_enumset1(X0,X1,X2,X3,X4))) ),
    inference(definition_unfolding,[],[f32,f36,f20,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f31,f20,f35])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).

fof(f117,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k4_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_enumset1(X0,X0,X0,X1,X2))) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(backward_demodulation,[],[f41,f115])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) = k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k4_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_enumset1(X0,X0,X0,X1,X2))) ),
    inference(definition_unfolding,[],[f27,f33,f20,f34,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f21,f24])).

fof(f21,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

% (30738)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(f92,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_enumset1(sK3,sK4,sK5,sK6,sK6,sK7,sK8),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl9_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl9_4
  <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_enumset1(sK3,sK4,sK5,sK6,sK6,sK7,sK8),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f93,plain,
    ( ~ spl9_4
    | spl9_3 ),
    inference(avatar_split_clause,[],[f84,f71,f90])).

fof(f71,plain,
    ( spl9_3
  <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k4_xboole_0(k3_enumset1(sK6,sK6,sK6,sK7,sK8),k3_enumset1(sK1,sK2,sK3,sK4,sK5))),k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f84,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_enumset1(sK3,sK4,sK5,sK6,sK6,sK7,sK8),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl9_3 ),
    inference(backward_demodulation,[],[f73,f43])).

fof(f73,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k4_xboole_0(k3_enumset1(sK6,sK6,sK6,sK7,sK8),k3_enumset1(sK1,sK2,sK3,sK4,sK5))),k1_tarski(sK0)))
    | spl9_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f74,plain,
    ( ~ spl9_3
    | spl9_1 ),
    inference(avatar_split_clause,[],[f65,f45,f71])).

fof(f45,plain,
    ( spl9_1
  <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_tarski(sK0))),k4_xboole_0(k3_enumset1(sK6,sK6,sK6,sK7,sK8),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_tarski(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f65,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k4_xboole_0(k3_enumset1(sK6,sK6,sK6,sK7,sK8),k3_enumset1(sK1,sK2,sK3,sK4,sK5))),k1_tarski(sK0)))
    | spl9_1 ),
    inference(superposition,[],[f47,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
    inference(definition_unfolding,[],[f23,f20,f20,f20,f20])).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f47,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_tarski(sK0))),k4_xboole_0(k3_enumset1(sK6,sK6,sK6,sK7,sK8),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_tarski(sK0)))))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f48,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f39,f45])).

fof(f39,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_tarski(sK0))),k4_xboole_0(k3_enumset1(sK6,sK6,sK6,sK7,sK8),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_tarski(sK0))))) ),
    inference(definition_unfolding,[],[f19,f36,f20,f33,f34])).

fof(f19,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:36:07 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.21/0.46  % (30740)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (30741)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (30737)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (30743)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (30752)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (30749)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (30744)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (30748)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (30745)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (30748)Refutation not found, incomplete strategy% (30748)------------------------------
% 0.21/0.49  % (30748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (30748)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (30748)Memory used [KB]: 10618
% 0.21/0.49  % (30748)Time elapsed: 0.072 s
% 0.21/0.49  % (30748)------------------------------
% 0.21/0.49  % (30748)------------------------------
% 0.21/0.49  % (30742)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (30750)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (30746)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (30739)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (30743)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f519,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f48,f74,f93,f507])).
% 0.21/0.50  fof(f507,plain,(
% 0.21/0.50    spl9_4),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f506])).
% 0.21/0.50  fof(f506,plain,(
% 0.21/0.50    $false | spl9_4),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f505])).
% 0.21/0.50  fof(f505,plain,(
% 0.21/0.50    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK1))),k1_tarski(sK0))) | spl9_4),
% 0.21/0.50    inference(forward_demodulation,[],[f464,f118])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_enumset1(X1,X1,X2,X3,X4,X5,X6),k1_tarski(X0)))) )),
% 0.21/0.50    inference(backward_demodulation,[],[f42,f115])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f100,f42])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))),k1_tarski(X0)))) )),
% 0.21/0.50    inference(superposition,[],[f38,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X5,X0,X0,X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X5),k4_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)))) )),
% 0.21/0.50    inference(superposition,[],[f42,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X0)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f25,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f26,f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X0)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f28,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X0)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f30,f20])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f29,f20,f33])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).
% 0.21/0.50  fof(f464,plain,(
% 0.21/0.50    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_enumset1(sK3,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl9_4),
% 0.21/0.50    inference(backward_demodulation,[],[f92,f186])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.50    inference(superposition,[],[f132,f38])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_enumset1(X0,X1,X2,X3,X3,X4,X5),k1_tarski(X0))) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f128,f38])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_enumset1(X0,X1,X2,X3,X3,X4,X5),k1_tarski(X0))),k1_tarski(X0))) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.50    inference(superposition,[],[f117,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1))),k1_tarski(X0))) = k5_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k4_xboole_0(k3_enumset1(X5,X5,X6,X7,X8),k3_enumset1(X0,X1,X2,X3,X4)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f32,f36,f20,f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f31,f20,f35])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k4_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_enumset1(X0,X0,X0,X1,X2))) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f41,f115])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) = k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k4_xboole_0(k3_enumset1(X3,X3,X3,X4,X5),k3_enumset1(X0,X0,X0,X1,X2)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f27,f33,f20,f34,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f21,f24])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.50  % (30738)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_enumset1(sK3,sK4,sK5,sK6,sK6,sK7,sK8),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl9_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f90])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    spl9_4 <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_enumset1(sK3,sK4,sK5,sK6,sK6,sK7,sK8),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ~spl9_4 | spl9_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f84,f71,f90])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    spl9_3 <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k4_xboole_0(k3_enumset1(sK6,sK6,sK6,sK7,sK8),k3_enumset1(sK1,sK2,sK3,sK4,sK5))),k1_tarski(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_enumset1(sK3,sK4,sK5,sK6,sK6,sK7,sK8),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl9_3),
% 0.21/0.50    inference(backward_demodulation,[],[f73,f43])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k4_xboole_0(k3_enumset1(sK6,sK6,sK6,sK7,sK8),k3_enumset1(sK1,sK2,sK3,sK4,sK5))),k1_tarski(sK0))) | spl9_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f71])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ~spl9_3 | spl9_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f65,f45,f71])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    spl9_1 <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_tarski(sK0))),k4_xboole_0(k3_enumset1(sK6,sK6,sK6,sK7,sK8),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_tarski(sK0)))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k4_xboole_0(k3_enumset1(sK6,sK6,sK6,sK7,sK8),k3_enumset1(sK1,sK2,sK3,sK4,sK5))),k1_tarski(sK0))) | spl9_1),
% 0.21/0.50    inference(superposition,[],[f47,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f23,f20,f20,f20,f20])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_tarski(sK0))),k4_xboole_0(k3_enumset1(sK6,sK6,sK6,sK7,sK8),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_tarski(sK0))))) | spl9_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f45])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ~spl9_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f39,f45])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_tarski(sK0))),k4_xboole_0(k3_enumset1(sK6,sK6,sK6,sK7,sK8),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_tarski(sK0)))))),
% 0.21/0.50    inference(definition_unfolding,[],[f19,f36,f20,f33,f34])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8))),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f16,f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 0.21/0.50    inference(negated_conjecture,[],[f14])).
% 0.21/0.50  fof(f14,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (30743)------------------------------
% 0.21/0.50  % (30743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30743)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (30743)Memory used [KB]: 6652
% 0.21/0.50  % (30743)Time elapsed: 0.035 s
% 0.21/0.50  % (30743)------------------------------
% 0.21/0.50  % (30743)------------------------------
% 0.21/0.51  % (30736)Success in time 0.145 s
%------------------------------------------------------------------------------
