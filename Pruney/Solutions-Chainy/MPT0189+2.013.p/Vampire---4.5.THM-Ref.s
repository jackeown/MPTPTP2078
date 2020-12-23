%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:19 EST 2020

% Result     : Theorem 3.35s
% Output     : Refutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   92 (1487 expanded)
%              Number of leaves         :   13 ( 495 expanded)
%              Depth                    :   28
%              Number of atoms          :   99 (1497 expanded)
%              Number of equality atoms :   87 (1482 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5202,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f5075,f5077])).

fof(f5077,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f5076])).

fof(f5076,plain,
    ( $false
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f4976])).

fof(f4976,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3)
    | spl4_1 ),
    inference(superposition,[],[f44,f4853])).

fof(f4853,plain,(
    ! [X54,X52,X55,X53] : k2_enumset1(X52,X53,X54,X55) = k2_enumset1(X53,X52,X54,X55) ),
    inference(superposition,[],[f4808,f1809])).

fof(f1809,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X0,X2,X3) ),
    inference(superposition,[],[f1807,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f1807,plain,(
    ! [X6,X8,X7,X5,X9] : k3_enumset1(X5,X7,X6,X8,X9) = k3_enumset1(X5,X6,X7,X8,X9) ),
    inference(superposition,[],[f1796,f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f1796,plain,(
    ! [X6,X8,X7,X5,X9] : k4_enumset1(X5,X5,X6,X7,X8,X9) = k3_enumset1(X5,X7,X6,X8,X9) ),
    inference(forward_demodulation,[],[f1757,f1795])).

fof(f1795,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X2,X1),k2_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f1756,f34])).

fof(f1756,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X2,X1),k2_tarski(X3,X4)) ),
    inference(superposition,[],[f36,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X2,X1) ),
    inference(superposition,[],[f30,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

fof(f1757,plain,(
    ! [X6,X8,X7,X5,X9] : k4_enumset1(X5,X5,X6,X7,X8,X9) = k2_xboole_0(k1_enumset1(X5,X6,X7),k2_tarski(X8,X9)) ),
    inference(superposition,[],[f36,f29])).

fof(f4808,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X5,X4,X6,X7) = k2_enumset1(X5,X4,X6,X7) ),
    inference(forward_demodulation,[],[f4787,f4807])).

fof(f4807,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X3)) ),
    inference(forward_demodulation,[],[f4786,f1809])).

fof(f4786,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X1,X0,X2,X3) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X3)) ),
    inference(superposition,[],[f1795,f2777])).

fof(f2777,plain,(
    ! [X8,X9] : k2_tarski(X9,X8) = k1_enumset1(X8,X8,X9) ),
    inference(superposition,[],[f2758,f1903])).

fof(f1903,plain,(
    ! [X26,X27,X25] : k2_enumset1(X27,X26,X25,X26) = k1_enumset1(X27,X25,X26) ),
    inference(forward_demodulation,[],[f1902,f1878])).

fof(f1878,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(forward_demodulation,[],[f1853,f29])).

fof(f1853,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(superposition,[],[f1833,f32])).

fof(f1833,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(superposition,[],[f1760,f1796])).

fof(f1760,plain,(
    ! [X19,X20,X18] : k2_xboole_0(k1_tarski(X18),k2_tarski(X19,X20)) = k4_enumset1(X18,X18,X18,X18,X19,X20) ),
    inference(superposition,[],[f36,f354])).

fof(f354,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(superposition,[],[f238,f263])).

fof(f263,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(superposition,[],[f255,f24])).

fof(f24,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f255,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(forward_demodulation,[],[f226,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0) ),
    inference(superposition,[],[f50,f26])).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k1_enumset1(X3,X5,X4) ),
    inference(superposition,[],[f46,f29])).

fof(f226,plain,(
    ! [X0,X1] : k1_enumset1(X0,X1,X0) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f218,f46])).

fof(f218,plain,(
    ! [X2,X0,X1] : k2_enumset1(X2,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f33,f26])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f238,plain,(
    ! [X0,X1] : k2_enumset1(X1,X0,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) ),
    inference(superposition,[],[f218,f24])).

fof(f1902,plain,(
    ! [X26,X27,X25] : k2_enumset1(X27,X26,X25,X26) = k2_xboole_0(k1_tarski(X27),k2_tarski(X25,X26)) ),
    inference(forward_demodulation,[],[f1901,f56])).

fof(f1901,plain,(
    ! [X26,X27,X25] : k2_enumset1(X27,X26,X25,X26) = k2_xboole_0(k1_tarski(X27),k1_enumset1(X25,X26,X25)) ),
    inference(forward_demodulation,[],[f1900,f29])).

fof(f1900,plain,(
    ! [X26,X27,X25] : k2_enumset1(X27,X26,X25,X26) = k2_xboole_0(k1_tarski(X27),k2_enumset1(X25,X25,X26,X25)) ),
    inference(forward_demodulation,[],[f1864,f32])).

fof(f1864,plain,(
    ! [X26,X27,X25] : k2_enumset1(X27,X26,X25,X26) = k2_xboole_0(k1_tarski(X27),k3_enumset1(X25,X25,X25,X26,X25)) ),
    inference(superposition,[],[f916,f1833])).

fof(f916,plain,(
    ! [X30,X31,X32] : k2_enumset1(X30,X32,X31,X32) = k2_xboole_0(k1_tarski(X30),k2_xboole_0(k1_tarski(X31),k2_tarski(X32,X31))) ),
    inference(superposition,[],[f478,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

fof(f478,plain,(
    ! [X4,X2,X3] : k2_enumset1(X4,X2,X3,X3) = k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X2),k2_tarski(X3,X2))) ),
    inference(superposition,[],[f33,f234])).

fof(f234,plain,(
    ! [X28,X29] : k1_enumset1(X28,X29,X29) = k2_xboole_0(k1_tarski(X28),k2_tarski(X29,X28)) ),
    inference(superposition,[],[f218,f93])).

fof(f93,plain,(
    ! [X12,X10,X11] : k2_enumset1(X10,X11,X12,X10) = k1_enumset1(X10,X12,X11) ),
    inference(superposition,[],[f64,f30])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X2,X1) = k2_enumset1(X0,X1,X0,X2) ),
    inference(superposition,[],[f31,f46])).

fof(f2758,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X1,X0,X1,X0) ),
    inference(superposition,[],[f2066,f573])).

fof(f573,plain,(
    ! [X10,X8,X9] : k2_enumset1(X8,X9,X10,X9) = k2_xboole_0(k2_tarski(X9,X10),k1_tarski(X8)) ),
    inference(superposition,[],[f239,f30])).

fof(f239,plain,(
    ! [X4,X5,X3] : k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) = k2_enumset1(X3,X4,X4,X5) ),
    inference(superposition,[],[f218,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2066,plain,(
    ! [X15,X16] : k2_tarski(X16,X15) = k2_xboole_0(k2_tarski(X16,X15),k1_tarski(X15)) ),
    inference(superposition,[],[f2061,f579])).

fof(f579,plain,(
    ! [X33,X32] : k1_enumset1(X32,X33,X33) = k2_xboole_0(k2_tarski(X33,X32),k1_tarski(X32)) ),
    inference(superposition,[],[f239,f93])).

fof(f2061,plain,(
    ! [X80,X81] : k1_enumset1(X80,X81,X81) = k2_tarski(X81,X80) ),
    inference(forward_demodulation,[],[f2040,f2049])).

fof(f2049,plain,(
    ! [X76,X77] : k2_xboole_0(k1_tarski(X77),k1_tarski(X76)) = k2_tarski(X76,X77) ),
    inference(forward_demodulation,[],[f2012,f1891])).

fof(f1891,plain,(
    ! [X17,X18] : k2_tarski(X17,X18) = k1_enumset1(X17,X18,X18) ),
    inference(forward_demodulation,[],[f1890,f255])).

fof(f1890,plain,(
    ! [X17,X18] : k1_enumset1(X17,X18,X18) = k2_xboole_0(k1_tarski(X17),k2_tarski(X17,X18)) ),
    inference(forward_demodulation,[],[f1889,f56])).

fof(f1889,plain,(
    ! [X17,X18] : k1_enumset1(X17,X18,X18) = k2_xboole_0(k1_tarski(X17),k1_enumset1(X17,X18,X17)) ),
    inference(forward_demodulation,[],[f1888,f29])).

fof(f1888,plain,(
    ! [X17,X18] : k1_enumset1(X17,X18,X18) = k2_xboole_0(k1_tarski(X17),k2_enumset1(X17,X17,X18,X17)) ),
    inference(forward_demodulation,[],[f1861,f32])).

fof(f1861,plain,(
    ! [X17,X18] : k1_enumset1(X17,X18,X18) = k2_xboole_0(k1_tarski(X17),k3_enumset1(X17,X17,X17,X18,X17)) ),
    inference(superposition,[],[f910,f1833])).

fof(f910,plain,(
    ! [X0,X1] : k1_enumset1(X0,X1,X1) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X0))) ),
    inference(superposition,[],[f478,f46])).

fof(f2012,plain,(
    ! [X76,X77] : k2_xboole_0(k1_tarski(X77),k1_tarski(X76)) = k1_enumset1(X76,X77,X77) ),
    inference(superposition,[],[f1883,f355])).

fof(f355,plain,(
    ! [X4,X3] : k2_xboole_0(k1_tarski(X4),k1_tarski(X3)) = k2_enumset1(X3,X4,X4,X4) ),
    inference(superposition,[],[f238,f25])).

fof(f1883,plain,(
    ! [X12,X13,X11] : k2_enumset1(X13,X11,X12,X12) = k1_enumset1(X13,X11,X12) ),
    inference(forward_demodulation,[],[f1882,f1878])).

fof(f1882,plain,(
    ! [X12,X13,X11] : k2_xboole_0(k1_tarski(X13),k2_tarski(X11,X12)) = k2_enumset1(X13,X11,X12,X12) ),
    inference(forward_demodulation,[],[f1881,f56])).

fof(f1881,plain,(
    ! [X12,X13,X11] : k2_xboole_0(k1_tarski(X13),k1_enumset1(X11,X12,X11)) = k2_enumset1(X13,X11,X12,X12) ),
    inference(forward_demodulation,[],[f1880,f29])).

fof(f1880,plain,(
    ! [X12,X13,X11] : k2_enumset1(X13,X11,X12,X12) = k2_xboole_0(k1_tarski(X13),k2_enumset1(X11,X11,X12,X11)) ),
    inference(forward_demodulation,[],[f1859,f32])).

fof(f1859,plain,(
    ! [X12,X13,X11] : k2_enumset1(X13,X11,X12,X12) = k2_xboole_0(k1_tarski(X13),k3_enumset1(X11,X11,X11,X12,X11)) ),
    inference(superposition,[],[f478,f1833])).

fof(f2040,plain,(
    ! [X80,X81] : k1_enumset1(X80,X81,X81) = k2_xboole_0(k1_tarski(X80),k1_tarski(X81)) ),
    inference(superposition,[],[f238,f1883])).

fof(f4787,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X5,X4,X6,X7) = k2_xboole_0(k2_tarski(X4,X5),k2_tarski(X6,X7)) ),
    inference(superposition,[],[f1795,f26])).

fof(f44,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f5075,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f5074])).

fof(f5074,plain,
    ( $false
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f5025])).

fof(f5025,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3)
    | spl4_1 ),
    inference(superposition,[],[f44,f4853])).

fof(f45,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f23,f42])).

fof(f23,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:49:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.45  % (19542)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.45  % (19527)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (19540)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.49  % (19528)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (19526)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.50  % (19525)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.50  % (19536)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.50  % (19529)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (19536)Refutation not found, incomplete strategy% (19536)------------------------------
% 0.20/0.50  % (19536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (19536)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (19536)Memory used [KB]: 10618
% 0.20/0.50  % (19536)Time elapsed: 0.076 s
% 0.20/0.50  % (19536)------------------------------
% 0.20/0.50  % (19536)------------------------------
% 0.20/0.50  % (19535)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (19532)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.51  % (19533)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.51  % (19538)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.51  % (19537)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.52  % (19531)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (19534)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.52  % (19530)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.53  % (19539)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.53  % (19541)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 3.35/0.84  % (19525)Refutation found. Thanks to Tanya!
% 3.35/0.84  % SZS status Theorem for theBenchmark
% 3.35/0.84  % SZS output start Proof for theBenchmark
% 3.35/0.84  fof(f5202,plain,(
% 3.35/0.84    $false),
% 3.35/0.84    inference(avatar_sat_refutation,[],[f45,f5075,f5077])).
% 3.35/0.84  fof(f5077,plain,(
% 3.35/0.84    spl4_1),
% 3.35/0.84    inference(avatar_contradiction_clause,[],[f5076])).
% 3.35/0.84  fof(f5076,plain,(
% 3.35/0.84    $false | spl4_1),
% 3.35/0.84    inference(trivial_inequality_removal,[],[f4976])).
% 3.35/0.84  fof(f4976,plain,(
% 3.35/0.84    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3) | spl4_1),
% 3.35/0.84    inference(superposition,[],[f44,f4853])).
% 3.35/0.84  fof(f4853,plain,(
% 3.35/0.84    ( ! [X54,X52,X55,X53] : (k2_enumset1(X52,X53,X54,X55) = k2_enumset1(X53,X52,X54,X55)) )),
% 3.35/0.84    inference(superposition,[],[f4808,f1809])).
% 3.35/0.84  fof(f1809,plain,(
% 3.35/0.84    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X0,X2,X3)) )),
% 3.35/0.84    inference(superposition,[],[f1807,f32])).
% 3.35/0.84  fof(f32,plain,(
% 3.35/0.84    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.35/0.84    inference(cnf_transformation,[],[f14])).
% 3.35/0.84  fof(f14,axiom,(
% 3.35/0.84    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.35/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 3.35/0.84  fof(f1807,plain,(
% 3.35/0.84    ( ! [X6,X8,X7,X5,X9] : (k3_enumset1(X5,X7,X6,X8,X9) = k3_enumset1(X5,X6,X7,X8,X9)) )),
% 3.35/0.84    inference(superposition,[],[f1796,f34])).
% 3.35/0.84  fof(f34,plain,(
% 3.35/0.84    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.35/0.84    inference(cnf_transformation,[],[f15])).
% 3.35/0.84  fof(f15,axiom,(
% 3.35/0.84    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.35/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 3.35/0.84  fof(f1796,plain,(
% 3.35/0.84    ( ! [X6,X8,X7,X5,X9] : (k4_enumset1(X5,X5,X6,X7,X8,X9) = k3_enumset1(X5,X7,X6,X8,X9)) )),
% 3.35/0.84    inference(forward_demodulation,[],[f1757,f1795])).
% 3.35/0.84  fof(f1795,plain,(
% 3.35/0.84    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X2,X1),k2_tarski(X3,X4))) )),
% 3.35/0.84    inference(forward_demodulation,[],[f1756,f34])).
% 3.35/0.84  fof(f1756,plain,(
% 3.35/0.84    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X2,X1),k2_tarski(X3,X4))) )),
% 3.35/0.84    inference(superposition,[],[f36,f46])).
% 3.35/0.84  fof(f46,plain,(
% 3.35/0.84    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X2,X1)) )),
% 3.35/0.84    inference(superposition,[],[f30,f29])).
% 3.35/0.84  fof(f29,plain,(
% 3.35/0.84    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.35/0.84    inference(cnf_transformation,[],[f13])).
% 3.35/0.84  fof(f13,axiom,(
% 3.35/0.84    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.35/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 3.35/0.84  fof(f30,plain,(
% 3.35/0.84    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 3.35/0.84    inference(cnf_transformation,[],[f5])).
% 3.35/0.84  fof(f5,axiom,(
% 3.35/0.84    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 3.35/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).
% 3.35/0.84  fof(f36,plain,(
% 3.35/0.84    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 3.35/0.84    inference(cnf_transformation,[],[f8])).
% 3.35/0.84  fof(f8,axiom,(
% 3.35/0.84    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 3.35/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).
% 3.35/0.84  fof(f1757,plain,(
% 3.35/0.84    ( ! [X6,X8,X7,X5,X9] : (k4_enumset1(X5,X5,X6,X7,X8,X9) = k2_xboole_0(k1_enumset1(X5,X6,X7),k2_tarski(X8,X9))) )),
% 3.35/0.84    inference(superposition,[],[f36,f29])).
% 3.35/0.84  fof(f4808,plain,(
% 3.35/0.84    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X5,X4,X6,X7) = k2_enumset1(X5,X4,X6,X7)) )),
% 3.35/0.84    inference(forward_demodulation,[],[f4787,f4807])).
% 3.35/0.84  fof(f4807,plain,(
% 3.35/0.84    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X3))) )),
% 3.35/0.84    inference(forward_demodulation,[],[f4786,f1809])).
% 3.35/0.84  fof(f4786,plain,(
% 3.35/0.84    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X1,X0,X2,X3) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X3))) )),
% 3.35/0.84    inference(superposition,[],[f1795,f2777])).
% 3.35/0.84  fof(f2777,plain,(
% 3.35/0.84    ( ! [X8,X9] : (k2_tarski(X9,X8) = k1_enumset1(X8,X8,X9)) )),
% 3.35/0.84    inference(superposition,[],[f2758,f1903])).
% 3.35/0.84  fof(f1903,plain,(
% 3.35/0.84    ( ! [X26,X27,X25] : (k2_enumset1(X27,X26,X25,X26) = k1_enumset1(X27,X25,X26)) )),
% 3.35/0.84    inference(forward_demodulation,[],[f1902,f1878])).
% 3.35/0.84  fof(f1878,plain,(
% 3.35/0.84    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 3.35/0.84    inference(forward_demodulation,[],[f1853,f29])).
% 3.35/0.84  fof(f1853,plain,(
% 3.35/0.84    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 3.35/0.84    inference(superposition,[],[f1833,f32])).
% 3.35/0.84  fof(f1833,plain,(
% 3.35/0.84    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.35/0.84    inference(superposition,[],[f1760,f1796])).
% 3.35/0.84  fof(f1760,plain,(
% 3.35/0.84    ( ! [X19,X20,X18] : (k2_xboole_0(k1_tarski(X18),k2_tarski(X19,X20)) = k4_enumset1(X18,X18,X18,X18,X19,X20)) )),
% 3.35/0.84    inference(superposition,[],[f36,f354])).
% 3.35/0.84  fof(f354,plain,(
% 3.35/0.84    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.35/0.84    inference(superposition,[],[f238,f263])).
% 3.35/0.84  fof(f263,plain,(
% 3.35/0.84    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 3.35/0.84    inference(superposition,[],[f255,f24])).
% 3.35/0.84  fof(f24,plain,(
% 3.35/0.84    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.35/0.84    inference(cnf_transformation,[],[f11])).
% 3.35/0.84  fof(f11,axiom,(
% 3.35/0.84    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.35/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 3.35/0.84  fof(f255,plain,(
% 3.35/0.84    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 3.35/0.84    inference(forward_demodulation,[],[f226,f56])).
% 3.35/0.84  fof(f56,plain,(
% 3.35/0.84    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)) )),
% 3.35/0.84    inference(superposition,[],[f50,f26])).
% 3.35/0.84  fof(f26,plain,(
% 3.35/0.84    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.35/0.84    inference(cnf_transformation,[],[f12])).
% 3.35/0.84  fof(f12,axiom,(
% 3.35/0.84    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.35/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.35/0.84  fof(f50,plain,(
% 3.35/0.84    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k1_enumset1(X3,X5,X4)) )),
% 3.35/0.84    inference(superposition,[],[f46,f29])).
% 3.35/0.84  fof(f226,plain,(
% 3.35/0.84    ( ! [X0,X1] : (k1_enumset1(X0,X1,X0) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 3.35/0.84    inference(superposition,[],[f218,f46])).
% 3.35/0.84  fof(f218,plain,(
% 3.35/0.84    ( ! [X2,X0,X1] : (k2_enumset1(X2,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1))) )),
% 3.35/0.84    inference(superposition,[],[f33,f26])).
% 3.35/0.84  fof(f33,plain,(
% 3.35/0.84    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 3.35/0.84    inference(cnf_transformation,[],[f7])).
% 3.35/0.84  fof(f7,axiom,(
% 3.35/0.84    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 3.35/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 3.35/0.84  fof(f238,plain,(
% 3.35/0.84    ( ! [X0,X1] : (k2_enumset1(X1,X0,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) )),
% 3.35/0.84    inference(superposition,[],[f218,f24])).
% 3.35/0.84  fof(f1902,plain,(
% 3.35/0.84    ( ! [X26,X27,X25] : (k2_enumset1(X27,X26,X25,X26) = k2_xboole_0(k1_tarski(X27),k2_tarski(X25,X26))) )),
% 3.35/0.84    inference(forward_demodulation,[],[f1901,f56])).
% 3.35/0.84  fof(f1901,plain,(
% 3.35/0.84    ( ! [X26,X27,X25] : (k2_enumset1(X27,X26,X25,X26) = k2_xboole_0(k1_tarski(X27),k1_enumset1(X25,X26,X25))) )),
% 3.35/0.84    inference(forward_demodulation,[],[f1900,f29])).
% 3.35/0.84  fof(f1900,plain,(
% 3.35/0.84    ( ! [X26,X27,X25] : (k2_enumset1(X27,X26,X25,X26) = k2_xboole_0(k1_tarski(X27),k2_enumset1(X25,X25,X26,X25))) )),
% 3.35/0.84    inference(forward_demodulation,[],[f1864,f32])).
% 3.35/0.84  fof(f1864,plain,(
% 3.35/0.84    ( ! [X26,X27,X25] : (k2_enumset1(X27,X26,X25,X26) = k2_xboole_0(k1_tarski(X27),k3_enumset1(X25,X25,X25,X26,X25))) )),
% 3.35/0.84    inference(superposition,[],[f916,f1833])).
% 3.35/0.84  fof(f916,plain,(
% 3.35/0.84    ( ! [X30,X31,X32] : (k2_enumset1(X30,X32,X31,X32) = k2_xboole_0(k1_tarski(X30),k2_xboole_0(k1_tarski(X31),k2_tarski(X32,X31)))) )),
% 3.35/0.84    inference(superposition,[],[f478,f31])).
% 3.35/0.84  fof(f31,plain,(
% 3.35/0.84    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)) )),
% 3.35/0.84    inference(cnf_transformation,[],[f6])).
% 3.35/0.84  fof(f6,axiom,(
% 3.35/0.84    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 3.35/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).
% 3.35/0.84  fof(f478,plain,(
% 3.35/0.84    ( ! [X4,X2,X3] : (k2_enumset1(X4,X2,X3,X3) = k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X2),k2_tarski(X3,X2)))) )),
% 3.35/0.84    inference(superposition,[],[f33,f234])).
% 3.35/0.84  fof(f234,plain,(
% 3.35/0.84    ( ! [X28,X29] : (k1_enumset1(X28,X29,X29) = k2_xboole_0(k1_tarski(X28),k2_tarski(X29,X28))) )),
% 3.35/0.84    inference(superposition,[],[f218,f93])).
% 3.35/0.84  fof(f93,plain,(
% 3.35/0.84    ( ! [X12,X10,X11] : (k2_enumset1(X10,X11,X12,X10) = k1_enumset1(X10,X12,X11)) )),
% 3.35/0.84    inference(superposition,[],[f64,f30])).
% 3.35/0.84  fof(f64,plain,(
% 3.35/0.84    ( ! [X2,X0,X1] : (k1_enumset1(X0,X2,X1) = k2_enumset1(X0,X1,X0,X2)) )),
% 3.35/0.84    inference(superposition,[],[f31,f46])).
% 3.35/0.84  fof(f2758,plain,(
% 3.35/0.84    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X1,X0,X1,X0)) )),
% 3.35/0.84    inference(superposition,[],[f2066,f573])).
% 3.35/0.84  fof(f573,plain,(
% 3.35/0.84    ( ! [X10,X8,X9] : (k2_enumset1(X8,X9,X10,X9) = k2_xboole_0(k2_tarski(X9,X10),k1_tarski(X8))) )),
% 3.35/0.84    inference(superposition,[],[f239,f30])).
% 3.35/0.84  fof(f239,plain,(
% 3.35/0.84    ( ! [X4,X5,X3] : (k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) = k2_enumset1(X3,X4,X4,X5)) )),
% 3.35/0.84    inference(superposition,[],[f218,f25])).
% 3.35/0.84  fof(f25,plain,(
% 3.35/0.84    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.35/0.84    inference(cnf_transformation,[],[f1])).
% 3.35/0.84  fof(f1,axiom,(
% 3.35/0.84    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.35/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.35/0.84  fof(f2066,plain,(
% 3.35/0.84    ( ! [X15,X16] : (k2_tarski(X16,X15) = k2_xboole_0(k2_tarski(X16,X15),k1_tarski(X15))) )),
% 3.35/0.84    inference(superposition,[],[f2061,f579])).
% 3.35/0.84  fof(f579,plain,(
% 3.35/0.84    ( ! [X33,X32] : (k1_enumset1(X32,X33,X33) = k2_xboole_0(k2_tarski(X33,X32),k1_tarski(X32))) )),
% 3.35/0.84    inference(superposition,[],[f239,f93])).
% 3.35/0.84  fof(f2061,plain,(
% 3.35/0.84    ( ! [X80,X81] : (k1_enumset1(X80,X81,X81) = k2_tarski(X81,X80)) )),
% 3.35/0.84    inference(forward_demodulation,[],[f2040,f2049])).
% 3.35/0.84  fof(f2049,plain,(
% 3.35/0.84    ( ! [X76,X77] : (k2_xboole_0(k1_tarski(X77),k1_tarski(X76)) = k2_tarski(X76,X77)) )),
% 3.35/0.84    inference(forward_demodulation,[],[f2012,f1891])).
% 3.35/0.84  fof(f1891,plain,(
% 3.35/0.84    ( ! [X17,X18] : (k2_tarski(X17,X18) = k1_enumset1(X17,X18,X18)) )),
% 3.35/0.84    inference(forward_demodulation,[],[f1890,f255])).
% 3.35/0.84  fof(f1890,plain,(
% 3.35/0.84    ( ! [X17,X18] : (k1_enumset1(X17,X18,X18) = k2_xboole_0(k1_tarski(X17),k2_tarski(X17,X18))) )),
% 3.35/0.84    inference(forward_demodulation,[],[f1889,f56])).
% 3.35/0.84  fof(f1889,plain,(
% 3.35/0.84    ( ! [X17,X18] : (k1_enumset1(X17,X18,X18) = k2_xboole_0(k1_tarski(X17),k1_enumset1(X17,X18,X17))) )),
% 3.35/0.84    inference(forward_demodulation,[],[f1888,f29])).
% 3.35/0.84  fof(f1888,plain,(
% 3.35/0.84    ( ! [X17,X18] : (k1_enumset1(X17,X18,X18) = k2_xboole_0(k1_tarski(X17),k2_enumset1(X17,X17,X18,X17))) )),
% 3.35/0.84    inference(forward_demodulation,[],[f1861,f32])).
% 3.35/0.84  fof(f1861,plain,(
% 3.35/0.84    ( ! [X17,X18] : (k1_enumset1(X17,X18,X18) = k2_xboole_0(k1_tarski(X17),k3_enumset1(X17,X17,X17,X18,X17))) )),
% 3.35/0.84    inference(superposition,[],[f910,f1833])).
% 3.35/0.84  fof(f910,plain,(
% 3.35/0.84    ( ! [X0,X1] : (k1_enumset1(X0,X1,X1) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X0)))) )),
% 3.35/0.84    inference(superposition,[],[f478,f46])).
% 3.35/0.84  fof(f2012,plain,(
% 3.35/0.84    ( ! [X76,X77] : (k2_xboole_0(k1_tarski(X77),k1_tarski(X76)) = k1_enumset1(X76,X77,X77)) )),
% 3.35/0.84    inference(superposition,[],[f1883,f355])).
% 3.35/0.84  fof(f355,plain,(
% 3.35/0.84    ( ! [X4,X3] : (k2_xboole_0(k1_tarski(X4),k1_tarski(X3)) = k2_enumset1(X3,X4,X4,X4)) )),
% 3.35/0.84    inference(superposition,[],[f238,f25])).
% 3.35/0.84  fof(f1883,plain,(
% 3.35/0.84    ( ! [X12,X13,X11] : (k2_enumset1(X13,X11,X12,X12) = k1_enumset1(X13,X11,X12)) )),
% 3.35/0.84    inference(forward_demodulation,[],[f1882,f1878])).
% 3.35/0.84  fof(f1882,plain,(
% 3.35/0.84    ( ! [X12,X13,X11] : (k2_xboole_0(k1_tarski(X13),k2_tarski(X11,X12)) = k2_enumset1(X13,X11,X12,X12)) )),
% 3.35/0.84    inference(forward_demodulation,[],[f1881,f56])).
% 3.35/0.84  fof(f1881,plain,(
% 3.35/0.84    ( ! [X12,X13,X11] : (k2_xboole_0(k1_tarski(X13),k1_enumset1(X11,X12,X11)) = k2_enumset1(X13,X11,X12,X12)) )),
% 3.35/0.84    inference(forward_demodulation,[],[f1880,f29])).
% 3.35/0.84  fof(f1880,plain,(
% 3.35/0.84    ( ! [X12,X13,X11] : (k2_enumset1(X13,X11,X12,X12) = k2_xboole_0(k1_tarski(X13),k2_enumset1(X11,X11,X12,X11))) )),
% 3.35/0.84    inference(forward_demodulation,[],[f1859,f32])).
% 3.35/0.84  fof(f1859,plain,(
% 3.35/0.84    ( ! [X12,X13,X11] : (k2_enumset1(X13,X11,X12,X12) = k2_xboole_0(k1_tarski(X13),k3_enumset1(X11,X11,X11,X12,X11))) )),
% 3.35/0.84    inference(superposition,[],[f478,f1833])).
% 3.35/0.84  fof(f2040,plain,(
% 3.35/0.84    ( ! [X80,X81] : (k1_enumset1(X80,X81,X81) = k2_xboole_0(k1_tarski(X80),k1_tarski(X81))) )),
% 3.35/0.84    inference(superposition,[],[f238,f1883])).
% 3.35/0.84  fof(f4787,plain,(
% 3.35/0.84    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X5,X4,X6,X7) = k2_xboole_0(k2_tarski(X4,X5),k2_tarski(X6,X7))) )),
% 3.35/0.84    inference(superposition,[],[f1795,f26])).
% 3.35/0.84  fof(f44,plain,(
% 3.35/0.84    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) | spl4_1),
% 3.35/0.84    inference(avatar_component_clause,[],[f42])).
% 3.35/0.84  fof(f42,plain,(
% 3.35/0.84    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK0,sK2,sK3)),
% 3.35/0.84    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 3.35/0.84  fof(f5075,plain,(
% 3.35/0.84    spl4_1),
% 3.35/0.84    inference(avatar_contradiction_clause,[],[f5074])).
% 3.35/0.84  fof(f5074,plain,(
% 3.35/0.84    $false | spl4_1),
% 3.35/0.84    inference(trivial_inequality_removal,[],[f5025])).
% 3.35/0.84  fof(f5025,plain,(
% 3.35/0.84    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3) | spl4_1),
% 3.35/0.84    inference(superposition,[],[f44,f4853])).
% 3.35/0.84  fof(f45,plain,(
% 3.35/0.84    ~spl4_1),
% 3.35/0.84    inference(avatar_split_clause,[],[f23,f42])).
% 3.35/0.84  fof(f23,plain,(
% 3.35/0.84    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 3.35/0.84    inference(cnf_transformation,[],[f22])).
% 3.35/0.84  fof(f22,plain,(
% 3.35/0.84    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 3.35/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f21])).
% 3.35/0.84  fof(f21,plain,(
% 3.35/0.84    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 3.35/0.84    introduced(choice_axiom,[])).
% 3.35/0.84  fof(f20,plain,(
% 3.35/0.84    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 3.35/0.84    inference(ennf_transformation,[],[f19])).
% 3.35/0.84  fof(f19,negated_conjecture,(
% 3.35/0.84    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 3.35/0.84    inference(negated_conjecture,[],[f18])).
% 3.35/0.84  fof(f18,conjecture,(
% 3.35/0.84    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 3.35/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).
% 3.35/0.84  % SZS output end Proof for theBenchmark
% 3.35/0.84  % (19525)------------------------------
% 3.35/0.84  % (19525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.35/0.84  % (19525)Termination reason: Refutation
% 3.35/0.84  
% 3.35/0.84  % (19525)Memory used [KB]: 8187
% 3.35/0.84  % (19525)Time elapsed: 0.397 s
% 3.35/0.84  % (19525)------------------------------
% 3.35/0.84  % (19525)------------------------------
% 3.35/0.84  % (19524)Success in time 0.489 s
%------------------------------------------------------------------------------
