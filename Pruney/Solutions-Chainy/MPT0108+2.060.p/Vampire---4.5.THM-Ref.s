%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:27 EST 2020

% Result     : Theorem 23.53s
% Output     : Refutation 23.53s
% Verified   : 
% Statistics : Number of formulae       :  136 (107935 expanded)
%              Number of leaves         :   12 (36165 expanded)
%              Depth                    :   42
%              Number of atoms          :  140 (107940 expanded)
%              Number of equality atoms :  133 (107932 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f39819,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f39801])).

fof(f39801,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f39800])).

fof(f39800,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f34,f39799])).

fof(f39799,plain,(
    ! [X227,X226] : k5_xboole_0(X226,X227) = k4_xboole_0(k5_xboole_0(X226,k4_xboole_0(X227,X226)),k4_xboole_0(X226,k4_xboole_0(X226,X227))) ),
    inference(forward_demodulation,[],[f39621,f39701])).

fof(f39701,plain,(
    ! [X26,X27] : k4_xboole_0(X26,k4_xboole_0(X26,X27)) = k4_xboole_0(X26,k5_xboole_0(X26,X27)) ),
    inference(forward_demodulation,[],[f39700,f153])).

fof(f153,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f131,f146])).

fof(f146,plain,(
    ! [X3] : k5_xboole_0(k1_xboole_0,X3) = X3 ),
    inference(forward_demodulation,[],[f130,f64])).

fof(f64,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f46,f60])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f27,f46])).

fof(f27,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f17,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f17,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f25,f16])).

fof(f16,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f130,plain,(
    ! [X3] : k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f56,f53])).

fof(f53,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f47,f16])).

fof(f47,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f25,f27])).

fof(f56,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f23,f53])).

fof(f23,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f131,plain,(
    ! [X4,X5] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X4,k4_xboole_0(X4,X5))) = k5_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f56,f25])).

fof(f39700,plain,(
    ! [X26,X27] : k5_xboole_0(X26,k4_xboole_0(X26,X27)) = k4_xboole_0(X26,k5_xboole_0(X26,X27)) ),
    inference(forward_demodulation,[],[f39545,f24737])).

fof(f24737,plain,(
    ! [X107,X108] : k4_xboole_0(X107,X108) = k4_xboole_0(k5_xboole_0(X107,X108),k4_xboole_0(X108,X107)) ),
    inference(forward_demodulation,[],[f24736,f64])).

fof(f24736,plain,(
    ! [X107,X108] : k5_xboole_0(k4_xboole_0(X107,X108),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X107,X108),k4_xboole_0(X108,X107)) ),
    inference(backward_demodulation,[],[f24087,f24550])).

fof(f24550,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f2134,f22521])).

fof(f22521,plain,(
    ! [X4,X3] : k5_xboole_0(X3,X4) = k5_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,X3)) ),
    inference(superposition,[],[f207,f22348])).

fof(f22348,plain,(
    ! [X70,X71] : k4_xboole_0(X71,X70) = k5_xboole_0(X70,k5_xboole_0(X71,k4_xboole_0(X70,X71))) ),
    inference(backward_demodulation,[],[f18761,f22346])).

fof(f22346,plain,(
    ! [X35,X34] : k4_xboole_0(X34,X35) = k4_xboole_0(k5_xboole_0(X34,k4_xboole_0(X35,X34)),X35) ),
    inference(forward_demodulation,[],[f22345,f451])).

fof(f451,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X5,X6))) ),
    inference(forward_demodulation,[],[f443,f16])).

fof(f443,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X5,X6))) = k4_xboole_0(k4_xboole_0(X5,X6),k1_xboole_0) ),
    inference(superposition,[],[f28,f427])).

fof(f427,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),X4) ),
    inference(backward_demodulation,[],[f297,f407])).

fof(f407,plain,(
    ! [X10,X9] : k5_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X10,k4_xboole_0(X10,X9))) = X9 ),
    inference(superposition,[],[f210,f295])).

fof(f295,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f25,f28])).

fof(f210,plain,(
    ! [X6,X7] : k5_xboole_0(k5_xboole_0(X6,X7),X7) = X6 ),
    inference(superposition,[],[f199,f152])).

fof(f152,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    inference(forward_demodulation,[],[f148,f146])).

fof(f148,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3))) = X3 ),
    inference(backward_demodulation,[],[f127,f146])).

fof(f127,plain,(
    ! [X2,X3] : k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f118,f23])).

fof(f118,plain,(
    ! [X2,X3] : k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),X3)) ),
    inference(superposition,[],[f23,f99])).

fof(f99,plain,(
    ! [X8] : k1_xboole_0 = k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,X8)) ),
    inference(superposition,[],[f54,f64])).

fof(f54,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) ),
    inference(superposition,[],[f53,f23])).

fof(f199,plain,(
    ! [X6,X7] : k5_xboole_0(X7,k5_xboole_0(X6,X7)) = X6 ),
    inference(forward_demodulation,[],[f187,f64])).

fof(f187,plain,(
    ! [X6,X7] : k5_xboole_0(X7,k5_xboole_0(X6,X7)) = k5_xboole_0(X6,k1_xboole_0) ),
    inference(superposition,[],[f152,f54])).

fof(f297,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X5,X4)))) ),
    inference(superposition,[],[f27,f28])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f18,f21,f21])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f22345,plain,(
    ! [X35,X34] : k4_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(X34,X35))) = k4_xboole_0(k5_xboole_0(X34,k4_xboole_0(X35,X34)),X35) ),
    inference(forward_demodulation,[],[f22344,f20976])).

fof(f20976,plain,(
    ! [X10,X11,X9] : k4_xboole_0(X9,k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),X11)) = k4_xboole_0(X9,k4_xboole_0(X9,X11)) ),
    inference(backward_demodulation,[],[f20969,f20975])).

fof(f20975,plain,(
    ! [X33,X31,X32] : k4_xboole_0(X31,X33) = k4_xboole_0(X31,k4_xboole_0(X33,k4_xboole_0(X33,k5_xboole_0(X31,k4_xboole_0(X32,X31))))) ),
    inference(forward_demodulation,[],[f20797,f1703])).

fof(f1703,plain,(
    ! [X21,X22,X20] : k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k5_xboole_0(X20,k4_xboole_0(X21,X20)),X22))) = k4_xboole_0(X20,X22) ),
    inference(forward_demodulation,[],[f1623,f16])).

fof(f1623,plain,(
    ! [X21,X22,X20] : k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k5_xboole_0(X20,k4_xboole_0(X21,X20)),X22))) = k4_xboole_0(k4_xboole_0(X20,k1_xboole_0),X22) ),
    inference(superposition,[],[f30,f27])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f24,f21,f21])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f20797,plain,(
    ! [X33,X31,X32] : k4_xboole_0(X31,k4_xboole_0(X33,k4_xboole_0(X33,k5_xboole_0(X31,k4_xboole_0(X32,X31))))) = k4_xboole_0(X31,k4_xboole_0(X31,k4_xboole_0(k5_xboole_0(X31,k4_xboole_0(X32,X31)),X33))) ),
    inference(superposition,[],[f1703,f491])).

fof(f491,plain,(
    ! [X10,X9] : k4_xboole_0(X10,X9) = k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f490,f295])).

fof(f490,plain,(
    ! [X10,X9] : k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k5_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f473,f16])).

fof(f473,plain,(
    ! [X10,X9] : k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k5_xboole_0(X10,k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),k1_xboole_0)) ),
    inference(superposition,[],[f295,f430])).

fof(f430,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1) ),
    inference(superposition,[],[f427,f28])).

fof(f20969,plain,(
    ! [X10,X11,X9] : k4_xboole_0(X9,k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),X11)) = k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X11,k4_xboole_0(X11,k5_xboole_0(X9,k4_xboole_0(X10,X9)))))) ),
    inference(forward_demodulation,[],[f20968,f153])).

fof(f20968,plain,(
    ! [X10,X11,X9] : k4_xboole_0(X9,k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),X11)) = k4_xboole_0(X9,k4_xboole_0(X9,k5_xboole_0(X11,k4_xboole_0(X11,k5_xboole_0(X9,k4_xboole_0(X10,X9)))))) ),
    inference(forward_demodulation,[],[f20790,f217])).

fof(f217,plain,(
    ! [X2,X3] : k5_xboole_0(X2,X3) = k5_xboole_0(X3,X2) ),
    inference(superposition,[],[f152,f199])).

fof(f20790,plain,(
    ! [X10,X11,X9] : k4_xboole_0(X9,k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),X11)) = k4_xboole_0(X9,k4_xboole_0(X9,k5_xboole_0(k4_xboole_0(X11,k5_xboole_0(X9,k4_xboole_0(X10,X9))),X11))) ),
    inference(superposition,[],[f1703,f408])).

fof(f408,plain,(
    ! [X12,X11] : k4_xboole_0(X12,k4_xboole_0(X12,X11)) = k5_xboole_0(k4_xboole_0(X11,X12),X11) ),
    inference(superposition,[],[f211,f295])).

fof(f211,plain,(
    ! [X8,X9] : k5_xboole_0(k5_xboole_0(X9,X8),X9) = X8 ),
    inference(superposition,[],[f199,f199])).

fof(f22344,plain,(
    ! [X35,X34] : k4_xboole_0(k5_xboole_0(X34,k4_xboole_0(X35,X34)),X35) = k4_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(k5_xboole_0(X34,k4_xboole_0(X35,X34)),X35))) ),
    inference(forward_demodulation,[],[f22191,f16])).

fof(f22191,plain,(
    ! [X35,X34] : k4_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(k5_xboole_0(X34,k4_xboole_0(X35,X34)),X35))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X34,k4_xboole_0(X35,X34)),X35),k1_xboole_0) ),
    inference(superposition,[],[f28,f21879])).

fof(f21879,plain,(
    ! [X88,X87] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X87,k4_xboole_0(X88,X87)),X88),X87) ),
    inference(superposition,[],[f21466,f524])).

fof(f524,plain,(
    ! [X8,X9] : k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) = X9 ),
    inference(forward_demodulation,[],[f523,f210])).

fof(f523,plain,(
    ! [X8,X9] : k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) = k5_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) ),
    inference(forward_demodulation,[],[f512,f16])).

fof(f512,plain,(
    ! [X8,X9] : k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) = k5_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(k4_xboole_0(X8,X9),k1_xboole_0)) ),
    inference(superposition,[],[f295,f370])).

fof(f370,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,X9),k5_xboole_0(X9,k4_xboole_0(X10,X9))) ),
    inference(forward_demodulation,[],[f365,f217])).

fof(f365,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,X9),k5_xboole_0(k4_xboole_0(X10,X9),X9)) ),
    inference(superposition,[],[f27,f322])).

fof(f322,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k4_xboole_0(X6,X5)) = X5 ),
    inference(superposition,[],[f36,f25])).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    inference(backward_demodulation,[],[f29,f30])).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
    inference(definition_unfolding,[],[f19,f20,f21])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f21466,plain,(
    ! [X6,X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f21176,f1988])).

fof(f1988,plain,(
    ! [X14,X15,X16] : k4_xboole_0(X15,X14) = k4_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X14,X16)) ),
    inference(superposition,[],[f1941,f322])).

fof(f1941,plain,(
    ! [X21,X22,X20] : k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X20,X21),X22)) = X21 ),
    inference(forward_demodulation,[],[f1878,f16])).

fof(f1878,plain,(
    ! [X21,X22,X20] : k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(k4_xboole_0(X20,X21),X22),k1_xboole_0)) = X21 ),
    inference(superposition,[],[f1666,f427])).

fof(f1666,plain,(
    ! [X33,X31,X32] : k4_xboole_0(X33,k4_xboole_0(X31,k4_xboole_0(X31,k4_xboole_0(X32,X33)))) = X33 ),
    inference(superposition,[],[f322,f30])).

fof(f21176,plain,(
    ! [X12,X10,X11] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),k4_xboole_0(X10,X12)) ),
    inference(superposition,[],[f20829,f230])).

fof(f230,plain,(
    ! [X6,X7] : k5_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,k4_xboole_0(X6,X7))) = X6 ),
    inference(superposition,[],[f210,f25])).

fof(f20829,plain,(
    ! [X45,X43,X44] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X43,X45),k4_xboole_0(k5_xboole_0(X43,k4_xboole_0(X44,X43)),X45)) ),
    inference(superposition,[],[f430,f1703])).

fof(f18761,plain,(
    ! [X70,X71] : k4_xboole_0(k5_xboole_0(X71,k4_xboole_0(X70,X71)),X70) = k5_xboole_0(X70,k5_xboole_0(X71,k4_xboole_0(X70,X71))) ),
    inference(forward_demodulation,[],[f18675,f16])).

fof(f18675,plain,(
    ! [X70,X71] : k4_xboole_0(k5_xboole_0(X71,k4_xboole_0(X70,X71)),X70) = k5_xboole_0(k4_xboole_0(X70,k1_xboole_0),k5_xboole_0(X71,k4_xboole_0(X70,X71))) ),
    inference(superposition,[],[f924,f18383])).

fof(f18383,plain,(
    ! [X78,X79] : k1_xboole_0 = k4_xboole_0(X79,k5_xboole_0(X78,k4_xboole_0(X79,X78))) ),
    inference(superposition,[],[f13034,f211])).

fof(f13034,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X3,X2),X2))) ),
    inference(forward_demodulation,[],[f13033,f217])).

fof(f13033,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(k4_xboole_0(k5_xboole_0(X3,X2),X2),X2)) ),
    inference(forward_demodulation,[],[f12819,f4370])).

fof(f4370,plain,(
    ! [X80,X81,X79] : k5_xboole_0(k4_xboole_0(k5_xboole_0(X79,X80),X81),X80) = k5_xboole_0(X79,k4_xboole_0(X81,k4_xboole_0(X81,k5_xboole_0(X79,X80)))) ),
    inference(superposition,[],[f225,f408])).

fof(f225,plain,(
    ! [X6,X4,X5] : k5_xboole_0(X5,X6) = k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X4,X6))) ),
    inference(forward_demodulation,[],[f218,f23])).

fof(f218,plain,(
    ! [X6,X4,X5] : k5_xboole_0(X5,X6) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X5,X4),X6)) ),
    inference(superposition,[],[f23,f199])).

fof(f12819,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X3,X2))))) ),
    inference(superposition,[],[f43,f153])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X0,X1))))) ),
    inference(superposition,[],[f27,f23])).

fof(f924,plain,(
    ! [X26,X25] : k4_xboole_0(X25,X26) = k5_xboole_0(k4_xboole_0(X26,k4_xboole_0(X26,X25)),X25) ),
    inference(superposition,[],[f211,f405])).

fof(f405,plain,(
    ! [X6,X5] : k4_xboole_0(X6,k4_xboole_0(X6,X5)) = k5_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f152,f295])).

fof(f207,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2))) ),
    inference(superposition,[],[f199,f23])).

fof(f2134,plain,(
    ! [X52,X50,X51] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X50,X51),k5_xboole_0(k4_xboole_0(X51,X52),k4_xboole_0(X50,X51))) ),
    inference(superposition,[],[f370,f1988])).

fof(f24087,plain,(
    ! [X107,X108] : k4_xboole_0(k5_xboole_0(X107,X108),k4_xboole_0(X108,X107)) = k5_xboole_0(k4_xboole_0(X107,X108),k4_xboole_0(k4_xboole_0(X108,X107),k5_xboole_0(X107,X108))) ),
    inference(superposition,[],[f22520,f22520])).

fof(f22520,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(superposition,[],[f147,f22348])).

fof(f147,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(backward_demodulation,[],[f129,f146])).

fof(f129,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) ),
    inference(superposition,[],[f56,f23])).

fof(f39545,plain,(
    ! [X26,X27] : k4_xboole_0(X26,k5_xboole_0(X26,X27)) = k5_xboole_0(X26,k4_xboole_0(k5_xboole_0(X26,X27),k4_xboole_0(X27,X26))) ),
    inference(superposition,[],[f295,f38943])).

fof(f38943,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f38737,f217])).

fof(f38737,plain,(
    ! [X66,X65] : k4_xboole_0(X65,X66) = k4_xboole_0(k5_xboole_0(X65,X66),X66) ),
    inference(forward_demodulation,[],[f38736,f64])).

fof(f38736,plain,(
    ! [X66,X65] : k5_xboole_0(k4_xboole_0(X65,X66),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X65,X66),X66) ),
    inference(forward_demodulation,[],[f38735,f38297])).

fof(f38297,plain,(
    ! [X116,X117] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X116,X117),k4_xboole_0(k5_xboole_0(X116,X117),X117)) ),
    inference(superposition,[],[f35711,f210])).

fof(f35711,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X2,X3),X3),k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f21466,f24737])).

fof(f38735,plain,(
    ! [X66,X65] : k4_xboole_0(k5_xboole_0(X65,X66),X66) = k5_xboole_0(k4_xboole_0(X65,X66),k4_xboole_0(k4_xboole_0(X65,X66),k4_xboole_0(k5_xboole_0(X65,X66),X66))) ),
    inference(forward_demodulation,[],[f38428,f16])).

fof(f38428,plain,(
    ! [X66,X65] : k5_xboole_0(k4_xboole_0(X65,X66),k4_xboole_0(k4_xboole_0(X65,X66),k4_xboole_0(k5_xboole_0(X65,X66),X66))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X65,X66),X66),k1_xboole_0) ),
    inference(superposition,[],[f405,f35711])).

fof(f39621,plain,(
    ! [X227,X226] : k5_xboole_0(X226,X227) = k4_xboole_0(k5_xboole_0(X226,k4_xboole_0(X227,X226)),k4_xboole_0(X226,k5_xboole_0(X226,X227))) ),
    inference(superposition,[],[f23222,f38943])).

fof(f23222,plain,(
    ! [X8,X9] : k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X9,X8)) = X8 ),
    inference(forward_demodulation,[],[f23022,f217])).

fof(f23022,plain,(
    ! [X8,X9] : k4_xboole_0(k5_xboole_0(k4_xboole_0(X8,X9),X9),k4_xboole_0(X9,X8)) = X8 ),
    inference(superposition,[],[f524,f22349])).

fof(f22349,plain,(
    ! [X41,X40] : k5_xboole_0(k4_xboole_0(X41,X40),X40) = k5_xboole_0(X41,k4_xboole_0(X40,X41)) ),
    inference(backward_demodulation,[],[f18743,f22346])).

fof(f18743,plain,(
    ! [X41,X40] : k5_xboole_0(X41,k4_xboole_0(X40,X41)) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X41,k4_xboole_0(X40,X41)),X40),X40) ),
    inference(forward_demodulation,[],[f18662,f16])).

fof(f18662,plain,(
    ! [X41,X40] : k5_xboole_0(X41,k4_xboole_0(X40,X41)) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X41,k4_xboole_0(X40,X41)),X40),k4_xboole_0(X40,k1_xboole_0)) ),
    inference(superposition,[],[f407,f18383])).

fof(f34,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl2_1
  <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f35,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f26,f32])).

fof(f26,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f15,f20,f21])).

fof(f15,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:46:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (1508)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.47  % (1505)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (1503)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (1513)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (1500)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (1512)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (1502)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (1509)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (1507)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (1511)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (1510)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (1510)Refutation not found, incomplete strategy% (1510)------------------------------
% 0.22/0.50  % (1510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (1510)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (1510)Memory used [KB]: 10490
% 0.22/0.50  % (1510)Time elapsed: 0.087 s
% 0.22/0.50  % (1510)------------------------------
% 0.22/0.50  % (1510)------------------------------
% 0.22/0.50  % (1501)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (1516)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (1515)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.50  % (1506)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (1499)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.50  % (1504)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.52  % (1514)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 5.09/1.03  % (1503)Time limit reached!
% 5.09/1.03  % (1503)------------------------------
% 5.09/1.03  % (1503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.09/1.03  % (1503)Termination reason: Time limit
% 5.09/1.03  % (1503)Termination phase: Saturation
% 5.09/1.03  
% 5.09/1.03  % (1503)Memory used [KB]: 17142
% 5.09/1.03  % (1503)Time elapsed: 0.600 s
% 5.09/1.03  % (1503)------------------------------
% 5.09/1.03  % (1503)------------------------------
% 12.52/1.93  % (1504)Time limit reached!
% 12.52/1.93  % (1504)------------------------------
% 12.52/1.93  % (1504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.52/1.93  % (1504)Termination reason: Time limit
% 12.52/1.93  
% 12.52/1.93  % (1504)Memory used [KB]: 46054
% 12.52/1.93  % (1504)Time elapsed: 1.514 s
% 12.52/1.93  % (1504)------------------------------
% 12.52/1.93  % (1504)------------------------------
% 12.52/1.96  % (1505)Time limit reached!
% 12.52/1.96  % (1505)------------------------------
% 12.52/1.96  % (1505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.52/1.96  % (1505)Termination reason: Time limit
% 12.52/1.96  
% 12.52/1.96  % (1505)Memory used [KB]: 41705
% 12.52/1.96  % (1505)Time elapsed: 1.505 s
% 12.52/1.96  % (1505)------------------------------
% 12.52/1.96  % (1505)------------------------------
% 14.76/2.22  % (1501)Time limit reached!
% 14.76/2.22  % (1501)------------------------------
% 14.76/2.22  % (1501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.76/2.22  % (1501)Termination reason: Time limit
% 14.76/2.22  
% 14.76/2.22  % (1501)Memory used [KB]: 40681
% 14.76/2.22  % (1501)Time elapsed: 1.804 s
% 14.76/2.22  % (1501)------------------------------
% 14.76/2.22  % (1501)------------------------------
% 18.01/2.63  % (1511)Time limit reached!
% 18.01/2.63  % (1511)------------------------------
% 18.01/2.63  % (1511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.01/2.64  % (1511)Termination reason: Time limit
% 18.01/2.64  
% 18.01/2.64  % (1511)Memory used [KB]: 42984
% 18.01/2.64  % (1511)Time elapsed: 2.218 s
% 18.01/2.64  % (1511)------------------------------
% 18.01/2.64  % (1511)------------------------------
% 23.53/3.35  % (1509)Refutation found. Thanks to Tanya!
% 23.53/3.35  % SZS status Theorem for theBenchmark
% 23.53/3.35  % SZS output start Proof for theBenchmark
% 23.53/3.35  fof(f39819,plain,(
% 23.53/3.35    $false),
% 23.53/3.35    inference(avatar_sat_refutation,[],[f35,f39801])).
% 23.53/3.35  fof(f39801,plain,(
% 23.53/3.35    spl2_1),
% 23.53/3.35    inference(avatar_contradiction_clause,[],[f39800])).
% 23.53/3.35  fof(f39800,plain,(
% 23.53/3.35    $false | spl2_1),
% 23.53/3.35    inference(subsumption_resolution,[],[f34,f39799])).
% 23.53/3.35  fof(f39799,plain,(
% 23.53/3.35    ( ! [X227,X226] : (k5_xboole_0(X226,X227) = k4_xboole_0(k5_xboole_0(X226,k4_xboole_0(X227,X226)),k4_xboole_0(X226,k4_xboole_0(X226,X227)))) )),
% 23.53/3.35    inference(forward_demodulation,[],[f39621,f39701])).
% 23.53/3.35  fof(f39701,plain,(
% 23.53/3.35    ( ! [X26,X27] : (k4_xboole_0(X26,k4_xboole_0(X26,X27)) = k4_xboole_0(X26,k5_xboole_0(X26,X27))) )),
% 23.53/3.35    inference(forward_demodulation,[],[f39700,f153])).
% 23.53/3.35  fof(f153,plain,(
% 23.53/3.35    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) )),
% 23.53/3.35    inference(forward_demodulation,[],[f131,f146])).
% 23.53/3.35  fof(f146,plain,(
% 23.53/3.35    ( ! [X3] : (k5_xboole_0(k1_xboole_0,X3) = X3) )),
% 23.53/3.35    inference(forward_demodulation,[],[f130,f64])).
% 23.53/3.35  fof(f64,plain,(
% 23.53/3.35    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.53/3.35    inference(backward_demodulation,[],[f46,f60])).
% 23.53/3.35  fof(f60,plain,(
% 23.53/3.35    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 23.53/3.35    inference(superposition,[],[f27,f46])).
% 23.53/3.35  fof(f27,plain,(
% 23.53/3.35    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 23.53/3.35    inference(definition_unfolding,[],[f17,f20])).
% 23.53/3.35  fof(f20,plain,(
% 23.53/3.35    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 23.53/3.35    inference(cnf_transformation,[],[f9])).
% 23.53/3.35  fof(f9,axiom,(
% 23.53/3.35    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 23.53/3.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 23.53/3.35  fof(f17,plain,(
% 23.53/3.35    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 23.53/3.35    inference(cnf_transformation,[],[f5])).
% 23.53/3.35  fof(f5,axiom,(
% 23.53/3.35    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 23.53/3.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 23.53/3.35  fof(f46,plain,(
% 23.53/3.35    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 23.53/3.35    inference(superposition,[],[f25,f16])).
% 23.53/3.35  fof(f16,plain,(
% 23.53/3.35    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.53/3.35    inference(cnf_transformation,[],[f4])).
% 23.53/3.35  fof(f4,axiom,(
% 23.53/3.35    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 23.53/3.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 23.53/3.35  fof(f25,plain,(
% 23.53/3.35    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 23.53/3.35    inference(definition_unfolding,[],[f22,f21])).
% 23.53/3.35  fof(f21,plain,(
% 23.53/3.35    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 23.53/3.35    inference(cnf_transformation,[],[f6])).
% 23.53/3.35  fof(f6,axiom,(
% 23.53/3.35    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 23.53/3.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 23.53/3.35  fof(f22,plain,(
% 23.53/3.35    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 23.53/3.35    inference(cnf_transformation,[],[f2])).
% 23.53/3.35  fof(f2,axiom,(
% 23.53/3.35    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 23.53/3.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 23.53/3.35  fof(f130,plain,(
% 23.53/3.35    ( ! [X3] : (k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X3,k1_xboole_0)) )),
% 23.53/3.35    inference(superposition,[],[f56,f53])).
% 23.53/3.35  fof(f53,plain,(
% 23.53/3.35    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 23.53/3.35    inference(forward_demodulation,[],[f47,f16])).
% 23.53/3.35  fof(f47,plain,(
% 23.53/3.35    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 23.53/3.35    inference(superposition,[],[f25,f27])).
% 23.53/3.35  fof(f56,plain,(
% 23.53/3.35    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 23.53/3.35    inference(superposition,[],[f23,f53])).
% 23.53/3.35  fof(f23,plain,(
% 23.53/3.35    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 23.53/3.35    inference(cnf_transformation,[],[f8])).
% 23.53/3.35  fof(f8,axiom,(
% 23.53/3.35    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 23.53/3.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 23.53/3.35  fof(f131,plain,(
% 23.53/3.35    ( ! [X4,X5] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X4,k4_xboole_0(X4,X5))) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) )),
% 23.53/3.35    inference(superposition,[],[f56,f25])).
% 23.53/3.35  fof(f39700,plain,(
% 23.53/3.35    ( ! [X26,X27] : (k5_xboole_0(X26,k4_xboole_0(X26,X27)) = k4_xboole_0(X26,k5_xboole_0(X26,X27))) )),
% 23.53/3.35    inference(forward_demodulation,[],[f39545,f24737])).
% 23.53/3.35  fof(f24737,plain,(
% 23.53/3.35    ( ! [X107,X108] : (k4_xboole_0(X107,X108) = k4_xboole_0(k5_xboole_0(X107,X108),k4_xboole_0(X108,X107))) )),
% 23.53/3.35    inference(forward_demodulation,[],[f24736,f64])).
% 23.53/3.35  fof(f24736,plain,(
% 23.53/3.35    ( ! [X107,X108] : (k5_xboole_0(k4_xboole_0(X107,X108),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X107,X108),k4_xboole_0(X108,X107))) )),
% 23.53/3.35    inference(backward_demodulation,[],[f24087,f24550])).
% 23.53/3.35  fof(f24550,plain,(
% 23.53/3.35    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),k5_xboole_0(X0,X1))) )),
% 23.53/3.35    inference(superposition,[],[f2134,f22521])).
% 23.53/3.35  fof(f22521,plain,(
% 23.53/3.35    ( ! [X4,X3] : (k5_xboole_0(X3,X4) = k5_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,X3))) )),
% 23.53/3.35    inference(superposition,[],[f207,f22348])).
% 23.53/3.35  fof(f22348,plain,(
% 23.53/3.35    ( ! [X70,X71] : (k4_xboole_0(X71,X70) = k5_xboole_0(X70,k5_xboole_0(X71,k4_xboole_0(X70,X71)))) )),
% 23.53/3.35    inference(backward_demodulation,[],[f18761,f22346])).
% 23.53/3.35  fof(f22346,plain,(
% 23.53/3.35    ( ! [X35,X34] : (k4_xboole_0(X34,X35) = k4_xboole_0(k5_xboole_0(X34,k4_xboole_0(X35,X34)),X35)) )),
% 23.53/3.35    inference(forward_demodulation,[],[f22345,f451])).
% 23.53/3.35  fof(f451,plain,(
% 23.53/3.35    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X5,X6)))) )),
% 23.53/3.35    inference(forward_demodulation,[],[f443,f16])).
% 23.53/3.35  fof(f443,plain,(
% 23.53/3.35    ( ! [X6,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X5,X6))) = k4_xboole_0(k4_xboole_0(X5,X6),k1_xboole_0)) )),
% 23.53/3.35    inference(superposition,[],[f28,f427])).
% 23.53/3.35  fof(f427,plain,(
% 23.53/3.35    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),X4)) )),
% 23.53/3.35    inference(backward_demodulation,[],[f297,f407])).
% 23.53/3.35  fof(f407,plain,(
% 23.53/3.35    ( ! [X10,X9] : (k5_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X10,k4_xboole_0(X10,X9))) = X9) )),
% 23.53/3.35    inference(superposition,[],[f210,f295])).
% 23.53/3.35  fof(f295,plain,(
% 23.53/3.35    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 23.53/3.35    inference(superposition,[],[f25,f28])).
% 23.53/3.35  fof(f210,plain,(
% 23.53/3.35    ( ! [X6,X7] : (k5_xboole_0(k5_xboole_0(X6,X7),X7) = X6) )),
% 23.53/3.35    inference(superposition,[],[f199,f152])).
% 23.53/3.35  fof(f152,plain,(
% 23.53/3.35    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) )),
% 23.53/3.35    inference(forward_demodulation,[],[f148,f146])).
% 23.53/3.35  fof(f148,plain,(
% 23.53/3.35    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3))) = X3) )),
% 23.53/3.35    inference(backward_demodulation,[],[f127,f146])).
% 23.53/3.35  fof(f127,plain,(
% 23.53/3.35    ( ! [X2,X3] : (k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)))) )),
% 23.53/3.35    inference(forward_demodulation,[],[f118,f23])).
% 23.53/3.35  fof(f118,plain,(
% 23.53/3.35    ( ! [X2,X3] : (k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),X3))) )),
% 23.53/3.35    inference(superposition,[],[f23,f99])).
% 23.53/3.35  fof(f99,plain,(
% 23.53/3.35    ( ! [X8] : (k1_xboole_0 = k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,X8))) )),
% 23.53/3.35    inference(superposition,[],[f54,f64])).
% 23.53/3.35  fof(f54,plain,(
% 23.53/3.35    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) )),
% 23.53/3.35    inference(superposition,[],[f53,f23])).
% 23.53/3.35  fof(f199,plain,(
% 23.53/3.35    ( ! [X6,X7] : (k5_xboole_0(X7,k5_xboole_0(X6,X7)) = X6) )),
% 23.53/3.35    inference(forward_demodulation,[],[f187,f64])).
% 23.53/3.35  fof(f187,plain,(
% 23.53/3.35    ( ! [X6,X7] : (k5_xboole_0(X7,k5_xboole_0(X6,X7)) = k5_xboole_0(X6,k1_xboole_0)) )),
% 23.53/3.35    inference(superposition,[],[f152,f54])).
% 23.53/3.35  fof(f297,plain,(
% 23.53/3.35    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X5,X4))))) )),
% 23.53/3.35    inference(superposition,[],[f27,f28])).
% 23.53/3.35  fof(f28,plain,(
% 23.53/3.35    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 23.53/3.35    inference(definition_unfolding,[],[f18,f21,f21])).
% 23.53/3.35  fof(f18,plain,(
% 23.53/3.35    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 23.53/3.35    inference(cnf_transformation,[],[f1])).
% 23.53/3.35  fof(f1,axiom,(
% 23.53/3.35    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 23.53/3.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 23.53/3.35  fof(f22345,plain,(
% 23.53/3.35    ( ! [X35,X34] : (k4_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(X34,X35))) = k4_xboole_0(k5_xboole_0(X34,k4_xboole_0(X35,X34)),X35)) )),
% 23.53/3.35    inference(forward_demodulation,[],[f22344,f20976])).
% 23.53/3.35  fof(f20976,plain,(
% 23.53/3.35    ( ! [X10,X11,X9] : (k4_xboole_0(X9,k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),X11)) = k4_xboole_0(X9,k4_xboole_0(X9,X11))) )),
% 23.53/3.35    inference(backward_demodulation,[],[f20969,f20975])).
% 23.53/3.35  fof(f20975,plain,(
% 23.53/3.35    ( ! [X33,X31,X32] : (k4_xboole_0(X31,X33) = k4_xboole_0(X31,k4_xboole_0(X33,k4_xboole_0(X33,k5_xboole_0(X31,k4_xboole_0(X32,X31)))))) )),
% 23.53/3.35    inference(forward_demodulation,[],[f20797,f1703])).
% 23.53/3.35  fof(f1703,plain,(
% 23.53/3.35    ( ! [X21,X22,X20] : (k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k5_xboole_0(X20,k4_xboole_0(X21,X20)),X22))) = k4_xboole_0(X20,X22)) )),
% 23.53/3.35    inference(forward_demodulation,[],[f1623,f16])).
% 23.53/3.35  fof(f1623,plain,(
% 23.53/3.35    ( ! [X21,X22,X20] : (k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k5_xboole_0(X20,k4_xboole_0(X21,X20)),X22))) = k4_xboole_0(k4_xboole_0(X20,k1_xboole_0),X22)) )),
% 23.53/3.35    inference(superposition,[],[f30,f27])).
% 23.53/3.35  fof(f30,plain,(
% 23.53/3.35    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 23.53/3.35    inference(definition_unfolding,[],[f24,f21,f21])).
% 23.53/3.35  fof(f24,plain,(
% 23.53/3.35    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 23.53/3.35    inference(cnf_transformation,[],[f7])).
% 23.53/3.35  fof(f7,axiom,(
% 23.53/3.35    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 23.53/3.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 23.53/3.35  fof(f20797,plain,(
% 23.53/3.35    ( ! [X33,X31,X32] : (k4_xboole_0(X31,k4_xboole_0(X33,k4_xboole_0(X33,k5_xboole_0(X31,k4_xboole_0(X32,X31))))) = k4_xboole_0(X31,k4_xboole_0(X31,k4_xboole_0(k5_xboole_0(X31,k4_xboole_0(X32,X31)),X33)))) )),
% 23.53/3.35    inference(superposition,[],[f1703,f491])).
% 23.53/3.35  fof(f491,plain,(
% 23.53/3.35    ( ! [X10,X9] : (k4_xboole_0(X10,X9) = k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 23.53/3.35    inference(forward_demodulation,[],[f490,f295])).
% 23.53/3.35  fof(f490,plain,(
% 23.53/3.35    ( ! [X10,X9] : (k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k5_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 23.53/3.35    inference(forward_demodulation,[],[f473,f16])).
% 23.53/3.35  fof(f473,plain,(
% 23.53/3.35    ( ! [X10,X9] : (k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k5_xboole_0(X10,k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),k1_xboole_0))) )),
% 23.53/3.35    inference(superposition,[],[f295,f430])).
% 23.53/3.35  fof(f430,plain,(
% 23.53/3.35    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1)) )),
% 23.53/3.35    inference(superposition,[],[f427,f28])).
% 23.53/3.35  fof(f20969,plain,(
% 23.53/3.35    ( ! [X10,X11,X9] : (k4_xboole_0(X9,k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),X11)) = k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X11,k4_xboole_0(X11,k5_xboole_0(X9,k4_xboole_0(X10,X9))))))) )),
% 23.53/3.35    inference(forward_demodulation,[],[f20968,f153])).
% 23.53/3.35  fof(f20968,plain,(
% 23.53/3.35    ( ! [X10,X11,X9] : (k4_xboole_0(X9,k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),X11)) = k4_xboole_0(X9,k4_xboole_0(X9,k5_xboole_0(X11,k4_xboole_0(X11,k5_xboole_0(X9,k4_xboole_0(X10,X9))))))) )),
% 23.53/3.35    inference(forward_demodulation,[],[f20790,f217])).
% 23.53/3.35  fof(f217,plain,(
% 23.53/3.35    ( ! [X2,X3] : (k5_xboole_0(X2,X3) = k5_xboole_0(X3,X2)) )),
% 23.53/3.35    inference(superposition,[],[f152,f199])).
% 23.53/3.35  fof(f20790,plain,(
% 23.53/3.35    ( ! [X10,X11,X9] : (k4_xboole_0(X9,k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),X11)) = k4_xboole_0(X9,k4_xboole_0(X9,k5_xboole_0(k4_xboole_0(X11,k5_xboole_0(X9,k4_xboole_0(X10,X9))),X11)))) )),
% 23.53/3.35    inference(superposition,[],[f1703,f408])).
% 23.53/3.35  fof(f408,plain,(
% 23.53/3.35    ( ! [X12,X11] : (k4_xboole_0(X12,k4_xboole_0(X12,X11)) = k5_xboole_0(k4_xboole_0(X11,X12),X11)) )),
% 23.53/3.35    inference(superposition,[],[f211,f295])).
% 23.53/3.35  fof(f211,plain,(
% 23.53/3.35    ( ! [X8,X9] : (k5_xboole_0(k5_xboole_0(X9,X8),X9) = X8) )),
% 23.53/3.35    inference(superposition,[],[f199,f199])).
% 23.53/3.35  fof(f22344,plain,(
% 23.53/3.35    ( ! [X35,X34] : (k4_xboole_0(k5_xboole_0(X34,k4_xboole_0(X35,X34)),X35) = k4_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(k5_xboole_0(X34,k4_xboole_0(X35,X34)),X35)))) )),
% 23.53/3.35    inference(forward_demodulation,[],[f22191,f16])).
% 23.53/3.35  fof(f22191,plain,(
% 23.53/3.35    ( ! [X35,X34] : (k4_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(k5_xboole_0(X34,k4_xboole_0(X35,X34)),X35))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X34,k4_xboole_0(X35,X34)),X35),k1_xboole_0)) )),
% 23.53/3.35    inference(superposition,[],[f28,f21879])).
% 23.53/3.35  fof(f21879,plain,(
% 23.53/3.35    ( ! [X88,X87] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X87,k4_xboole_0(X88,X87)),X88),X87)) )),
% 23.53/3.35    inference(superposition,[],[f21466,f524])).
% 23.53/3.35  fof(f524,plain,(
% 23.53/3.35    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) = X9) )),
% 23.53/3.35    inference(forward_demodulation,[],[f523,f210])).
% 23.53/3.35  fof(f523,plain,(
% 23.53/3.35    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) = k5_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9))) )),
% 23.53/3.35    inference(forward_demodulation,[],[f512,f16])).
% 23.53/3.35  fof(f512,plain,(
% 23.53/3.35    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) = k5_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(k4_xboole_0(X8,X9),k1_xboole_0))) )),
% 23.53/3.35    inference(superposition,[],[f295,f370])).
% 23.53/3.35  fof(f370,plain,(
% 23.53/3.35    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,X9),k5_xboole_0(X9,k4_xboole_0(X10,X9)))) )),
% 23.53/3.35    inference(forward_demodulation,[],[f365,f217])).
% 23.53/3.35  fof(f365,plain,(
% 23.53/3.35    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,X9),k5_xboole_0(k4_xboole_0(X10,X9),X9))) )),
% 23.53/3.35    inference(superposition,[],[f27,f322])).
% 23.53/3.35  fof(f322,plain,(
% 23.53/3.35    ( ! [X6,X5] : (k4_xboole_0(X5,k4_xboole_0(X6,X5)) = X5) )),
% 23.53/3.35    inference(superposition,[],[f36,f25])).
% 23.53/3.35  fof(f36,plain,(
% 23.53/3.35    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0) )),
% 23.53/3.35    inference(backward_demodulation,[],[f29,f30])).
% 23.53/3.35  fof(f29,plain,(
% 23.53/3.35    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0) )),
% 23.53/3.35    inference(definition_unfolding,[],[f19,f20,f21])).
% 23.53/3.35  fof(f19,plain,(
% 23.53/3.35    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 23.53/3.35    inference(cnf_transformation,[],[f3])).
% 23.53/3.35  fof(f3,axiom,(
% 23.53/3.35    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 23.53/3.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 23.53/3.35  fof(f21466,plain,(
% 23.53/3.35    ( ! [X6,X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,k4_xboole_0(X5,X6)))) )),
% 23.53/3.35    inference(superposition,[],[f21176,f1988])).
% 23.53/3.35  fof(f1988,plain,(
% 23.53/3.35    ( ! [X14,X15,X16] : (k4_xboole_0(X15,X14) = k4_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X14,X16))) )),
% 23.53/3.35    inference(superposition,[],[f1941,f322])).
% 23.53/3.35  fof(f1941,plain,(
% 23.53/3.35    ( ! [X21,X22,X20] : (k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X20,X21),X22)) = X21) )),
% 23.53/3.35    inference(forward_demodulation,[],[f1878,f16])).
% 23.53/3.35  fof(f1878,plain,(
% 23.53/3.35    ( ! [X21,X22,X20] : (k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(k4_xboole_0(X20,X21),X22),k1_xboole_0)) = X21) )),
% 23.53/3.35    inference(superposition,[],[f1666,f427])).
% 23.53/3.35  fof(f1666,plain,(
% 23.53/3.35    ( ! [X33,X31,X32] : (k4_xboole_0(X33,k4_xboole_0(X31,k4_xboole_0(X31,k4_xboole_0(X32,X33)))) = X33) )),
% 23.53/3.35    inference(superposition,[],[f322,f30])).
% 23.53/3.35  fof(f21176,plain,(
% 23.53/3.35    ( ! [X12,X10,X11] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),k4_xboole_0(X10,X12))) )),
% 23.53/3.35    inference(superposition,[],[f20829,f230])).
% 23.53/3.35  fof(f230,plain,(
% 23.53/3.35    ( ! [X6,X7] : (k5_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,k4_xboole_0(X6,X7))) = X6) )),
% 23.53/3.35    inference(superposition,[],[f210,f25])).
% 23.53/3.35  fof(f20829,plain,(
% 23.53/3.35    ( ! [X45,X43,X44] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X43,X45),k4_xboole_0(k5_xboole_0(X43,k4_xboole_0(X44,X43)),X45))) )),
% 23.53/3.35    inference(superposition,[],[f430,f1703])).
% 23.53/3.35  fof(f18761,plain,(
% 23.53/3.35    ( ! [X70,X71] : (k4_xboole_0(k5_xboole_0(X71,k4_xboole_0(X70,X71)),X70) = k5_xboole_0(X70,k5_xboole_0(X71,k4_xboole_0(X70,X71)))) )),
% 23.53/3.35    inference(forward_demodulation,[],[f18675,f16])).
% 23.53/3.35  fof(f18675,plain,(
% 23.53/3.35    ( ! [X70,X71] : (k4_xboole_0(k5_xboole_0(X71,k4_xboole_0(X70,X71)),X70) = k5_xboole_0(k4_xboole_0(X70,k1_xboole_0),k5_xboole_0(X71,k4_xboole_0(X70,X71)))) )),
% 23.53/3.35    inference(superposition,[],[f924,f18383])).
% 23.53/3.35  fof(f18383,plain,(
% 23.53/3.35    ( ! [X78,X79] : (k1_xboole_0 = k4_xboole_0(X79,k5_xboole_0(X78,k4_xboole_0(X79,X78)))) )),
% 23.53/3.35    inference(superposition,[],[f13034,f211])).
% 23.53/3.35  fof(f13034,plain,(
% 23.53/3.35    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X3,X2),X2)))) )),
% 23.53/3.35    inference(forward_demodulation,[],[f13033,f217])).
% 23.53/3.35  fof(f13033,plain,(
% 23.53/3.35    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(k4_xboole_0(k5_xboole_0(X3,X2),X2),X2))) )),
% 23.53/3.35    inference(forward_demodulation,[],[f12819,f4370])).
% 23.53/3.35  fof(f4370,plain,(
% 23.53/3.35    ( ! [X80,X81,X79] : (k5_xboole_0(k4_xboole_0(k5_xboole_0(X79,X80),X81),X80) = k5_xboole_0(X79,k4_xboole_0(X81,k4_xboole_0(X81,k5_xboole_0(X79,X80))))) )),
% 23.53/3.35    inference(superposition,[],[f225,f408])).
% 23.53/3.35  fof(f225,plain,(
% 23.53/3.35    ( ! [X6,X4,X5] : (k5_xboole_0(X5,X6) = k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X4,X6)))) )),
% 23.53/3.35    inference(forward_demodulation,[],[f218,f23])).
% 23.53/3.35  fof(f218,plain,(
% 23.53/3.35    ( ! [X6,X4,X5] : (k5_xboole_0(X5,X6) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X5,X4),X6))) )),
% 23.53/3.35    inference(superposition,[],[f23,f199])).
% 23.53/3.35  fof(f12819,plain,(
% 23.53/3.35    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X3,X2)))))) )),
% 23.53/3.35    inference(superposition,[],[f43,f153])).
% 23.53/3.35  fof(f43,plain,(
% 23.53/3.35    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X0,X1)))))) )),
% 23.53/3.35    inference(superposition,[],[f27,f23])).
% 23.53/3.35  fof(f924,plain,(
% 23.53/3.35    ( ! [X26,X25] : (k4_xboole_0(X25,X26) = k5_xboole_0(k4_xboole_0(X26,k4_xboole_0(X26,X25)),X25)) )),
% 23.53/3.35    inference(superposition,[],[f211,f405])).
% 23.53/3.35  fof(f405,plain,(
% 23.53/3.35    ( ! [X6,X5] : (k4_xboole_0(X6,k4_xboole_0(X6,X5)) = k5_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 23.53/3.35    inference(superposition,[],[f152,f295])).
% 23.53/3.35  fof(f207,plain,(
% 23.53/3.35    ( ! [X2,X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) )),
% 23.53/3.35    inference(superposition,[],[f199,f23])).
% 23.53/3.35  fof(f2134,plain,(
% 23.53/3.35    ( ! [X52,X50,X51] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X50,X51),k5_xboole_0(k4_xboole_0(X51,X52),k4_xboole_0(X50,X51)))) )),
% 23.53/3.35    inference(superposition,[],[f370,f1988])).
% 23.53/3.35  fof(f24087,plain,(
% 23.53/3.35    ( ! [X107,X108] : (k4_xboole_0(k5_xboole_0(X107,X108),k4_xboole_0(X108,X107)) = k5_xboole_0(k4_xboole_0(X107,X108),k4_xboole_0(k4_xboole_0(X108,X107),k5_xboole_0(X107,X108)))) )),
% 23.53/3.35    inference(superposition,[],[f22520,f22520])).
% 23.53/3.35  fof(f22520,plain,(
% 23.53/3.35    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X1))) )),
% 23.53/3.35    inference(superposition,[],[f147,f22348])).
% 23.53/3.35  fof(f147,plain,(
% 23.53/3.35    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2) )),
% 23.53/3.35    inference(backward_demodulation,[],[f129,f146])).
% 23.53/3.35  fof(f129,plain,(
% 23.53/3.35    ( ! [X2,X0,X1] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2)))) )),
% 23.53/3.35    inference(superposition,[],[f56,f23])).
% 23.53/3.35  fof(f39545,plain,(
% 23.53/3.35    ( ! [X26,X27] : (k4_xboole_0(X26,k5_xboole_0(X26,X27)) = k5_xboole_0(X26,k4_xboole_0(k5_xboole_0(X26,X27),k4_xboole_0(X27,X26)))) )),
% 23.53/3.35    inference(superposition,[],[f295,f38943])).
% 23.53/3.35  fof(f38943,plain,(
% 23.53/3.35    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(X2,X1),X2)) )),
% 23.53/3.35    inference(superposition,[],[f38737,f217])).
% 23.53/3.35  fof(f38737,plain,(
% 23.53/3.35    ( ! [X66,X65] : (k4_xboole_0(X65,X66) = k4_xboole_0(k5_xboole_0(X65,X66),X66)) )),
% 23.53/3.35    inference(forward_demodulation,[],[f38736,f64])).
% 23.53/3.35  fof(f38736,plain,(
% 23.53/3.35    ( ! [X66,X65] : (k5_xboole_0(k4_xboole_0(X65,X66),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X65,X66),X66)) )),
% 23.53/3.35    inference(forward_demodulation,[],[f38735,f38297])).
% 23.53/3.35  fof(f38297,plain,(
% 23.53/3.35    ( ! [X116,X117] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X116,X117),k4_xboole_0(k5_xboole_0(X116,X117),X117))) )),
% 23.53/3.35    inference(superposition,[],[f35711,f210])).
% 23.53/3.35  fof(f35711,plain,(
% 23.53/3.35    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X2,X3),X3),k4_xboole_0(X2,X3))) )),
% 23.53/3.35    inference(superposition,[],[f21466,f24737])).
% 23.53/3.35  fof(f38735,plain,(
% 23.53/3.35    ( ! [X66,X65] : (k4_xboole_0(k5_xboole_0(X65,X66),X66) = k5_xboole_0(k4_xboole_0(X65,X66),k4_xboole_0(k4_xboole_0(X65,X66),k4_xboole_0(k5_xboole_0(X65,X66),X66)))) )),
% 23.53/3.35    inference(forward_demodulation,[],[f38428,f16])).
% 23.53/3.35  fof(f38428,plain,(
% 23.53/3.35    ( ! [X66,X65] : (k5_xboole_0(k4_xboole_0(X65,X66),k4_xboole_0(k4_xboole_0(X65,X66),k4_xboole_0(k5_xboole_0(X65,X66),X66))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X65,X66),X66),k1_xboole_0)) )),
% 23.53/3.35    inference(superposition,[],[f405,f35711])).
% 23.53/3.35  fof(f39621,plain,(
% 23.53/3.35    ( ! [X227,X226] : (k5_xboole_0(X226,X227) = k4_xboole_0(k5_xboole_0(X226,k4_xboole_0(X227,X226)),k4_xboole_0(X226,k5_xboole_0(X226,X227)))) )),
% 23.53/3.35    inference(superposition,[],[f23222,f38943])).
% 23.53/3.35  fof(f23222,plain,(
% 23.53/3.35    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X8,X9)),k4_xboole_0(X9,X8)) = X8) )),
% 23.53/3.35    inference(forward_demodulation,[],[f23022,f217])).
% 23.53/3.35  fof(f23022,plain,(
% 23.53/3.35    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(k4_xboole_0(X8,X9),X9),k4_xboole_0(X9,X8)) = X8) )),
% 23.53/3.35    inference(superposition,[],[f524,f22349])).
% 23.53/3.35  fof(f22349,plain,(
% 23.53/3.35    ( ! [X41,X40] : (k5_xboole_0(k4_xboole_0(X41,X40),X40) = k5_xboole_0(X41,k4_xboole_0(X40,X41))) )),
% 23.53/3.35    inference(backward_demodulation,[],[f18743,f22346])).
% 23.53/3.35  fof(f18743,plain,(
% 23.53/3.35    ( ! [X41,X40] : (k5_xboole_0(X41,k4_xboole_0(X40,X41)) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X41,k4_xboole_0(X40,X41)),X40),X40)) )),
% 23.53/3.35    inference(forward_demodulation,[],[f18662,f16])).
% 23.53/3.35  fof(f18662,plain,(
% 23.53/3.35    ( ! [X41,X40] : (k5_xboole_0(X41,k4_xboole_0(X40,X41)) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X41,k4_xboole_0(X40,X41)),X40),k4_xboole_0(X40,k1_xboole_0))) )),
% 23.53/3.35    inference(superposition,[],[f407,f18383])).
% 23.53/3.35  fof(f34,plain,(
% 23.53/3.35    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_1),
% 23.53/3.35    inference(avatar_component_clause,[],[f32])).
% 23.53/3.35  fof(f32,plain,(
% 23.53/3.35    spl2_1 <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 23.53/3.35    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 23.53/3.35  fof(f35,plain,(
% 23.53/3.35    ~spl2_1),
% 23.53/3.35    inference(avatar_split_clause,[],[f26,f32])).
% 23.53/3.35  fof(f26,plain,(
% 23.53/3.35    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 23.53/3.35    inference(definition_unfolding,[],[f15,f20,f21])).
% 23.53/3.35  fof(f15,plain,(
% 23.53/3.35    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 23.53/3.35    inference(cnf_transformation,[],[f14])).
% 23.53/3.35  fof(f14,plain,(
% 23.53/3.35    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 23.53/3.35    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 23.53/3.35  fof(f13,plain,(
% 23.53/3.35    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 23.53/3.35    introduced(choice_axiom,[])).
% 23.53/3.35  fof(f12,plain,(
% 23.53/3.35    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 23.53/3.35    inference(ennf_transformation,[],[f11])).
% 23.53/3.35  fof(f11,negated_conjecture,(
% 23.53/3.35    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 23.53/3.35    inference(negated_conjecture,[],[f10])).
% 23.53/3.35  fof(f10,conjecture,(
% 23.53/3.35    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 23.53/3.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 23.53/3.35  % SZS output end Proof for theBenchmark
% 23.53/3.35  % (1509)------------------------------
% 23.53/3.35  % (1509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.53/3.35  % (1509)Termination reason: Refutation
% 23.53/3.35  
% 23.53/3.35  % (1509)Memory used [KB]: 74455
% 23.53/3.35  % (1509)Time elapsed: 2.908 s
% 23.53/3.35  % (1509)------------------------------
% 23.53/3.35  % (1509)------------------------------
% 23.53/3.35  % (1498)Success in time 2.99 s
%------------------------------------------------------------------------------
