%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 618 expanded)
%              Number of leaves         :   13 ( 206 expanded)
%              Depth                    :   23
%              Number of atoms          :   80 ( 619 expanded)
%              Number of equality atoms :   79 ( 618 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f796,plain,(
    $false ),
    inference(subsumption_resolution,[],[f778,f126])).

fof(f126,plain,(
    ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k1_enumset1(X3,X5,X4) ),
    inference(superposition,[],[f54,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(forward_demodulation,[],[f43,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(superposition,[],[f42,f21])).

fof(f21,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(forward_demodulation,[],[f38,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(superposition,[],[f29,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

fof(f54,plain,(
    ! [X4,X2,X3] : k1_enumset1(X4,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_tarski(X3,X2)) ),
    inference(superposition,[],[f50,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f778,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1) ),
    inference(superposition,[],[f560,f619])).

fof(f619,plain,(
    ! [X14,X12,X13] : k1_enumset1(X12,X13,X14) = k1_enumset1(X13,X14,X12) ),
    inference(superposition,[],[f559,f306])).

fof(f306,plain,(
    ! [X30,X28,X29] : k2_enumset1(X30,X28,X29,X29) = k1_enumset1(X30,X28,X29) ),
    inference(forward_demodulation,[],[f300,f50])).

fof(f300,plain,(
    ! [X30,X28,X29] : k2_enumset1(X30,X28,X29,X29) = k2_xboole_0(k1_tarski(X30),k2_tarski(X28,X29)) ),
    inference(superposition,[],[f150,f267])).

fof(f267,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X1) ),
    inference(forward_demodulation,[],[f264,f128])).

fof(f128,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0) ),
    inference(superposition,[],[f126,f23])).

fof(f264,plain,(
    ! [X0,X1] : k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X1,X0) ),
    inference(superposition,[],[f252,f25])).

fof(f252,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X1,X2,X2) = k1_enumset1(X0,X2,X1) ),
    inference(forward_demodulation,[],[f243,f25])).

fof(f243,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X1,X2,X2) = k2_enumset1(X0,X0,X2,X1) ),
    inference(superposition,[],[f229,f26])).

fof(f229,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X1,X2,X3,X0,X0) = k2_enumset1(X1,X2,X0,X3) ),
    inference(backward_demodulation,[],[f39,f228])).

fof(f228,plain,(
    ! [X10,X8,X11,X9] : k2_xboole_0(k1_enumset1(X8,X9,X10),k1_tarski(X11)) = k2_enumset1(X8,X9,X11,X10) ),
    inference(forward_demodulation,[],[f222,f151])).

fof(f151,plain,(
    ! [X6,X8,X7,X5] : k4_enumset1(X5,X5,X5,X6,X7,X8) = k2_enumset1(X5,X6,X8,X7) ),
    inference(backward_demodulation,[],[f82,f148])).

fof(f148,plain,(
    ! [X23,X21,X22,X20] : k2_xboole_0(k1_tarski(X23),k1_enumset1(X20,X22,X21)) = k2_enumset1(X23,X20,X21,X22) ),
    inference(backward_demodulation,[],[f134,f147])).

fof(f147,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X5,X5,X6,X7) = k2_enumset1(X4,X5,X6,X7) ),
    inference(forward_demodulation,[],[f143,f146])).

fof(f146,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X2,X3) ),
    inference(forward_demodulation,[],[f142,f26])).

fof(f142,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X2,X3) ),
    inference(superposition,[],[f59,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X2,X3,X4,X0,X0,X1) = k3_enumset1(X2,X3,X4,X0,X1) ),
    inference(forward_demodulation,[],[f57,f29])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X2,X3,X4,X0,X0,X1) = k2_xboole_0(k1_enumset1(X2,X3,X4),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f32,f23])).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(f143,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X5,X6,X6,X7) = k3_enumset1(X4,X5,X5,X6,X7) ),
    inference(superposition,[],[f59,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X4,X0,X0,X1,X2,X3) = k3_enumset1(X4,X0,X1,X2,X3) ),
    inference(forward_demodulation,[],[f51,f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X4,X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f31,f26])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(f134,plain,(
    ! [X23,X21,X22,X20] : k3_enumset1(X23,X20,X20,X21,X22) = k2_xboole_0(k1_tarski(X23),k1_enumset1(X20,X22,X21)) ),
    inference(superposition,[],[f37,f126])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X3,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f28,f25])).

fof(f82,plain,(
    ! [X6,X8,X7,X5] : k4_enumset1(X5,X5,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X5),k1_enumset1(X6,X7,X8)) ),
    inference(superposition,[],[f32,f70])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(superposition,[],[f65,f53])).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X1,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) ),
    inference(superposition,[],[f50,f21])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(forward_demodulation,[],[f60,f21])).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(superposition,[],[f53,f23])).

fof(f222,plain,(
    ! [X10,X8,X11,X9] : k2_xboole_0(k1_enumset1(X8,X9,X10),k1_tarski(X11)) = k4_enumset1(X8,X8,X8,X9,X10,X11) ),
    inference(superposition,[],[f33,f85])).

fof(f85,plain,(
    ! [X10,X11,X9] : k3_enumset1(X9,X9,X9,X10,X11) = k1_enumset1(X9,X10,X11) ),
    inference(forward_demodulation,[],[f83,f50])).

fof(f83,plain,(
    ! [X10,X11,X9] : k3_enumset1(X9,X9,X9,X10,X11) = k2_xboole_0(k1_tarski(X9),k2_tarski(X10,X11)) ),
    inference(superposition,[],[f29,f70])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X1,X2,X3,X0,X0) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)) ),
    inference(superposition,[],[f29,f21])).

fof(f150,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) = k2_enumset1(X3,X0,X1,X2) ),
    inference(backward_demodulation,[],[f37,f147])).

fof(f559,plain,(
    ! [X2,X0,X1] : k2_enumset1(X1,X2,X0,X0) = k1_enumset1(X2,X0,X1) ),
    inference(forward_demodulation,[],[f552,f254])).

fof(f254,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) = k1_enumset1(X1,X0,X2) ),
    inference(backward_demodulation,[],[f46,f252])).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) ),
    inference(superposition,[],[f42,f21])).

% (25841)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f552,plain,(
    ! [X2,X0,X1] : k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X2,X1),k1_tarski(X0)) ),
    inference(superposition,[],[f44,f21])).

fof(f44,plain,(
    ! [X6,X4,X5,X3] : k2_enumset1(X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X4,X3),k2_tarski(X5,X6)) ),
    inference(superposition,[],[f42,f22])).

fof(f560,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    inference(superposition,[],[f556,f183])).

fof(f183,plain,(
    ! [X2,X0,X1] : k1_enumset1(X2,X0,X1) = k2_enumset1(X2,X0,X0,X1) ),
    inference(forward_demodulation,[],[f177,f50])).

fof(f177,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)) = k2_enumset1(X2,X0,X0,X1) ),
    inference(superposition,[],[f150,f23])).

fof(f556,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK0,sK2) ),
    inference(superposition,[],[f36,f44])).

fof(f36,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2)) ),
    inference(forward_demodulation,[],[f35,f22])).

fof(f35,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK2)) ),
    inference(backward_demodulation,[],[f20,f22])).

fof(f20,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:54:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (25840)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (25839)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (25837)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (25848)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (25838)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (25848)Refutation not found, incomplete strategy% (25848)------------------------------
% 0.21/0.50  % (25848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (25848)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (25848)Memory used [KB]: 10618
% 0.21/0.50  % (25848)Time elapsed: 0.065 s
% 0.21/0.50  % (25848)------------------------------
% 0.21/0.50  % (25848)------------------------------
% 0.21/0.50  % (25840)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f796,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f778,f126])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k1_enumset1(X3,X5,X4)) )),
% 0.21/0.50    inference(superposition,[],[f54,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f43,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.21/0.50    inference(superposition,[],[f42,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f38,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.21/0.50    inference(superposition,[],[f29,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X4,X2,X3] : (k1_enumset1(X4,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_tarski(X3,X2))) )),
% 0.21/0.50    inference(superposition,[],[f50,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.50  fof(f778,plain,(
% 0.21/0.50    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1)),
% 0.21/0.50    inference(superposition,[],[f560,f619])).
% 0.21/0.50  fof(f619,plain,(
% 0.21/0.50    ( ! [X14,X12,X13] : (k1_enumset1(X12,X13,X14) = k1_enumset1(X13,X14,X12)) )),
% 0.21/0.50    inference(superposition,[],[f559,f306])).
% 0.21/0.50  fof(f306,plain,(
% 0.21/0.50    ( ! [X30,X28,X29] : (k2_enumset1(X30,X28,X29,X29) = k1_enumset1(X30,X28,X29)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f300,f50])).
% 0.21/0.50  fof(f300,plain,(
% 0.21/0.50    ( ! [X30,X28,X29] : (k2_enumset1(X30,X28,X29,X29) = k2_xboole_0(k1_tarski(X30),k2_tarski(X28,X29))) )),
% 0.21/0.50    inference(superposition,[],[f150,f267])).
% 0.21/0.50  fof(f267,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X1)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f264,f128])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)) )),
% 0.21/0.50    inference(superposition,[],[f126,f23])).
% 0.21/0.50  fof(f264,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X1,X0)) )),
% 0.21/0.50    inference(superposition,[],[f252,f25])).
% 0.21/0.50  fof(f252,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X1,X2,X2) = k1_enumset1(X0,X2,X1)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f243,f25])).
% 0.21/0.50  fof(f243,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X1,X2,X2) = k2_enumset1(X0,X0,X2,X1)) )),
% 0.21/0.50    inference(superposition,[],[f229,f26])).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X1,X2,X3,X0,X0) = k2_enumset1(X1,X2,X0,X3)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f39,f228])).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    ( ! [X10,X8,X11,X9] : (k2_xboole_0(k1_enumset1(X8,X9,X10),k1_tarski(X11)) = k2_enumset1(X8,X9,X11,X10)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f222,f151])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    ( ! [X6,X8,X7,X5] : (k4_enumset1(X5,X5,X5,X6,X7,X8) = k2_enumset1(X5,X6,X8,X7)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f82,f148])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    ( ! [X23,X21,X22,X20] : (k2_xboole_0(k1_tarski(X23),k1_enumset1(X20,X22,X21)) = k2_enumset1(X23,X20,X21,X22)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f134,f147])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X5,X5,X6,X7) = k2_enumset1(X4,X5,X6,X7)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f143,f146])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X2,X3)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f142,f26])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X2,X3)) )),
% 0.21/0.50    inference(superposition,[],[f59,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X2,X3,X4,X0,X0,X1) = k3_enumset1(X2,X3,X4,X0,X1)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f57,f29])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X2,X3,X4,X0,X0,X1) = k2_xboole_0(k1_enumset1(X2,X3,X4),k2_tarski(X0,X1))) )),
% 0.21/0.50    inference(superposition,[],[f32,f23])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X5,X6,X6,X7) = k3_enumset1(X4,X5,X5,X6,X7)) )),
% 0.21/0.50    inference(superposition,[],[f59,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X4,X0,X0,X1,X2,X3) = k3_enumset1(X4,X0,X1,X2,X3)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f51,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X4,X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3))) )),
% 0.21/0.50    inference(superposition,[],[f31,f26])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    ( ! [X23,X21,X22,X20] : (k3_enumset1(X23,X20,X20,X21,X22) = k2_xboole_0(k1_tarski(X23),k1_enumset1(X20,X22,X21))) )),
% 0.21/0.50    inference(superposition,[],[f37,f126])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X3,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))) )),
% 0.21/0.50    inference(superposition,[],[f28,f25])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X6,X8,X7,X5] : (k4_enumset1(X5,X5,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X5),k1_enumset1(X6,X7,X8))) )),
% 0.21/0.50    inference(superposition,[],[f32,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.50    inference(superposition,[],[f65,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_enumset1(X1,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) )),
% 0.21/0.50    inference(superposition,[],[f50,f21])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f60,f21])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 0.21/0.50    inference(superposition,[],[f53,f23])).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    ( ! [X10,X8,X11,X9] : (k2_xboole_0(k1_enumset1(X8,X9,X10),k1_tarski(X11)) = k4_enumset1(X8,X8,X8,X9,X10,X11)) )),
% 0.21/0.50    inference(superposition,[],[f33,f85])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X10,X11,X9] : (k3_enumset1(X9,X9,X9,X10,X11) = k1_enumset1(X9,X10,X11)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f83,f50])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X10,X11,X9] : (k3_enumset1(X9,X9,X9,X10,X11) = k2_xboole_0(k1_tarski(X9),k2_tarski(X10,X11))) )),
% 0.21/0.50    inference(superposition,[],[f29,f70])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X1,X2,X3,X0,X0) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0))) )),
% 0.21/0.50    inference(superposition,[],[f29,f21])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) = k2_enumset1(X3,X0,X1,X2)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f37,f147])).
% 0.21/0.50  fof(f559,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X1,X2,X0,X0) = k1_enumset1(X2,X0,X1)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f552,f254])).
% 0.21/0.50  fof(f254,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) = k1_enumset1(X1,X0,X2)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f46,f252])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))) )),
% 0.21/0.50    inference(superposition,[],[f42,f21])).
% 0.21/0.50  % (25841)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  fof(f552,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X2,X1),k1_tarski(X0))) )),
% 0.21/0.50    inference(superposition,[],[f44,f21])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X6,X4,X5,X3] : (k2_enumset1(X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X4,X3),k2_tarski(X5,X6))) )),
% 0.21/0.50    inference(superposition,[],[f42,f22])).
% 0.21/0.50  fof(f560,plain,(
% 0.21/0.50    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 0.21/0.50    inference(superposition,[],[f556,f183])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X2,X0,X1) = k2_enumset1(X2,X0,X0,X1)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f177,f50])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)) = k2_enumset1(X2,X0,X0,X1)) )),
% 0.21/0.50    inference(superposition,[],[f150,f23])).
% 0.21/0.50  fof(f556,plain,(
% 0.21/0.50    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK0,sK2)),
% 0.21/0.50    inference(superposition,[],[f36,f44])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2))),
% 0.21/0.50    inference(forward_demodulation,[],[f35,f22])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK2))),
% 0.21/0.50    inference(backward_demodulation,[],[f20,f22])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.21/0.50    inference(negated_conjecture,[],[f15])).
% 0.21/0.50  fof(f15,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (25840)------------------------------
% 0.21/0.50  % (25840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (25840)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (25840)Memory used [KB]: 2302
% 0.21/0.50  % (25840)Time elapsed: 0.066 s
% 0.21/0.50  % (25840)------------------------------
% 0.21/0.50  % (25840)------------------------------
% 0.21/0.51  % (25836)Success in time 0.145 s
%------------------------------------------------------------------------------
