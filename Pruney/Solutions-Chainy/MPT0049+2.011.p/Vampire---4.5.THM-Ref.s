%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:54 EST 2020

% Result     : Theorem 38.05s
% Output     : Refutation 38.05s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 778 expanded)
%              Number of leaves         :   12 ( 256 expanded)
%              Depth                    :   29
%              Number of atoms          :  112 ( 820 expanded)
%              Number of equality atoms :   94 ( 740 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134149,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f50,f133821])).

fof(f133821,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f133794])).

fof(f133794,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f27,f133793])).

fof(f133793,plain,(
    ! [X57,X56,X55] : k4_xboole_0(k2_xboole_0(X55,X57),X56) = k2_xboole_0(k4_xboole_0(X55,X56),k4_xboole_0(X57,X56)) ),
    inference(backward_demodulation,[],[f75825,f133383])).

fof(f133383,plain,(
    ! [X90,X91,X89] : k4_xboole_0(k2_xboole_0(X90,X91),X89) = k2_xboole_0(k4_xboole_0(X90,X89),k4_xboole_0(k2_xboole_0(X90,X91),X89)) ),
    inference(superposition,[],[f61536,f130307])).

fof(f130307,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(k2_xboole_0(X3,X2),X4))) = X4 ),
    inference(superposition,[],[f129903,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f129903,plain,(
    ! [X586,X585,X587] : k2_xboole_0(X587,k4_xboole_0(X585,k4_xboole_0(k2_xboole_0(X586,X585),X587))) = X587 ),
    inference(backward_demodulation,[],[f108365,f129399])).

fof(f129399,plain,(
    ! [X130,X128,X129] : k4_xboole_0(X128,k4_xboole_0(k2_xboole_0(X129,X128),X130)) = k4_xboole_0(k2_xboole_0(X128,k4_xboole_0(X129,X130)),k4_xboole_0(k2_xboole_0(X129,X128),X130)) ),
    inference(superposition,[],[f19,f58654])).

fof(f58654,plain,(
    ! [X30,X28,X29] : k2_xboole_0(X29,k4_xboole_0(k2_xboole_0(X28,X29),X30)) = k2_xboole_0(X29,k4_xboole_0(X28,X30)) ),
    inference(forward_demodulation,[],[f58317,f32910])).

fof(f32910,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X3,k4_xboole_0(X4,X2)) = k2_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2))) ),
    inference(superposition,[],[f1314,f18])).

fof(f1314,plain,(
    ! [X14,X15,X13] : k2_xboole_0(X15,k4_xboole_0(X13,X14)) = k2_xboole_0(X15,k4_xboole_0(X13,k2_xboole_0(X14,X15))) ),
    inference(superposition,[],[f20,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f58317,plain,(
    ! [X30,X28,X29] : k2_xboole_0(X29,k4_xboole_0(k2_xboole_0(X28,X29),X30)) = k2_xboole_0(X29,k4_xboole_0(X28,k2_xboole_0(X29,X30))) ),
    inference(superposition,[],[f32910,f1339])).

fof(f1339,plain,(
    ! [X14,X15,X13] : k4_xboole_0(k2_xboole_0(X13,X14),k2_xboole_0(X14,X15)) = k4_xboole_0(X13,k2_xboole_0(X14,X15)) ),
    inference(forward_demodulation,[],[f1291,f22])).

fof(f1291,plain,(
    ! [X14,X15,X13] : k4_xboole_0(k2_xboole_0(X13,X14),k2_xboole_0(X14,X15)) = k4_xboole_0(k4_xboole_0(X13,X14),X15) ),
    inference(superposition,[],[f22,f19])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f108365,plain,(
    ! [X586,X585,X587] : k2_xboole_0(X587,k4_xboole_0(k2_xboole_0(X585,k4_xboole_0(X586,X587)),k4_xboole_0(k2_xboole_0(X586,X585),X587))) = X587 ),
    inference(superposition,[],[f60288,f45118])).

fof(f45118,plain,(
    ! [X196,X194,X195] : k4_xboole_0(k2_xboole_0(X196,k4_xboole_0(X194,X195)),X195) = k4_xboole_0(k2_xboole_0(X194,X196),X195) ),
    inference(forward_demodulation,[],[f44863,f2398])).

fof(f2398,plain,(
    ! [X30,X31,X29] : k4_xboole_0(k2_xboole_0(X30,X31),X29) = k4_xboole_0(k2_xboole_0(X31,k2_xboole_0(X29,X30)),X29) ),
    inference(superposition,[],[f55,f2001])).

fof(f2001,plain,(
    ! [X17,X15,X16] : k2_xboole_0(X17,k2_xboole_0(X15,X16)) = k2_xboole_0(X15,k2_xboole_0(X16,X17)) ),
    inference(superposition,[],[f23,f18])).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f55,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f19,f18])).

fof(f44863,plain,(
    ! [X196,X194,X195] : k4_xboole_0(k2_xboole_0(X196,k4_xboole_0(X194,X195)),X195) = k4_xboole_0(k2_xboole_0(X196,k2_xboole_0(X195,X194)),X195) ),
    inference(superposition,[],[f2019,f175])).

fof(f175,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k2_xboole_0(k4_xboole_0(X11,X10),X10) ),
    inference(forward_demodulation,[],[f164,f89])).

fof(f89,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) ),
    inference(resolution,[],[f73,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f73,plain,(
    ! [X2,X1] : r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f61,f18])).

fof(f61,plain,(
    ! [X4,X5] : r1_tarski(k4_xboole_0(X4,X5),k2_xboole_0(X4,X5)) ),
    inference(superposition,[],[f17,f19])).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f164,plain,(
    ! [X10,X11] : k2_xboole_0(k4_xboole_0(X11,X10),X10) = k2_xboole_0(k4_xboole_0(X11,X10),k2_xboole_0(X10,X11)) ),
    inference(superposition,[],[f113,f20])).

fof(f113,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X2,k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f103,f20])).

fof(f103,plain,(
    ! [X2,X1] : k2_xboole_0(X2,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f20,f19])).

fof(f2019,plain,(
    ! [X19,X20,X18] : k4_xboole_0(k2_xboole_0(X18,X19),X20) = k4_xboole_0(k2_xboole_0(X18,k2_xboole_0(X19,X20)),X20) ),
    inference(superposition,[],[f19,f23])).

fof(f60288,plain,(
    ! [X35,X36] : k2_xboole_0(X35,k4_xboole_0(X36,k4_xboole_0(X36,X35))) = X35 ),
    inference(forward_demodulation,[],[f60287,f39])).

fof(f39,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3 ),
    inference(superposition,[],[f37,f18])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f21,f17])).

fof(f60287,plain,(
    ! [X35,X36] : k2_xboole_0(X35,k4_xboole_0(X35,X36)) = k2_xboole_0(X35,k4_xboole_0(X36,k4_xboole_0(X36,X35))) ),
    inference(forward_demodulation,[],[f59939,f33241])).

fof(f33241,plain,(
    ! [X189,X187,X188] : k2_xboole_0(X188,k4_xboole_0(X189,k4_xboole_0(X187,X188))) = k2_xboole_0(X188,k4_xboole_0(X189,X187)) ),
    inference(forward_demodulation,[],[f32954,f1314])).

fof(f32954,plain,(
    ! [X189,X187,X188] : k2_xboole_0(X188,k4_xboole_0(X189,k4_xboole_0(X187,X188))) = k2_xboole_0(X188,k4_xboole_0(X189,k2_xboole_0(X187,X188))) ),
    inference(superposition,[],[f1314,f1185])).

fof(f1185,plain,(
    ! [X19,X20] : k2_xboole_0(X20,X19) = k2_xboole_0(k4_xboole_0(X20,X19),X19) ),
    inference(forward_demodulation,[],[f1148,f60])).

fof(f60,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X2,X3),k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f37,f19])).

fof(f1148,plain,(
    ! [X19,X20] : k2_xboole_0(k4_xboole_0(X20,X19),X19) = k2_xboole_0(k4_xboole_0(X20,X19),k2_xboole_0(X20,X19)) ),
    inference(superposition,[],[f113,f828])).

fof(f828,plain,(
    ! [X26,X25] : k2_xboole_0(X26,k4_xboole_0(X25,X26)) = k2_xboole_0(X25,X26) ),
    inference(forward_demodulation,[],[f797,f705])).

fof(f705,plain,(
    ! [X8,X7] : k2_xboole_0(X8,X7) = k4_xboole_0(k2_xboole_0(X7,X8),k1_xboole_0) ),
    inference(forward_demodulation,[],[f678,f116])).

fof(f116,plain,(
    ! [X7] : k4_xboole_0(X7,k1_xboole_0) = X7 ),
    inference(forward_demodulation,[],[f106,f29])).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f18,f16])).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f106,plain,(
    ! [X7] : k2_xboole_0(k1_xboole_0,X7) = k4_xboole_0(X7,k1_xboole_0) ),
    inference(superposition,[],[f20,f29])).

fof(f678,plain,(
    ! [X8,X7] : k4_xboole_0(k2_xboole_0(X7,X8),k1_xboole_0) = k4_xboole_0(k2_xboole_0(X8,X7),k1_xboole_0) ),
    inference(superposition,[],[f19,f427])).

fof(f427,plain,(
    ! [X4,X3] : k2_xboole_0(X3,X4) = k2_xboole_0(k2_xboole_0(X4,X3),k1_xboole_0) ),
    inference(forward_demodulation,[],[f401,f174])).

fof(f174,plain,(
    ! [X6,X5] : k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f173,f113])).

fof(f173,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X5)) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f163,f18])).

fof(f163,plain,(
    ! [X6,X5] : k2_xboole_0(k2_xboole_0(X6,X5),X5) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f113,f113])).

fof(f401,plain,(
    ! [X4,X3] : k2_xboole_0(k2_xboole_0(X4,X3),k1_xboole_0) = k2_xboole_0(k2_xboole_0(X4,X3),k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f20,f264])).

fof(f264,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X4)) ),
    inference(backward_demodulation,[],[f168,f245])).

fof(f245,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f240,f18])).

fof(f240,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f235,f62])).

fof(f62,plain,(
    ! [X7] : k1_xboole_0 = k4_xboole_0(X7,X7) ),
    inference(forward_demodulation,[],[f57,f38])).

fof(f38,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f37,f16])).

fof(f57,plain,(
    ! [X7] : k4_xboole_0(k1_xboole_0,X7) = k4_xboole_0(X7,X7) ),
    inference(superposition,[],[f19,f29])).

fof(f235,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f19,f155])).

fof(f155,plain,(
    ! [X4,X3] : k2_xboole_0(X3,X4) = k2_xboole_0(X3,k2_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f144,f20])).

fof(f144,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(X4,X3)) = k2_xboole_0(X3,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f20,f55])).

fof(f168,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k2_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X4)) ),
    inference(superposition,[],[f19,f113])).

fof(f797,plain,(
    ! [X26,X25] : k2_xboole_0(X26,k4_xboole_0(X25,X26)) = k4_xboole_0(k2_xboole_0(X26,X25),k1_xboole_0) ),
    inference(superposition,[],[f705,f175])).

fof(f59939,plain,(
    ! [X35,X36] : k2_xboole_0(X35,k4_xboole_0(X36,k4_xboole_0(X36,X35))) = k2_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X36,X35))) ),
    inference(superposition,[],[f33287,f110])).

fof(f110,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k4_xboole_0(X6,X5)) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5)) ),
    inference(superposition,[],[f19,f20])).

fof(f33287,plain,(
    ! [X39,X37,X38] : k2_xboole_0(X38,k4_xboole_0(X39,X37)) = k2_xboole_0(X38,k4_xboole_0(k2_xboole_0(X38,X39),X37)) ),
    inference(forward_demodulation,[],[f33286,f55])).

fof(f33286,plain,(
    ! [X39,X37,X38] : k2_xboole_0(X38,k4_xboole_0(X39,X37)) = k2_xboole_0(X38,k4_xboole_0(k2_xboole_0(X37,k2_xboole_0(X38,X39)),X37)) ),
    inference(forward_demodulation,[],[f33285,f23])).

fof(f33285,plain,(
    ! [X39,X37,X38] : k2_xboole_0(X38,k4_xboole_0(k2_xboole_0(k2_xboole_0(X37,X38),X39),X37)) = k2_xboole_0(X38,k4_xboole_0(X39,X37)) ),
    inference(forward_demodulation,[],[f32975,f1314])).

fof(f32975,plain,(
    ! [X39,X37,X38] : k2_xboole_0(X38,k4_xboole_0(k2_xboole_0(k2_xboole_0(X37,X38),X39),X37)) = k2_xboole_0(X38,k4_xboole_0(X39,k2_xboole_0(X37,X38))) ),
    inference(superposition,[],[f1314,f55])).

fof(f61536,plain,(
    ! [X94,X92,X93] : k2_xboole_0(k4_xboole_0(X92,k2_xboole_0(X93,k4_xboole_0(X92,X94))),X94) = X94 ),
    inference(forward_demodulation,[],[f61535,f32910])).

fof(f61535,plain,(
    ! [X94,X92,X93] : k2_xboole_0(k4_xboole_0(X92,k2_xboole_0(X93,k4_xboole_0(X92,k2_xboole_0(X93,X94)))),X94) = X94 ),
    inference(forward_demodulation,[],[f61208,f22])).

fof(f61208,plain,(
    ! [X94,X92,X93] : k2_xboole_0(k4_xboole_0(k4_xboole_0(X92,X93),k4_xboole_0(X92,k2_xboole_0(X93,X94))),X94) = X94 ),
    inference(superposition,[],[f60698,f22])).

fof(f60698,plain,(
    ! [X70,X71] : k2_xboole_0(k4_xboole_0(X71,k4_xboole_0(X71,X70)),X70) = X70 ),
    inference(superposition,[],[f226,f60288])).

fof(f226,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f155,f18])).

fof(f75825,plain,(
    ! [X57,X56,X55] : k2_xboole_0(k4_xboole_0(X55,X56),k4_xboole_0(X57,X56)) = k2_xboole_0(k4_xboole_0(X55,X56),k4_xboole_0(k2_xboole_0(X55,X57),X56)) ),
    inference(superposition,[],[f33287,f45981])).

fof(f45981,plain,(
    ! [X198,X196,X197] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X197,X196),X198),X196) = k4_xboole_0(k2_xboole_0(X197,X198),X196) ),
    inference(forward_demodulation,[],[f45579,f55])).

fof(f45579,plain,(
    ! [X198,X196,X197] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X197,X196),X198),X196) = k4_xboole_0(k2_xboole_0(X196,k2_xboole_0(X197,X198)),X196) ),
    inference(superposition,[],[f55,f2068])).

fof(f2068,plain,(
    ! [X30,X28,X29] : k2_xboole_0(X28,k2_xboole_0(k4_xboole_0(X29,X28),X30)) = k2_xboole_0(X28,k2_xboole_0(X29,X30)) ),
    inference(forward_demodulation,[],[f1983,f23])).

fof(f1983,plain,(
    ! [X30,X28,X29] : k2_xboole_0(X28,k2_xboole_0(k4_xboole_0(X29,X28),X30)) = k2_xboole_0(k2_xboole_0(X28,X29),X30) ),
    inference(superposition,[],[f23,f20])).

fof(f27,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl3_1
  <=> k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f50,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f45,f47])).

fof(f47,plain,
    ( spl3_2
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f45,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f17,f38])).

fof(f28,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f15,f25])).

fof(f15,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
   => k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n020.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 18:27:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  ipcrm: permission denied for id (814350336)
% 0.15/0.37  ipcrm: permission denied for id (814383106)
% 0.22/0.38  ipcrm: permission denied for id (814448649)
% 0.22/0.38  ipcrm: permission denied for id (814481419)
% 0.22/0.38  ipcrm: permission denied for id (814514188)
% 0.22/0.38  ipcrm: permission denied for id (814546957)
% 0.22/0.38  ipcrm: permission denied for id (814612496)
% 0.22/0.39  ipcrm: permission denied for id (814645266)
% 0.22/0.39  ipcrm: permission denied for id (814678035)
% 0.22/0.40  ipcrm: permission denied for id (814809113)
% 0.22/0.40  ipcrm: permission denied for id (814874651)
% 0.22/0.40  ipcrm: permission denied for id (815005728)
% 0.22/0.40  ipcrm: permission denied for id (815038497)
% 0.22/0.42  ipcrm: permission denied for id (815202346)
% 0.22/0.42  ipcrm: permission denied for id (815235116)
% 0.22/0.42  ipcrm: permission denied for id (815300655)
% 0.22/0.43  ipcrm: permission denied for id (815366196)
% 0.22/0.44  ipcrm: permission denied for id (815497277)
% 0.22/0.44  ipcrm: permission denied for id (815530046)
% 0.22/0.44  ipcrm: permission denied for id (815562816)
% 0.22/0.44  ipcrm: permission denied for id (815595585)
% 0.22/0.45  ipcrm: permission denied for id (815661127)
% 0.22/0.45  ipcrm: permission denied for id (815726665)
% 0.22/0.46  ipcrm: permission denied for id (815759434)
% 0.22/0.46  ipcrm: permission denied for id (815824973)
% 0.22/0.47  ipcrm: permission denied for id (815890514)
% 0.22/0.48  ipcrm: permission denied for id (815988826)
% 0.22/0.48  ipcrm: permission denied for id (816087133)
% 0.22/0.48  ipcrm: permission denied for id (816119904)
% 0.22/0.49  ipcrm: permission denied for id (816349289)
% 0.22/0.50  ipcrm: permission denied for id (816382058)
% 0.22/0.51  ipcrm: permission denied for id (816480370)
% 0.22/0.51  ipcrm: permission denied for id (816513140)
% 0.22/0.52  ipcrm: permission denied for id (816611449)
% 0.22/0.52  ipcrm: permission denied for id (816644218)
% 0.22/0.52  ipcrm: permission denied for id (816676987)
% 0.22/0.52  ipcrm: permission denied for id (816775293)
% 0.22/0.52  ipcrm: permission denied for id (816808062)
% 0.22/0.52  ipcrm: permission denied for id (816840831)
% 0.39/0.59  % (26284)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.39/0.59  % (26290)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.39/0.59  % (26288)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.39/0.59  % (26283)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.39/0.61  % (26293)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.39/0.61  % (26294)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.39/0.61  % (26285)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.39/0.61  % (26287)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.39/0.62  % (26295)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.39/0.62  % (26291)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.39/0.62  % (26292)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.39/0.63  % (26286)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 5.42/1.19  % (26284)Time limit reached!
% 5.42/1.19  % (26284)------------------------------
% 5.42/1.19  % (26284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.42/1.19  % (26284)Termination reason: Time limit
% 5.42/1.19  
% 5.42/1.19  % (26284)Memory used [KB]: 28912
% 5.42/1.19  % (26284)Time elapsed: 0.621 s
% 5.42/1.19  % (26284)------------------------------
% 5.42/1.19  % (26284)------------------------------
% 8.55/1.60  % (26283)Time limit reached!
% 8.55/1.60  % (26283)------------------------------
% 8.55/1.60  % (26283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.55/1.61  % (26283)Termination reason: Time limit
% 8.55/1.61  % (26283)Termination phase: Saturation
% 8.55/1.61  
% 8.55/1.61  % (26283)Memory used [KB]: 44903
% 8.55/1.61  % (26283)Time elapsed: 1.0000 s
% 8.55/1.61  % (26283)------------------------------
% 8.55/1.61  % (26283)------------------------------
% 38.05/5.32  % (26291)Refutation found. Thanks to Tanya!
% 38.05/5.32  % SZS status Theorem for theBenchmark
% 38.05/5.32  % SZS output start Proof for theBenchmark
% 38.05/5.32  fof(f134149,plain,(
% 38.05/5.32    $false),
% 38.05/5.32    inference(avatar_sat_refutation,[],[f28,f50,f133821])).
% 38.05/5.32  fof(f133821,plain,(
% 38.05/5.32    spl3_1),
% 38.05/5.32    inference(avatar_contradiction_clause,[],[f133794])).
% 38.05/5.32  fof(f133794,plain,(
% 38.05/5.32    $false | spl3_1),
% 38.05/5.32    inference(subsumption_resolution,[],[f27,f133793])).
% 38.05/5.32  fof(f133793,plain,(
% 38.05/5.32    ( ! [X57,X56,X55] : (k4_xboole_0(k2_xboole_0(X55,X57),X56) = k2_xboole_0(k4_xboole_0(X55,X56),k4_xboole_0(X57,X56))) )),
% 38.05/5.32    inference(backward_demodulation,[],[f75825,f133383])).
% 38.05/5.32  fof(f133383,plain,(
% 38.05/5.32    ( ! [X90,X91,X89] : (k4_xboole_0(k2_xboole_0(X90,X91),X89) = k2_xboole_0(k4_xboole_0(X90,X89),k4_xboole_0(k2_xboole_0(X90,X91),X89))) )),
% 38.05/5.32    inference(superposition,[],[f61536,f130307])).
% 38.05/5.32  fof(f130307,plain,(
% 38.05/5.32    ( ! [X4,X2,X3] : (k2_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(k2_xboole_0(X3,X2),X4))) = X4) )),
% 38.05/5.32    inference(superposition,[],[f129903,f18])).
% 38.05/5.32  fof(f18,plain,(
% 38.05/5.32    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 38.05/5.32    inference(cnf_transformation,[],[f1])).
% 38.05/5.32  fof(f1,axiom,(
% 38.05/5.32    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 38.05/5.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 38.05/5.32  fof(f129903,plain,(
% 38.05/5.32    ( ! [X586,X585,X587] : (k2_xboole_0(X587,k4_xboole_0(X585,k4_xboole_0(k2_xboole_0(X586,X585),X587))) = X587) )),
% 38.05/5.32    inference(backward_demodulation,[],[f108365,f129399])).
% 38.05/5.32  fof(f129399,plain,(
% 38.05/5.32    ( ! [X130,X128,X129] : (k4_xboole_0(X128,k4_xboole_0(k2_xboole_0(X129,X128),X130)) = k4_xboole_0(k2_xboole_0(X128,k4_xboole_0(X129,X130)),k4_xboole_0(k2_xboole_0(X129,X128),X130))) )),
% 38.05/5.32    inference(superposition,[],[f19,f58654])).
% 38.05/5.32  fof(f58654,plain,(
% 38.05/5.32    ( ! [X30,X28,X29] : (k2_xboole_0(X29,k4_xboole_0(k2_xboole_0(X28,X29),X30)) = k2_xboole_0(X29,k4_xboole_0(X28,X30))) )),
% 38.05/5.32    inference(forward_demodulation,[],[f58317,f32910])).
% 38.05/5.32  fof(f32910,plain,(
% 38.05/5.32    ( ! [X4,X2,X3] : (k2_xboole_0(X3,k4_xboole_0(X4,X2)) = k2_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2)))) )),
% 38.05/5.32    inference(superposition,[],[f1314,f18])).
% 38.05/5.32  fof(f1314,plain,(
% 38.05/5.32    ( ! [X14,X15,X13] : (k2_xboole_0(X15,k4_xboole_0(X13,X14)) = k2_xboole_0(X15,k4_xboole_0(X13,k2_xboole_0(X14,X15)))) )),
% 38.05/5.32    inference(superposition,[],[f20,f22])).
% 38.05/5.32  fof(f22,plain,(
% 38.05/5.32    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 38.05/5.32    inference(cnf_transformation,[],[f7])).
% 38.05/5.32  fof(f7,axiom,(
% 38.05/5.32    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 38.05/5.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 38.05/5.32  fof(f20,plain,(
% 38.05/5.32    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 38.05/5.32    inference(cnf_transformation,[],[f5])).
% 38.05/5.32  fof(f5,axiom,(
% 38.05/5.32    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 38.05/5.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 38.05/5.32  fof(f58317,plain,(
% 38.05/5.32    ( ! [X30,X28,X29] : (k2_xboole_0(X29,k4_xboole_0(k2_xboole_0(X28,X29),X30)) = k2_xboole_0(X29,k4_xboole_0(X28,k2_xboole_0(X29,X30)))) )),
% 38.05/5.32    inference(superposition,[],[f32910,f1339])).
% 38.05/5.32  fof(f1339,plain,(
% 38.05/5.32    ( ! [X14,X15,X13] : (k4_xboole_0(k2_xboole_0(X13,X14),k2_xboole_0(X14,X15)) = k4_xboole_0(X13,k2_xboole_0(X14,X15))) )),
% 38.05/5.32    inference(forward_demodulation,[],[f1291,f22])).
% 38.05/5.32  fof(f1291,plain,(
% 38.05/5.32    ( ! [X14,X15,X13] : (k4_xboole_0(k2_xboole_0(X13,X14),k2_xboole_0(X14,X15)) = k4_xboole_0(k4_xboole_0(X13,X14),X15)) )),
% 38.05/5.32    inference(superposition,[],[f22,f19])).
% 38.05/5.32  fof(f19,plain,(
% 38.05/5.32    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 38.05/5.32    inference(cnf_transformation,[],[f6])).
% 38.05/5.32  fof(f6,axiom,(
% 38.05/5.32    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 38.05/5.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 38.05/5.32  fof(f108365,plain,(
% 38.05/5.32    ( ! [X586,X585,X587] : (k2_xboole_0(X587,k4_xboole_0(k2_xboole_0(X585,k4_xboole_0(X586,X587)),k4_xboole_0(k2_xboole_0(X586,X585),X587))) = X587) )),
% 38.05/5.32    inference(superposition,[],[f60288,f45118])).
% 38.05/5.32  fof(f45118,plain,(
% 38.05/5.32    ( ! [X196,X194,X195] : (k4_xboole_0(k2_xboole_0(X196,k4_xboole_0(X194,X195)),X195) = k4_xboole_0(k2_xboole_0(X194,X196),X195)) )),
% 38.05/5.32    inference(forward_demodulation,[],[f44863,f2398])).
% 38.05/5.32  fof(f2398,plain,(
% 38.05/5.32    ( ! [X30,X31,X29] : (k4_xboole_0(k2_xboole_0(X30,X31),X29) = k4_xboole_0(k2_xboole_0(X31,k2_xboole_0(X29,X30)),X29)) )),
% 38.05/5.32    inference(superposition,[],[f55,f2001])).
% 38.05/5.32  fof(f2001,plain,(
% 38.05/5.32    ( ! [X17,X15,X16] : (k2_xboole_0(X17,k2_xboole_0(X15,X16)) = k2_xboole_0(X15,k2_xboole_0(X16,X17))) )),
% 38.05/5.32    inference(superposition,[],[f23,f18])).
% 38.05/5.32  fof(f23,plain,(
% 38.05/5.32    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 38.05/5.32    inference(cnf_transformation,[],[f8])).
% 38.05/5.32  fof(f8,axiom,(
% 38.05/5.32    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 38.05/5.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 38.05/5.32  fof(f55,plain,(
% 38.05/5.32    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 38.05/5.32    inference(superposition,[],[f19,f18])).
% 38.05/5.32  fof(f44863,plain,(
% 38.05/5.32    ( ! [X196,X194,X195] : (k4_xboole_0(k2_xboole_0(X196,k4_xboole_0(X194,X195)),X195) = k4_xboole_0(k2_xboole_0(X196,k2_xboole_0(X195,X194)),X195)) )),
% 38.05/5.32    inference(superposition,[],[f2019,f175])).
% 38.05/5.32  fof(f175,plain,(
% 38.05/5.32    ( ! [X10,X11] : (k2_xboole_0(X10,X11) = k2_xboole_0(k4_xboole_0(X11,X10),X10)) )),
% 38.05/5.32    inference(forward_demodulation,[],[f164,f89])).
% 38.05/5.32  fof(f89,plain,(
% 38.05/5.32    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0))) )),
% 38.05/5.32    inference(resolution,[],[f73,f21])).
% 38.05/5.32  fof(f21,plain,(
% 38.05/5.32    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 38.05/5.32    inference(cnf_transformation,[],[f12])).
% 38.05/5.32  fof(f12,plain,(
% 38.05/5.32    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 38.05/5.32    inference(ennf_transformation,[],[f2])).
% 38.05/5.32  fof(f2,axiom,(
% 38.05/5.32    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 38.05/5.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 38.05/5.32  fof(f73,plain,(
% 38.05/5.32    ( ! [X2,X1] : (r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X2,X1))) )),
% 38.05/5.32    inference(superposition,[],[f61,f18])).
% 38.05/5.32  fof(f61,plain,(
% 38.05/5.32    ( ! [X4,X5] : (r1_tarski(k4_xboole_0(X4,X5),k2_xboole_0(X4,X5))) )),
% 38.05/5.32    inference(superposition,[],[f17,f19])).
% 38.05/5.32  fof(f17,plain,(
% 38.05/5.32    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 38.05/5.32    inference(cnf_transformation,[],[f4])).
% 38.05/5.32  fof(f4,axiom,(
% 38.05/5.32    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 38.05/5.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 38.05/5.32  fof(f164,plain,(
% 38.05/5.32    ( ! [X10,X11] : (k2_xboole_0(k4_xboole_0(X11,X10),X10) = k2_xboole_0(k4_xboole_0(X11,X10),k2_xboole_0(X10,X11))) )),
% 38.05/5.32    inference(superposition,[],[f113,f20])).
% 38.05/5.32  fof(f113,plain,(
% 38.05/5.32    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X2,k2_xboole_0(X1,X2))) )),
% 38.05/5.32    inference(forward_demodulation,[],[f103,f20])).
% 38.05/5.32  fof(f103,plain,(
% 38.05/5.32    ( ! [X2,X1] : (k2_xboole_0(X2,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k4_xboole_0(X1,X2))) )),
% 38.05/5.32    inference(superposition,[],[f20,f19])).
% 38.05/5.32  fof(f2019,plain,(
% 38.05/5.32    ( ! [X19,X20,X18] : (k4_xboole_0(k2_xboole_0(X18,X19),X20) = k4_xboole_0(k2_xboole_0(X18,k2_xboole_0(X19,X20)),X20)) )),
% 38.05/5.32    inference(superposition,[],[f19,f23])).
% 38.05/5.32  fof(f60288,plain,(
% 38.05/5.32    ( ! [X35,X36] : (k2_xboole_0(X35,k4_xboole_0(X36,k4_xboole_0(X36,X35))) = X35) )),
% 38.05/5.32    inference(forward_demodulation,[],[f60287,f39])).
% 38.05/5.32  fof(f39,plain,(
% 38.05/5.32    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3) )),
% 38.05/5.32    inference(superposition,[],[f37,f18])).
% 38.05/5.32  fof(f37,plain,(
% 38.05/5.32    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 38.05/5.32    inference(resolution,[],[f21,f17])).
% 38.05/5.32  fof(f60287,plain,(
% 38.05/5.32    ( ! [X35,X36] : (k2_xboole_0(X35,k4_xboole_0(X35,X36)) = k2_xboole_0(X35,k4_xboole_0(X36,k4_xboole_0(X36,X35)))) )),
% 38.05/5.32    inference(forward_demodulation,[],[f59939,f33241])).
% 38.05/5.32  fof(f33241,plain,(
% 38.05/5.32    ( ! [X189,X187,X188] : (k2_xboole_0(X188,k4_xboole_0(X189,k4_xboole_0(X187,X188))) = k2_xboole_0(X188,k4_xboole_0(X189,X187))) )),
% 38.05/5.32    inference(forward_demodulation,[],[f32954,f1314])).
% 38.05/5.32  fof(f32954,plain,(
% 38.05/5.32    ( ! [X189,X187,X188] : (k2_xboole_0(X188,k4_xboole_0(X189,k4_xboole_0(X187,X188))) = k2_xboole_0(X188,k4_xboole_0(X189,k2_xboole_0(X187,X188)))) )),
% 38.05/5.32    inference(superposition,[],[f1314,f1185])).
% 38.05/5.32  fof(f1185,plain,(
% 38.05/5.32    ( ! [X19,X20] : (k2_xboole_0(X20,X19) = k2_xboole_0(k4_xboole_0(X20,X19),X19)) )),
% 38.05/5.32    inference(forward_demodulation,[],[f1148,f60])).
% 38.05/5.32  fof(f60,plain,(
% 38.05/5.32    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X2,X3),k2_xboole_0(X2,X3))) )),
% 38.05/5.32    inference(superposition,[],[f37,f19])).
% 38.05/5.32  fof(f1148,plain,(
% 38.05/5.32    ( ! [X19,X20] : (k2_xboole_0(k4_xboole_0(X20,X19),X19) = k2_xboole_0(k4_xboole_0(X20,X19),k2_xboole_0(X20,X19))) )),
% 38.05/5.32    inference(superposition,[],[f113,f828])).
% 38.05/5.32  fof(f828,plain,(
% 38.05/5.32    ( ! [X26,X25] : (k2_xboole_0(X26,k4_xboole_0(X25,X26)) = k2_xboole_0(X25,X26)) )),
% 38.05/5.32    inference(forward_demodulation,[],[f797,f705])).
% 38.05/5.32  fof(f705,plain,(
% 38.05/5.32    ( ! [X8,X7] : (k2_xboole_0(X8,X7) = k4_xboole_0(k2_xboole_0(X7,X8),k1_xboole_0)) )),
% 38.05/5.32    inference(forward_demodulation,[],[f678,f116])).
% 38.05/5.32  fof(f116,plain,(
% 38.05/5.32    ( ! [X7] : (k4_xboole_0(X7,k1_xboole_0) = X7) )),
% 38.05/5.32    inference(forward_demodulation,[],[f106,f29])).
% 38.05/5.32  fof(f29,plain,(
% 38.05/5.32    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 38.05/5.32    inference(superposition,[],[f18,f16])).
% 38.05/5.32  fof(f16,plain,(
% 38.05/5.32    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 38.05/5.32    inference(cnf_transformation,[],[f3])).
% 38.05/5.32  fof(f3,axiom,(
% 38.05/5.32    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 38.05/5.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 38.05/5.32  fof(f106,plain,(
% 38.05/5.32    ( ! [X7] : (k2_xboole_0(k1_xboole_0,X7) = k4_xboole_0(X7,k1_xboole_0)) )),
% 38.05/5.32    inference(superposition,[],[f20,f29])).
% 38.05/5.32  fof(f678,plain,(
% 38.05/5.32    ( ! [X8,X7] : (k4_xboole_0(k2_xboole_0(X7,X8),k1_xboole_0) = k4_xboole_0(k2_xboole_0(X8,X7),k1_xboole_0)) )),
% 38.05/5.32    inference(superposition,[],[f19,f427])).
% 38.05/5.32  fof(f427,plain,(
% 38.05/5.32    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k2_xboole_0(k2_xboole_0(X4,X3),k1_xboole_0)) )),
% 38.05/5.32    inference(forward_demodulation,[],[f401,f174])).
% 38.05/5.32  fof(f174,plain,(
% 38.05/5.32    ( ! [X6,X5] : (k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6))) )),
% 38.05/5.32    inference(forward_demodulation,[],[f173,f113])).
% 38.05/5.32  fof(f173,plain,(
% 38.05/5.32    ( ! [X6,X5] : (k2_xboole_0(X5,k2_xboole_0(X6,X5)) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6))) )),
% 38.05/5.32    inference(forward_demodulation,[],[f163,f18])).
% 38.05/5.32  fof(f163,plain,(
% 38.05/5.32    ( ! [X6,X5] : (k2_xboole_0(k2_xboole_0(X6,X5),X5) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6))) )),
% 38.05/5.32    inference(superposition,[],[f113,f113])).
% 38.05/5.32  fof(f401,plain,(
% 38.05/5.32    ( ! [X4,X3] : (k2_xboole_0(k2_xboole_0(X4,X3),k1_xboole_0) = k2_xboole_0(k2_xboole_0(X4,X3),k2_xboole_0(X3,X4))) )),
% 38.05/5.32    inference(superposition,[],[f20,f264])).
% 38.05/5.32  fof(f264,plain,(
% 38.05/5.32    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X4))) )),
% 38.05/5.32    inference(backward_demodulation,[],[f168,f245])).
% 38.05/5.32  fof(f245,plain,(
% 38.05/5.32    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 38.05/5.32    inference(superposition,[],[f240,f18])).
% 38.05/5.32  fof(f240,plain,(
% 38.05/5.32    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6))) )),
% 38.05/5.32    inference(forward_demodulation,[],[f235,f62])).
% 38.05/5.32  fof(f62,plain,(
% 38.05/5.32    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(X7,X7)) )),
% 38.05/5.32    inference(forward_demodulation,[],[f57,f38])).
% 38.05/5.32  fof(f38,plain,(
% 38.05/5.32    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) )),
% 38.05/5.32    inference(superposition,[],[f37,f16])).
% 38.05/5.32  fof(f57,plain,(
% 38.05/5.32    ( ! [X7] : (k4_xboole_0(k1_xboole_0,X7) = k4_xboole_0(X7,X7)) )),
% 38.05/5.32    inference(superposition,[],[f19,f29])).
% 38.05/5.32  fof(f235,plain,(
% 38.05/5.32    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6))) )),
% 38.05/5.32    inference(superposition,[],[f19,f155])).
% 38.05/5.32  fof(f155,plain,(
% 38.05/5.32    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k2_xboole_0(X3,k2_xboole_0(X3,X4))) )),
% 38.05/5.32    inference(forward_demodulation,[],[f144,f20])).
% 38.05/5.32  fof(f144,plain,(
% 38.05/5.32    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(X4,X3)) = k2_xboole_0(X3,k2_xboole_0(X3,X4))) )),
% 38.05/5.32    inference(superposition,[],[f20,f55])).
% 38.05/5.32  fof(f168,plain,(
% 38.05/5.32    ( ! [X4,X5] : (k4_xboole_0(X4,k2_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X4))) )),
% 38.05/5.32    inference(superposition,[],[f19,f113])).
% 38.05/5.32  fof(f797,plain,(
% 38.05/5.32    ( ! [X26,X25] : (k2_xboole_0(X26,k4_xboole_0(X25,X26)) = k4_xboole_0(k2_xboole_0(X26,X25),k1_xboole_0)) )),
% 38.05/5.32    inference(superposition,[],[f705,f175])).
% 38.05/5.32  fof(f59939,plain,(
% 38.05/5.32    ( ! [X35,X36] : (k2_xboole_0(X35,k4_xboole_0(X36,k4_xboole_0(X36,X35))) = k2_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X36,X35)))) )),
% 38.05/5.32    inference(superposition,[],[f33287,f110])).
% 38.05/5.32  fof(f110,plain,(
% 38.05/5.32    ( ! [X6,X5] : (k4_xboole_0(X5,k4_xboole_0(X6,X5)) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5))) )),
% 38.05/5.32    inference(superposition,[],[f19,f20])).
% 38.05/5.32  fof(f33287,plain,(
% 38.05/5.32    ( ! [X39,X37,X38] : (k2_xboole_0(X38,k4_xboole_0(X39,X37)) = k2_xboole_0(X38,k4_xboole_0(k2_xboole_0(X38,X39),X37))) )),
% 38.05/5.32    inference(forward_demodulation,[],[f33286,f55])).
% 38.05/5.32  fof(f33286,plain,(
% 38.05/5.32    ( ! [X39,X37,X38] : (k2_xboole_0(X38,k4_xboole_0(X39,X37)) = k2_xboole_0(X38,k4_xboole_0(k2_xboole_0(X37,k2_xboole_0(X38,X39)),X37))) )),
% 38.05/5.32    inference(forward_demodulation,[],[f33285,f23])).
% 38.05/5.32  fof(f33285,plain,(
% 38.05/5.32    ( ! [X39,X37,X38] : (k2_xboole_0(X38,k4_xboole_0(k2_xboole_0(k2_xboole_0(X37,X38),X39),X37)) = k2_xboole_0(X38,k4_xboole_0(X39,X37))) )),
% 38.05/5.32    inference(forward_demodulation,[],[f32975,f1314])).
% 38.05/5.32  fof(f32975,plain,(
% 38.05/5.32    ( ! [X39,X37,X38] : (k2_xboole_0(X38,k4_xboole_0(k2_xboole_0(k2_xboole_0(X37,X38),X39),X37)) = k2_xboole_0(X38,k4_xboole_0(X39,k2_xboole_0(X37,X38)))) )),
% 38.05/5.32    inference(superposition,[],[f1314,f55])).
% 38.05/5.32  fof(f61536,plain,(
% 38.05/5.32    ( ! [X94,X92,X93] : (k2_xboole_0(k4_xboole_0(X92,k2_xboole_0(X93,k4_xboole_0(X92,X94))),X94) = X94) )),
% 38.05/5.32    inference(forward_demodulation,[],[f61535,f32910])).
% 38.05/5.32  fof(f61535,plain,(
% 38.05/5.32    ( ! [X94,X92,X93] : (k2_xboole_0(k4_xboole_0(X92,k2_xboole_0(X93,k4_xboole_0(X92,k2_xboole_0(X93,X94)))),X94) = X94) )),
% 38.05/5.32    inference(forward_demodulation,[],[f61208,f22])).
% 38.05/5.32  fof(f61208,plain,(
% 38.05/5.32    ( ! [X94,X92,X93] : (k2_xboole_0(k4_xboole_0(k4_xboole_0(X92,X93),k4_xboole_0(X92,k2_xboole_0(X93,X94))),X94) = X94) )),
% 38.05/5.32    inference(superposition,[],[f60698,f22])).
% 38.05/5.32  fof(f60698,plain,(
% 38.05/5.32    ( ! [X70,X71] : (k2_xboole_0(k4_xboole_0(X71,k4_xboole_0(X71,X70)),X70) = X70) )),
% 38.05/5.32    inference(superposition,[],[f226,f60288])).
% 38.05/5.32  fof(f226,plain,(
% 38.05/5.32    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 38.05/5.32    inference(superposition,[],[f155,f18])).
% 38.05/5.32  fof(f75825,plain,(
% 38.05/5.32    ( ! [X57,X56,X55] : (k2_xboole_0(k4_xboole_0(X55,X56),k4_xboole_0(X57,X56)) = k2_xboole_0(k4_xboole_0(X55,X56),k4_xboole_0(k2_xboole_0(X55,X57),X56))) )),
% 38.05/5.32    inference(superposition,[],[f33287,f45981])).
% 38.05/5.32  fof(f45981,plain,(
% 38.05/5.32    ( ! [X198,X196,X197] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X197,X196),X198),X196) = k4_xboole_0(k2_xboole_0(X197,X198),X196)) )),
% 38.05/5.32    inference(forward_demodulation,[],[f45579,f55])).
% 38.05/5.32  fof(f45579,plain,(
% 38.05/5.32    ( ! [X198,X196,X197] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X197,X196),X198),X196) = k4_xboole_0(k2_xboole_0(X196,k2_xboole_0(X197,X198)),X196)) )),
% 38.05/5.32    inference(superposition,[],[f55,f2068])).
% 38.05/5.32  fof(f2068,plain,(
% 38.05/5.32    ( ! [X30,X28,X29] : (k2_xboole_0(X28,k2_xboole_0(k4_xboole_0(X29,X28),X30)) = k2_xboole_0(X28,k2_xboole_0(X29,X30))) )),
% 38.05/5.32    inference(forward_demodulation,[],[f1983,f23])).
% 38.05/5.32  fof(f1983,plain,(
% 38.05/5.32    ( ! [X30,X28,X29] : (k2_xboole_0(X28,k2_xboole_0(k4_xboole_0(X29,X28),X30)) = k2_xboole_0(k2_xboole_0(X28,X29),X30)) )),
% 38.05/5.32    inference(superposition,[],[f23,f20])).
% 38.05/5.32  fof(f27,plain,(
% 38.05/5.32    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) | spl3_1),
% 38.05/5.32    inference(avatar_component_clause,[],[f25])).
% 38.05/5.32  fof(f25,plain,(
% 38.05/5.32    spl3_1 <=> k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 38.05/5.32    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 38.05/5.32  fof(f50,plain,(
% 38.05/5.32    spl3_2),
% 38.05/5.32    inference(avatar_split_clause,[],[f45,f47])).
% 38.05/5.32  fof(f47,plain,(
% 38.05/5.32    spl3_2 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 38.05/5.32    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 38.05/5.32  fof(f45,plain,(
% 38.05/5.32    r1_tarski(k1_xboole_0,k1_xboole_0)),
% 38.05/5.32    inference(superposition,[],[f17,f38])).
% 38.05/5.32  fof(f28,plain,(
% 38.05/5.32    ~spl3_1),
% 38.05/5.32    inference(avatar_split_clause,[],[f15,f25])).
% 38.05/5.32  fof(f15,plain,(
% 38.05/5.32    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 38.05/5.32    inference(cnf_transformation,[],[f14])).
% 38.05/5.32  fof(f14,plain,(
% 38.05/5.32    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 38.05/5.32    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 38.05/5.32  fof(f13,plain,(
% 38.05/5.32    ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) => k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 38.05/5.32    introduced(choice_axiom,[])).
% 38.05/5.32  fof(f11,plain,(
% 38.05/5.32    ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 38.05/5.32    inference(ennf_transformation,[],[f10])).
% 38.05/5.32  fof(f10,negated_conjecture,(
% 38.05/5.32    ~! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 38.05/5.32    inference(negated_conjecture,[],[f9])).
% 38.05/5.32  fof(f9,conjecture,(
% 38.05/5.32    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 38.05/5.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 38.05/5.32  % SZS output end Proof for theBenchmark
% 38.05/5.32  % (26291)------------------------------
% 38.05/5.32  % (26291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 38.05/5.32  % (26291)Termination reason: Refutation
% 38.05/5.32  
% 38.05/5.32  % (26291)Memory used [KB]: 154411
% 38.05/5.32  % (26291)Time elapsed: 4.729 s
% 38.05/5.32  % (26291)------------------------------
% 38.05/5.32  % (26291)------------------------------
% 38.05/5.33  % (26109)Success in time 4.971 s
%------------------------------------------------------------------------------
