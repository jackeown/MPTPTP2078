%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:02 EST 2020

% Result     : Timeout 57.91s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   83 ( 301 expanded)
%              Number of leaves         :   15 ( 104 expanded)
%              Depth                    :   23
%              Number of atoms          :   98 ( 325 expanded)
%              Number of equality atoms :   77 ( 295 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81490,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f4988,f4994,f7405,f81450])).

fof(f81450,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f81449])).

fof(f81449,plain,
    ( $false
    | spl3_2 ),
    inference(trivial_inequality_removal,[],[f81400])).

fof(f81400,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | spl3_2 ),
    inference(superposition,[],[f4987,f81332])).

fof(f81332,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X2),k2_tarski(X1,X0)) = k1_enumset1(X1,X0,X2) ),
    inference(forward_demodulation,[],[f81249,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f81249,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X2),k2_tarski(X1,X0)) = k2_xboole_0(k1_tarski(X1),k2_tarski(X0,X2)) ),
    inference(superposition,[],[f79010,f4966])).

fof(f4966,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) ),
    inference(superposition,[],[f4920,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f4920,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f4846,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f4846,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k5_xboole_0(X3,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f4799,f16])).

fof(f16,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f4799,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X3,X2),X2) = k2_xboole_0(X3,X2) ),
    inference(forward_demodulation,[],[f4722,f20])).

fof(f4722,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X3,X2),X2) = k5_xboole_0(X3,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f159,f135])).

fof(f135,plain,(
    ! [X10,X11,X9] : k5_xboole_0(k4_xboole_0(X9,X10),X11) = k5_xboole_0(k3_xboole_0(X10,X9),k5_xboole_0(X9,X11)) ),
    inference(superposition,[],[f45,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f18,f17])).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f45,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(superposition,[],[f23,f16])).

fof(f23,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f159,plain,(
    ! [X6,X8,X7] : k5_xboole_0(X8,k4_xboole_0(X6,X7)) = k5_xboole_0(k3_xboole_0(X6,X7),k5_xboole_0(X8,X6)) ),
    inference(superposition,[],[f51,f18])).

fof(f51,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4)) ),
    inference(superposition,[],[f23,f16])).

fof(f79010,plain,(
    ! [X189,X190,X188] : k2_xboole_0(k1_tarski(X189),k2_xboole_0(k1_tarski(X188),X190)) = k2_xboole_0(X190,k2_tarski(X188,X189)) ),
    inference(forward_demodulation,[],[f78964,f20])).

fof(f78964,plain,(
    ! [X189,X190,X188] : k2_xboole_0(k1_tarski(X189),k2_xboole_0(k1_tarski(X188),X190)) = k5_xboole_0(X190,k4_xboole_0(k2_tarski(X188,X189),X190)) ),
    inference(superposition,[],[f78913,f19])).

fof(f78913,plain,(
    ! [X540,X542,X541] : k2_xboole_0(X542,k2_xboole_0(X541,X540)) = k5_xboole_0(X540,k4_xboole_0(k2_xboole_0(X541,X542),X540)) ),
    inference(forward_demodulation,[],[f78912,f20])).

fof(f78912,plain,(
    ! [X540,X542,X541] : k2_xboole_0(X542,k2_xboole_0(X541,X540)) = k5_xboole_0(X540,k4_xboole_0(k5_xboole_0(X541,k4_xboole_0(X542,X541)),X540)) ),
    inference(forward_demodulation,[],[f78885,f46004])).

fof(f46004,plain,(
    ! [X94,X92,X93,X91] : k4_xboole_0(k5_xboole_0(X94,k4_xboole_0(X91,X92)),X93) = k5_xboole_0(k4_xboole_0(X94,X93),k4_xboole_0(X91,k2_xboole_0(X92,X93))) ),
    inference(superposition,[],[f45978,f33113])).

fof(f33113,plain,(
    ! [X6,X8,X7] : k4_xboole_0(k4_xboole_0(X6,X7),X8) = k4_xboole_0(X6,k2_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f33112,f30])).

fof(f33112,plain,(
    ! [X6,X8,X7] : k4_xboole_0(k4_xboole_0(X6,X7),X8) = k5_xboole_0(X6,k3_xboole_0(k2_xboole_0(X7,X8),X6)) ),
    inference(forward_demodulation,[],[f33111,f20])).

fof(f33111,plain,(
    ! [X6,X8,X7] : k4_xboole_0(k4_xboole_0(X6,X7),X8) = k5_xboole_0(X6,k3_xboole_0(k5_xboole_0(X7,k4_xboole_0(X8,X7)),X6)) ),
    inference(forward_demodulation,[],[f33003,f9613])).

fof(f9613,plain,(
    ! [X146,X144,X145,X143] : k3_xboole_0(k5_xboole_0(X146,k4_xboole_0(X143,X144)),X145) = k5_xboole_0(k3_xboole_0(X145,X146),k3_xboole_0(X143,k4_xboole_0(X145,X144))) ),
    inference(superposition,[],[f1286,f8863])).

fof(f8863,plain,(
    ! [X10,X8,X9] : k3_xboole_0(X10,k4_xboole_0(X8,X9)) = k3_xboole_0(k4_xboole_0(X10,X9),X8) ),
    inference(superposition,[],[f8647,f17])).

fof(f8647,plain,(
    ! [X8,X7,X9] : k3_xboole_0(k4_xboole_0(X7,X9),X8) = k3_xboole_0(k4_xboole_0(X8,X9),X7) ),
    inference(superposition,[],[f8523,f8477])).

fof(f8477,plain,(
    ! [X10,X8,X9] : k4_xboole_0(k3_xboole_0(X8,X9),X10) = k3_xboole_0(k4_xboole_0(X9,X10),X8) ),
    inference(forward_demodulation,[],[f8406,f18])).

fof(f8406,plain,(
    ! [X10,X8,X9] : k4_xboole_0(k3_xboole_0(X8,X9),X10) = k3_xboole_0(k5_xboole_0(X9,k3_xboole_0(X9,X10)),X8) ),
    inference(superposition,[],[f1815,f40])).

fof(f40,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k3_xboole_0(X3,X4),X5) = k5_xboole_0(k3_xboole_0(X3,X4),k3_xboole_0(X3,k3_xboole_0(X4,X5))) ),
    inference(superposition,[],[f18,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f1815,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k5_xboole_0(X2,X0),X1) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f1286,f17])).

fof(f8523,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X1,X0),X2) = k3_xboole_0(k4_xboole_0(X1,X2),X0) ),
    inference(superposition,[],[f8477,f17])).

fof(f1286,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f24,f17])).

fof(f24,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f33003,plain,(
    ! [X6,X8,X7] : k4_xboole_0(k4_xboole_0(X6,X7),X8) = k5_xboole_0(X6,k5_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X8,k4_xboole_0(X6,X7)))) ),
    inference(superposition,[],[f54,f18])).

fof(f54,plain,(
    ! [X14,X12,X13] : k4_xboole_0(k5_xboole_0(X12,X13),X14) = k5_xboole_0(X12,k5_xboole_0(X13,k3_xboole_0(X14,k5_xboole_0(X12,X13)))) ),
    inference(superposition,[],[f23,f30])).

fof(f45978,plain,(
    ! [X45,X43,X44] : k5_xboole_0(k4_xboole_0(X43,X44),k4_xboole_0(X45,X44)) = k4_xboole_0(k5_xboole_0(X43,X45),X44) ),
    inference(forward_demodulation,[],[f45951,f142])).

fof(f142,plain,(
    ! [X14,X12,X13] : k4_xboole_0(k5_xboole_0(X12,X13),X14) = k5_xboole_0(X13,k5_xboole_0(X12,k3_xboole_0(k5_xboole_0(X12,X13),X14))) ),
    inference(superposition,[],[f45,f18])).

fof(f45951,plain,(
    ! [X45,X43,X44] : k5_xboole_0(k4_xboole_0(X43,X44),k4_xboole_0(X45,X44)) = k5_xboole_0(X45,k5_xboole_0(X43,k3_xboole_0(k5_xboole_0(X43,X45),X44))) ),
    inference(superposition,[],[f437,f1647])).

fof(f1647,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,X2),X1)) ),
    inference(superposition,[],[f47,f24])).

fof(f47,plain,(
    ! [X6,X8,X7] : k5_xboole_0(X6,k5_xboole_0(k3_xboole_0(X6,X7),X8)) = k5_xboole_0(k4_xboole_0(X6,X7),X8) ),
    inference(superposition,[],[f23,f18])).

fof(f437,plain,(
    ! [X6,X8,X7] : k5_xboole_0(X8,k4_xboole_0(X6,X7)) = k5_xboole_0(X6,k5_xboole_0(X8,k3_xboole_0(X6,X7))) ),
    inference(superposition,[],[f139,f18])).

fof(f139,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5)) ),
    inference(superposition,[],[f45,f23])).

fof(f78885,plain,(
    ! [X540,X542,X541] : k5_xboole_0(X540,k5_xboole_0(k4_xboole_0(X541,X540),k4_xboole_0(X542,k2_xboole_0(X541,X540)))) = k2_xboole_0(X542,k2_xboole_0(X541,X540)) ),
    inference(superposition,[],[f4849,f4846])).

fof(f4849,plain,(
    ! [X10,X11,X9] : k5_xboole_0(X10,k5_xboole_0(X11,k4_xboole_0(X9,k5_xboole_0(X10,X11)))) = k2_xboole_0(X9,k5_xboole_0(X10,X11)) ),
    inference(superposition,[],[f4799,f51])).

fof(f4987,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f4985])).

fof(f4985,plain,
    ( spl3_2
  <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f7405,plain,
    ( ~ spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f7371,f4985,f7402])).

fof(f7402,plain,
    ( spl3_4
  <=> k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f7371,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK2,sK1,sK0)
    | spl3_2 ),
    inference(superposition,[],[f4987,f4982])).

fof(f4982,plain,(
    ! [X2,X0,X1] : k1_enumset1(X2,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X1,X0)) ),
    inference(superposition,[],[f21,f4976])).

fof(f4976,plain,(
    ! [X2,X3] : k2_tarski(X2,X3) = k2_tarski(X3,X2) ),
    inference(superposition,[],[f4966,f19])).

fof(f4994,plain,
    ( ~ spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f4989,f4985,f4991])).

fof(f4991,plain,
    ( spl3_3
  <=> k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f4989,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK2,sK0,sK1)
    | spl3_2 ),
    inference(superposition,[],[f4987,f21])).

fof(f4988,plain,
    ( ~ spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f4972,f26,f4985])).

fof(f26,plain,
    ( spl3_1
  <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f4972,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1))
    | spl3_1 ),
    inference(superposition,[],[f28,f4920])).

fof(f28,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f29,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f15,f26])).

fof(f15,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:16:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (18498)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.46  % (18496)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.46  % (18494)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.46  % (18495)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.46  % (18493)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.46  % (18502)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.47  % (18502)Refutation not found, incomplete strategy% (18502)------------------------------
% 0.19/0.47  % (18502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (18502)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (18502)Memory used [KB]: 10490
% 0.19/0.47  % (18502)Time elapsed: 0.051 s
% 0.19/0.47  % (18502)------------------------------
% 0.19/0.47  % (18502)------------------------------
% 0.19/0.47  % (18503)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.47  % (18506)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.47  % (18492)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.48  % (18501)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.48  % (18504)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.48  % (18500)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.49  % (18497)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.50  % (18507)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.50  % (18505)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.50  % (18491)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.51  % (18508)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.51  % (18499)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 5.27/1.02  % (18495)Time limit reached!
% 5.27/1.02  % (18495)------------------------------
% 5.27/1.02  % (18495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.27/1.02  % (18495)Termination reason: Time limit
% 5.27/1.02  % (18495)Termination phase: Saturation
% 5.27/1.02  
% 5.27/1.02  % (18495)Memory used [KB]: 20596
% 5.27/1.02  % (18495)Time elapsed: 0.600 s
% 5.27/1.02  % (18495)------------------------------
% 5.27/1.02  % (18495)------------------------------
% 12.38/1.96  % (18497)Time limit reached!
% 12.38/1.96  % (18497)------------------------------
% 12.38/1.96  % (18497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.38/1.96  % (18497)Termination reason: Time limit
% 12.38/1.96  % (18497)Termination phase: Saturation
% 12.38/1.96  
% 12.38/1.96  % (18497)Memory used [KB]: 34668
% 12.38/1.96  % (18497)Time elapsed: 1.500 s
% 12.38/1.96  % (18497)------------------------------
% 12.38/1.96  % (18497)------------------------------
% 12.97/1.99  % (18496)Time limit reached!
% 12.97/1.99  % (18496)------------------------------
% 12.97/1.99  % (18496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.97/1.99  % (18496)Termination reason: Time limit
% 12.97/1.99  % (18496)Termination phase: Saturation
% 12.97/1.99  
% 12.97/1.99  % (18496)Memory used [KB]: 45542
% 12.97/1.99  % (18496)Time elapsed: 1.500 s
% 12.97/1.99  % (18496)------------------------------
% 12.97/1.99  % (18496)------------------------------
% 14.86/2.23  % (18493)Time limit reached!
% 14.86/2.23  % (18493)------------------------------
% 14.86/2.23  % (18493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.86/2.24  % (18493)Termination reason: Time limit
% 14.86/2.24  % (18493)Termination phase: Saturation
% 14.86/2.24  
% 14.86/2.24  % (18493)Memory used [KB]: 38762
% 14.86/2.24  % (18493)Time elapsed: 1.800 s
% 14.86/2.24  % (18493)------------------------------
% 14.86/2.24  % (18493)------------------------------
% 17.86/2.62  % (18503)Time limit reached!
% 17.86/2.62  % (18503)------------------------------
% 17.86/2.62  % (18503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.86/2.62  % (18503)Termination reason: Time limit
% 17.86/2.62  % (18503)Termination phase: Saturation
% 17.86/2.62  
% 17.86/2.62  % (18503)Memory used [KB]: 59999
% 17.86/2.62  % (18503)Time elapsed: 2.200 s
% 17.86/2.62  % (18503)------------------------------
% 17.86/2.62  % (18503)------------------------------
% 57.91/7.65  % (18491)Refutation found. Thanks to Tanya!
% 57.91/7.65  % SZS status Theorem for theBenchmark
% 57.91/7.65  % SZS output start Proof for theBenchmark
% 57.91/7.65  fof(f81490,plain,(
% 57.91/7.65    $false),
% 57.91/7.65    inference(avatar_sat_refutation,[],[f29,f4988,f4994,f7405,f81450])).
% 57.91/7.65  fof(f81450,plain,(
% 57.91/7.65    spl3_2),
% 57.91/7.65    inference(avatar_contradiction_clause,[],[f81449])).
% 57.91/7.65  fof(f81449,plain,(
% 57.91/7.65    $false | spl3_2),
% 57.91/7.65    inference(trivial_inequality_removal,[],[f81400])).
% 57.91/7.65  fof(f81400,plain,(
% 57.91/7.65    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) | spl3_2),
% 57.91/7.65    inference(superposition,[],[f4987,f81332])).
% 57.91/7.65  fof(f81332,plain,(
% 57.91/7.65    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X2),k2_tarski(X1,X0)) = k1_enumset1(X1,X0,X2)) )),
% 57.91/7.65    inference(forward_demodulation,[],[f81249,f21])).
% 57.91/7.65  fof(f21,plain,(
% 57.91/7.65    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 57.91/7.65    inference(cnf_transformation,[],[f9])).
% 57.91/7.65  fof(f9,axiom,(
% 57.91/7.65    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 57.91/7.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 57.91/7.65  fof(f81249,plain,(
% 57.91/7.65    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X2),k2_tarski(X1,X0)) = k2_xboole_0(k1_tarski(X1),k2_tarski(X0,X2))) )),
% 57.91/7.65    inference(superposition,[],[f79010,f4966])).
% 57.91/7.65  fof(f4966,plain,(
% 57.91/7.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) )),
% 57.91/7.65    inference(superposition,[],[f4920,f19])).
% 57.91/7.65  fof(f19,plain,(
% 57.91/7.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 57.91/7.65    inference(cnf_transformation,[],[f8])).
% 57.91/7.65  fof(f8,axiom,(
% 57.91/7.65    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 57.91/7.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 57.91/7.65  fof(f4920,plain,(
% 57.91/7.65    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 57.91/7.65    inference(superposition,[],[f4846,f20])).
% 57.91/7.65  fof(f20,plain,(
% 57.91/7.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 57.91/7.65    inference(cnf_transformation,[],[f7])).
% 57.91/7.65  fof(f7,axiom,(
% 57.91/7.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 57.91/7.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 57.91/7.65  fof(f4846,plain,(
% 57.91/7.65    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k5_xboole_0(X3,k4_xboole_0(X2,X3))) )),
% 57.91/7.65    inference(superposition,[],[f4799,f16])).
% 57.91/7.65  fof(f16,plain,(
% 57.91/7.65    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 57.91/7.65    inference(cnf_transformation,[],[f2])).
% 57.91/7.65  fof(f2,axiom,(
% 57.91/7.65    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 57.91/7.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 57.91/7.65  fof(f4799,plain,(
% 57.91/7.65    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X3,X2),X2) = k2_xboole_0(X3,X2)) )),
% 57.91/7.65    inference(forward_demodulation,[],[f4722,f20])).
% 57.91/7.65  fof(f4722,plain,(
% 57.91/7.65    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X3,X2),X2) = k5_xboole_0(X3,k4_xboole_0(X2,X3))) )),
% 57.91/7.65    inference(superposition,[],[f159,f135])).
% 57.91/7.65  fof(f135,plain,(
% 57.91/7.65    ( ! [X10,X11,X9] : (k5_xboole_0(k4_xboole_0(X9,X10),X11) = k5_xboole_0(k3_xboole_0(X10,X9),k5_xboole_0(X9,X11))) )),
% 57.91/7.65    inference(superposition,[],[f45,f30])).
% 57.91/7.65  fof(f30,plain,(
% 57.91/7.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 57.91/7.65    inference(superposition,[],[f18,f17])).
% 57.91/7.65  fof(f17,plain,(
% 57.91/7.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 57.91/7.65    inference(cnf_transformation,[],[f1])).
% 57.91/7.65  fof(f1,axiom,(
% 57.91/7.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 57.91/7.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 57.91/7.65  fof(f18,plain,(
% 57.91/7.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 57.91/7.65    inference(cnf_transformation,[],[f3])).
% 57.91/7.65  fof(f3,axiom,(
% 57.91/7.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 57.91/7.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 57.91/7.65  fof(f45,plain,(
% 57.91/7.65    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2)) )),
% 57.91/7.65    inference(superposition,[],[f23,f16])).
% 57.91/7.65  fof(f23,plain,(
% 57.91/7.65    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 57.91/7.65    inference(cnf_transformation,[],[f6])).
% 57.91/7.65  fof(f6,axiom,(
% 57.91/7.65    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 57.91/7.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 57.91/7.65  fof(f159,plain,(
% 57.91/7.65    ( ! [X6,X8,X7] : (k5_xboole_0(X8,k4_xboole_0(X6,X7)) = k5_xboole_0(k3_xboole_0(X6,X7),k5_xboole_0(X8,X6))) )),
% 57.91/7.65    inference(superposition,[],[f51,f18])).
% 57.91/7.65  fof(f51,plain,(
% 57.91/7.65    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))) )),
% 57.91/7.65    inference(superposition,[],[f23,f16])).
% 57.91/7.65  fof(f79010,plain,(
% 57.91/7.65    ( ! [X189,X190,X188] : (k2_xboole_0(k1_tarski(X189),k2_xboole_0(k1_tarski(X188),X190)) = k2_xboole_0(X190,k2_tarski(X188,X189))) )),
% 57.91/7.65    inference(forward_demodulation,[],[f78964,f20])).
% 57.91/7.65  fof(f78964,plain,(
% 57.91/7.65    ( ! [X189,X190,X188] : (k2_xboole_0(k1_tarski(X189),k2_xboole_0(k1_tarski(X188),X190)) = k5_xboole_0(X190,k4_xboole_0(k2_tarski(X188,X189),X190))) )),
% 57.91/7.65    inference(superposition,[],[f78913,f19])).
% 57.91/7.65  fof(f78913,plain,(
% 57.91/7.65    ( ! [X540,X542,X541] : (k2_xboole_0(X542,k2_xboole_0(X541,X540)) = k5_xboole_0(X540,k4_xboole_0(k2_xboole_0(X541,X542),X540))) )),
% 57.91/7.65    inference(forward_demodulation,[],[f78912,f20])).
% 57.91/7.65  fof(f78912,plain,(
% 57.91/7.65    ( ! [X540,X542,X541] : (k2_xboole_0(X542,k2_xboole_0(X541,X540)) = k5_xboole_0(X540,k4_xboole_0(k5_xboole_0(X541,k4_xboole_0(X542,X541)),X540))) )),
% 57.91/7.65    inference(forward_demodulation,[],[f78885,f46004])).
% 57.91/7.65  fof(f46004,plain,(
% 57.91/7.65    ( ! [X94,X92,X93,X91] : (k4_xboole_0(k5_xboole_0(X94,k4_xboole_0(X91,X92)),X93) = k5_xboole_0(k4_xboole_0(X94,X93),k4_xboole_0(X91,k2_xboole_0(X92,X93)))) )),
% 57.91/7.65    inference(superposition,[],[f45978,f33113])).
% 57.91/7.65  fof(f33113,plain,(
% 57.91/7.65    ( ! [X6,X8,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),X8) = k4_xboole_0(X6,k2_xboole_0(X7,X8))) )),
% 57.91/7.65    inference(forward_demodulation,[],[f33112,f30])).
% 57.91/7.65  fof(f33112,plain,(
% 57.91/7.65    ( ! [X6,X8,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),X8) = k5_xboole_0(X6,k3_xboole_0(k2_xboole_0(X7,X8),X6))) )),
% 57.91/7.65    inference(forward_demodulation,[],[f33111,f20])).
% 57.91/7.65  fof(f33111,plain,(
% 57.91/7.65    ( ! [X6,X8,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),X8) = k5_xboole_0(X6,k3_xboole_0(k5_xboole_0(X7,k4_xboole_0(X8,X7)),X6))) )),
% 57.91/7.65    inference(forward_demodulation,[],[f33003,f9613])).
% 57.91/7.65  fof(f9613,plain,(
% 57.91/7.65    ( ! [X146,X144,X145,X143] : (k3_xboole_0(k5_xboole_0(X146,k4_xboole_0(X143,X144)),X145) = k5_xboole_0(k3_xboole_0(X145,X146),k3_xboole_0(X143,k4_xboole_0(X145,X144)))) )),
% 57.91/7.65    inference(superposition,[],[f1286,f8863])).
% 57.91/7.65  fof(f8863,plain,(
% 57.91/7.65    ( ! [X10,X8,X9] : (k3_xboole_0(X10,k4_xboole_0(X8,X9)) = k3_xboole_0(k4_xboole_0(X10,X9),X8)) )),
% 57.91/7.65    inference(superposition,[],[f8647,f17])).
% 57.91/7.65  fof(f8647,plain,(
% 57.91/7.65    ( ! [X8,X7,X9] : (k3_xboole_0(k4_xboole_0(X7,X9),X8) = k3_xboole_0(k4_xboole_0(X8,X9),X7)) )),
% 57.91/7.65    inference(superposition,[],[f8523,f8477])).
% 57.91/7.65  fof(f8477,plain,(
% 57.91/7.65    ( ! [X10,X8,X9] : (k4_xboole_0(k3_xboole_0(X8,X9),X10) = k3_xboole_0(k4_xboole_0(X9,X10),X8)) )),
% 57.91/7.65    inference(forward_demodulation,[],[f8406,f18])).
% 57.91/7.65  fof(f8406,plain,(
% 57.91/7.65    ( ! [X10,X8,X9] : (k4_xboole_0(k3_xboole_0(X8,X9),X10) = k3_xboole_0(k5_xboole_0(X9,k3_xboole_0(X9,X10)),X8)) )),
% 57.91/7.65    inference(superposition,[],[f1815,f40])).
% 57.91/7.65  fof(f40,plain,(
% 57.91/7.65    ( ! [X4,X5,X3] : (k4_xboole_0(k3_xboole_0(X3,X4),X5) = k5_xboole_0(k3_xboole_0(X3,X4),k3_xboole_0(X3,k3_xboole_0(X4,X5)))) )),
% 57.91/7.65    inference(superposition,[],[f18,f22])).
% 57.91/7.65  fof(f22,plain,(
% 57.91/7.65    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 57.91/7.65    inference(cnf_transformation,[],[f5])).
% 57.91/7.65  fof(f5,axiom,(
% 57.91/7.65    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 57.91/7.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 57.91/7.65  fof(f1815,plain,(
% 57.91/7.65    ( ! [X2,X0,X1] : (k3_xboole_0(k5_xboole_0(X2,X0),X1) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X0))) )),
% 57.91/7.65    inference(superposition,[],[f1286,f17])).
% 57.91/7.65  fof(f8523,plain,(
% 57.91/7.65    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X1,X0),X2) = k3_xboole_0(k4_xboole_0(X1,X2),X0)) )),
% 57.91/7.65    inference(superposition,[],[f8477,f17])).
% 57.91/7.65  fof(f1286,plain,(
% 57.91/7.65    ( ! [X2,X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X2,X1))) )),
% 57.91/7.65    inference(superposition,[],[f24,f17])).
% 57.91/7.65  fof(f24,plain,(
% 57.91/7.65    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 57.91/7.65    inference(cnf_transformation,[],[f4])).
% 57.91/7.65  fof(f4,axiom,(
% 57.91/7.65    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 57.91/7.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 57.91/7.65  fof(f33003,plain,(
% 57.91/7.65    ( ! [X6,X8,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),X8) = k5_xboole_0(X6,k5_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X8,k4_xboole_0(X6,X7))))) )),
% 57.91/7.65    inference(superposition,[],[f54,f18])).
% 57.91/7.65  fof(f54,plain,(
% 57.91/7.65    ( ! [X14,X12,X13] : (k4_xboole_0(k5_xboole_0(X12,X13),X14) = k5_xboole_0(X12,k5_xboole_0(X13,k3_xboole_0(X14,k5_xboole_0(X12,X13))))) )),
% 57.91/7.65    inference(superposition,[],[f23,f30])).
% 57.91/7.65  fof(f45978,plain,(
% 57.91/7.65    ( ! [X45,X43,X44] : (k5_xboole_0(k4_xboole_0(X43,X44),k4_xboole_0(X45,X44)) = k4_xboole_0(k5_xboole_0(X43,X45),X44)) )),
% 57.91/7.65    inference(forward_demodulation,[],[f45951,f142])).
% 57.91/7.65  fof(f142,plain,(
% 57.91/7.65    ( ! [X14,X12,X13] : (k4_xboole_0(k5_xboole_0(X12,X13),X14) = k5_xboole_0(X13,k5_xboole_0(X12,k3_xboole_0(k5_xboole_0(X12,X13),X14)))) )),
% 57.91/7.65    inference(superposition,[],[f45,f18])).
% 57.91/7.65  fof(f45951,plain,(
% 57.91/7.65    ( ! [X45,X43,X44] : (k5_xboole_0(k4_xboole_0(X43,X44),k4_xboole_0(X45,X44)) = k5_xboole_0(X45,k5_xboole_0(X43,k3_xboole_0(k5_xboole_0(X43,X45),X44)))) )),
% 57.91/7.65    inference(superposition,[],[f437,f1647])).
% 57.91/7.65  fof(f1647,plain,(
% 57.91/7.65    ( ! [X2,X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,X2),X1))) )),
% 57.91/7.65    inference(superposition,[],[f47,f24])).
% 57.91/7.65  fof(f47,plain,(
% 57.91/7.65    ( ! [X6,X8,X7] : (k5_xboole_0(X6,k5_xboole_0(k3_xboole_0(X6,X7),X8)) = k5_xboole_0(k4_xboole_0(X6,X7),X8)) )),
% 57.91/7.65    inference(superposition,[],[f23,f18])).
% 57.91/7.65  fof(f437,plain,(
% 57.91/7.65    ( ! [X6,X8,X7] : (k5_xboole_0(X8,k4_xboole_0(X6,X7)) = k5_xboole_0(X6,k5_xboole_0(X8,k3_xboole_0(X6,X7)))) )),
% 57.91/7.65    inference(superposition,[],[f139,f18])).
% 57.91/7.65  fof(f139,plain,(
% 57.91/7.65    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5))) )),
% 57.91/7.65    inference(superposition,[],[f45,f23])).
% 57.91/7.65  fof(f78885,plain,(
% 57.91/7.65    ( ! [X540,X542,X541] : (k5_xboole_0(X540,k5_xboole_0(k4_xboole_0(X541,X540),k4_xboole_0(X542,k2_xboole_0(X541,X540)))) = k2_xboole_0(X542,k2_xboole_0(X541,X540))) )),
% 57.91/7.65    inference(superposition,[],[f4849,f4846])).
% 57.91/7.65  fof(f4849,plain,(
% 57.91/7.65    ( ! [X10,X11,X9] : (k5_xboole_0(X10,k5_xboole_0(X11,k4_xboole_0(X9,k5_xboole_0(X10,X11)))) = k2_xboole_0(X9,k5_xboole_0(X10,X11))) )),
% 57.91/7.65    inference(superposition,[],[f4799,f51])).
% 57.91/7.65  fof(f4987,plain,(
% 57.91/7.65    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)) | spl3_2),
% 57.91/7.65    inference(avatar_component_clause,[],[f4985])).
% 57.91/7.65  fof(f4985,plain,(
% 57.91/7.65    spl3_2 <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1))),
% 57.91/7.65    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 57.91/7.65  fof(f7405,plain,(
% 57.91/7.65    ~spl3_4 | spl3_2),
% 57.91/7.65    inference(avatar_split_clause,[],[f7371,f4985,f7402])).
% 57.91/7.65  fof(f7402,plain,(
% 57.91/7.65    spl3_4 <=> k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK2,sK1,sK0)),
% 57.91/7.65    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 57.91/7.65  fof(f7371,plain,(
% 57.91/7.65    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK2,sK1,sK0) | spl3_2),
% 57.91/7.65    inference(superposition,[],[f4987,f4982])).
% 57.91/7.65  fof(f4982,plain,(
% 57.91/7.65    ( ! [X2,X0,X1] : (k1_enumset1(X2,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X1,X0))) )),
% 57.91/7.65    inference(superposition,[],[f21,f4976])).
% 57.91/7.65  fof(f4976,plain,(
% 57.91/7.65    ( ! [X2,X3] : (k2_tarski(X2,X3) = k2_tarski(X3,X2)) )),
% 57.91/7.65    inference(superposition,[],[f4966,f19])).
% 57.91/7.65  fof(f4994,plain,(
% 57.91/7.65    ~spl3_3 | spl3_2),
% 57.91/7.65    inference(avatar_split_clause,[],[f4989,f4985,f4991])).
% 57.91/7.65  fof(f4991,plain,(
% 57.91/7.65    spl3_3 <=> k1_enumset1(sK0,sK1,sK2) = k1_enumset1(sK2,sK0,sK1)),
% 57.91/7.65    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 57.91/7.65  fof(f4989,plain,(
% 57.91/7.65    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK2,sK0,sK1) | spl3_2),
% 57.91/7.65    inference(superposition,[],[f4987,f21])).
% 57.91/7.65  fof(f4988,plain,(
% 57.91/7.65    ~spl3_2 | spl3_1),
% 57.91/7.65    inference(avatar_split_clause,[],[f4972,f26,f4985])).
% 57.91/7.65  fof(f26,plain,(
% 57.91/7.65    spl3_1 <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 57.91/7.65    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 57.91/7.65  fof(f4972,plain,(
% 57.91/7.65    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)) | spl3_1),
% 57.91/7.65    inference(superposition,[],[f28,f4920])).
% 57.91/7.65  fof(f28,plain,(
% 57.91/7.65    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) | spl3_1),
% 57.91/7.65    inference(avatar_component_clause,[],[f26])).
% 57.91/7.65  fof(f29,plain,(
% 57.91/7.65    ~spl3_1),
% 57.91/7.65    inference(avatar_split_clause,[],[f15,f26])).
% 57.91/7.65  fof(f15,plain,(
% 57.91/7.65    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 57.91/7.65    inference(cnf_transformation,[],[f14])).
% 57.91/7.65  fof(f14,plain,(
% 57.91/7.65    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 57.91/7.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 57.91/7.65  fof(f13,plain,(
% 57.91/7.65    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 57.91/7.65    introduced(choice_axiom,[])).
% 57.91/7.65  fof(f12,plain,(
% 57.91/7.65    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 57.91/7.65    inference(ennf_transformation,[],[f11])).
% 57.91/7.65  fof(f11,negated_conjecture,(
% 57.91/7.65    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 57.91/7.65    inference(negated_conjecture,[],[f10])).
% 57.91/7.65  fof(f10,conjecture,(
% 57.91/7.65    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 57.91/7.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 57.91/7.65  % SZS output end Proof for theBenchmark
% 57.91/7.65  % (18491)------------------------------
% 57.91/7.65  % (18491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 57.91/7.65  % (18491)Termination reason: Refutation
% 57.91/7.65  
% 57.91/7.65  % (18491)Memory used [KB]: 77653
% 57.91/7.65  % (18491)Time elapsed: 7.241 s
% 57.91/7.65  % (18491)------------------------------
% 57.91/7.65  % (18491)------------------------------
% 57.91/7.66  % (18490)Success in time 7.302 s
%------------------------------------------------------------------------------
