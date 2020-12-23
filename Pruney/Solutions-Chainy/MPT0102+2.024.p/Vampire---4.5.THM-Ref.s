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
% DateTime   : Thu Dec  3 12:31:59 EST 2020

% Result     : Theorem 9.02s
% Output     : Refutation 9.02s
% Verified   : 
% Statistics : Number of formulae       :  125 (14394 expanded)
%              Number of leaves         :   15 (5070 expanded)
%              Depth                    :   32
%              Number of atoms          :  159 (14444 expanded)
%              Number of equality atoms :  116 (14385 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22441,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f146,f147,f2518,f2524,f22349,f22357,f22440])).

fof(f22440,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f22439])).

fof(f22439,plain,
    ( $false
    | spl2_6 ),
    inference(trivial_inequality_removal,[],[f22438])).

fof(f22438,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | spl2_6 ),
    inference(superposition,[],[f22356,f965])).

fof(f965,plain,(
    ! [X6,X7,X5] : k2_xboole_0(k4_xboole_0(X5,k2_xboole_0(X5,X6)),X7) = X7 ),
    inference(superposition,[],[f198,f673])).

fof(f673,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,X2) = k4_xboole_0(X1,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f241,f15])).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f241,plain,(
    ! [X17,X18,X16] : k4_xboole_0(X16,X16) = k4_xboole_0(X17,k2_xboole_0(X18,X17)) ),
    inference(forward_demodulation,[],[f222,f238])).

fof(f238,plain,(
    ! [X10,X9] : k4_xboole_0(X10,k4_xboole_0(X9,X9)) = X10 ),
    inference(forward_demodulation,[],[f219,f198])).

fof(f219,plain,(
    ! [X10,X9] : k4_xboole_0(X10,k4_xboole_0(X9,X9)) = k2_xboole_0(k4_xboole_0(X9,X9),X10) ),
    inference(superposition,[],[f198,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f222,plain,(
    ! [X17,X18,X16] : k4_xboole_0(X16,X16) = k4_xboole_0(X17,k2_xboole_0(X18,k4_xboole_0(X17,k4_xboole_0(X16,X16)))) ),
    inference(superposition,[],[f198,f164])).

fof(f164,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2)))) = X2 ),
    inference(backward_demodulation,[],[f92,f148])).

fof(f148,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X1,k4_xboole_0(X2,X0)) = k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X0))) ),
    inference(superposition,[],[f30,f15])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f17,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f92,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = X2 ),
    inference(forward_demodulation,[],[f86,f20])).

fof(f86,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = X2 ),
    inference(superposition,[],[f82,f20])).

fof(f82,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X3))) = X3 ),
    inference(superposition,[],[f80,f22])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f14,f16,f16])).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f80,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3 ),
    inference(backward_demodulation,[],[f45,f70])).

fof(f70,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = X4 ),
    inference(superposition,[],[f50,f15])).

fof(f50,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X3)),k4_xboole_0(X3,X4)) = X3 ),
    inference(superposition,[],[f23,f22])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f18,f16])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f45,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))) = k2_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f38,f15])).

fof(f38,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))) ),
    inference(superposition,[],[f17,f22])).

fof(f198,plain,(
    ! [X6,X7] : k2_xboole_0(k4_xboole_0(X7,X7),X6) = X6 ),
    inference(superposition,[],[f180,f15])).

fof(f180,plain,(
    ! [X10,X11] : k2_xboole_0(X11,k4_xboole_0(X10,X10)) = X11 ),
    inference(superposition,[],[f164,f80])).

fof(f22356,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f22354])).

fof(f22354,plain,
    ( spl2_6
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f22357,plain,
    ( ~ spl2_6
    | spl2_4 ),
    inference(avatar_split_clause,[],[f22352,f2521,f22354])).

fof(f2521,plain,
    ( spl2_4
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f22352,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_4 ),
    inference(forward_demodulation,[],[f22351,f84])).

fof(f84,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f80,f17])).

fof(f22351,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK0,k2_xboole_0(sK1,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_4 ),
    inference(forward_demodulation,[],[f22350,f394])).

fof(f394,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(X3,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X3,k2_xboole_0(X2,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f32,f15])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f31,f20])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(forward_demodulation,[],[f29,f20])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[],[f20,f20])).

fof(f22350,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_4 ),
    inference(forward_demodulation,[],[f22341,f20])).

fof(f22341,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_4 ),
    inference(backward_demodulation,[],[f2523,f22152])).

fof(f22152,plain,(
    ! [X333,X331,X332] : k4_xboole_0(X333,k2_xboole_0(X331,X332)) = k4_xboole_0(k2_xboole_0(X333,k4_xboole_0(X332,X331)),k2_xboole_0(X331,X332)) ),
    inference(superposition,[],[f18676,f2254])).

fof(f2254,plain,(
    ! [X26,X25] : k4_xboole_0(X26,X25) = k4_xboole_0(k2_xboole_0(X25,X26),X25) ),
    inference(forward_demodulation,[],[f2093,f340])).

fof(f340,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X0))) = X2 ),
    inference(forward_demodulation,[],[f308,f17])).

fof(f308,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1)))) = X2 ),
    inference(superposition,[],[f238,f20])).

fof(f2093,plain,(
    ! [X26,X25] : k4_xboole_0(k2_xboole_0(X25,X26),X25) = k4_xboole_0(k4_xboole_0(X26,k4_xboole_0(X26,k2_xboole_0(X25,X26))),X25) ),
    inference(superposition,[],[f37,f1327])).

fof(f1327,plain,(
    ! [X26,X27] : k2_xboole_0(k4_xboole_0(k2_xboole_0(X26,X27),X27),X26) = X26 ),
    inference(superposition,[],[f759,f345])).

fof(f345,plain,(
    ! [X0,X1] : k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X0),X0)) = X1 ),
    inference(superposition,[],[f197,f15])).

fof(f197,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(k2_xboole_0(X4,X3),X4)) = X3 ),
    inference(superposition,[],[f180,f30])).

fof(f759,plain,(
    ! [X56,X55] : k2_xboole_0(X56,X55) = k2_xboole_0(X55,k2_xboole_0(X56,X55)) ),
    inference(forward_demodulation,[],[f735,f238])).

fof(f735,plain,(
    ! [X57,X56,X55] : k2_xboole_0(X56,X55) = k2_xboole_0(k4_xboole_0(X55,k4_xboole_0(X57,X57)),k2_xboole_0(X56,X55)) ),
    inference(superposition,[],[f105,f241])).

fof(f105,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X3)),X3) = X3 ),
    inference(superposition,[],[f100,f22])).

fof(f100,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2 ),
    inference(superposition,[],[f55,f17])).

fof(f55,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2 ),
    inference(superposition,[],[f23,f15])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[],[f20,f22])).

fof(f18676,plain,(
    ! [X210,X211,X209] : k4_xboole_0(X209,X210) = k4_xboole_0(k2_xboole_0(X209,k4_xboole_0(X210,X211)),X210) ),
    inference(forward_demodulation,[],[f18510,f2254])).

fof(f18510,plain,(
    ! [X210,X211,X209] : k4_xboole_0(k2_xboole_0(X209,k4_xboole_0(X210,X211)),X210) = k4_xboole_0(k2_xboole_0(X210,X209),X210) ),
    inference(superposition,[],[f2243,f4611])).

fof(f4611,plain,(
    ! [X130,X128,X129] : k2_xboole_0(k2_xboole_0(X129,k4_xboole_0(X128,X130)),X128) = k2_xboole_0(X128,X129) ),
    inference(forward_demodulation,[],[f4466,f4610])).

fof(f4610,plain,(
    ! [X127,X125,X126] : k2_xboole_0(k4_xboole_0(X127,k4_xboole_0(X127,k4_xboole_0(X125,X126))),k2_xboole_0(X126,k4_xboole_0(X125,X127))) = k2_xboole_0(X125,X126) ),
    inference(forward_demodulation,[],[f4465,f2912])).

fof(f2912,plain,(
    ! [X70,X72,X71] : k2_xboole_0(X71,X70) = k2_xboole_0(X71,k2_xboole_0(X70,k4_xboole_0(X71,X72))) ),
    inference(forward_demodulation,[],[f2866,f170])).

fof(f170,plain,(
    ! [X35,X33,X34] : k2_xboole_0(X33,k4_xboole_0(X35,k4_xboole_0(X33,X34))) = k2_xboole_0(X33,X35) ),
    inference(forward_demodulation,[],[f156,f17])).

fof(f156,plain,(
    ! [X35,X33,X34] : k2_xboole_0(X33,k4_xboole_0(X35,k4_xboole_0(X33,X34))) = k2_xboole_0(X33,k4_xboole_0(X35,X33)) ),
    inference(superposition,[],[f30,f100])).

fof(f2866,plain,(
    ! [X70,X72,X71] : k2_xboole_0(X71,k2_xboole_0(X70,k4_xboole_0(X71,X72))) = k2_xboole_0(X71,k4_xboole_0(X70,k4_xboole_0(X71,X72))) ),
    inference(superposition,[],[f170,f2243])).

fof(f4465,plain,(
    ! [X127,X125,X126] : k2_xboole_0(X125,k2_xboole_0(X126,k4_xboole_0(X125,X127))) = k2_xboole_0(k4_xboole_0(X127,k4_xboole_0(X127,k4_xboole_0(X125,X126))),k2_xboole_0(X126,k4_xboole_0(X125,X127))) ),
    inference(superposition,[],[f2247,f161])).

fof(f161,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) ),
    inference(backward_demodulation,[],[f43,f148])).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) ),
    inference(forward_demodulation,[],[f34,f20])).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(superposition,[],[f22,f20])).

fof(f2247,plain,(
    ! [X41,X40] : k2_xboole_0(X41,X40) = k2_xboole_0(k4_xboole_0(X41,X40),X40) ),
    inference(backward_demodulation,[],[f756,f2243])).

fof(f756,plain,(
    ! [X41,X40] : k2_xboole_0(X41,X40) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X41,X40),X40),X40) ),
    inference(forward_demodulation,[],[f730,f238])).

fof(f730,plain,(
    ! [X41,X42,X40] : k2_xboole_0(X41,X40) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X41,X40),X40),k4_xboole_0(X40,k4_xboole_0(X42,X42))) ),
    inference(superposition,[],[f70,f241])).

fof(f4466,plain,(
    ! [X130,X128,X129] : k2_xboole_0(k2_xboole_0(X129,k4_xboole_0(X128,X130)),X128) = k2_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,k4_xboole_0(X128,X129))),k2_xboole_0(X129,k4_xboole_0(X128,X130))) ),
    inference(superposition,[],[f2260,f161])).

fof(f2260,plain,(
    ! [X47,X48] : k2_xboole_0(X47,X48) = k2_xboole_0(k4_xboole_0(X48,X47),X47) ),
    inference(backward_demodulation,[],[f1026,f2254])).

fof(f1026,plain,(
    ! [X47,X48] : k2_xboole_0(X47,X48) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X47,X48),X47),X47) ),
    inference(forward_demodulation,[],[f1001,f238])).

fof(f1001,plain,(
    ! [X47,X48,X49] : k2_xboole_0(X47,X48) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X47,X48),X47),k4_xboole_0(X47,k4_xboole_0(X49,X49))) ),
    inference(superposition,[],[f70,f673])).

fof(f2243,plain,(
    ! [X24,X23] : k4_xboole_0(X23,X24) = k4_xboole_0(k2_xboole_0(X23,X24),X24) ),
    inference(forward_demodulation,[],[f2092,f844])).

fof(f844,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X1,X0))) = X2 ),
    inference(superposition,[],[f340,f15])).

fof(f2092,plain,(
    ! [X24,X23] : k4_xboole_0(k2_xboole_0(X23,X24),X24) = k4_xboole_0(k4_xboole_0(X23,k4_xboole_0(X23,k2_xboole_0(X23,X24))),X24) ),
    inference(superposition,[],[f37,f1326])).

fof(f1326,plain,(
    ! [X24,X25] : k2_xboole_0(k4_xboole_0(k2_xboole_0(X25,X24),X25),X24) = X24 ),
    inference(superposition,[],[f759,f197])).

fof(f2523,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f2521])).

fof(f22349,plain,
    ( ~ spl2_5
    | spl2_3 ),
    inference(avatar_split_clause,[],[f22344,f2515,f22346])).

fof(f22346,plain,
    ( spl2_5
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f2515,plain,
    ( spl2_3
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f22344,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)))
    | spl2_3 ),
    inference(forward_demodulation,[],[f22343,f84])).

fof(f22343,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k2_xboole_0(sK0,k2_xboole_0(sK1,sK1))))
    | spl2_3 ),
    inference(forward_demodulation,[],[f22342,f394])).

fof(f22342,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))))
    | spl2_3 ),
    inference(forward_demodulation,[],[f22340,f20])).

fof(f22340,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)))
    | spl2_3 ),
    inference(backward_demodulation,[],[f2517,f22152])).

fof(f2517,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f2515])).

fof(f2524,plain,
    ( ~ spl2_4
    | spl2_1 ),
    inference(avatar_split_clause,[],[f2519,f25,f2521])).

fof(f25,plain,
    ( spl2_1
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f2519,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(forward_demodulation,[],[f2512,f22])).

fof(f2512,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))
    | spl2_1 ),
    inference(backward_demodulation,[],[f27,f2439])).

fof(f2439,plain,(
    ! [X10,X11,X9] : k4_xboole_0(X10,X11) = k4_xboole_0(k2_xboole_0(X9,X10),k2_xboole_0(k4_xboole_0(X9,X10),X11)) ),
    inference(superposition,[],[f20,f2245])).

fof(f2245,plain,(
    ! [X19,X20] : k4_xboole_0(k2_xboole_0(X19,X20),k4_xboole_0(X19,X20)) = X20 ),
    inference(backward_demodulation,[],[f533,f2243])).

fof(f533,plain,(
    ! [X19,X20] : k4_xboole_0(k2_xboole_0(X19,X20),k4_xboole_0(k2_xboole_0(X19,X20),X20)) = X20 ),
    inference(superposition,[],[f213,f50])).

fof(f213,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X0))) = X2 ),
    inference(forward_demodulation,[],[f195,f17])).

fof(f195,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1)))) = X2 ),
    inference(superposition,[],[f180,f20])).

fof(f27,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f2518,plain,
    ( ~ spl2_3
    | spl2_2 ),
    inference(avatar_split_clause,[],[f2513,f143,f2515])).

fof(f143,plain,
    ( spl2_2
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f2513,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)))
    | spl2_2 ),
    inference(forward_demodulation,[],[f2511,f22])).

fof(f2511,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)))
    | spl2_2 ),
    inference(backward_demodulation,[],[f145,f2439])).

fof(f145,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f143])).

fof(f147,plain,
    ( ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f141,f25,f143])).

fof(f141,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(superposition,[],[f27,f15])).

fof(f146,plain,
    ( ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f140,f25,f143])).

fof(f140,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(superposition,[],[f27,f15])).

fof(f28,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f21,f25])).

fof(f21,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f13,f16,f19,f19])).

fof(f19,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f13,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (12073)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.45  % (12086)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.46  % (12074)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (12082)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % (12079)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (12084)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.51  % (12075)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (12071)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.52  % (12077)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.52  % (12068)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.53  % (12080)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.53  % (12080)Refutation not found, incomplete strategy% (12080)------------------------------
% 0.20/0.53  % (12080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (12080)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (12080)Memory used [KB]: 10490
% 0.20/0.53  % (12080)Time elapsed: 0.082 s
% 0.20/0.53  % (12080)------------------------------
% 0.20/0.53  % (12080)------------------------------
% 0.20/0.53  % (12070)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.53  % (12083)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.54  % (12076)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.54  % (12087)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.54  % (12078)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.55  % (12085)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.55  % (12069)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 5.71/1.08  % (12073)Time limit reached!
% 5.71/1.08  % (12073)------------------------------
% 5.71/1.08  % (12073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.71/1.08  % (12073)Termination reason: Time limit
% 5.71/1.08  
% 5.71/1.08  % (12073)Memory used [KB]: 24178
% 5.71/1.08  % (12073)Time elapsed: 0.638 s
% 5.71/1.08  % (12073)------------------------------
% 5.71/1.08  % (12073)------------------------------
% 9.02/1.50  % (12079)Refutation found. Thanks to Tanya!
% 9.02/1.50  % SZS status Theorem for theBenchmark
% 9.02/1.50  % SZS output start Proof for theBenchmark
% 9.02/1.50  fof(f22441,plain,(
% 9.02/1.50    $false),
% 9.02/1.50    inference(avatar_sat_refutation,[],[f28,f146,f147,f2518,f2524,f22349,f22357,f22440])).
% 9.02/1.50  fof(f22440,plain,(
% 9.02/1.50    spl2_6),
% 9.02/1.50    inference(avatar_contradiction_clause,[],[f22439])).
% 9.02/1.50  fof(f22439,plain,(
% 9.02/1.50    $false | spl2_6),
% 9.02/1.50    inference(trivial_inequality_removal,[],[f22438])).
% 9.02/1.50  fof(f22438,plain,(
% 9.02/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | spl2_6),
% 9.02/1.50    inference(superposition,[],[f22356,f965])).
% 9.02/1.50  fof(f965,plain,(
% 9.02/1.50    ( ! [X6,X7,X5] : (k2_xboole_0(k4_xboole_0(X5,k2_xboole_0(X5,X6)),X7) = X7) )),
% 9.02/1.50    inference(superposition,[],[f198,f673])).
% 9.02/1.50  fof(f673,plain,(
% 9.02/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X2,X2) = k4_xboole_0(X1,k2_xboole_0(X1,X0))) )),
% 9.02/1.50    inference(superposition,[],[f241,f15])).
% 9.02/1.50  fof(f15,plain,(
% 9.02/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 9.02/1.50    inference(cnf_transformation,[],[f1])).
% 9.02/1.50  fof(f1,axiom,(
% 9.02/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 9.02/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 9.02/1.50  fof(f241,plain,(
% 9.02/1.50    ( ! [X17,X18,X16] : (k4_xboole_0(X16,X16) = k4_xboole_0(X17,k2_xboole_0(X18,X17))) )),
% 9.02/1.50    inference(forward_demodulation,[],[f222,f238])).
% 9.02/1.50  fof(f238,plain,(
% 9.02/1.50    ( ! [X10,X9] : (k4_xboole_0(X10,k4_xboole_0(X9,X9)) = X10) )),
% 9.02/1.50    inference(forward_demodulation,[],[f219,f198])).
% 9.02/1.50  fof(f219,plain,(
% 9.02/1.50    ( ! [X10,X9] : (k4_xboole_0(X10,k4_xboole_0(X9,X9)) = k2_xboole_0(k4_xboole_0(X9,X9),X10)) )),
% 9.02/1.50    inference(superposition,[],[f198,f17])).
% 9.02/1.50  fof(f17,plain,(
% 9.02/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 9.02/1.50    inference(cnf_transformation,[],[f4])).
% 9.02/1.50  fof(f4,axiom,(
% 9.02/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 9.02/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 9.02/1.50  fof(f222,plain,(
% 9.02/1.50    ( ! [X17,X18,X16] : (k4_xboole_0(X16,X16) = k4_xboole_0(X17,k2_xboole_0(X18,k4_xboole_0(X17,k4_xboole_0(X16,X16))))) )),
% 9.02/1.50    inference(superposition,[],[f198,f164])).
% 9.02/1.50  fof(f164,plain,(
% 9.02/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2)))) = X2) )),
% 9.02/1.50    inference(backward_demodulation,[],[f92,f148])).
% 9.02/1.50  fof(f148,plain,(
% 9.02/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(X1,k4_xboole_0(X2,X0)) = k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X0)))) )),
% 9.02/1.50    inference(superposition,[],[f30,f15])).
% 9.02/1.50  fof(f30,plain,(
% 9.02/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 9.02/1.50    inference(superposition,[],[f17,f20])).
% 9.02/1.50  fof(f20,plain,(
% 9.02/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 9.02/1.50    inference(cnf_transformation,[],[f5])).
% 9.02/1.50  fof(f5,axiom,(
% 9.02/1.50    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 9.02/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 9.02/1.50  fof(f92,plain,(
% 9.02/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = X2) )),
% 9.02/1.50    inference(forward_demodulation,[],[f86,f20])).
% 9.02/1.50  fof(f86,plain,(
% 9.02/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = X2) )),
% 9.02/1.50    inference(superposition,[],[f82,f20])).
% 9.02/1.50  fof(f82,plain,(
% 9.02/1.50    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X3))) = X3) )),
% 9.02/1.50    inference(superposition,[],[f80,f22])).
% 9.02/1.50  fof(f22,plain,(
% 9.02/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 9.02/1.50    inference(definition_unfolding,[],[f14,f16,f16])).
% 9.02/1.50  fof(f16,plain,(
% 9.02/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 9.02/1.50    inference(cnf_transformation,[],[f6])).
% 9.02/1.50  fof(f6,axiom,(
% 9.02/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 9.02/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 9.02/1.50  fof(f14,plain,(
% 9.02/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 9.02/1.50    inference(cnf_transformation,[],[f2])).
% 9.02/1.50  fof(f2,axiom,(
% 9.02/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 9.02/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 9.02/1.50  fof(f80,plain,(
% 9.02/1.50    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3) )),
% 9.02/1.50    inference(backward_demodulation,[],[f45,f70])).
% 9.02/1.50  fof(f70,plain,(
% 9.02/1.50    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = X4) )),
% 9.02/1.50    inference(superposition,[],[f50,f15])).
% 9.02/1.50  fof(f50,plain,(
% 9.02/1.50    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X3)),k4_xboole_0(X3,X4)) = X3) )),
% 9.02/1.50    inference(superposition,[],[f23,f22])).
% 9.02/1.50  fof(f23,plain,(
% 9.02/1.50    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 9.02/1.50    inference(definition_unfolding,[],[f18,f16])).
% 9.02/1.50  fof(f18,plain,(
% 9.02/1.50    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 9.02/1.50    inference(cnf_transformation,[],[f7])).
% 9.02/1.50  fof(f7,axiom,(
% 9.02/1.50    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 9.02/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 9.02/1.50  fof(f45,plain,(
% 9.02/1.50    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))) = k2_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 9.02/1.50    inference(forward_demodulation,[],[f38,f15])).
% 9.02/1.50  fof(f38,plain,(
% 9.02/1.50    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3)))) )),
% 9.02/1.50    inference(superposition,[],[f17,f22])).
% 9.02/1.50  fof(f198,plain,(
% 9.02/1.50    ( ! [X6,X7] : (k2_xboole_0(k4_xboole_0(X7,X7),X6) = X6) )),
% 9.02/1.50    inference(superposition,[],[f180,f15])).
% 9.02/1.50  fof(f180,plain,(
% 9.02/1.50    ( ! [X10,X11] : (k2_xboole_0(X11,k4_xboole_0(X10,X10)) = X11) )),
% 9.02/1.50    inference(superposition,[],[f164,f80])).
% 9.02/1.50  fof(f22356,plain,(
% 9.02/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_6),
% 9.02/1.50    inference(avatar_component_clause,[],[f22354])).
% 9.02/1.50  fof(f22354,plain,(
% 9.02/1.50    spl2_6 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 9.02/1.50    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 9.02/1.50  fof(f22357,plain,(
% 9.02/1.50    ~spl2_6 | spl2_4),
% 9.02/1.50    inference(avatar_split_clause,[],[f22352,f2521,f22354])).
% 9.02/1.50  fof(f2521,plain,(
% 9.02/1.50    spl2_4 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 9.02/1.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 9.02/1.50  fof(f22352,plain,(
% 9.02/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_4),
% 9.02/1.50    inference(forward_demodulation,[],[f22351,f84])).
% 9.02/1.50  fof(f84,plain,(
% 9.02/1.50    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 9.02/1.50    inference(superposition,[],[f80,f17])).
% 9.02/1.50  fof(f22351,plain,(
% 9.02/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK0,k2_xboole_0(sK1,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_4),
% 9.02/1.50    inference(forward_demodulation,[],[f22350,f394])).
% 9.02/1.50  fof(f394,plain,(
% 9.02/1.50    ( ! [X2,X0,X3,X1] : (k4_xboole_0(X3,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X3,k2_xboole_0(X2,k2_xboole_0(X0,X1)))) )),
% 9.02/1.50    inference(superposition,[],[f32,f15])).
% 9.02/1.50  fof(f32,plain,(
% 9.02/1.50    ( ! [X2,X0,X3,X1] : (k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3)))) )),
% 9.02/1.50    inference(forward_demodulation,[],[f31,f20])).
% 9.02/1.50  fof(f31,plain,(
% 9.02/1.50    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3))) )),
% 9.02/1.50    inference(forward_demodulation,[],[f29,f20])).
% 9.02/1.50  fof(f29,plain,(
% 9.02/1.50    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3)) )),
% 9.02/1.50    inference(superposition,[],[f20,f20])).
% 9.02/1.50  fof(f22350,plain,(
% 9.02/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_4),
% 9.02/1.50    inference(forward_demodulation,[],[f22341,f20])).
% 9.02/1.50  fof(f22341,plain,(
% 9.02/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_4),
% 9.02/1.50    inference(backward_demodulation,[],[f2523,f22152])).
% 9.02/1.50  fof(f22152,plain,(
% 9.02/1.50    ( ! [X333,X331,X332] : (k4_xboole_0(X333,k2_xboole_0(X331,X332)) = k4_xboole_0(k2_xboole_0(X333,k4_xboole_0(X332,X331)),k2_xboole_0(X331,X332))) )),
% 9.02/1.50    inference(superposition,[],[f18676,f2254])).
% 9.02/1.50  fof(f2254,plain,(
% 9.02/1.50    ( ! [X26,X25] : (k4_xboole_0(X26,X25) = k4_xboole_0(k2_xboole_0(X25,X26),X25)) )),
% 9.02/1.50    inference(forward_demodulation,[],[f2093,f340])).
% 9.02/1.50  fof(f340,plain,(
% 9.02/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X0))) = X2) )),
% 9.02/1.50    inference(forward_demodulation,[],[f308,f17])).
% 9.02/1.50  fof(f308,plain,(
% 9.02/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1)))) = X2) )),
% 9.02/1.50    inference(superposition,[],[f238,f20])).
% 9.02/1.50  fof(f2093,plain,(
% 9.02/1.50    ( ! [X26,X25] : (k4_xboole_0(k2_xboole_0(X25,X26),X25) = k4_xboole_0(k4_xboole_0(X26,k4_xboole_0(X26,k2_xboole_0(X25,X26))),X25)) )),
% 9.02/1.50    inference(superposition,[],[f37,f1327])).
% 9.02/1.50  fof(f1327,plain,(
% 9.02/1.50    ( ! [X26,X27] : (k2_xboole_0(k4_xboole_0(k2_xboole_0(X26,X27),X27),X26) = X26) )),
% 9.02/1.50    inference(superposition,[],[f759,f345])).
% 9.02/1.50  fof(f345,plain,(
% 9.02/1.50    ( ! [X0,X1] : (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X0),X0)) = X1) )),
% 9.02/1.50    inference(superposition,[],[f197,f15])).
% 9.02/1.50  fof(f197,plain,(
% 9.02/1.50    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(k2_xboole_0(X4,X3),X4)) = X3) )),
% 9.02/1.50    inference(superposition,[],[f180,f30])).
% 9.02/1.50  fof(f759,plain,(
% 9.02/1.50    ( ! [X56,X55] : (k2_xboole_0(X56,X55) = k2_xboole_0(X55,k2_xboole_0(X56,X55))) )),
% 9.02/1.50    inference(forward_demodulation,[],[f735,f238])).
% 9.02/1.50  fof(f735,plain,(
% 9.02/1.50    ( ! [X57,X56,X55] : (k2_xboole_0(X56,X55) = k2_xboole_0(k4_xboole_0(X55,k4_xboole_0(X57,X57)),k2_xboole_0(X56,X55))) )),
% 9.02/1.50    inference(superposition,[],[f105,f241])).
% 9.02/1.50  fof(f105,plain,(
% 9.02/1.50    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X3)),X3) = X3) )),
% 9.02/1.50    inference(superposition,[],[f100,f22])).
% 9.02/1.50  fof(f100,plain,(
% 9.02/1.50    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2) )),
% 9.02/1.50    inference(superposition,[],[f55,f17])).
% 9.02/1.50  fof(f55,plain,(
% 9.02/1.50    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2) )),
% 9.02/1.50    inference(superposition,[],[f23,f15])).
% 9.02/1.50  fof(f37,plain,(
% 9.02/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) )),
% 9.02/1.50    inference(superposition,[],[f20,f22])).
% 9.02/1.50  fof(f18676,plain,(
% 9.02/1.50    ( ! [X210,X211,X209] : (k4_xboole_0(X209,X210) = k4_xboole_0(k2_xboole_0(X209,k4_xboole_0(X210,X211)),X210)) )),
% 9.02/1.50    inference(forward_demodulation,[],[f18510,f2254])).
% 9.02/1.50  fof(f18510,plain,(
% 9.02/1.50    ( ! [X210,X211,X209] : (k4_xboole_0(k2_xboole_0(X209,k4_xboole_0(X210,X211)),X210) = k4_xboole_0(k2_xboole_0(X210,X209),X210)) )),
% 9.02/1.50    inference(superposition,[],[f2243,f4611])).
% 9.02/1.50  fof(f4611,plain,(
% 9.02/1.50    ( ! [X130,X128,X129] : (k2_xboole_0(k2_xboole_0(X129,k4_xboole_0(X128,X130)),X128) = k2_xboole_0(X128,X129)) )),
% 9.02/1.50    inference(forward_demodulation,[],[f4466,f4610])).
% 9.02/1.50  fof(f4610,plain,(
% 9.02/1.50    ( ! [X127,X125,X126] : (k2_xboole_0(k4_xboole_0(X127,k4_xboole_0(X127,k4_xboole_0(X125,X126))),k2_xboole_0(X126,k4_xboole_0(X125,X127))) = k2_xboole_0(X125,X126)) )),
% 9.02/1.50    inference(forward_demodulation,[],[f4465,f2912])).
% 9.02/1.50  fof(f2912,plain,(
% 9.02/1.50    ( ! [X70,X72,X71] : (k2_xboole_0(X71,X70) = k2_xboole_0(X71,k2_xboole_0(X70,k4_xboole_0(X71,X72)))) )),
% 9.02/1.50    inference(forward_demodulation,[],[f2866,f170])).
% 9.02/1.50  fof(f170,plain,(
% 9.02/1.50    ( ! [X35,X33,X34] : (k2_xboole_0(X33,k4_xboole_0(X35,k4_xboole_0(X33,X34))) = k2_xboole_0(X33,X35)) )),
% 9.02/1.50    inference(forward_demodulation,[],[f156,f17])).
% 9.02/1.50  fof(f156,plain,(
% 9.02/1.50    ( ! [X35,X33,X34] : (k2_xboole_0(X33,k4_xboole_0(X35,k4_xboole_0(X33,X34))) = k2_xboole_0(X33,k4_xboole_0(X35,X33))) )),
% 9.02/1.50    inference(superposition,[],[f30,f100])).
% 9.02/1.50  fof(f2866,plain,(
% 9.02/1.50    ( ! [X70,X72,X71] : (k2_xboole_0(X71,k2_xboole_0(X70,k4_xboole_0(X71,X72))) = k2_xboole_0(X71,k4_xboole_0(X70,k4_xboole_0(X71,X72)))) )),
% 9.02/1.50    inference(superposition,[],[f170,f2243])).
% 9.02/1.50  fof(f4465,plain,(
% 9.02/1.50    ( ! [X127,X125,X126] : (k2_xboole_0(X125,k2_xboole_0(X126,k4_xboole_0(X125,X127))) = k2_xboole_0(k4_xboole_0(X127,k4_xboole_0(X127,k4_xboole_0(X125,X126))),k2_xboole_0(X126,k4_xboole_0(X125,X127)))) )),
% 9.02/1.50    inference(superposition,[],[f2247,f161])).
% 9.02/1.50  fof(f161,plain,(
% 9.02/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2)))) )),
% 9.02/1.50    inference(backward_demodulation,[],[f43,f148])).
% 9.02/1.50  fof(f43,plain,(
% 9.02/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))))) )),
% 9.02/1.50    inference(forward_demodulation,[],[f34,f20])).
% 9.02/1.50  fof(f34,plain,(
% 9.02/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2)))) )),
% 9.02/1.50    inference(superposition,[],[f22,f20])).
% 9.02/1.50  fof(f2247,plain,(
% 9.02/1.50    ( ! [X41,X40] : (k2_xboole_0(X41,X40) = k2_xboole_0(k4_xboole_0(X41,X40),X40)) )),
% 9.02/1.50    inference(backward_demodulation,[],[f756,f2243])).
% 9.02/1.50  fof(f756,plain,(
% 9.02/1.50    ( ! [X41,X40] : (k2_xboole_0(X41,X40) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X41,X40),X40),X40)) )),
% 9.02/1.50    inference(forward_demodulation,[],[f730,f238])).
% 9.02/1.50  fof(f730,plain,(
% 9.02/1.50    ( ! [X41,X42,X40] : (k2_xboole_0(X41,X40) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X41,X40),X40),k4_xboole_0(X40,k4_xboole_0(X42,X42)))) )),
% 9.02/1.50    inference(superposition,[],[f70,f241])).
% 9.02/1.50  fof(f4466,plain,(
% 9.02/1.50    ( ! [X130,X128,X129] : (k2_xboole_0(k2_xboole_0(X129,k4_xboole_0(X128,X130)),X128) = k2_xboole_0(k4_xboole_0(X130,k4_xboole_0(X130,k4_xboole_0(X128,X129))),k2_xboole_0(X129,k4_xboole_0(X128,X130)))) )),
% 9.02/1.50    inference(superposition,[],[f2260,f161])).
% 9.02/1.50  fof(f2260,plain,(
% 9.02/1.50    ( ! [X47,X48] : (k2_xboole_0(X47,X48) = k2_xboole_0(k4_xboole_0(X48,X47),X47)) )),
% 9.02/1.50    inference(backward_demodulation,[],[f1026,f2254])).
% 9.02/1.50  fof(f1026,plain,(
% 9.02/1.50    ( ! [X47,X48] : (k2_xboole_0(X47,X48) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X47,X48),X47),X47)) )),
% 9.02/1.50    inference(forward_demodulation,[],[f1001,f238])).
% 9.02/1.50  fof(f1001,plain,(
% 9.02/1.50    ( ! [X47,X48,X49] : (k2_xboole_0(X47,X48) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X47,X48),X47),k4_xboole_0(X47,k4_xboole_0(X49,X49)))) )),
% 9.02/1.50    inference(superposition,[],[f70,f673])).
% 9.02/1.50  fof(f2243,plain,(
% 9.02/1.50    ( ! [X24,X23] : (k4_xboole_0(X23,X24) = k4_xboole_0(k2_xboole_0(X23,X24),X24)) )),
% 9.02/1.50    inference(forward_demodulation,[],[f2092,f844])).
% 9.02/1.50  fof(f844,plain,(
% 9.02/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X1,X0))) = X2) )),
% 9.02/1.50    inference(superposition,[],[f340,f15])).
% 9.02/1.50  fof(f2092,plain,(
% 9.02/1.50    ( ! [X24,X23] : (k4_xboole_0(k2_xboole_0(X23,X24),X24) = k4_xboole_0(k4_xboole_0(X23,k4_xboole_0(X23,k2_xboole_0(X23,X24))),X24)) )),
% 9.02/1.50    inference(superposition,[],[f37,f1326])).
% 9.02/1.50  fof(f1326,plain,(
% 9.02/1.50    ( ! [X24,X25] : (k2_xboole_0(k4_xboole_0(k2_xboole_0(X25,X24),X25),X24) = X24) )),
% 9.02/1.50    inference(superposition,[],[f759,f197])).
% 9.02/1.50  fof(f2523,plain,(
% 9.02/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_4),
% 9.02/1.50    inference(avatar_component_clause,[],[f2521])).
% 9.02/1.50  fof(f22349,plain,(
% 9.02/1.50    ~spl2_5 | spl2_3),
% 9.02/1.50    inference(avatar_split_clause,[],[f22344,f2515,f22346])).
% 9.02/1.50  fof(f22346,plain,(
% 9.02/1.50    spl2_5 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)))),
% 9.02/1.50    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 9.02/1.50  fof(f2515,plain,(
% 9.02/1.50    spl2_3 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)))),
% 9.02/1.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 9.02/1.50  fof(f22344,plain,(
% 9.02/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))) | spl2_3),
% 9.02/1.50    inference(forward_demodulation,[],[f22343,f84])).
% 9.02/1.50  fof(f22343,plain,(
% 9.02/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k2_xboole_0(sK0,k2_xboole_0(sK1,sK1)))) | spl2_3),
% 9.02/1.50    inference(forward_demodulation,[],[f22342,f394])).
% 9.02/1.50  fof(f22342,plain,(
% 9.02/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1)))) | spl2_3),
% 9.02/1.50    inference(forward_demodulation,[],[f22340,f20])).
% 9.02/1.50  fof(f22340,plain,(
% 9.02/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))) | spl2_3),
% 9.02/1.50    inference(backward_demodulation,[],[f2517,f22152])).
% 9.02/1.50  fof(f2517,plain,(
% 9.02/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) | spl2_3),
% 9.02/1.50    inference(avatar_component_clause,[],[f2515])).
% 9.02/1.50  fof(f2524,plain,(
% 9.02/1.50    ~spl2_4 | spl2_1),
% 9.02/1.50    inference(avatar_split_clause,[],[f2519,f25,f2521])).
% 9.02/1.50  fof(f25,plain,(
% 9.02/1.50    spl2_1 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 9.02/1.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 9.02/1.50  fof(f2519,plain,(
% 9.02/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_1),
% 9.02/1.50    inference(forward_demodulation,[],[f2512,f22])).
% 9.02/1.50  fof(f2512,plain,(
% 9.02/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) | spl2_1),
% 9.02/1.50    inference(backward_demodulation,[],[f27,f2439])).
% 9.02/1.50  fof(f2439,plain,(
% 9.02/1.50    ( ! [X10,X11,X9] : (k4_xboole_0(X10,X11) = k4_xboole_0(k2_xboole_0(X9,X10),k2_xboole_0(k4_xboole_0(X9,X10),X11))) )),
% 9.02/1.50    inference(superposition,[],[f20,f2245])).
% 9.02/1.50  fof(f2245,plain,(
% 9.02/1.50    ( ! [X19,X20] : (k4_xboole_0(k2_xboole_0(X19,X20),k4_xboole_0(X19,X20)) = X20) )),
% 9.02/1.50    inference(backward_demodulation,[],[f533,f2243])).
% 9.02/1.50  fof(f533,plain,(
% 9.02/1.50    ( ! [X19,X20] : (k4_xboole_0(k2_xboole_0(X19,X20),k4_xboole_0(k2_xboole_0(X19,X20),X20)) = X20) )),
% 9.02/1.50    inference(superposition,[],[f213,f50])).
% 9.02/1.50  fof(f213,plain,(
% 9.02/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X0))) = X2) )),
% 9.02/1.50    inference(forward_demodulation,[],[f195,f17])).
% 9.02/1.50  fof(f195,plain,(
% 9.02/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1)))) = X2) )),
% 9.02/1.50    inference(superposition,[],[f180,f20])).
% 9.02/1.50  fof(f27,plain,(
% 9.02/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl2_1),
% 9.02/1.50    inference(avatar_component_clause,[],[f25])).
% 9.02/1.50  fof(f2518,plain,(
% 9.02/1.50    ~spl2_3 | spl2_2),
% 9.02/1.50    inference(avatar_split_clause,[],[f2513,f143,f2515])).
% 9.02/1.50  fof(f143,plain,(
% 9.02/1.50    spl2_2 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)))),
% 9.02/1.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 9.02/1.50  fof(f2513,plain,(
% 9.02/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) | spl2_2),
% 9.02/1.50    inference(forward_demodulation,[],[f2511,f22])).
% 9.02/1.50  fof(f2511,plain,(
% 9.02/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) | spl2_2),
% 9.02/1.50    inference(backward_demodulation,[],[f145,f2439])).
% 9.02/1.50  fof(f145,plain,(
% 9.02/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) | spl2_2),
% 9.02/1.50    inference(avatar_component_clause,[],[f143])).
% 9.02/1.50  fof(f147,plain,(
% 9.02/1.50    ~spl2_2 | spl2_1),
% 9.02/1.50    inference(avatar_split_clause,[],[f141,f25,f143])).
% 9.02/1.50  fof(f141,plain,(
% 9.02/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) | spl2_1),
% 9.02/1.50    inference(superposition,[],[f27,f15])).
% 9.02/1.50  fof(f146,plain,(
% 9.02/1.50    ~spl2_2 | spl2_1),
% 9.02/1.50    inference(avatar_split_clause,[],[f140,f25,f143])).
% 9.02/1.50  fof(f140,plain,(
% 9.02/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) | spl2_1),
% 9.02/1.50    inference(superposition,[],[f27,f15])).
% 9.02/1.50  fof(f28,plain,(
% 9.02/1.50    ~spl2_1),
% 9.02/1.50    inference(avatar_split_clause,[],[f21,f25])).
% 9.02/1.50  fof(f21,plain,(
% 9.02/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 9.02/1.50    inference(definition_unfolding,[],[f13,f16,f19,f19])).
% 9.02/1.50  fof(f19,plain,(
% 9.02/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 9.02/1.50    inference(cnf_transformation,[],[f3])).
% 9.02/1.50  fof(f3,axiom,(
% 9.02/1.50    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 9.02/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 9.02/1.50  fof(f13,plain,(
% 9.02/1.50    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 9.02/1.50    inference(cnf_transformation,[],[f12])).
% 9.02/1.50  fof(f12,plain,(
% 9.02/1.50    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 9.02/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).
% 9.02/1.50  fof(f11,plain,(
% 9.02/1.50    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 9.02/1.50    introduced(choice_axiom,[])).
% 9.02/1.50  fof(f10,plain,(
% 9.02/1.50    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 9.02/1.50    inference(ennf_transformation,[],[f9])).
% 9.02/1.50  fof(f9,negated_conjecture,(
% 9.02/1.50    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 9.02/1.50    inference(negated_conjecture,[],[f8])).
% 9.02/1.50  fof(f8,conjecture,(
% 9.02/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 9.02/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 9.02/1.50  % SZS output end Proof for theBenchmark
% 9.02/1.50  % (12079)------------------------------
% 9.02/1.50  % (12079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.02/1.50  % (12079)Termination reason: Refutation
% 9.02/1.50  
% 9.02/1.50  % (12079)Memory used [KB]: 24306
% 9.02/1.50  % (12079)Time elapsed: 1.075 s
% 9.02/1.50  % (12079)------------------------------
% 9.02/1.50  % (12079)------------------------------
% 9.02/1.51  % (12061)Success in time 1.154 s
%------------------------------------------------------------------------------
