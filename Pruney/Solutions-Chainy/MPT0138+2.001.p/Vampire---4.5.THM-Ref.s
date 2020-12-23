%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:09 EST 2020

% Result     : Theorem 2.23s
% Output     : Refutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 253 expanded)
%              Number of leaves         :   13 (  87 expanded)
%              Depth                    :   19
%              Number of atoms          :   68 ( 260 expanded)
%              Number of equality atoms :   59 ( 250 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1142,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f1132])).

fof(f1132,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f1131])).

fof(f1131,plain,
    ( $false
    | spl6_1 ),
    inference(trivial_inequality_removal,[],[f1130])).

fof(f1130,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl6_1 ),
    inference(backward_demodulation,[],[f124,f1129])).

fof(f1129,plain,(
    ! [X132,X130,X128,X131,X129] : k5_xboole_0(k4_xboole_0(k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),X130)),X129),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X128,X129),X130),X131),X132)) = k4_xboole_0(k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(k5_xboole_0(X132,k4_xboole_0(X128,X132)),X131)),X130)),X129) ),
    inference(forward_demodulation,[],[f1128,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),X0)) ),
    inference(backward_demodulation,[],[f41,f100])).

fof(f100,plain,(
    ! [X6,X8,X7] : k4_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(X6,X7)) = k4_xboole_0(k4_xboole_0(X8,X7),X6) ),
    inference(forward_demodulation,[],[f95,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f26,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f95,plain,(
    ! [X6,X8,X7] : k4_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(X6,X7)) = k4_xboole_0(X8,k5_xboole_0(X7,k4_xboole_0(X6,X7))) ),
    inference(superposition,[],[f40,f62])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X0) = k4_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f40,f38])).

fof(f38,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f20,f23])).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f27,f23,f23])).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f1128,plain,(
    ! [X132,X130,X128,X131,X129] : k5_xboole_0(k4_xboole_0(k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),X130)),X129),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X128,X129),X130),X131),X132)) = k4_xboole_0(k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k5_xboole_0(k4_xboole_0(X132,X131),k4_xboole_0(k4_xboole_0(X128,X131),X132))),X130)),X129) ),
    inference(forward_demodulation,[],[f1127,f40])).

fof(f1127,plain,(
    ! [X132,X130,X128,X131,X129] : k5_xboole_0(k4_xboole_0(k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),X130)),X129),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X128,X129),X130),X131),X132)) = k4_xboole_0(k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k5_xboole_0(k4_xboole_0(X132,X131),k4_xboole_0(X128,k5_xboole_0(X131,k4_xboole_0(X132,X131))))),X130)),X129) ),
    inference(forward_demodulation,[],[f1126,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1126,plain,(
    ! [X132,X130,X128,X131,X129] : k5_xboole_0(k4_xboole_0(k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),X130)),X129),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X128,X129),X130),X131),X132)) = k4_xboole_0(k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),k4_xboole_0(X128,k5_xboole_0(X131,k4_xboole_0(X132,X131)))),X130)),X129) ),
    inference(forward_demodulation,[],[f1125,f103])).

fof(f1125,plain,(
    ! [X132,X130,X128,X131,X129] : k5_xboole_0(k4_xboole_0(k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),X130)),X129),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X128,X129),X130),X131),X132)) = k4_xboole_0(k5_xboole_0(X130,k5_xboole_0(k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),X130),k4_xboole_0(k4_xboole_0(X128,X130),k5_xboole_0(X131,k4_xboole_0(X132,X131))))),X129) ),
    inference(forward_demodulation,[],[f1124,f40])).

fof(f1124,plain,(
    ! [X132,X130,X128,X131,X129] : k5_xboole_0(k4_xboole_0(k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),X130)),X129),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X128,X129),X130),X131),X132)) = k4_xboole_0(k5_xboole_0(X130,k5_xboole_0(k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),X130),k4_xboole_0(X128,k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),X130))))),X129) ),
    inference(forward_demodulation,[],[f1001,f25])).

fof(f1001,plain,(
    ! [X132,X130,X128,X131,X129] : k4_xboole_0(k5_xboole_0(k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),X130)),k4_xboole_0(X128,k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),X130)))),X129) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),X130)),X129),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X128,X129),X130),X131),X132)) ),
    inference(superposition,[],[f103,f105])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0) = k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1))) ),
    inference(backward_demodulation,[],[f70,f103])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0) ),
    inference(forward_demodulation,[],[f69,f40])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))),X0) = k4_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) ),
    inference(forward_demodulation,[],[f61,f25])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))),X0) = k4_xboole_0(X3,k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(superposition,[],[f40,f40])).

fof(f124,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3))))
    | spl6_1 ),
    inference(superposition,[],[f88,f25])).

fof(f88,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl6_1
  <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f89,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f45,f86])).

fof(f45,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3))) ),
    inference(forward_demodulation,[],[f44,f40])).

fof(f44,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK0)),k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))))) ),
    inference(forward_demodulation,[],[f43,f40])).

fof(f43,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK0)),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))))) ),
    inference(backward_demodulation,[],[f37,f40])).

fof(f37,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))))) ),
    inference(definition_unfolding,[],[f19,f36,f23,f34,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f28,f23,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f24,f23,f32])).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f31,f23,f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f29,f23,f34])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(f19,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))
   => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:32:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.42  % (14226)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.42  % (14226)Refutation not found, incomplete strategy% (14226)------------------------------
% 0.21/0.42  % (14226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (14226)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.42  
% 0.21/0.42  % (14226)Memory used [KB]: 10618
% 0.21/0.42  % (14226)Time elapsed: 0.004 s
% 0.21/0.42  % (14226)------------------------------
% 0.21/0.42  % (14226)------------------------------
% 0.21/0.45  % (14228)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  % (14215)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (14216)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (14221)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (14218)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (14230)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (14220)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (14219)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (14222)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (14231)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (14223)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (14224)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (14227)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (14229)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (14217)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (14225)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (14232)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 2.23/0.64  % (14230)Refutation found. Thanks to Tanya!
% 2.23/0.64  % SZS status Theorem for theBenchmark
% 2.23/0.64  % SZS output start Proof for theBenchmark
% 2.23/0.64  fof(f1142,plain,(
% 2.23/0.64    $false),
% 2.23/0.64    inference(avatar_sat_refutation,[],[f89,f1132])).
% 2.23/0.64  fof(f1132,plain,(
% 2.23/0.64    spl6_1),
% 2.23/0.64    inference(avatar_contradiction_clause,[],[f1131])).
% 2.23/0.64  fof(f1131,plain,(
% 2.23/0.64    $false | spl6_1),
% 2.23/0.64    inference(trivial_inequality_removal,[],[f1130])).
% 2.23/0.64  fof(f1130,plain,(
% 2.23/0.64    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) | spl6_1),
% 2.23/0.64    inference(backward_demodulation,[],[f124,f1129])).
% 2.23/0.64  fof(f1129,plain,(
% 2.23/0.64    ( ! [X132,X130,X128,X131,X129] : (k5_xboole_0(k4_xboole_0(k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),X130)),X129),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X128,X129),X130),X131),X132)) = k4_xboole_0(k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(k5_xboole_0(X132,k4_xboole_0(X128,X132)),X131)),X130)),X129)) )),
% 2.23/0.64    inference(forward_demodulation,[],[f1128,f103])).
% 2.23/0.64  fof(f103,plain,(
% 2.23/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),X0))) )),
% 2.23/0.64    inference(backward_demodulation,[],[f41,f100])).
% 2.23/0.64  fof(f100,plain,(
% 2.23/0.64    ( ! [X6,X8,X7] : (k4_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(X6,X7)) = k4_xboole_0(k4_xboole_0(X8,X7),X6)) )),
% 2.23/0.64    inference(forward_demodulation,[],[f95,f40])).
% 2.23/0.64  fof(f40,plain,(
% 2.23/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 2.23/0.64    inference(definition_unfolding,[],[f26,f23])).
% 2.23/0.64  fof(f23,plain,(
% 2.23/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.23/0.64    inference(cnf_transformation,[],[f6])).
% 2.23/0.64  fof(f6,axiom,(
% 2.23/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.23/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.23/0.64  fof(f26,plain,(
% 2.23/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.23/0.64    inference(cnf_transformation,[],[f3])).
% 2.23/0.64  fof(f3,axiom,(
% 2.23/0.64    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.23/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.23/0.64  fof(f95,plain,(
% 2.23/0.64    ( ! [X6,X8,X7] : (k4_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(X6,X7)) = k4_xboole_0(X8,k5_xboole_0(X7,k4_xboole_0(X6,X7)))) )),
% 2.23/0.64    inference(superposition,[],[f40,f62])).
% 2.23/0.64  fof(f62,plain,(
% 2.23/0.64    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k4_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 2.23/0.64    inference(superposition,[],[f40,f38])).
% 2.23/0.64  fof(f38,plain,(
% 2.23/0.64    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 2.23/0.64    inference(definition_unfolding,[],[f20,f23])).
% 2.23/0.64  fof(f20,plain,(
% 2.23/0.64    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.23/0.64    inference(cnf_transformation,[],[f15])).
% 2.23/0.64  fof(f15,plain,(
% 2.23/0.64    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.23/0.64    inference(rectify,[],[f2])).
% 2.23/0.64  fof(f2,axiom,(
% 2.23/0.64    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.23/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.23/0.64  fof(f41,plain,(
% 2.23/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2)))) )),
% 2.23/0.64    inference(definition_unfolding,[],[f27,f23,f23])).
% 2.23/0.64  fof(f27,plain,(
% 2.23/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 2.23/0.64    inference(cnf_transformation,[],[f4])).
% 2.23/0.64  fof(f4,axiom,(
% 2.23/0.64    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 2.23/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).
% 2.23/0.64  fof(f1128,plain,(
% 2.23/0.64    ( ! [X132,X130,X128,X131,X129] : (k5_xboole_0(k4_xboole_0(k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),X130)),X129),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X128,X129),X130),X131),X132)) = k4_xboole_0(k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k5_xboole_0(k4_xboole_0(X132,X131),k4_xboole_0(k4_xboole_0(X128,X131),X132))),X130)),X129)) )),
% 2.23/0.64    inference(forward_demodulation,[],[f1127,f40])).
% 2.23/0.64  fof(f1127,plain,(
% 2.23/0.64    ( ! [X132,X130,X128,X131,X129] : (k5_xboole_0(k4_xboole_0(k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),X130)),X129),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X128,X129),X130),X131),X132)) = k4_xboole_0(k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k5_xboole_0(k4_xboole_0(X132,X131),k4_xboole_0(X128,k5_xboole_0(X131,k4_xboole_0(X132,X131))))),X130)),X129)) )),
% 2.23/0.64    inference(forward_demodulation,[],[f1126,f25])).
% 2.23/0.64  fof(f25,plain,(
% 2.23/0.64    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.23/0.64    inference(cnf_transformation,[],[f5])).
% 2.23/0.64  fof(f5,axiom,(
% 2.23/0.64    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.23/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.23/0.64  fof(f1126,plain,(
% 2.23/0.64    ( ! [X132,X130,X128,X131,X129] : (k5_xboole_0(k4_xboole_0(k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),X130)),X129),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X128,X129),X130),X131),X132)) = k4_xboole_0(k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),k4_xboole_0(X128,k5_xboole_0(X131,k4_xboole_0(X132,X131)))),X130)),X129)) )),
% 2.23/0.64    inference(forward_demodulation,[],[f1125,f103])).
% 2.23/0.64  fof(f1125,plain,(
% 2.23/0.64    ( ! [X132,X130,X128,X131,X129] : (k5_xboole_0(k4_xboole_0(k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),X130)),X129),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X128,X129),X130),X131),X132)) = k4_xboole_0(k5_xboole_0(X130,k5_xboole_0(k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),X130),k4_xboole_0(k4_xboole_0(X128,X130),k5_xboole_0(X131,k4_xboole_0(X132,X131))))),X129)) )),
% 2.23/0.64    inference(forward_demodulation,[],[f1124,f40])).
% 2.23/0.64  fof(f1124,plain,(
% 2.23/0.64    ( ! [X132,X130,X128,X131,X129] : (k5_xboole_0(k4_xboole_0(k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),X130)),X129),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X128,X129),X130),X131),X132)) = k4_xboole_0(k5_xboole_0(X130,k5_xboole_0(k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),X130),k4_xboole_0(X128,k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),X130))))),X129)) )),
% 2.23/0.64    inference(forward_demodulation,[],[f1001,f25])).
% 2.23/0.64  fof(f1001,plain,(
% 2.23/0.64    ( ! [X132,X130,X128,X131,X129] : (k4_xboole_0(k5_xboole_0(k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),X130)),k4_xboole_0(X128,k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),X130)))),X129) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X130,k4_xboole_0(k5_xboole_0(X131,k4_xboole_0(X132,X131)),X130)),X129),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X128,X129),X130),X131),X132))) )),
% 2.23/0.64    inference(superposition,[],[f103,f105])).
% 2.23/0.64  fof(f105,plain,(
% 2.23/0.64    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0) = k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X0,X2)),X1)))) )),
% 2.23/0.64    inference(backward_demodulation,[],[f70,f103])).
% 2.23/0.64  fof(f70,plain,(
% 2.23/0.64    ( ! [X2,X0,X3,X1] : (k4_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X1),X2),X0)) )),
% 2.23/0.64    inference(forward_demodulation,[],[f69,f40])).
% 2.23/0.64  fof(f69,plain,(
% 2.23/0.64    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))),X0) = k4_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))))) )),
% 2.23/0.64    inference(forward_demodulation,[],[f61,f25])).
% 2.23/0.64  fof(f61,plain,(
% 2.23/0.64    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))),X0) = k4_xboole_0(X3,k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) )),
% 2.23/0.64    inference(superposition,[],[f40,f40])).
% 2.23/0.64  fof(f124,plain,(
% 2.23/0.64    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)))) | spl6_1),
% 2.23/0.64    inference(superposition,[],[f88,f25])).
% 2.23/0.64  fof(f88,plain,(
% 2.23/0.64    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3))) | spl6_1),
% 2.23/0.64    inference(avatar_component_clause,[],[f86])).
% 2.23/0.64  fof(f86,plain,(
% 2.23/0.64    spl6_1 <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)))),
% 2.23/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.23/0.64  fof(f89,plain,(
% 2.23/0.64    ~spl6_1),
% 2.23/0.64    inference(avatar_split_clause,[],[f45,f86])).
% 2.23/0.64  fof(f45,plain,(
% 2.23/0.64    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)))),
% 2.23/0.64    inference(forward_demodulation,[],[f44,f40])).
% 2.23/0.64  fof(f44,plain,(
% 2.23/0.64    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK0)),k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2)))))),
% 2.23/0.64    inference(forward_demodulation,[],[f43,f40])).
% 2.23/0.64  fof(f43,plain,(
% 2.23/0.64    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK0)),k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1)))))),
% 2.23/0.64    inference(backward_demodulation,[],[f37,f40])).
% 2.23/0.64  fof(f37,plain,(
% 2.23/0.64    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k5_xboole_0(k1_tarski(sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k1_tarski(sK3))),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))))),
% 2.23/0.64    inference(definition_unfolding,[],[f19,f36,f23,f34,f32])).
% 2.23/0.64  fof(f32,plain,(
% 2.23/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))) )),
% 2.23/0.64    inference(definition_unfolding,[],[f22,f23])).
% 2.23/0.64  fof(f22,plain,(
% 2.23/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 2.23/0.64    inference(cnf_transformation,[],[f7])).
% 2.23/0.64  fof(f7,axiom,(
% 2.23/0.64    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 2.23/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 2.23/0.64  fof(f34,plain,(
% 2.23/0.64    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0)))) )),
% 2.23/0.64    inference(definition_unfolding,[],[f28,f23,f33])).
% 2.23/0.64  fof(f33,plain,(
% 2.23/0.64    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0)))) )),
% 2.23/0.64    inference(definition_unfolding,[],[f24,f23,f32])).
% 2.23/0.64  fof(f24,plain,(
% 2.23/0.64    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 2.23/0.64    inference(cnf_transformation,[],[f8])).
% 2.23/0.64  fof(f8,axiom,(
% 2.23/0.64    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 2.23/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 2.23/0.64  fof(f28,plain,(
% 2.23/0.64    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 2.23/0.64    inference(cnf_transformation,[],[f9])).
% 2.23/0.64  fof(f9,axiom,(
% 2.23/0.64    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 2.23/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 2.23/0.64  fof(f36,plain,(
% 2.23/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0)))) )),
% 2.23/0.64    inference(definition_unfolding,[],[f31,f23,f35])).
% 2.23/0.64  fof(f35,plain,(
% 2.23/0.64    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))),k1_tarski(X0)))) )),
% 2.23/0.64    inference(definition_unfolding,[],[f29,f23,f34])).
% 2.23/0.64  fof(f29,plain,(
% 2.23/0.64    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 2.23/0.64    inference(cnf_transformation,[],[f10])).
% 2.23/0.64  fof(f10,axiom,(
% 2.23/0.64    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 2.23/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 2.23/0.64  fof(f31,plain,(
% 2.23/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 2.23/0.64    inference(cnf_transformation,[],[f12])).
% 2.23/0.64  fof(f12,axiom,(
% 2.23/0.64    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 2.23/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).
% 2.23/0.64  fof(f19,plain,(
% 2.23/0.64    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5))),
% 2.23/0.64    inference(cnf_transformation,[],[f18])).
% 2.23/0.64  fof(f18,plain,(
% 2.23/0.64    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5))),
% 2.23/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f16,f17])).
% 2.23/0.64  fof(f17,plain,(
% 2.23/0.64    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5))),
% 2.23/0.64    introduced(choice_axiom,[])).
% 2.23/0.64  fof(f16,plain,(
% 2.23/0.64    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 2.23/0.64    inference(ennf_transformation,[],[f14])).
% 2.23/0.64  fof(f14,negated_conjecture,(
% 2.23/0.64    ~! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 2.23/0.64    inference(negated_conjecture,[],[f13])).
% 2.23/0.64  fof(f13,conjecture,(
% 2.23/0.64    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 2.23/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).
% 2.23/0.64  % SZS output end Proof for theBenchmark
% 2.23/0.64  % (14230)------------------------------
% 2.23/0.64  % (14230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.23/0.64  % (14230)Termination reason: Refutation
% 2.23/0.64  
% 2.23/0.64  % (14230)Memory used [KB]: 13432
% 2.23/0.64  % (14230)Time elapsed: 0.211 s
% 2.23/0.64  % (14230)------------------------------
% 2.23/0.64  % (14230)------------------------------
% 2.23/0.65  % (14214)Success in time 0.289 s
%------------------------------------------------------------------------------
