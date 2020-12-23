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
% DateTime   : Thu Dec  3 12:32:07 EST 2020

% Result     : Theorem 20.29s
% Output     : Refutation 20.29s
% Verified   : 
% Statistics : Number of formulae       :  102 (1203 expanded)
%              Number of leaves         :   14 ( 402 expanded)
%              Depth                    :   24
%              Number of atoms          :  109 (1211 expanded)
%              Number of equality atoms :   97 (1198 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53699,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f81,f86,f53529])).

fof(f53529,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f53528])).

fof(f53528,plain,
    ( $false
    | spl2_1 ),
    inference(trivial_inequality_removal,[],[f53527])).

fof(f53527,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1)
    | spl2_1 ),
    inference(superposition,[],[f35,f52743])).

fof(f52743,plain,(
    ! [X8,X7] : k2_xboole_0(X7,X8) = k5_xboole_0(X7,k4_xboole_0(X8,X7)) ),
    inference(forward_demodulation,[],[f52742,f37755])).

fof(f37755,plain,(
    ! [X39,X40] : k2_xboole_0(X39,X40) = k2_xboole_0(k2_xboole_0(X39,X40),k5_xboole_0(X39,k4_xboole_0(X40,X39))) ),
    inference(forward_demodulation,[],[f37398,f206])).

fof(f206,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f200,f21])).

fof(f21,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f200,plain,(
    ! [X2] : k5_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f61,f182])).

fof(f182,plain,(
    ! [X7] : k1_xboole_0 = k3_xboole_0(X7,k1_xboole_0) ),
    inference(superposition,[],[f170,f22])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f170,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
    inference(forward_demodulation,[],[f151,f23])).

fof(f23,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f151,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
    inference(superposition,[],[f30,f47])).

fof(f47,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f26,f22])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f61,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f27,f21])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f37398,plain,(
    ! [X39,X40] : k2_xboole_0(k2_xboole_0(X39,X40),k1_xboole_0) = k2_xboole_0(k2_xboole_0(X39,X40),k5_xboole_0(X39,k4_xboole_0(X40,X39))) ),
    inference(superposition,[],[f25,f23306])).

fof(f23306,plain,(
    ! [X6,X7] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X6,X7)),k2_xboole_0(X7,X6)) ),
    inference(forward_demodulation,[],[f23209,f17669])).

fof(f17669,plain,(
    ! [X10,X11] : k2_xboole_0(k4_xboole_0(X10,X11),X11) = k5_xboole_0(X11,k4_xboole_0(X10,X11)) ),
    inference(forward_demodulation,[],[f17601,f1350])).

fof(f1350,plain,(
    ! [X19,X18] : k5_xboole_0(X19,X18) = k5_xboole_0(k5_xboole_0(X18,X19),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1311,f37])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f24,f21])).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f1311,plain,(
    ! [X19,X18] : k5_xboole_0(k5_xboole_0(X18,X19),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X19,X18)) ),
    inference(superposition,[],[f1175,f1175])).

fof(f1175,plain,(
    ! [X28,X27] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X27,X28)) = k5_xboole_0(X28,X27) ),
    inference(superposition,[],[f133,f37])).

fof(f133,plain,(
    ! [X6,X7,X5] : k5_xboole_0(X7,k5_xboole_0(X5,X6)) = k5_xboole_0(X5,k5_xboole_0(X6,X7)) ),
    inference(superposition,[],[f29,f24])).

fof(f29,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f17601,plain,(
    ! [X10,X11] : k2_xboole_0(k4_xboole_0(X10,X11),X11) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X10,X11),X11),k1_xboole_0) ),
    inference(superposition,[],[f27,f17403])).

fof(f17403,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(forward_demodulation,[],[f17210,f198])).

fof(f198,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f182,f47])).

fof(f17210,plain,(
    ! [X0,X1] : k3_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f164,f207])).

fof(f207,plain,(
    ! [X3] : k2_xboole_0(X3,X3) = X3 ),
    inference(forward_demodulation,[],[f201,f206])).

fof(f201,plain,(
    ! [X3] : k2_xboole_0(X3,X3) = k2_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f53,f182])).

fof(f53,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f25,f47])).

fof(f164,plain,(
    ! [X6,X4,X5] : k3_xboole_0(k4_xboole_0(X4,X5),X6) = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,k2_xboole_0(X5,X6))) ),
    inference(superposition,[],[f26,f30])).

fof(f23209,plain,(
    ! [X6,X7] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(X6,X7),X7),k2_xboole_0(X7,X6)) ),
    inference(superposition,[],[f22873,f5134])).

fof(f5134,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X2,X1),k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f4983,f25])).

fof(f4983,plain,(
    ! [X8,X7] : k2_xboole_0(X8,X7) = k2_xboole_0(X7,k2_xboole_0(X8,X7)) ),
    inference(forward_demodulation,[],[f4982,f1837])).

fof(f1837,plain,(
    ! [X26,X25] : k2_xboole_0(X26,X25) = k5_xboole_0(k5_xboole_0(X26,k3_xboole_0(X26,X25)),X25) ),
    inference(forward_demodulation,[],[f1808,f206])).

fof(f1808,plain,(
    ! [X26,X25] : k5_xboole_0(k5_xboole_0(X26,k3_xboole_0(X26,X25)),X25) = k2_xboole_0(k2_xboole_0(X26,X25),k1_xboole_0) ),
    inference(superposition,[],[f912,f821])).

fof(f821,plain,(
    ! [X4,X3] : k2_xboole_0(X4,X3) = k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))) ),
    inference(superposition,[],[f62,f29])).

fof(f62,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f27,f24])).

fof(f912,plain,(
    ! [X19,X20] : k2_xboole_0(k5_xboole_0(X19,X20),k1_xboole_0) = k5_xboole_0(X20,X19) ),
    inference(forward_demodulation,[],[f911,f21])).

fof(f911,plain,(
    ! [X19,X20] : k2_xboole_0(k5_xboole_0(X19,X20),k1_xboole_0) = k5_xboole_0(X20,k5_xboole_0(X19,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f910,f182])).

fof(f910,plain,(
    ! [X19,X20] : k2_xboole_0(k5_xboole_0(X19,X20),k1_xboole_0) = k5_xboole_0(X20,k5_xboole_0(X19,k3_xboole_0(k5_xboole_0(X19,X20),k1_xboole_0))) ),
    inference(forward_demodulation,[],[f875,f47])).

fof(f875,plain,(
    ! [X19,X20] : k2_xboole_0(k5_xboole_0(X19,X20),k1_xboole_0) = k5_xboole_0(X20,k5_xboole_0(X19,k4_xboole_0(k5_xboole_0(X19,X20),k5_xboole_0(X19,X20)))) ),
    inference(superposition,[],[f123,f68])).

fof(f68,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f66,f21])).

fof(f66,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f27,f47])).

fof(f123,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(superposition,[],[f29,f24])).

fof(f4982,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,k3_xboole_0(X8,X7)),X7) = k2_xboole_0(X7,k2_xboole_0(X8,X7)) ),
    inference(forward_demodulation,[],[f4850,f4216])).

fof(f4216,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X5)) = k5_xboole_0(k5_xboole_0(X5,X5),k2_xboole_0(X6,X5)) ),
    inference(superposition,[],[f1837,f360])).

fof(f360,plain,(
    ! [X4,X5] : k3_xboole_0(X4,k2_xboole_0(X5,X4)) = X4 ),
    inference(forward_demodulation,[],[f356,f22])).

fof(f356,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k1_xboole_0) = k3_xboole_0(X4,k2_xboole_0(X5,X4)) ),
    inference(superposition,[],[f26,f220])).

fof(f220,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f213,f25])).

fof(f213,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,X3))) ),
    inference(superposition,[],[f198,f30])).

fof(f4850,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,k3_xboole_0(X8,X7)),X7) = k5_xboole_0(k5_xboole_0(X7,X7),k2_xboole_0(X8,X7)) ),
    inference(superposition,[],[f1180,f821])).

fof(f1180,plain,(
    ! [X43,X44] : k5_xboole_0(k5_xboole_0(X43,X43),k5_xboole_0(X43,X44)) = k5_xboole_0(X44,X43) ),
    inference(superposition,[],[f133,f239])).

fof(f239,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f233,f207])).

fof(f233,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k5_xboole_0(k5_xboole_0(X0,X0),X0) ),
    inference(superposition,[],[f27,f208])).

fof(f208,plain,(
    ! [X4] : k3_xboole_0(X4,X4) = X4 ),
    inference(forward_demodulation,[],[f202,f22])).

fof(f202,plain,(
    ! [X4] : k3_xboole_0(X4,X4) = k4_xboole_0(X4,k1_xboole_0) ),
    inference(superposition,[],[f52,f182])).

fof(f52,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f26,f47])).

fof(f22873,plain,(
    ! [X14,X15,X13] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X13,X14),k2_xboole_0(X13,k2_xboole_0(X14,X15))) ),
    inference(superposition,[],[f172,f23])).

fof(f172,plain,(
    ! [X14,X12,X15,X13] : k4_xboole_0(X12,k2_xboole_0(k2_xboole_0(X13,X14),X15)) = k4_xboole_0(X12,k2_xboole_0(X13,k2_xboole_0(X14,X15))) ),
    inference(forward_demodulation,[],[f171,f30])).

fof(f171,plain,(
    ! [X14,X12,X15,X13] : k4_xboole_0(k4_xboole_0(X12,X13),k2_xboole_0(X14,X15)) = k4_xboole_0(X12,k2_xboole_0(k2_xboole_0(X13,X14),X15)) ),
    inference(forward_demodulation,[],[f156,f30])).

fof(f156,plain,(
    ! [X14,X12,X15,X13] : k4_xboole_0(k4_xboole_0(X12,X13),k2_xboole_0(X14,X15)) = k4_xboole_0(k4_xboole_0(X12,k2_xboole_0(X13,X14)),X15) ),
    inference(superposition,[],[f30,f30])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f52742,plain,(
    ! [X8,X7] : k5_xboole_0(X7,k4_xboole_0(X8,X7)) = k2_xboole_0(k2_xboole_0(X7,X8),k5_xboole_0(X7,k4_xboole_0(X8,X7))) ),
    inference(forward_demodulation,[],[f52471,f17669])).

fof(f52471,plain,(
    ! [X8,X7] : k2_xboole_0(k4_xboole_0(X8,X7),X7) = k2_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(k4_xboole_0(X8,X7),X7)) ),
    inference(superposition,[],[f39149,f25])).

fof(f39149,plain,(
    ! [X101,X100] : k2_xboole_0(X100,X101) = k2_xboole_0(k2_xboole_0(X101,X100),k2_xboole_0(X100,X101)) ),
    inference(superposition,[],[f4983,f23579])).

fof(f23579,plain,(
    ! [X28,X27] : k2_xboole_0(X28,X27) = k2_xboole_0(k2_xboole_0(X28,X27),k2_xboole_0(X27,X28)) ),
    inference(forward_demodulation,[],[f23456,f206])).

fof(f23456,plain,(
    ! [X28,X27] : k2_xboole_0(k2_xboole_0(X28,X27),k2_xboole_0(X27,X28)) = k2_xboole_0(k2_xboole_0(X28,X27),k1_xboole_0) ),
    inference(superposition,[],[f25,f23207])).

fof(f23207,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f22873,f4983])).

fof(f35,plain,
    ( k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl2_1
  <=> k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f86,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f76,f83])).

fof(f83,plain,
    ( spl2_3
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f76,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f72,f74])).

fof(f74,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f73,f22])).

fof(f73,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f70,f47])).

fof(f70,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f61,f37])).

fof(f72,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f37,f61])).

fof(f81,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f74,f78])).

fof(f78,plain,
    ( spl2_2
  <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f36,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f20,f33])).

fof(f20,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f18])).

fof(f18,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:31:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (3329)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.45  % (3318)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (3320)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (3331)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (3327)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (3327)Refutation not found, incomplete strategy% (3327)------------------------------
% 0.21/0.47  % (3327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (3327)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (3327)Memory used [KB]: 10490
% 0.21/0.47  % (3327)Time elapsed: 0.069 s
% 0.21/0.47  % (3327)------------------------------
% 0.21/0.47  % (3327)------------------------------
% 0.21/0.47  % (3322)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (3323)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (3330)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (3321)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (3325)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (3316)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (3317)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (3324)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (3328)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (3319)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (3326)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (3332)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (3333)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 4.60/1.00  % (3320)Time limit reached!
% 4.60/1.00  % (3320)------------------------------
% 4.60/1.00  % (3320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.60/1.00  % (3320)Termination reason: Time limit
% 4.60/1.00  % (3320)Termination phase: Saturation
% 4.60/1.00  
% 4.60/1.00  % (3320)Memory used [KB]: 21108
% 4.60/1.00  % (3320)Time elapsed: 0.600 s
% 4.60/1.00  % (3320)------------------------------
% 4.60/1.00  % (3320)------------------------------
% 12.51/1.93  % (3321)Time limit reached!
% 12.51/1.93  % (3321)------------------------------
% 12.51/1.93  % (3321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.51/1.93  % (3321)Termination reason: Time limit
% 12.51/1.93  % (3321)Termination phase: Saturation
% 12.51/1.93  
% 12.51/1.93  % (3321)Memory used [KB]: 42728
% 12.51/1.93  % (3321)Time elapsed: 1.500 s
% 12.51/1.93  % (3321)------------------------------
% 12.51/1.93  % (3321)------------------------------
% 13.03/1.98  % (3322)Time limit reached!
% 13.03/1.98  % (3322)------------------------------
% 13.03/1.98  % (3322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.03/1.98  % (3322)Termination reason: Time limit
% 13.03/1.98  
% 13.03/1.98  % (3322)Memory used [KB]: 38378
% 13.03/1.98  % (3322)Time elapsed: 1.549 s
% 13.03/1.98  % (3322)------------------------------
% 13.03/1.98  % (3322)------------------------------
% 14.91/2.29  % (3318)Time limit reached!
% 14.91/2.29  % (3318)------------------------------
% 14.91/2.29  % (3318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.91/2.29  % (3318)Termination reason: Time limit
% 14.91/2.29  
% 14.91/2.29  % (3318)Memory used [KB]: 39402
% 14.91/2.29  % (3318)Time elapsed: 1.882 s
% 14.91/2.29  % (3318)------------------------------
% 14.91/2.29  % (3318)------------------------------
% 17.80/2.61  % (3328)Time limit reached!
% 17.80/2.61  % (3328)------------------------------
% 17.80/2.61  % (3328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.80/2.61  % (3328)Termination reason: Time limit
% 17.80/2.61  % (3328)Termination phase: Saturation
% 17.80/2.61  
% 17.80/2.61  % (3328)Memory used [KB]: 38250
% 17.80/2.61  % (3328)Time elapsed: 2.200 s
% 17.80/2.61  % (3328)------------------------------
% 17.80/2.61  % (3328)------------------------------
% 20.29/2.96  % (3316)Refutation found. Thanks to Tanya!
% 20.29/2.96  % SZS status Theorem for theBenchmark
% 20.29/2.96  % SZS output start Proof for theBenchmark
% 20.29/2.96  fof(f53699,plain,(
% 20.29/2.96    $false),
% 20.29/2.96    inference(avatar_sat_refutation,[],[f36,f81,f86,f53529])).
% 20.29/2.96  fof(f53529,plain,(
% 20.29/2.96    spl2_1),
% 20.29/2.96    inference(avatar_contradiction_clause,[],[f53528])).
% 20.29/2.96  fof(f53528,plain,(
% 20.29/2.96    $false | spl2_1),
% 20.29/2.96    inference(trivial_inequality_removal,[],[f53527])).
% 20.29/2.96  fof(f53527,plain,(
% 20.29/2.96    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) | spl2_1),
% 20.29/2.96    inference(superposition,[],[f35,f52743])).
% 20.29/2.96  fof(f52743,plain,(
% 20.29/2.96    ( ! [X8,X7] : (k2_xboole_0(X7,X8) = k5_xboole_0(X7,k4_xboole_0(X8,X7))) )),
% 20.29/2.96    inference(forward_demodulation,[],[f52742,f37755])).
% 20.29/2.96  fof(f37755,plain,(
% 20.29/2.96    ( ! [X39,X40] : (k2_xboole_0(X39,X40) = k2_xboole_0(k2_xboole_0(X39,X40),k5_xboole_0(X39,k4_xboole_0(X40,X39)))) )),
% 20.29/2.96    inference(forward_demodulation,[],[f37398,f206])).
% 20.29/2.96  fof(f206,plain,(
% 20.29/2.96    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 20.29/2.96    inference(forward_demodulation,[],[f200,f21])).
% 20.29/2.96  fof(f21,plain,(
% 20.29/2.96    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 20.29/2.96    inference(cnf_transformation,[],[f7])).
% 20.29/2.96  fof(f7,axiom,(
% 20.29/2.96    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 20.29/2.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 20.29/2.96  fof(f200,plain,(
% 20.29/2.96    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k1_xboole_0)) )),
% 20.29/2.96    inference(superposition,[],[f61,f182])).
% 20.29/2.96  fof(f182,plain,(
% 20.29/2.96    ( ! [X7] : (k1_xboole_0 = k3_xboole_0(X7,k1_xboole_0)) )),
% 20.29/2.96    inference(superposition,[],[f170,f22])).
% 20.29/2.96  fof(f22,plain,(
% 20.29/2.96    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 20.29/2.96    inference(cnf_transformation,[],[f3])).
% 20.29/2.96  fof(f3,axiom,(
% 20.29/2.96    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 20.29/2.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 20.29/2.96  fof(f170,plain,(
% 20.29/2.96    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) )),
% 20.29/2.96    inference(forward_demodulation,[],[f151,f23])).
% 20.29/2.96  fof(f23,plain,(
% 20.29/2.96    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 20.29/2.96    inference(cnf_transformation,[],[f5])).
% 20.29/2.96  fof(f5,axiom,(
% 20.29/2.96    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 20.29/2.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 20.29/2.96  fof(f151,plain,(
% 20.29/2.96    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) )),
% 20.29/2.96    inference(superposition,[],[f30,f47])).
% 20.29/2.96  fof(f47,plain,(
% 20.29/2.96    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 20.29/2.96    inference(superposition,[],[f26,f22])).
% 20.29/2.96  fof(f26,plain,(
% 20.29/2.96    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 20.29/2.96    inference(cnf_transformation,[],[f6])).
% 20.29/2.96  fof(f6,axiom,(
% 20.29/2.96    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 20.29/2.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 20.29/2.96  fof(f30,plain,(
% 20.29/2.96    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 20.29/2.96    inference(cnf_transformation,[],[f4])).
% 20.29/2.96  fof(f4,axiom,(
% 20.29/2.96    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 20.29/2.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 20.29/2.96  fof(f61,plain,(
% 20.29/2.96    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) )),
% 20.29/2.96    inference(superposition,[],[f27,f21])).
% 20.29/2.96  fof(f27,plain,(
% 20.29/2.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 20.29/2.96    inference(cnf_transformation,[],[f11])).
% 20.29/2.96  fof(f11,axiom,(
% 20.29/2.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 20.29/2.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 20.29/2.96  fof(f37398,plain,(
% 20.29/2.96    ( ! [X39,X40] : (k2_xboole_0(k2_xboole_0(X39,X40),k1_xboole_0) = k2_xboole_0(k2_xboole_0(X39,X40),k5_xboole_0(X39,k4_xboole_0(X40,X39)))) )),
% 20.29/2.96    inference(superposition,[],[f25,f23306])).
% 20.29/2.96  fof(f23306,plain,(
% 20.29/2.96    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X7,k4_xboole_0(X6,X7)),k2_xboole_0(X7,X6))) )),
% 20.29/2.96    inference(forward_demodulation,[],[f23209,f17669])).
% 20.29/2.96  fof(f17669,plain,(
% 20.29/2.96    ( ! [X10,X11] : (k2_xboole_0(k4_xboole_0(X10,X11),X11) = k5_xboole_0(X11,k4_xboole_0(X10,X11))) )),
% 20.29/2.96    inference(forward_demodulation,[],[f17601,f1350])).
% 20.29/2.96  fof(f1350,plain,(
% 20.29/2.96    ( ! [X19,X18] : (k5_xboole_0(X19,X18) = k5_xboole_0(k5_xboole_0(X18,X19),k1_xboole_0)) )),
% 20.29/2.96    inference(forward_demodulation,[],[f1311,f37])).
% 20.29/2.96  fof(f37,plain,(
% 20.29/2.96    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 20.29/2.96    inference(superposition,[],[f24,f21])).
% 20.29/2.96  fof(f24,plain,(
% 20.29/2.96    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 20.29/2.96    inference(cnf_transformation,[],[f1])).
% 20.29/2.96  fof(f1,axiom,(
% 20.29/2.96    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 20.29/2.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 20.29/2.96  fof(f1311,plain,(
% 20.29/2.96    ( ! [X19,X18] : (k5_xboole_0(k5_xboole_0(X18,X19),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X19,X18))) )),
% 20.29/2.96    inference(superposition,[],[f1175,f1175])).
% 20.29/2.96  fof(f1175,plain,(
% 20.29/2.96    ( ! [X28,X27] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X27,X28)) = k5_xboole_0(X28,X27)) )),
% 20.29/2.96    inference(superposition,[],[f133,f37])).
% 20.29/2.96  fof(f133,plain,(
% 20.29/2.96    ( ! [X6,X7,X5] : (k5_xboole_0(X7,k5_xboole_0(X5,X6)) = k5_xboole_0(X5,k5_xboole_0(X6,X7))) )),
% 20.29/2.96    inference(superposition,[],[f29,f24])).
% 20.29/2.96  fof(f29,plain,(
% 20.29/2.96    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 20.29/2.96    inference(cnf_transformation,[],[f10])).
% 20.29/2.96  fof(f10,axiom,(
% 20.29/2.96    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 20.29/2.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 20.29/2.96  fof(f17601,plain,(
% 20.29/2.96    ( ! [X10,X11] : (k2_xboole_0(k4_xboole_0(X10,X11),X11) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X10,X11),X11),k1_xboole_0)) )),
% 20.29/2.96    inference(superposition,[],[f27,f17403])).
% 20.29/2.96  fof(f17403,plain,(
% 20.29/2.96    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 20.29/2.96    inference(forward_demodulation,[],[f17210,f198])).
% 20.29/2.96  fof(f198,plain,(
% 20.29/2.96    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 20.29/2.96    inference(superposition,[],[f182,f47])).
% 20.29/2.96  fof(f17210,plain,(
% 20.29/2.96    ( ! [X0,X1] : (k3_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0))) )),
% 20.29/2.96    inference(superposition,[],[f164,f207])).
% 20.29/2.96  fof(f207,plain,(
% 20.29/2.96    ( ! [X3] : (k2_xboole_0(X3,X3) = X3) )),
% 20.29/2.96    inference(forward_demodulation,[],[f201,f206])).
% 20.29/2.96  fof(f201,plain,(
% 20.29/2.96    ( ! [X3] : (k2_xboole_0(X3,X3) = k2_xboole_0(X3,k1_xboole_0)) )),
% 20.29/2.96    inference(superposition,[],[f53,f182])).
% 20.29/2.96  fof(f53,plain,(
% 20.29/2.96    ( ! [X1] : (k2_xboole_0(X1,X1) = k2_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) )),
% 20.29/2.96    inference(superposition,[],[f25,f47])).
% 20.29/2.96  fof(f164,plain,(
% 20.29/2.96    ( ! [X6,X4,X5] : (k3_xboole_0(k4_xboole_0(X4,X5),X6) = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,k2_xboole_0(X5,X6)))) )),
% 20.29/2.96    inference(superposition,[],[f26,f30])).
% 20.29/2.96  fof(f23209,plain,(
% 20.29/2.96    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(X6,X7),X7),k2_xboole_0(X7,X6))) )),
% 20.29/2.96    inference(superposition,[],[f22873,f5134])).
% 20.29/2.96  fof(f5134,plain,(
% 20.29/2.96    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X2,X1),k2_xboole_0(X1,X2))) )),
% 20.29/2.96    inference(superposition,[],[f4983,f25])).
% 20.29/2.96  fof(f4983,plain,(
% 20.29/2.96    ( ! [X8,X7] : (k2_xboole_0(X8,X7) = k2_xboole_0(X7,k2_xboole_0(X8,X7))) )),
% 20.29/2.96    inference(forward_demodulation,[],[f4982,f1837])).
% 20.29/2.96  fof(f1837,plain,(
% 20.29/2.96    ( ! [X26,X25] : (k2_xboole_0(X26,X25) = k5_xboole_0(k5_xboole_0(X26,k3_xboole_0(X26,X25)),X25)) )),
% 20.29/2.96    inference(forward_demodulation,[],[f1808,f206])).
% 20.29/2.96  fof(f1808,plain,(
% 20.29/2.96    ( ! [X26,X25] : (k5_xboole_0(k5_xboole_0(X26,k3_xboole_0(X26,X25)),X25) = k2_xboole_0(k2_xboole_0(X26,X25),k1_xboole_0)) )),
% 20.29/2.96    inference(superposition,[],[f912,f821])).
% 20.29/2.96  fof(f821,plain,(
% 20.29/2.96    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3)))) )),
% 20.29/2.96    inference(superposition,[],[f62,f29])).
% 20.29/2.96  fof(f62,plain,(
% 20.29/2.96    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X1,X2))) )),
% 20.29/2.96    inference(superposition,[],[f27,f24])).
% 20.29/2.96  fof(f912,plain,(
% 20.29/2.96    ( ! [X19,X20] : (k2_xboole_0(k5_xboole_0(X19,X20),k1_xboole_0) = k5_xboole_0(X20,X19)) )),
% 20.29/2.96    inference(forward_demodulation,[],[f911,f21])).
% 20.29/2.96  fof(f911,plain,(
% 20.29/2.96    ( ! [X19,X20] : (k2_xboole_0(k5_xboole_0(X19,X20),k1_xboole_0) = k5_xboole_0(X20,k5_xboole_0(X19,k1_xboole_0))) )),
% 20.29/2.96    inference(forward_demodulation,[],[f910,f182])).
% 20.29/2.96  fof(f910,plain,(
% 20.29/2.96    ( ! [X19,X20] : (k2_xboole_0(k5_xboole_0(X19,X20),k1_xboole_0) = k5_xboole_0(X20,k5_xboole_0(X19,k3_xboole_0(k5_xboole_0(X19,X20),k1_xboole_0)))) )),
% 20.29/2.96    inference(forward_demodulation,[],[f875,f47])).
% 20.29/2.96  fof(f875,plain,(
% 20.29/2.96    ( ! [X19,X20] : (k2_xboole_0(k5_xboole_0(X19,X20),k1_xboole_0) = k5_xboole_0(X20,k5_xboole_0(X19,k4_xboole_0(k5_xboole_0(X19,X20),k5_xboole_0(X19,X20))))) )),
% 20.29/2.96    inference(superposition,[],[f123,f68])).
% 20.29/2.96  fof(f68,plain,(
% 20.29/2.96    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k4_xboole_0(X0,X0))) )),
% 20.29/2.96    inference(forward_demodulation,[],[f66,f21])).
% 20.29/2.96  fof(f66,plain,(
% 20.29/2.96    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0))) )),
% 20.29/2.96    inference(superposition,[],[f27,f47])).
% 20.29/2.96  fof(f123,plain,(
% 20.29/2.96    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2)) )),
% 20.29/2.96    inference(superposition,[],[f29,f24])).
% 20.29/2.96  fof(f4982,plain,(
% 20.29/2.96    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,k3_xboole_0(X8,X7)),X7) = k2_xboole_0(X7,k2_xboole_0(X8,X7))) )),
% 20.29/2.96    inference(forward_demodulation,[],[f4850,f4216])).
% 20.29/2.96  fof(f4216,plain,(
% 20.29/2.96    ( ! [X6,X5] : (k2_xboole_0(X5,k2_xboole_0(X6,X5)) = k5_xboole_0(k5_xboole_0(X5,X5),k2_xboole_0(X6,X5))) )),
% 20.29/2.96    inference(superposition,[],[f1837,f360])).
% 20.29/2.96  fof(f360,plain,(
% 20.29/2.96    ( ! [X4,X5] : (k3_xboole_0(X4,k2_xboole_0(X5,X4)) = X4) )),
% 20.29/2.96    inference(forward_demodulation,[],[f356,f22])).
% 20.29/2.96  fof(f356,plain,(
% 20.29/2.96    ( ! [X4,X5] : (k4_xboole_0(X4,k1_xboole_0) = k3_xboole_0(X4,k2_xboole_0(X5,X4))) )),
% 20.29/2.96    inference(superposition,[],[f26,f220])).
% 20.29/2.96  fof(f220,plain,(
% 20.29/2.96    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))) )),
% 20.29/2.96    inference(forward_demodulation,[],[f213,f25])).
% 20.29/2.96  fof(f213,plain,(
% 20.29/2.96    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,X3)))) )),
% 20.29/2.96    inference(superposition,[],[f198,f30])).
% 20.29/2.96  fof(f4850,plain,(
% 20.29/2.96    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,k3_xboole_0(X8,X7)),X7) = k5_xboole_0(k5_xboole_0(X7,X7),k2_xboole_0(X8,X7))) )),
% 20.29/2.96    inference(superposition,[],[f1180,f821])).
% 20.29/2.96  fof(f1180,plain,(
% 20.29/2.96    ( ! [X43,X44] : (k5_xboole_0(k5_xboole_0(X43,X43),k5_xboole_0(X43,X44)) = k5_xboole_0(X44,X43)) )),
% 20.29/2.96    inference(superposition,[],[f133,f239])).
% 20.29/2.96  fof(f239,plain,(
% 20.29/2.96    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0) )),
% 20.29/2.96    inference(forward_demodulation,[],[f233,f207])).
% 20.29/2.96  fof(f233,plain,(
% 20.29/2.96    ( ! [X0] : (k2_xboole_0(X0,X0) = k5_xboole_0(k5_xboole_0(X0,X0),X0)) )),
% 20.29/2.96    inference(superposition,[],[f27,f208])).
% 20.29/2.96  fof(f208,plain,(
% 20.29/2.96    ( ! [X4] : (k3_xboole_0(X4,X4) = X4) )),
% 20.29/2.96    inference(forward_demodulation,[],[f202,f22])).
% 20.29/2.96  fof(f202,plain,(
% 20.29/2.96    ( ! [X4] : (k3_xboole_0(X4,X4) = k4_xboole_0(X4,k1_xboole_0)) )),
% 20.29/2.96    inference(superposition,[],[f52,f182])).
% 20.29/2.96  fof(f52,plain,(
% 20.29/2.96    ( ! [X0] : (k3_xboole_0(X0,X0) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) )),
% 20.29/2.96    inference(superposition,[],[f26,f47])).
% 20.29/2.96  fof(f22873,plain,(
% 20.29/2.96    ( ! [X14,X15,X13] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X13,X14),k2_xboole_0(X13,k2_xboole_0(X14,X15)))) )),
% 20.29/2.96    inference(superposition,[],[f172,f23])).
% 20.29/2.96  fof(f172,plain,(
% 20.29/2.96    ( ! [X14,X12,X15,X13] : (k4_xboole_0(X12,k2_xboole_0(k2_xboole_0(X13,X14),X15)) = k4_xboole_0(X12,k2_xboole_0(X13,k2_xboole_0(X14,X15)))) )),
% 20.29/2.96    inference(forward_demodulation,[],[f171,f30])).
% 20.29/2.96  fof(f171,plain,(
% 20.29/2.96    ( ! [X14,X12,X15,X13] : (k4_xboole_0(k4_xboole_0(X12,X13),k2_xboole_0(X14,X15)) = k4_xboole_0(X12,k2_xboole_0(k2_xboole_0(X13,X14),X15))) )),
% 20.29/2.96    inference(forward_demodulation,[],[f156,f30])).
% 20.29/2.96  fof(f156,plain,(
% 20.29/2.96    ( ! [X14,X12,X15,X13] : (k4_xboole_0(k4_xboole_0(X12,X13),k2_xboole_0(X14,X15)) = k4_xboole_0(k4_xboole_0(X12,k2_xboole_0(X13,X14)),X15)) )),
% 20.29/2.96    inference(superposition,[],[f30,f30])).
% 20.29/2.96  fof(f25,plain,(
% 20.29/2.96    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 20.29/2.96    inference(cnf_transformation,[],[f2])).
% 20.29/2.96  fof(f2,axiom,(
% 20.29/2.96    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 20.29/2.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 20.29/2.96  fof(f52742,plain,(
% 20.29/2.96    ( ! [X8,X7] : (k5_xboole_0(X7,k4_xboole_0(X8,X7)) = k2_xboole_0(k2_xboole_0(X7,X8),k5_xboole_0(X7,k4_xboole_0(X8,X7)))) )),
% 20.29/2.96    inference(forward_demodulation,[],[f52471,f17669])).
% 20.29/2.96  fof(f52471,plain,(
% 20.29/2.96    ( ! [X8,X7] : (k2_xboole_0(k4_xboole_0(X8,X7),X7) = k2_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(k4_xboole_0(X8,X7),X7))) )),
% 20.29/2.96    inference(superposition,[],[f39149,f25])).
% 20.29/2.96  fof(f39149,plain,(
% 20.29/2.96    ( ! [X101,X100] : (k2_xboole_0(X100,X101) = k2_xboole_0(k2_xboole_0(X101,X100),k2_xboole_0(X100,X101))) )),
% 20.29/2.96    inference(superposition,[],[f4983,f23579])).
% 20.29/2.96  fof(f23579,plain,(
% 20.29/2.96    ( ! [X28,X27] : (k2_xboole_0(X28,X27) = k2_xboole_0(k2_xboole_0(X28,X27),k2_xboole_0(X27,X28))) )),
% 20.29/2.96    inference(forward_demodulation,[],[f23456,f206])).
% 20.29/2.96  fof(f23456,plain,(
% 20.29/2.96    ( ! [X28,X27] : (k2_xboole_0(k2_xboole_0(X28,X27),k2_xboole_0(X27,X28)) = k2_xboole_0(k2_xboole_0(X28,X27),k1_xboole_0)) )),
% 20.29/2.96    inference(superposition,[],[f25,f23207])).
% 20.29/2.96  fof(f23207,plain,(
% 20.29/2.96    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2))) )),
% 20.29/2.96    inference(superposition,[],[f22873,f4983])).
% 20.29/2.96  fof(f35,plain,(
% 20.29/2.96    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | spl2_1),
% 20.29/2.96    inference(avatar_component_clause,[],[f33])).
% 20.29/2.96  fof(f33,plain,(
% 20.29/2.96    spl2_1 <=> k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 20.29/2.96    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 20.29/2.96  fof(f86,plain,(
% 20.29/2.96    spl2_3),
% 20.29/2.96    inference(avatar_split_clause,[],[f76,f83])).
% 20.29/2.96  fof(f83,plain,(
% 20.29/2.96    spl2_3 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)),
% 20.29/2.96    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 20.29/2.96  fof(f76,plain,(
% 20.29/2.96    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)),
% 20.29/2.96    inference(forward_demodulation,[],[f72,f74])).
% 20.29/2.96  fof(f74,plain,(
% 20.29/2.96    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 20.29/2.96    inference(forward_demodulation,[],[f73,f22])).
% 20.29/2.96  fof(f73,plain,(
% 20.29/2.96    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 20.29/2.96    inference(forward_demodulation,[],[f70,f47])).
% 20.29/2.96  fof(f70,plain,(
% 20.29/2.96    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 20.29/2.96    inference(superposition,[],[f61,f37])).
% 20.29/2.96  fof(f72,plain,(
% 20.29/2.96    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 20.29/2.96    inference(superposition,[],[f37,f61])).
% 20.29/2.96  fof(f81,plain,(
% 20.29/2.96    spl2_2),
% 20.29/2.96    inference(avatar_split_clause,[],[f74,f78])).
% 20.29/2.96  fof(f78,plain,(
% 20.29/2.96    spl2_2 <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 20.29/2.96    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 20.29/2.96  fof(f36,plain,(
% 20.29/2.96    ~spl2_1),
% 20.29/2.96    inference(avatar_split_clause,[],[f20,f33])).
% 20.29/2.96  fof(f20,plain,(
% 20.29/2.96    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 20.29/2.96    inference(cnf_transformation,[],[f19])).
% 20.29/2.96  fof(f19,plain,(
% 20.29/2.96    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 20.29/2.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f18])).
% 20.29/2.96  fof(f18,plain,(
% 20.29/2.96    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 20.29/2.96    introduced(choice_axiom,[])).
% 20.29/2.96  fof(f15,plain,(
% 20.29/2.96    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 20.29/2.96    inference(ennf_transformation,[],[f13])).
% 20.29/2.96  fof(f13,negated_conjecture,(
% 20.29/2.96    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 20.29/2.96    inference(negated_conjecture,[],[f12])).
% 20.29/2.96  fof(f12,conjecture,(
% 20.29/2.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 20.29/2.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 20.29/2.96  % SZS output end Proof for theBenchmark
% 20.29/2.96  % (3316)------------------------------
% 20.29/2.96  % (3316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.29/2.96  % (3316)Termination reason: Refutation
% 20.29/2.96  
% 20.29/2.96  % (3316)Memory used [KB]: 50788
% 20.29/2.96  % (3316)Time elapsed: 2.544 s
% 20.29/2.96  % (3316)------------------------------
% 20.29/2.96  % (3316)------------------------------
% 20.29/2.96  % (3315)Success in time 2.611 s
%------------------------------------------------------------------------------
