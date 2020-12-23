%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:58 EST 2020

% Result     : Theorem 5.79s
% Output     : Refutation 5.79s
% Verified   : 
% Statistics : Number of formulae       :  765 (7474 expanded)
%              Number of leaves         :  123 (2757 expanded)
%              Depth                    :   34
%              Number of atoms          : 1607 (9041 expanded)
%              Number of equality atoms :  527 (7092 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :   14 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17241,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f61,f88,f99,f100,f105,f106,f107,f114,f122,f133,f134,f139,f140,f141,f147,f160,f161,f166,f167,f168,f174,f187,f188,f193,f194,f195,f201,f214,f215,f220,f221,f222,f228,f257,f258,f263,f264,f265,f271,f299,f378,f385,f393,f402,f412,f418,f424,f431,f439,f448,f458,f463,f476,f483,f493,f500,f506,f518,f527,f533,f589,f595,f601,f607,f613,f618,f644,f652,f658,f664,f670,f676,f682,f700,f706,f712,f718,f732,f742,f747,f757,f762,f772,f777,f796,f817,f823,f846,f854,f856,f857,f922,f927,f950,f956,f976,f1094,f1104,f1117,f1129,f1142,f1185,f1192,f1202,f1211,f1221,f1264,f1269,f1274,f1279,f1295,f1300,f1305,f1310,f1316,f1321,f1327,f1376,f1377,f1378,f1379,f1391,f1397,f1410,f1454,f1470,f1487,f1500,f1896,f1919,f2012,f2120,f3695,f17216,f17222])).

fof(f17222,plain,
    ( ~ spl3_108
    | ~ spl3_5
    | spl3_7 ),
    inference(avatar_split_clause,[],[f17217,f111,f96,f17219])).

fof(f17219,plain,
    ( spl3_108
  <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_108])])).

fof(f96,plain,
    ( spl3_5
  <=> sK2 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f111,plain,
    ( spl3_7
  <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f17217,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | ~ spl3_5
    | spl3_7 ),
    inference(forward_demodulation,[],[f17211,f23])).

fof(f23,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f17211,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0))))
    | ~ spl3_5
    | spl3_7 ),
    inference(backward_demodulation,[],[f113,f17208])).

fof(f17208,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(X0,k3_xboole_0(X0,sK1)))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f17193,f1652])).

fof(f1652,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f1148,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1148,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f362,f1144])).

fof(f1144,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f1143,f23])).

fof(f1143,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f1039,f693])).

fof(f693,plain,(
    ! [X12,X11] : k5_xboole_0(X12,k3_xboole_0(k1_xboole_0,X11)) = X12 ),
    inference(forward_demodulation,[],[f692,f23])).

fof(f692,plain,(
    ! [X12,X11] : k5_xboole_0(X12,k3_xboole_0(k1_xboole_0,X11)) = k5_xboole_0(X12,k1_xboole_0) ),
    inference(forward_demodulation,[],[f565,f362])).

fof(f565,plain,(
    ! [X12,X11] : k5_xboole_0(X12,k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X11)))) = k5_xboole_0(X12,k3_xboole_0(k1_xboole_0,X11)) ),
    inference(superposition,[],[f274,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f31,f32,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f274,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f34,f23])).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1039,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[],[f41,f39])).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f24,f32])).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f27,f36,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f30,f32])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f362,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f42,f39])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f29,f36])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f17193,plain,
    ( ! [X0] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(X0,k3_xboole_0(X0,sK1))) = k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(X0,k3_xboole_0(X0,sK1))),k1_xboole_0)
    | ~ spl3_5 ),
    inference(resolution,[],[f16410,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f16410,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(X0,k3_xboole_0(X0,sK1))),k1_xboole_0)
    | ~ spl3_5 ),
    inference(superposition,[],[f15451,f28])).

fof(f15451,plain,
    ( ! [X61] : r1_tarski(k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(X61,k3_xboole_0(sK1,X61))),k1_xboole_0)
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f5875,f15187])).

fof(f15187,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k3_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f1787,f535])).

fof(f535,plain,(
    ! [X2,X1] : k3_xboole_0(X2,X1) = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) ),
    inference(superposition,[],[f37,f28])).

fof(f1787,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f43,f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f43,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f35,f32,f32])).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f5875,plain,
    ( ! [X61] : r1_tarski(k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(X61,k3_xboole_0(X61,k3_xboole_0(sK1,X61)))),k1_xboole_0)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f5728,f28])).

fof(f5728,plain,
    ( ! [X61] : r1_tarski(k3_xboole_0(k5_xboole_0(X61,k3_xboole_0(X61,k3_xboole_0(sK1,X61))),k5_xboole_0(sK1,sK2)),k1_xboole_0)
    | ~ spl3_5 ),
    inference(superposition,[],[f4883,f1828])).

fof(f1828,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1)))) ),
    inference(forward_demodulation,[],[f1799,f1668])).

fof(f1668,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f623,f1652])).

fof(f623,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f555,f25])).

fof(f555,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f37,f39])).

fof(f1799,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1)))) ),
    inference(superposition,[],[f43,f25])).

fof(f4883,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(X0,k5_xboole_0(sK1,sK2)),k3_xboole_0(sK1,X0))
    | ~ spl3_5 ),
    inference(superposition,[],[f4737,f28])).

fof(f4737,plain,
    ( ! [X43] : r1_tarski(k3_xboole_0(X43,k5_xboole_0(sK1,sK2)),k3_xboole_0(X43,sK1))
    | ~ spl3_5 ),
    inference(superposition,[],[f1810,f98])).

fof(f98,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f1810,plain,(
    ! [X17,X15,X16] : r1_tarski(k3_xboole_0(X15,k5_xboole_0(X16,k3_xboole_0(X16,X17))),k3_xboole_0(X15,X16)) ),
    inference(superposition,[],[f40,f43])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f26,f32])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f113,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f17216,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | spl3_24 ),
    inference(avatar_contradiction_clause,[],[f17215])).

fof(f17215,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_5
    | spl3_24 ),
    inference(trivial_inequality_removal,[],[f17214])).

fof(f17214,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl3_4
    | ~ spl3_5
    | spl3_24 ),
    inference(forward_demodulation,[],[f17213,f28])).

fof(f17213,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(sK0,k3_xboole_0(sK2,sK0))
    | ~ spl3_4
    | ~ spl3_5
    | spl3_24 ),
    inference(forward_demodulation,[],[f17212,f15375])).

fof(f15375,plain,
    ( ! [X19] : k3_xboole_0(sK2,X19) = k5_xboole_0(k3_xboole_0(X19,sK1),k3_xboole_0(X19,k5_xboole_0(sK1,sK2)))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f13879,f15374])).

fof(f15374,plain,
    ( ! [X26] : k3_xboole_0(X26,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k3_xboole_0(X26,sK1),k3_xboole_0(X26,k5_xboole_0(sK1,sK2)))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f15137,f13871])).

fof(f13871,plain,
    ( ! [X0] : k3_xboole_0(X0,k5_xboole_0(sK1,sK2)) = k5_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(sK2,X0))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f13813,f98])).

fof(f13813,plain,
    ( ! [X0] : k5_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(sK2,X0)) = k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_4 ),
    inference(superposition,[],[f43,f13317])).

fof(f13317,plain,
    ( ! [X52] : k3_xboole_0(sK2,X52) = k3_xboole_0(k3_xboole_0(X52,sK1),sK2)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f13251,f23])).

fof(f13251,plain,
    ( ! [X52] : k3_xboole_0(k3_xboole_0(X52,sK1),sK2) = k5_xboole_0(k3_xboole_0(sK2,X52),k1_xboole_0)
    | ~ spl3_4 ),
    inference(superposition,[],[f7101,f13177])).

fof(f13177,plain,
    ( ! [X38] : k3_xboole_0(sK2,X38) = k3_xboole_0(sK2,k3_xboole_0(X38,sK1))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f13176,f1697])).

fof(f1697,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f1686,f1144])).

fof(f1686,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f34,f1668])).

fof(f13176,plain,
    ( ! [X38] : k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,X38))) = k3_xboole_0(sK2,k3_xboole_0(X38,sK1))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f12979,f2094])).

fof(f2094,plain,
    ( ! [X0] : k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) = k3_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(X0,sK1)))
    | ~ spl3_4 ),
    inference(superposition,[],[f1796,f28])).

fof(f1796,plain,
    ( ! [X18] : k3_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,X18))) = k5_xboole_0(sK2,k3_xboole_0(sK2,X18))
    | ~ spl3_4 ),
    inference(superposition,[],[f43,f87])).

fof(f87,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_4
  <=> sK2 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f12979,plain,
    ( ! [X38] : k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(X38,sK1)))) = k3_xboole_0(sK2,k3_xboole_0(X38,sK1))
    | ~ spl3_4 ),
    inference(superposition,[],[f1796,f535])).

fof(f7101,plain,
    ( ! [X9] : k3_xboole_0(X9,sK2) = k5_xboole_0(k3_xboole_0(sK2,X9),k1_xboole_0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f7100,f23])).

fof(f7100,plain,
    ( ! [X9] : k5_xboole_0(k3_xboole_0(sK2,X9),k1_xboole_0) = k5_xboole_0(k3_xboole_0(X9,sK2),k1_xboole_0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f7099,f5766])).

fof(f5766,plain,(
    ! [X2,X1] : k1_xboole_0 = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(forward_demodulation,[],[f5652,f1815])).

fof(f1815,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(backward_demodulation,[],[f556,f1787])).

fof(f556,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(superposition,[],[f37,f37])).

fof(f5652,plain,(
    ! [X2,X1] : k1_xboole_0 = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(superposition,[],[f1828,f28])).

fof(f7099,plain,
    ( ! [X9] : k5_xboole_0(k3_xboole_0(X9,sK2),k1_xboole_0) = k5_xboole_0(k3_xboole_0(sK2,X9),k3_xboole_0(X9,k5_xboole_0(sK2,k3_xboole_0(sK2,X9))))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f7098,f1815])).

fof(f7098,plain,
    ( ! [X9] : k5_xboole_0(k3_xboole_0(X9,sK2),k1_xboole_0) = k5_xboole_0(k3_xboole_0(sK2,X9),k3_xboole_0(X9,k5_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK2,X9)))))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f7097,f43])).

fof(f7097,plain,
    ( ! [X9] : k5_xboole_0(k3_xboole_0(X9,sK2),k1_xboole_0) = k5_xboole_0(k3_xboole_0(sK2,X9),k5_xboole_0(k3_xboole_0(X9,sK2),k3_xboole_0(k3_xboole_0(X9,sK2),k3_xboole_0(sK2,X9))))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f7046,f1668])).

fof(f7046,plain,
    ( ! [X9] : k5_xboole_0(k3_xboole_0(sK2,X9),k5_xboole_0(k3_xboole_0(X9,sK2),k3_xboole_0(k3_xboole_0(X9,sK2),k3_xboole_0(sK2,X9)))) = k5_xboole_0(k3_xboole_0(X9,sK2),k5_xboole_0(k3_xboole_0(sK2,X9),k3_xboole_0(sK2,X9)))
    | ~ spl3_4 ),
    inference(superposition,[],[f41,f5112])).

fof(f5112,plain,
    ( ! [X0] : k3_xboole_0(sK2,X0) = k3_xboole_0(k3_xboole_0(sK2,X0),k3_xboole_0(X0,sK2))
    | ~ spl3_4 ),
    inference(resolution,[],[f5051,f33])).

fof(f5051,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK2,X0),k3_xboole_0(X0,sK2))
    | ~ spl3_4 ),
    inference(superposition,[],[f4912,f87])).

fof(f4912,plain,
    ( ! [X2,X1] : r1_tarski(k3_xboole_0(k3_xboole_0(sK2,X2),X1),k3_xboole_0(X1,sK2))
    | ~ spl3_4 ),
    inference(superposition,[],[f4827,f28])).

fof(f4827,plain,
    ( ! [X54,X53] : r1_tarski(k3_xboole_0(X54,k3_xboole_0(sK2,X53)),k3_xboole_0(X54,sK2))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f4743,f1697])).

fof(f4743,plain,
    ( ! [X54,X53] : r1_tarski(k3_xboole_0(X54,k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,X53)))),k3_xboole_0(X54,sK2))
    | ~ spl3_4 ),
    inference(superposition,[],[f1810,f1796])).

fof(f15137,plain,
    ( ! [X26] : k5_xboole_0(k3_xboole_0(X26,sK1),k3_xboole_0(sK2,X26)) = k3_xboole_0(k3_xboole_0(X26,sK1),k5_xboole_0(k3_xboole_0(X26,sK1),k3_xboole_0(sK2,X26)))
    | ~ spl3_4 ),
    inference(superposition,[],[f1787,f2782])).

fof(f2782,plain,
    ( ! [X1] : k3_xboole_0(sK2,X1) = k3_xboole_0(k3_xboole_0(X1,sK1),k3_xboole_0(sK2,X1))
    | ~ spl3_4 ),
    inference(superposition,[],[f2290,f28])).

fof(f2290,plain,
    ( ! [X0] : k3_xboole_0(sK2,X0) = k3_xboole_0(k3_xboole_0(sK2,X0),k3_xboole_0(X0,sK1))
    | ~ spl3_4 ),
    inference(resolution,[],[f2267,f33])).

fof(f2267,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK2,X0),k3_xboole_0(X0,sK1))
    | ~ spl3_4 ),
    inference(superposition,[],[f2229,f28])).

fof(f2229,plain,
    ( ! [X2] : r1_tarski(k3_xboole_0(sK2,X2),k3_xboole_0(sK1,X2))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f2228,f1697])).

fof(f2228,plain,
    ( ! [X2] : r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,X2))),k3_xboole_0(sK1,X2))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f2227,f1697])).

fof(f2227,plain,
    ( ! [X2] : r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,X2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,X2))))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f2208,f1787])).

fof(f2208,plain,
    ( ! [X2] : r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,X2))),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,X2)))))
    | ~ spl3_4 ),
    inference(superposition,[],[f2113,f1796])).

fof(f2113,plain,
    ( ! [X15] : r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,X15)),k5_xboole_0(sK1,k3_xboole_0(sK1,X15)))
    | ~ spl3_4 ),
    inference(superposition,[],[f898,f1796])).

fof(f898,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f561,f28])).

fof(f561,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(X2,X3),X2) ),
    inference(superposition,[],[f40,f37])).

fof(f13879,plain,
    ( ! [X19] : k3_xboole_0(sK2,X19) = k5_xboole_0(k3_xboole_0(X19,sK1),k3_xboole_0(k3_xboole_0(X19,sK1),k3_xboole_0(X19,k5_xboole_0(sK1,sK2))))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f12897,f13871])).

fof(f12897,plain,
    ( ! [X19] : k3_xboole_0(sK2,X19) = k5_xboole_0(k3_xboole_0(X19,sK1),k3_xboole_0(k3_xboole_0(X19,sK1),k5_xboole_0(k3_xboole_0(X19,sK1),k3_xboole_0(sK2,X19))))
    | ~ spl3_4 ),
    inference(superposition,[],[f535,f2290])).

fof(f17212,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))))
    | ~ spl3_5
    | spl3_24 ),
    inference(forward_demodulation,[],[f17210,f23])).

fof(f17210,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0)))))
    | ~ spl3_5
    | spl3_24 ),
    inference(backward_demodulation,[],[f298,f17208])).

fof(f298,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl3_24
  <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f3695,plain,
    ( spl3_107
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_106 ),
    inference(avatar_split_clause,[],[f3690,f2117,f130,f85,f3692])).

fof(f3692,plain,
    ( spl3_107
  <=> k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_107])])).

fof(f130,plain,
    ( spl3_9
  <=> k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f2117,plain,
    ( spl3_106
  <=> k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_106])])).

fof(f3690,plain,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK1,sK2),sK2)
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_106 ),
    inference(forward_demodulation,[],[f3689,f23])).

fof(f3689,plain,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK2,k1_xboole_0))
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_106 ),
    inference(forward_demodulation,[],[f3635,f2119])).

fof(f2119,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))
    | ~ spl3_106 ),
    inference(avatar_component_clause,[],[f2117])).

fof(f3635,plain,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))))
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(superposition,[],[f2751,f132])).

fof(f132,plain,
    ( k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f2751,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK1,X0))))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f2735,f1668])).

fof(f2735,plain,
    ( ! [X0] : k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK1,X0)))) = k5_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(X0,sK2))
    | ~ spl3_4 ),
    inference(superposition,[],[f43,f2274])).

fof(f2274,plain,
    ( ! [X0] : k3_xboole_0(X0,sK2) = k3_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(sK1,X0))
    | ~ spl3_4 ),
    inference(resolution,[],[f2260,f33])).

fof(f2260,plain,
    ( ! [X3] : r1_tarski(k3_xboole_0(X3,sK2),k3_xboole_0(sK1,X3))
    | ~ spl3_4 ),
    inference(superposition,[],[f2229,f28])).

fof(f2120,plain,
    ( spl3_106
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f2115,f96,f85,f2117])).

fof(f2115,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f2114,f1668])).

fof(f2114,plain,
    ( k5_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f2091,f25])).

fof(f2091,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(superposition,[],[f1796,f98])).

fof(f2012,plain,
    ( spl3_105
    | ~ spl3_101
    | ~ spl3_103 ),
    inference(avatar_split_clause,[],[f2005,f1893,f1484,f2009])).

fof(f2009,plain,
    ( spl3_105
  <=> sK2 = k5_xboole_0(k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_105])])).

fof(f1484,plain,
    ( spl3_101
  <=> k1_xboole_0 = k5_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_101])])).

fof(f1893,plain,
    ( spl3_103
  <=> sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_103])])).

fof(f2005,plain,
    ( sK2 = k5_xboole_0(k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK2)
    | ~ spl3_101
    | ~ spl3_103 ),
    inference(superposition,[],[f1863,f1895])).

fof(f1895,plain,
    ( sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_103 ),
    inference(avatar_component_clause,[],[f1893])).

fof(f1863,plain,
    ( ! [X0] : sK2 = k5_xboole_0(k3_xboole_0(sK2,X0),k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))
    | ~ spl3_101 ),
    inference(superposition,[],[f1853,f28])).

fof(f1853,plain,
    ( ! [X4] : sK2 = k5_xboole_0(k3_xboole_0(X4,sK2),k5_xboole_0(sK2,k3_xboole_0(X4,sK2)))
    | ~ spl3_101 ),
    inference(forward_demodulation,[],[f1852,f23])).

fof(f1852,plain,
    ( ! [X4] : k5_xboole_0(sK2,k1_xboole_0) = k5_xboole_0(k3_xboole_0(X4,sK2),k5_xboole_0(sK2,k3_xboole_0(X4,sK2)))
    | ~ spl3_101 ),
    inference(forward_demodulation,[],[f1851,f1652])).

fof(f1851,plain,
    ( ! [X4] : k5_xboole_0(k3_xboole_0(X4,sK2),k5_xboole_0(sK2,k3_xboole_0(X4,sK2))) = k5_xboole_0(sK2,k3_xboole_0(X4,k1_xboole_0))
    | ~ spl3_101 ),
    inference(forward_demodulation,[],[f1850,f1668])).

fof(f1850,plain,
    ( ! [X4] : k5_xboole_0(k3_xboole_0(X4,sK2),k5_xboole_0(sK2,k3_xboole_0(X4,sK2))) = k5_xboole_0(sK2,k3_xboole_0(X4,k5_xboole_0(sK2,sK2)))
    | ~ spl3_101 ),
    inference(forward_demodulation,[],[f1849,f25])).

fof(f1849,plain,
    ( ! [X4] : k5_xboole_0(k3_xboole_0(X4,sK2),k5_xboole_0(sK2,k3_xboole_0(X4,sK2))) = k5_xboole_0(sK2,k3_xboole_0(X4,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))))
    | ~ spl3_101 ),
    inference(forward_demodulation,[],[f1842,f43])).

fof(f1842,plain,
    ( ! [X4] : k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(X4,sK2),k3_xboole_0(k3_xboole_0(X4,sK2),sK2))) = k5_xboole_0(k3_xboole_0(X4,sK2),k5_xboole_0(sK2,k3_xboole_0(X4,sK2)))
    | ~ spl3_101 ),
    inference(superposition,[],[f41,f1770])).

fof(f1770,plain,
    ( ! [X2] : k3_xboole_0(X2,sK2) = k3_xboole_0(sK2,k3_xboole_0(X2,sK2))
    | ~ spl3_101 ),
    inference(superposition,[],[f1743,f28])).

fof(f1743,plain,
    ( ! [X0] : k3_xboole_0(sK2,X0) = k3_xboole_0(sK2,k3_xboole_0(sK2,X0))
    | ~ spl3_101 ),
    inference(forward_demodulation,[],[f1726,f1697])).

fof(f1726,plain,
    ( ! [X0] : k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))) = k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))))
    | ~ spl3_101 ),
    inference(superposition,[],[f1510,f1510])).

fof(f1510,plain,
    ( ! [X2] : k5_xboole_0(sK2,k3_xboole_0(sK2,X2)) = k3_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,X2)))
    | ~ spl3_101 ),
    inference(superposition,[],[f1501,f37])).

fof(f1501,plain,
    ( ! [X0] : k5_xboole_0(sK2,k5_xboole_0(sK2,X0)) = X0
    | ~ spl3_101 ),
    inference(forward_demodulation,[],[f1493,f1144])).

fof(f1493,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK2,k5_xboole_0(sK2,X0))
    | ~ spl3_101 ),
    inference(superposition,[],[f34,f1486])).

fof(f1486,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,sK2)
    | ~ spl3_101 ),
    inference(avatar_component_clause,[],[f1484])).

fof(f1919,plain,
    ( spl3_104
    | ~ spl3_80
    | ~ spl3_103 ),
    inference(avatar_split_clause,[],[f1914,f1893,f1101,f1916])).

fof(f1916,plain,
    ( spl3_104
  <=> sK1 = k5_xboole_0(sK1,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_104])])).

fof(f1101,plain,
    ( spl3_80
  <=> sK1 = k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).

fof(f1914,plain,
    ( sK1 = k5_xboole_0(sK1,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_80
    | ~ spl3_103 ),
    inference(forward_demodulation,[],[f1908,f1103])).

fof(f1103,plain,
    ( sK1 = k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))
    | ~ spl3_80 ),
    inference(avatar_component_clause,[],[f1101])).

fof(f1908,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_80
    | ~ spl3_103 ),
    inference(superposition,[],[f1351,f1895])).

fof(f1351,plain,
    ( ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,X0)))
    | ~ spl3_80 ),
    inference(forward_demodulation,[],[f1349,f34])).

fof(f1349,plain,
    ( ! [X0] : k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),X0)) = k5_xboole_0(sK1,X0)
    | ~ spl3_80 ),
    inference(superposition,[],[f34,f1103])).

fof(f1896,plain,
    ( spl3_103
    | ~ spl3_5
    | ~ spl3_101 ),
    inference(avatar_split_clause,[],[f1876,f1484,f96,f1893])).

fof(f1876,plain,
    ( sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_5
    | ~ spl3_101 ),
    inference(superposition,[],[f1868,f98])).

fof(f1868,plain,
    ( ! [X5] : sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(X5,k3_xboole_0(X5,sK2))))
    | ~ spl3_101 ),
    inference(backward_demodulation,[],[f1783,f1863])).

fof(f1783,plain,
    ( ! [X5] : k5_xboole_0(k3_xboole_0(sK2,X5),k5_xboole_0(sK2,k3_xboole_0(sK2,X5))) = k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(X5,k3_xboole_0(X5,sK2))))
    | ~ spl3_101 ),
    inference(forward_demodulation,[],[f1777,f43])).

fof(f1777,plain,
    ( ! [X5] : k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,X5),k3_xboole_0(k3_xboole_0(sK2,X5),sK2))) = k5_xboole_0(k3_xboole_0(sK2,X5),k5_xboole_0(sK2,k3_xboole_0(sK2,X5)))
    | ~ spl3_101 ),
    inference(superposition,[],[f41,f1743])).

fof(f1500,plain,
    ( spl3_102
    | ~ spl3_45
    | ~ spl3_101 ),
    inference(avatar_split_clause,[],[f1495,f1484,f586,f1497])).

fof(f1497,plain,
    ( spl3_102
  <=> k1_xboole_0 = k5_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_102])])).

fof(f586,plain,
    ( spl3_45
  <=> sK2 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f1495,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,sK1)
    | ~ spl3_45
    | ~ spl3_101 ),
    inference(forward_demodulation,[],[f1492,f23])).

fof(f1492,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK1,k1_xboole_0))
    | ~ spl3_45
    | ~ spl3_101 ),
    inference(superposition,[],[f834,f1486])).

fof(f834,plain,
    ( ! [X0] : k5_xboole_0(sK2,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,X0)))
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f833,f34])).

fof(f833,plain,
    ( ! [X0] : k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),X0)) = k5_xboole_0(sK2,X0)
    | ~ spl3_45 ),
    inference(superposition,[],[f34,f588])).

fof(f588,plain,
    ( sK2 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f586])).

fof(f1487,plain,
    ( spl3_101
    | ~ spl3_45
    | ~ spl3_80
    | ~ spl3_100 ),
    inference(avatar_split_clause,[],[f1482,f1467,f1101,f586,f1484])).

fof(f1467,plain,
    ( spl3_100
  <=> k5_xboole_0(sK1,sK2) = k5_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_100])])).

fof(f1482,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,sK2)
    | ~ spl3_45
    | ~ spl3_80
    | ~ spl3_100 ),
    inference(forward_demodulation,[],[f1481,f588])).

fof(f1481,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))
    | ~ spl3_80
    | ~ spl3_100 ),
    inference(forward_demodulation,[],[f1480,f1148])).

fof(f1480,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k1_xboole_0,sK1)
    | ~ spl3_80
    | ~ spl3_100 ),
    inference(forward_demodulation,[],[f1479,f28])).

fof(f1479,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_80
    | ~ spl3_100 ),
    inference(forward_demodulation,[],[f1476,f623])).

fof(f1476,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,sK1)
    | ~ spl3_80
    | ~ spl3_100 ),
    inference(superposition,[],[f1351,f1469])).

fof(f1469,plain,
    ( k5_xboole_0(sK1,sK2) = k5_xboole_0(sK2,sK1)
    | ~ spl3_100 ),
    inference(avatar_component_clause,[],[f1467])).

fof(f1470,plain,
    ( spl3_100
    | ~ spl3_5
    | ~ spl3_98
    | ~ spl3_99 ),
    inference(avatar_split_clause,[],[f1465,f1451,f1407,f96,f1467])).

fof(f1407,plain,
    ( spl3_98
  <=> k5_xboole_0(sK2,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_98])])).

fof(f1451,plain,
    ( spl3_99
  <=> sK2 = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_99])])).

fof(f1465,plain,
    ( k5_xboole_0(sK1,sK2) = k5_xboole_0(sK2,sK1)
    | ~ spl3_5
    | ~ spl3_98
    | ~ spl3_99 ),
    inference(forward_demodulation,[],[f1462,f98])).

fof(f1462,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,sK1)
    | ~ spl3_98
    | ~ spl3_99 ),
    inference(backward_demodulation,[],[f1409,f1453])).

fof(f1453,plain,
    ( sK2 = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))
    | ~ spl3_99 ),
    inference(avatar_component_clause,[],[f1451])).

fof(f1409,plain,
    ( k5_xboole_0(sK2,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))))
    | ~ spl3_98 ),
    inference(avatar_component_clause,[],[f1407])).

fof(f1454,plain,
    ( spl3_99
    | ~ spl3_80
    | ~ spl3_93 ),
    inference(avatar_split_clause,[],[f1449,f1318,f1101,f1451])).

fof(f1318,plain,
    ( spl3_93
  <=> sK1 = k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).

fof(f1449,plain,
    ( sK2 = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))
    | ~ spl3_80
    | ~ spl3_93 ),
    inference(forward_demodulation,[],[f1448,f23])).

fof(f1448,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = k5_xboole_0(sK2,k1_xboole_0)
    | ~ spl3_80
    | ~ spl3_93 ),
    inference(forward_demodulation,[],[f1447,f1148])).

fof(f1447,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK1))
    | ~ spl3_80
    | ~ spl3_93 ),
    inference(forward_demodulation,[],[f1446,f28])).

fof(f1446,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = k5_xboole_0(sK2,k3_xboole_0(sK1,k1_xboole_0))
    | ~ spl3_80
    | ~ spl3_93 ),
    inference(forward_demodulation,[],[f1433,f623])).

fof(f1433,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))
    | ~ spl3_80
    | ~ spl3_93 ),
    inference(superposition,[],[f1351,f1320])).

fof(f1320,plain,
    ( sK1 = k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))
    | ~ spl3_93 ),
    inference(avatar_component_clause,[],[f1318])).

fof(f1410,plain,
    ( spl3_98
    | ~ spl3_95 ),
    inference(avatar_split_clause,[],[f1398,f1373,f1407])).

fof(f1373,plain,
    ( spl3_95
  <=> k5_xboole_0(sK2,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_95])])).

fof(f1398,plain,
    ( k5_xboole_0(sK2,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))))
    | ~ spl3_95 ),
    inference(superposition,[],[f37,f1375])).

fof(f1375,plain,
    ( k5_xboole_0(sK2,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK2,sK1))
    | ~ spl3_95 ),
    inference(avatar_component_clause,[],[f1373])).

fof(f1397,plain,
    ( spl3_97
    | ~ spl3_96 ),
    inference(avatar_split_clause,[],[f1392,f1388,f1394])).

fof(f1394,plain,
    ( spl3_97
  <=> k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_97])])).

fof(f1388,plain,
    ( spl3_96
  <=> r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).

fof(f1392,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1)
    | ~ spl3_96 ),
    inference(resolution,[],[f1390,f33])).

fof(f1390,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1)
    | ~ spl3_96 ),
    inference(avatar_component_clause,[],[f1388])).

fof(f1391,plain,
    ( spl3_96
    | ~ spl3_88 ),
    inference(avatar_split_clause,[],[f1369,f1292,f1388])).

fof(f1292,plain,
    ( spl3_88
  <=> k5_xboole_0(sK2,sK1) = k3_xboole_0(k5_xboole_0(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_88])])).

fof(f1369,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1)
    | ~ spl3_88 ),
    inference(superposition,[],[f66,f1294])).

fof(f1294,plain,
    ( k5_xboole_0(sK2,sK1) = k3_xboole_0(k5_xboole_0(sK2,sK1),sK1)
    | ~ spl3_88 ),
    inference(avatar_component_clause,[],[f1292])).

fof(f66,plain,(
    ! [X2,X1] : r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1) ),
    inference(superposition,[],[f40,f28])).

fof(f1379,plain,
    ( spl3_95
    | ~ spl3_88 ),
    inference(avatar_split_clause,[],[f1365,f1292,f1373])).

fof(f1365,plain,
    ( k5_xboole_0(sK2,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK2,sK1))
    | ~ spl3_88 ),
    inference(superposition,[],[f28,f1294])).

fof(f1378,plain,
    ( spl3_95
    | ~ spl3_88 ),
    inference(avatar_split_clause,[],[f1364,f1292,f1373])).

fof(f1364,plain,
    ( k5_xboole_0(sK2,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK2,sK1))
    | ~ spl3_88 ),
    inference(superposition,[],[f28,f1294])).

fof(f1377,plain,
    ( spl3_95
    | ~ spl3_88 ),
    inference(avatar_split_clause,[],[f1363,f1292,f1373])).

fof(f1363,plain,
    ( k5_xboole_0(sK2,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK2,sK1))
    | ~ spl3_88 ),
    inference(superposition,[],[f1294,f28])).

fof(f1376,plain,
    ( spl3_95
    | ~ spl3_88 ),
    inference(avatar_split_clause,[],[f1362,f1292,f1373])).

fof(f1362,plain,
    ( k5_xboole_0(sK2,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK2,sK1))
    | ~ spl3_88 ),
    inference(superposition,[],[f1294,f28])).

fof(f1327,plain,
    ( spl3_94
    | ~ spl3_79
    | ~ spl3_80 ),
    inference(avatar_split_clause,[],[f1322,f1101,f1091,f1324])).

fof(f1324,plain,
    ( spl3_94
  <=> sK1 = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_94])])).

fof(f1091,plain,
    ( spl3_79
  <=> k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_79])])).

fof(f1322,plain,
    ( sK1 = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))))))
    | ~ spl3_79
    | ~ spl3_80 ),
    inference(forward_demodulation,[],[f1093,f1103])).

fof(f1093,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))))))
    | ~ spl3_79 ),
    inference(avatar_component_clause,[],[f1091])).

fof(f1321,plain,
    ( spl3_93
    | ~ spl3_80
    | ~ spl3_83 ),
    inference(avatar_split_clause,[],[f1290,f1139,f1101,f1318])).

fof(f1139,plain,
    ( spl3_83
  <=> k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).

fof(f1290,plain,
    ( sK1 = k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))
    | ~ spl3_80
    | ~ spl3_83 ),
    inference(backward_demodulation,[],[f1141,f1103])).

fof(f1141,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))
    | ~ spl3_83 ),
    inference(avatar_component_clause,[],[f1139])).

fof(f1316,plain,
    ( spl3_92
    | ~ spl3_80
    | ~ spl3_82 ),
    inference(avatar_split_clause,[],[f1289,f1126,f1101,f1313])).

fof(f1313,plain,
    ( spl3_92
  <=> sK1 = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_92])])).

fof(f1126,plain,
    ( spl3_82
  <=> k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).

fof(f1289,plain,
    ( sK1 = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))))
    | ~ spl3_80
    | ~ spl3_82 ),
    inference(backward_demodulation,[],[f1128,f1103])).

fof(f1128,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))))
    | ~ spl3_82 ),
    inference(avatar_component_clause,[],[f1126])).

fof(f1310,plain,
    ( spl3_91
    | ~ spl3_77
    | ~ spl3_80 ),
    inference(avatar_split_clause,[],[f1287,f1101,f953,f1307])).

fof(f1307,plain,
    ( spl3_91
  <=> k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_91])])).

fof(f953,plain,
    ( spl3_77
  <=> k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).

fof(f1287,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),sK1)
    | ~ spl3_77
    | ~ spl3_80 ),
    inference(backward_demodulation,[],[f955,f1103])).

fof(f955,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_77 ),
    inference(avatar_component_clause,[],[f953])).

fof(f1305,plain,
    ( spl3_90
    | ~ spl3_72
    | ~ spl3_80 ),
    inference(avatar_split_clause,[],[f1283,f1101,f843,f1302])).

fof(f1302,plain,
    ( spl3_90
  <=> r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_90])])).

fof(f843,plain,
    ( spl3_72
  <=> r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f1283,plain,
    ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),sK1)
    | ~ spl3_72
    | ~ spl3_80 ),
    inference(backward_demodulation,[],[f845,f1103])).

fof(f845,plain,
    ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_72 ),
    inference(avatar_component_clause,[],[f843])).

fof(f1300,plain,
    ( spl3_89
    | ~ spl3_60
    | ~ spl3_80 ),
    inference(avatar_split_clause,[],[f1282,f1101,f709,f1297])).

fof(f1297,plain,
    ( spl3_89
  <=> r1_tarski(k5_xboole_0(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_89])])).

fof(f709,plain,
    ( spl3_60
  <=> r1_tarski(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f1282,plain,
    ( r1_tarski(k5_xboole_0(sK2,sK1),sK1)
    | ~ spl3_60
    | ~ spl3_80 ),
    inference(backward_demodulation,[],[f711,f1103])).

fof(f711,plain,
    ( r1_tarski(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_60 ),
    inference(avatar_component_clause,[],[f709])).

fof(f1295,plain,
    ( spl3_88
    | ~ spl3_58
    | ~ spl3_80 ),
    inference(avatar_split_clause,[],[f1281,f1101,f697,f1292])).

fof(f697,plain,
    ( spl3_58
  <=> k5_xboole_0(sK2,sK1) = k3_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f1281,plain,
    ( k5_xboole_0(sK2,sK1) = k3_xboole_0(k5_xboole_0(sK2,sK1),sK1)
    | ~ spl3_58
    | ~ spl3_80 ),
    inference(backward_demodulation,[],[f699,f1103])).

fof(f699,plain,
    ( k5_xboole_0(sK2,sK1) = k3_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f697])).

fof(f1279,plain,
    ( spl3_87
    | ~ spl3_61
    | ~ spl3_83 ),
    inference(avatar_split_clause,[],[f1259,f1139,f715,f1276])).

fof(f1276,plain,
    ( spl3_87
  <=> r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_87])])).

fof(f715,plain,
    ( spl3_61
  <=> r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f1259,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))),sK1)
    | ~ spl3_61
    | ~ spl3_83 ),
    inference(backward_demodulation,[],[f717,f1141])).

fof(f717,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),sK1)
    | ~ spl3_61 ),
    inference(avatar_component_clause,[],[f715])).

fof(f1274,plain,
    ( spl3_86
    | ~ spl3_59
    | ~ spl3_83 ),
    inference(avatar_split_clause,[],[f1258,f1139,f703,f1271])).

fof(f1271,plain,
    ( spl3_86
  <=> k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).

fof(f703,plain,
    ( spl3_59
  <=> k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f1258,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))),sK1)
    | ~ spl3_59
    | ~ spl3_83 ),
    inference(backward_demodulation,[],[f705,f1141])).

fof(f705,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),sK1)
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f703])).

fof(f1269,plain,
    ( spl3_85
    | ~ spl3_76
    | ~ spl3_83 ),
    inference(avatar_split_clause,[],[f1257,f1139,f947,f1266])).

fof(f1266,plain,
    ( spl3_85
  <=> r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).

fof(f947,plain,
    ( spl3_76
  <=> r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f1257,plain,
    ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_76
    | ~ spl3_83 ),
    inference(backward_demodulation,[],[f949,f1141])).

fof(f949,plain,
    ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_76 ),
    inference(avatar_component_clause,[],[f947])).

fof(f1264,plain,
    ( spl3_84
    | ~ spl3_78
    | ~ spl3_83 ),
    inference(avatar_split_clause,[],[f1256,f1139,f973,f1261])).

fof(f1261,plain,
    ( spl3_84
  <=> k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).

fof(f973,plain,
    ( spl3_78
  <=> k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).

fof(f1256,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_78
    | ~ spl3_83 ),
    inference(backward_demodulation,[],[f975,f1141])).

fof(f975,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_78 ),
    inference(avatar_component_clause,[],[f973])).

fof(f1221,plain,
    ( spl3_83
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f1220,f415,f1139])).

fof(f415,plain,
    ( spl3_30
  <=> sK2 = k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f1220,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f1219,f23])).

fof(f1219,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k1_xboole_0)
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f1218,f23])).

fof(f1218,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k1_xboole_0) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k1_xboole_0)))
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f1217,f1148])).

fof(f1217,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k1_xboole_0,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))))
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f1216,f28])).

fof(f1216,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(sK2,k1_xboole_0)) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0))))
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f1215,f623])).

fof(f1215,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))))
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f1214,f417])).

fof(f417,plain,
    ( sK2 = k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f415])).

fof(f1214,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))))
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f1213,f28])).

fof(f1213,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK2)))))
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f1212,f34])).

fof(f1212,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK2))))
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f1051,f34])).

fof(f1051,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK2)))
    | ~ spl3_30 ),
    inference(superposition,[],[f41,f417])).

fof(f1211,plain,
    ( spl3_82
    | ~ spl3_73 ),
    inference(avatar_split_clause,[],[f1210,f851,f1126])).

fof(f851,plain,
    ( spl3_73
  <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).

fof(f1210,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))))
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f1209,f23])).

fof(f1209,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k1_xboole_0)
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f1208,f1148])).

fof(f1208,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k1_xboole_0,sK1))
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f1207,f28])).

fof(f1207,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(sK1,k1_xboole_0))
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f1206,f623])).

fof(f1206,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))))
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f1205,f853])).

fof(f853,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_73 ),
    inference(avatar_component_clause,[],[f851])).

fof(f1205,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))))
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f1204,f28])).

fof(f1204,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK1)))))
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f1203,f34])).

fof(f1203,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK1))))
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f1050,f34])).

fof(f1050,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK1)))
    | ~ spl3_73 ),
    inference(superposition,[],[f41,f853])).

fof(f1202,plain,
    ( spl3_81
    | ~ spl3_9
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f1201,f586,f130,f1114])).

fof(f1114,plain,
    ( spl3_81
  <=> sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).

fof(f1201,plain,
    ( sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))
    | ~ spl3_9
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f1200,f132])).

fof(f1200,plain,
    ( sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_9
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f1199,f28])).

fof(f1199,plain,
    ( sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))))
    | ~ spl3_9
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f1198,f34])).

fof(f1198,plain,
    ( sK1 = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1)))
    | ~ spl3_9
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f1197,f23])).

fof(f1197,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_9
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f1196,f1148])).

fof(f1196,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))) = k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))
    | ~ spl3_9
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f1195,f28])).

fof(f1195,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))) = k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0))
    | ~ spl3_9
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f1194,f623])).

fof(f1194,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))
    | ~ spl3_9
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f1193,f588])).

fof(f1193,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f1049,f34])).

fof(f1049,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))) = k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))
    | ~ spl3_9 ),
    inference(superposition,[],[f41,f132])).

fof(f1192,plain,
    ( spl3_80
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f1191,f96,f1101])).

fof(f1191,plain,
    ( sK1 = k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f1190,f23])).

fof(f1190,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f1189,f1148])).

fof(f1189,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f1188,f28])).

fof(f1188,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f1187,f623])).

fof(f1187,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f1186,f98])).

fof(f1186,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f1048,f28])).

fof(f1048,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)))
    | ~ spl3_5 ),
    inference(superposition,[],[f41,f98])).

fof(f1185,plain,
    ( spl3_79
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f1184,f697,f1091])).

fof(f1184,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))))))
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f1183,f23])).

fof(f1183,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))))) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0)))
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f1182,f1148])).

fof(f1182,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,k5_xboole_0(sK2,sK1))))) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))))))
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f1181,f28])).

fof(f1181,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0)))) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))))))
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f1180,f34])).

fof(f1180,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))))) = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0)))
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f1179,f34])).

fof(f1179,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))))) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0))
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f1178,f623])).

fof(f1178,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1))) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))))))
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f1177,f34])).

fof(f1177,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))))
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f1176,f699])).

fof(f1176,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))))
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f1175,f28])).

fof(f1175,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK1))))))
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f1174,f34])).

fof(f1174,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK1)))))
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f1047,f34])).

fof(f1047,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK1))))
    | ~ spl3_58 ),
    inference(superposition,[],[f41,f699])).

fof(f1142,plain,
    ( spl3_83
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f1137,f415,f1139])).

fof(f1137,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f1136,f693])).

fof(f1136,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k1_xboole_0,sK2))
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f1135,f693])).

fof(f1135,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k1_xboole_0,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))))
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f1134,f28])).

fof(f1134,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(sK2,k1_xboole_0)) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0))))
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f1133,f623])).

fof(f1133,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))))
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f1132,f417])).

fof(f1132,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))))
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f1131,f28])).

fof(f1131,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK2)))))
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f1130,f34])).

fof(f1130,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK2))))
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f1038,f34])).

fof(f1038,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK2)))
    | ~ spl3_30 ),
    inference(superposition,[],[f41,f417])).

fof(f1129,plain,
    ( spl3_82
    | ~ spl3_73 ),
    inference(avatar_split_clause,[],[f1124,f851,f1126])).

fof(f1124,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))))
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f1123,f693])).

fof(f1123,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k1_xboole_0,sK1))
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f1122,f28])).

fof(f1122,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(sK1,k1_xboole_0))
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f1121,f623])).

fof(f1121,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))))
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f1120,f853])).

fof(f1120,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))))
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f1119,f28])).

fof(f1119,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK1)))))
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f1118,f34])).

fof(f1118,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK1))))
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f1037,f34])).

fof(f1037,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK1)))
    | ~ spl3_73 ),
    inference(superposition,[],[f41,f853])).

fof(f1117,plain,
    ( spl3_81
    | ~ spl3_9
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f1112,f586,f130,f1114])).

fof(f1112,plain,
    ( sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))
    | ~ spl3_9
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f1111,f132])).

fof(f1111,plain,
    ( sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_9
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f1110,f28])).

fof(f1110,plain,
    ( sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))))
    | ~ spl3_9
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f1109,f34])).

fof(f1109,plain,
    ( sK1 = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1)))
    | ~ spl3_9
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f1108,f693])).

fof(f1108,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))) = k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))
    | ~ spl3_9
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f1107,f28])).

fof(f1107,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))) = k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0))
    | ~ spl3_9
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f1106,f623])).

fof(f1106,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))
    | ~ spl3_9
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f1105,f588])).

fof(f1105,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f1036,f34])).

fof(f1036,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))) = k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))
    | ~ spl3_9 ),
    inference(superposition,[],[f41,f132])).

fof(f1104,plain,
    ( spl3_80
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f1099,f96,f1101])).

fof(f1099,plain,
    ( sK1 = k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f1098,f693])).

fof(f1098,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f1097,f28])).

fof(f1097,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f1096,f623])).

fof(f1096,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f1095,f98])).

fof(f1095,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f1035,f28])).

fof(f1035,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)))
    | ~ spl3_5 ),
    inference(superposition,[],[f41,f98])).

fof(f1094,plain,
    ( spl3_79
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f1089,f697,f1091])).

fof(f1089,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))))))
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f1088,f693])).

fof(f1088,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,k5_xboole_0(sK2,sK1))))) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))))))
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f1087,f28])).

fof(f1087,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0)))) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))))))
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f1086,f34])).

fof(f1086,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))))) = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0)))
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f1085,f34])).

fof(f1085,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))))) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0))
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f1084,f623])).

fof(f1084,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1))) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))))))
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f1083,f34])).

fof(f1083,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))))
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f1082,f699])).

fof(f1082,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))))
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f1081,f28])).

fof(f1081,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK1))))))
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f1080,f34])).

fof(f1080,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK1)))))
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f1034,f34])).

fof(f1034,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK1))))
    | ~ spl3_58 ),
    inference(superposition,[],[f41,f699])).

fof(f976,plain,
    ( spl3_78
    | ~ spl3_76 ),
    inference(avatar_split_clause,[],[f971,f947,f973])).

fof(f971,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_76 ),
    inference(resolution,[],[f949,f33])).

fof(f956,plain,
    ( spl3_77
    | ~ spl3_72 ),
    inference(avatar_split_clause,[],[f951,f843,f953])).

fof(f951,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_72 ),
    inference(resolution,[],[f845,f33])).

fof(f950,plain,
    ( spl3_76
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f945,f697,f947])).

fof(f945,plain,
    ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f944,f34])).

fof(f944,plain,
    ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK2,sK1))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f933,f34])).

fof(f933,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK1)),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_58 ),
    inference(superposition,[],[f66,f699])).

fof(f927,plain,
    ( spl3_75
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f917,f415,f924])).

fof(f924,plain,
    ( spl3_75
  <=> r1_tarski(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).

fof(f917,plain,
    ( r1_tarski(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_30 ),
    inference(superposition,[],[f898,f417])).

fof(f922,plain,
    ( spl3_74
    | ~ spl3_73 ),
    inference(avatar_split_clause,[],[f915,f851,f919])).

fof(f919,plain,
    ( spl3_74
  <=> r1_tarski(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).

fof(f915,plain,
    ( r1_tarski(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_73 ),
    inference(superposition,[],[f898,f853])).

fof(f857,plain,
    ( spl3_73
    | ~ spl3_25
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f840,f586,f375,f851])).

fof(f375,plain,
    ( spl3_25
  <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f840,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_25
    | ~ spl3_45 ),
    inference(backward_demodulation,[],[f377,f834])).

fof(f377,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f375])).

fof(f856,plain,
    ( spl3_73
    | ~ spl3_45
    | ~ spl3_67 ),
    inference(avatar_split_clause,[],[f855,f769,f586,f851])).

fof(f769,plain,
    ( spl3_67
  <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f855,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_45
    | ~ spl3_67 ),
    inference(forward_demodulation,[],[f839,f834])).

fof(f839,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_45
    | ~ spl3_67 ),
    inference(backward_demodulation,[],[f771,f834])).

fof(f771,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))))
    | ~ spl3_67 ),
    inference(avatar_component_clause,[],[f769])).

fof(f854,plain,
    ( spl3_73
    | ~ spl3_45
    | ~ spl3_71 ),
    inference(avatar_split_clause,[],[f849,f820,f586,f851])).

fof(f820,plain,
    ( spl3_71
  <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).

fof(f849,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_45
    | ~ spl3_71 ),
    inference(forward_demodulation,[],[f848,f834])).

fof(f848,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_45
    | ~ spl3_71 ),
    inference(forward_demodulation,[],[f838,f834])).

fof(f838,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))))
    | ~ spl3_45
    | ~ spl3_71 ),
    inference(backward_demodulation,[],[f822,f834])).

fof(f822,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))))))
    | ~ spl3_71 ),
    inference(avatar_component_clause,[],[f820])).

fof(f846,plain,
    ( spl3_72
    | ~ spl3_43
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f841,f586,f524,f843])).

fof(f524,plain,
    ( spl3_43
  <=> r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f841,plain,
    ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_43
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f835,f834])).

fof(f835,plain,
    ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_43
    | ~ spl3_45 ),
    inference(backward_demodulation,[],[f526,f834])).

fof(f526,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f524])).

fof(f823,plain,
    ( spl3_71
    | ~ spl3_45
    | ~ spl3_63 ),
    inference(avatar_split_clause,[],[f818,f739,f586,f820])).

fof(f739,plain,
    ( spl3_63
  <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f818,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))))))
    | ~ spl3_45
    | ~ spl3_63 ),
    inference(forward_demodulation,[],[f741,f588])).

fof(f741,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))))
    | ~ spl3_63 ),
    inference(avatar_component_clause,[],[f739])).

fof(f817,plain,
    ( spl3_70
    | ~ spl3_45
    | ~ spl3_64 ),
    inference(avatar_split_clause,[],[f812,f744,f586,f814])).

fof(f814,plain,
    ( spl3_70
  <=> sK2 = k3_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f744,plain,
    ( spl3_64
  <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f812,plain,
    ( sK2 = k3_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))))
    | ~ spl3_45
    | ~ spl3_64 ),
    inference(forward_demodulation,[],[f811,f588])).

fof(f811,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))))
    | ~ spl3_45
    | ~ spl3_64 ),
    inference(forward_demodulation,[],[f746,f588])).

fof(f746,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))
    | ~ spl3_64 ),
    inference(avatar_component_clause,[],[f744])).

fof(f796,plain,
    ( spl3_69
    | ~ spl3_45
    | ~ spl3_68 ),
    inference(avatar_split_clause,[],[f791,f774,f586,f793])).

fof(f793,plain,
    ( spl3_69
  <=> sK2 = k3_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f774,plain,
    ( spl3_68
  <=> k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f791,plain,
    ( sK2 = k3_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_45
    | ~ spl3_68 ),
    inference(forward_demodulation,[],[f776,f588])).

fof(f776,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_68 ),
    inference(avatar_component_clause,[],[f774])).

fof(f777,plain,
    ( spl3_68
    | ~ spl3_32
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f767,f592,f428,f774])).

fof(f428,plain,
    ( spl3_32
  <=> k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f592,plain,
    ( spl3_46
  <=> k5_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f767,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_32
    | ~ spl3_46 ),
    inference(backward_demodulation,[],[f430,f594])).

fof(f594,plain,
    ( k5_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f592])).

fof(f430,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f428])).

fof(f772,plain,
    ( spl3_67
    | ~ spl3_27
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f766,f592,f390,f769])).

fof(f390,plain,
    ( spl3_27
  <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f766,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))))
    | ~ spl3_27
    | ~ spl3_46 ),
    inference(backward_demodulation,[],[f392,f594])).

fof(f392,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f390])).

fof(f762,plain,
    ( spl3_66
    | ~ spl3_33
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f752,f598,f436,f759])).

fof(f759,plain,
    ( spl3_66
  <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f436,plain,
    ( spl3_33
  <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f598,plain,
    ( spl3_47
  <=> k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f752,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))
    | ~ spl3_33
    | ~ spl3_47 ),
    inference(backward_demodulation,[],[f438,f600])).

fof(f600,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f598])).

fof(f438,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f436])).

fof(f757,plain,
    ( spl3_65
    | ~ spl3_28
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f751,f598,f399,f754])).

fof(f754,plain,
    ( spl3_65
  <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f399,plain,
    ( spl3_28
  <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f751,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))
    | ~ spl3_28
    | ~ spl3_47 ),
    inference(backward_demodulation,[],[f401,f600])).

fof(f401,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f399])).

fof(f747,plain,
    ( spl3_64
    | ~ spl3_34
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f737,f604,f445,f744])).

fof(f445,plain,
    ( spl3_34
  <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f604,plain,
    ( spl3_48
  <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f737,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))
    | ~ spl3_34
    | ~ spl3_48 ),
    inference(backward_demodulation,[],[f447,f606])).

fof(f606,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f604])).

fof(f447,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f445])).

fof(f742,plain,
    ( spl3_63
    | ~ spl3_29
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f736,f604,f409,f739])).

fof(f409,plain,
    ( spl3_29
  <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f736,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))))
    | ~ spl3_29
    | ~ spl3_48 ),
    inference(backward_demodulation,[],[f411,f606])).

fof(f411,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))))))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f409])).

fof(f732,plain,
    ( spl3_62
    | ~ spl3_35
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f725,f610,f455,f729])).

fof(f729,plain,
    ( spl3_62
  <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f455,plain,
    ( spl3_35
  <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f610,plain,
    ( spl3_49
  <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f725,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))))
    | ~ spl3_35
    | ~ spl3_49 ),
    inference(backward_demodulation,[],[f457,f612])).

fof(f612,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f610])).

fof(f457,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))))))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f455])).

fof(f718,plain,
    ( spl3_61
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f713,f661,f715])).

fof(f661,plain,
    ( spl3_54
  <=> r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f713,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),sK1)
    | ~ spl3_54 ),
    inference(forward_demodulation,[],[f663,f693])).

fof(f663,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2)))
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f661])).

fof(f712,plain,
    ( spl3_60
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f707,f667,f709])).

fof(f667,plain,
    ( spl3_55
  <=> r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f707,plain,
    ( r1_tarski(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_55 ),
    inference(forward_demodulation,[],[f669,f693])).

fof(f669,plain,
    ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f667])).

fof(f706,plain,
    ( spl3_59
    | ~ spl3_56 ),
    inference(avatar_split_clause,[],[f701,f673,f703])).

fof(f673,plain,
    ( spl3_56
  <=> k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f701,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),sK1)
    | ~ spl3_56 ),
    inference(forward_demodulation,[],[f675,f693])).

fof(f675,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2)))
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f673])).

fof(f700,plain,
    ( spl3_58
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f695,f679,f697])).

fof(f679,plain,
    ( spl3_57
  <=> k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f695,plain,
    ( k5_xboole_0(sK2,sK1) = k3_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_57 ),
    inference(forward_demodulation,[],[f681,f693])).

fof(f681,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f679])).

fof(f682,plain,
    ( spl3_57
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f677,f530,f679])).

fof(f530,plain,
    ( spl3_44
  <=> k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f677,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f638,f28])).

fof(f638,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_44 ),
    inference(backward_demodulation,[],[f532,f623])).

fof(f532,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f530])).

fof(f676,plain,
    ( spl3_56
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f671,f503,f673])).

fof(f503,plain,
    ( spl3_41
  <=> k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f671,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2)))
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f637,f28])).

fof(f637,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0)))
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f505,f623])).

fof(f505,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)))
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f503])).

fof(f670,plain,
    ( spl3_55
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f665,f497,f667])).

fof(f497,plain,
    ( spl3_40
  <=> r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f665,plain,
    ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_40 ),
    inference(forward_demodulation,[],[f636,f28])).

fof(f636,plain,
    ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_40 ),
    inference(backward_demodulation,[],[f499,f623])).

fof(f499,plain,
    ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f497])).

fof(f664,plain,
    ( spl3_54
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f659,f480,f661])).

fof(f480,plain,
    ( spl3_38
  <=> r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f659,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2)))
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f635,f28])).

fof(f635,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0)))
    | ~ spl3_38 ),
    inference(backward_demodulation,[],[f482,f623])).

fof(f482,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)))
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f480])).

fof(f658,plain,
    ( spl3_53
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f653,f460,f655])).

fof(f655,plain,
    ( spl3_53
  <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f460,plain,
    ( spl3_36
  <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f653,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2)))
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f634,f28])).

fof(f634,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0)))
    | ~ spl3_36 ),
    inference(backward_demodulation,[],[f462,f623])).

fof(f462,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f460])).

fof(f652,plain,
    ( spl3_52
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f647,f473,f649])).

fof(f649,plain,
    ( spl3_52
  <=> k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f473,plain,
    ( spl3_37
  <=> k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f647,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK1)))))
    | ~ spl3_37 ),
    inference(forward_demodulation,[],[f646,f28])).

fof(f646,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0)) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0)),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK1)))))
    | ~ spl3_37 ),
    inference(forward_demodulation,[],[f645,f623])).

fof(f645,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK1)))))
    | ~ spl3_37 ),
    inference(forward_demodulation,[],[f633,f28])).

fof(f633,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK1,k1_xboole_0)))))
    | ~ spl3_37 ),
    inference(backward_demodulation,[],[f475,f623])).

fof(f475,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK1)))))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f473])).

fof(f644,plain,
    ( spl3_51
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f639,f515,f641])).

fof(f641,plain,
    ( spl3_51
  <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f515,plain,
    ( spl3_42
  <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f639,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK1)))))))
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f632,f28])).

fof(f632,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,k1_xboole_0)))))))
    | ~ spl3_42 ),
    inference(backward_demodulation,[],[f517,f623])).

fof(f517,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK1)))))))
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f515])).

fof(f618,plain,
    ( spl3_50
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f550,f254,f615])).

fof(f615,plain,
    ( spl3_50
  <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f254,plain,
    ( spl3_21
  <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f550,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))
    | ~ spl3_21 ),
    inference(superposition,[],[f37,f256])).

fof(f256,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f254])).

fof(f613,plain,
    ( spl3_49
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f608,f254,f211,f610])).

fof(f211,plain,
    ( spl3_18
  <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f608,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f549,f256])).

fof(f549,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))
    | ~ spl3_18 ),
    inference(superposition,[],[f37,f213])).

fof(f213,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f211])).

fof(f607,plain,
    ( spl3_48
    | ~ spl3_15
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f602,f211,f184,f604])).

fof(f184,plain,
    ( spl3_15
  <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f602,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_15
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f548,f213])).

fof(f548,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))
    | ~ spl3_15 ),
    inference(superposition,[],[f37,f186])).

fof(f186,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f184])).

fof(f601,plain,
    ( spl3_47
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f596,f184,f157,f598])).

fof(f157,plain,
    ( spl3_12
  <=> k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f596,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f547,f186])).

fof(f547,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_12 ),
    inference(superposition,[],[f37,f159])).

fof(f159,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f157])).

fof(f595,plain,
    ( spl3_46
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f590,f157,f130,f592])).

fof(f590,plain,
    ( k5_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f546,f159])).

fof(f546,plain,
    ( k5_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))
    | ~ spl3_9 ),
    inference(superposition,[],[f37,f132])).

fof(f589,plain,
    ( spl3_45
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f584,f130,f96,f586])).

fof(f584,plain,
    ( sK2 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f545,f132])).

fof(f545,plain,
    ( sK2 = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)))
    | ~ spl3_5 ),
    inference(superposition,[],[f37,f98])).

fof(f533,plain,
    ( spl3_44
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f528,f497,f530])).

fof(f528,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_40 ),
    inference(resolution,[],[f499,f33])).

fof(f527,plain,
    ( spl3_43
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f522,f375,f524])).

fof(f522,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f521,f34])).

fof(f521,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f520,f34])).

fof(f520,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK1))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f519,f34])).

fof(f519,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))),sK1)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f508,f34])).

fof(f508,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),sK1),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_25 ),
    inference(superposition,[],[f66,f377])).

fof(f518,plain,
    ( spl3_42
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f513,f375,f515])).

fof(f513,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK1)))))))
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f512,f34])).

fof(f512,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK1))))))
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f511,f34])).

fof(f511,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK1)))))
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f510,f34])).

fof(f510,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,sK1))))
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f507,f34])).

fof(f507,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,sK1)))
    | ~ spl3_25 ),
    inference(superposition,[],[f42,f377])).

fof(f506,plain,
    ( spl3_41
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f501,f480,f503])).

fof(f501,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)))
    | ~ spl3_38 ),
    inference(resolution,[],[f482,f33])).

fof(f500,plain,
    ( spl3_40
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f495,f415,f497])).

fof(f495,plain,
    ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f494,f34])).

fof(f494,plain,
    ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),sK2)),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f485,f34])).

fof(f485,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK2),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_30 ),
    inference(superposition,[],[f66,f417])).

fof(f493,plain,
    ( spl3_39
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f488,f415,f490])).

fof(f490,plain,
    ( spl3_39
  <=> k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f488,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK2)))))
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f487,f34])).

fof(f487,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK2,sK2))))
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f484,f34])).

fof(f484,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK2)))
    | ~ spl3_30 ),
    inference(superposition,[],[f42,f417])).

fof(f483,plain,
    ( spl3_38
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f478,f460,f480])).

fof(f478,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)))
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f477,f34])).

fof(f477,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,sK2),sK1)),k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)))
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f468,f34])).

fof(f468,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)),sK1),k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)))
    | ~ spl3_36 ),
    inference(superposition,[],[f66,f462])).

fof(f476,plain,
    ( spl3_37
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f471,f460,f473])).

fof(f471,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK1)))))
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f470,f34])).

fof(f470,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(sK1,sK1))))
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f467,f34])).

fof(f467,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)),k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)),k5_xboole_0(sK1,sK1)))
    | ~ spl3_36 ),
    inference(superposition,[],[f42,f462])).

fof(f463,plain,
    ( spl3_36
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f361,f85,f460])).

fof(f361,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)))
    | ~ spl3_4 ),
    inference(superposition,[],[f42,f87])).

fof(f458,plain,
    ( spl3_35
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f453,f254,f455])).

fof(f453,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))))))
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f452,f34])).

fof(f452,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))))
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f451,f34])).

fof(f451,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))))
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f450,f34])).

fof(f450,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f449,f34])).

fof(f449,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f360,f34])).

fof(f360,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))
    | ~ spl3_21 ),
    inference(superposition,[],[f42,f256])).

fof(f448,plain,
    ( spl3_34
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f443,f211,f445])).

fof(f443,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))))
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f442,f34])).

fof(f442,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f441,f34])).

fof(f441,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f440,f34])).

fof(f440,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f359,f34])).

fof(f359,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))
    | ~ spl3_18 ),
    inference(superposition,[],[f42,f213])).

fof(f439,plain,
    ( spl3_33
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f434,f184,f436])).

fof(f434,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f433,f34])).

fof(f433,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f432,f34])).

fof(f432,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f358,f34])).

fof(f358,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))
    | ~ spl3_15 ),
    inference(superposition,[],[f42,f186])).

fof(f431,plain,
    ( spl3_32
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f426,f157,f428])).

fof(f426,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f425,f34])).

fof(f425,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f357,f34])).

fof(f357,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_12 ),
    inference(superposition,[],[f42,f159])).

fof(f424,plain,
    ( spl3_31
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f419,f130,f421])).

fof(f421,plain,
    ( spl3_31
  <=> k5_xboole_0(sK1,sK2) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f419,plain,
    ( k5_xboole_0(sK1,sK2) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f356,f34])).

fof(f356,plain,
    ( k5_xboole_0(sK1,sK2) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))
    | ~ spl3_9 ),
    inference(superposition,[],[f42,f132])).

fof(f418,plain,
    ( spl3_30
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f355,f96,f415])).

fof(f355,plain,
    ( sK2 = k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_5 ),
    inference(superposition,[],[f42,f98])).

fof(f412,plain,
    ( spl3_29
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f407,f225,f409])).

fof(f225,plain,
    ( spl3_20
  <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f407,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))))))
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f406,f34])).

fof(f406,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))))
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f405,f34])).

fof(f405,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))))
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f404,f34])).

fof(f404,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f403,f34])).

fof(f403,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f353,f34])).

fof(f353,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))
    | ~ spl3_20 ),
    inference(superposition,[],[f42,f227])).

fof(f227,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),sK1)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f225])).

fof(f402,plain,
    ( spl3_28
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f397,f198,f399])).

fof(f198,plain,
    ( spl3_17
  <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f397,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))))
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f396,f34])).

fof(f396,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f395,f34])).

fof(f395,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f394,f34])).

fof(f394,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f352,f34])).

fof(f352,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))
    | ~ spl3_17 ),
    inference(superposition,[],[f42,f200])).

fof(f200,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),sK1)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f198])).

fof(f393,plain,
    ( spl3_27
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f388,f171,f390])).

fof(f171,plain,
    ( spl3_14
  <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f388,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f387,f34])).

fof(f387,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f386,f34])).

fof(f386,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f351,f34])).

fof(f351,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))
    | ~ spl3_14 ),
    inference(superposition,[],[f42,f173])).

fof(f173,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f171])).

fof(f385,plain,
    ( spl3_26
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f380,f144,f382])).

fof(f382,plain,
    ( spl3_26
  <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f144,plain,
    ( spl3_11
  <=> k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f380,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f379,f34])).

fof(f379,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f350,f34])).

fof(f350,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_11 ),
    inference(superposition,[],[f42,f146])).

fof(f146,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f144])).

fof(f378,plain,
    ( spl3_25
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f373,f119,f375])).

fof(f119,plain,
    ( spl3_8
  <=> k5_xboole_0(sK1,sK2) = k3_xboole_0(k5_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f373,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f349,f34])).

fof(f349,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))))
    | ~ spl3_8 ),
    inference(superposition,[],[f42,f121])).

fof(f121,plain,
    ( k5_xboole_0(sK1,sK2) = k3_xboole_0(k5_xboole_0(sK1,sK2),sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f119])).

fof(f299,plain,
    ( ~ spl3_24
    | spl3_7 ),
    inference(avatar_split_clause,[],[f281,f111,f296])).

fof(f281,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))))
    | spl3_7 ),
    inference(superposition,[],[f113,f34])).

fof(f271,plain,
    ( spl3_23
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f266,f260,f268])).

fof(f268,plain,
    ( spl3_23
  <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f260,plain,
    ( spl3_22
  <=> r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f266,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))),sK1)
    | ~ spl3_22 ),
    inference(resolution,[],[f262,f33])).

fof(f262,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))),sK1)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f260])).

fof(f265,plain,
    ( spl3_21
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f252,f225,f254])).

fof(f252,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))
    | ~ spl3_20 ),
    inference(superposition,[],[f28,f227])).

fof(f264,plain,
    ( spl3_21
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f251,f225,f254])).

fof(f251,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))
    | ~ spl3_20 ),
    inference(superposition,[],[f28,f227])).

fof(f263,plain,
    ( spl3_22
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f249,f225,f260])).

fof(f249,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))),sK1)
    | ~ spl3_20 ),
    inference(superposition,[],[f66,f227])).

fof(f258,plain,
    ( spl3_21
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f248,f225,f254])).

fof(f248,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))
    | ~ spl3_20 ),
    inference(superposition,[],[f227,f28])).

fof(f257,plain,
    ( spl3_21
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f247,f225,f254])).

fof(f247,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))
    | ~ spl3_20 ),
    inference(superposition,[],[f227,f28])).

fof(f228,plain,
    ( spl3_20
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f223,f217,f225])).

fof(f217,plain,
    ( spl3_19
  <=> r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f223,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),sK1)
    | ~ spl3_19 ),
    inference(resolution,[],[f219,f33])).

fof(f219,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),sK1)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f217])).

fof(f222,plain,
    ( spl3_18
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f209,f198,f211])).

fof(f209,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_17 ),
    inference(superposition,[],[f28,f200])).

fof(f221,plain,
    ( spl3_18
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f208,f198,f211])).

fof(f208,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_17 ),
    inference(superposition,[],[f28,f200])).

fof(f220,plain,
    ( spl3_19
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f206,f198,f217])).

fof(f206,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),sK1)
    | ~ spl3_17 ),
    inference(superposition,[],[f66,f200])).

fof(f215,plain,
    ( spl3_18
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f205,f198,f211])).

fof(f205,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_17 ),
    inference(superposition,[],[f200,f28])).

fof(f214,plain,
    ( spl3_18
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f204,f198,f211])).

fof(f204,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))
    | ~ spl3_17 ),
    inference(superposition,[],[f200,f28])).

fof(f201,plain,
    ( spl3_17
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f196,f190,f198])).

fof(f190,plain,
    ( spl3_16
  <=> r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f196,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),sK1)
    | ~ spl3_16 ),
    inference(resolution,[],[f192,f33])).

fof(f192,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),sK1)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f190])).

fof(f195,plain,
    ( spl3_15
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f182,f171,f184])).

fof(f182,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))
    | ~ spl3_14 ),
    inference(superposition,[],[f28,f173])).

fof(f194,plain,
    ( spl3_15
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f181,f171,f184])).

fof(f181,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))
    | ~ spl3_14 ),
    inference(superposition,[],[f28,f173])).

fof(f193,plain,
    ( spl3_16
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f179,f171,f190])).

fof(f179,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),sK1)
    | ~ spl3_14 ),
    inference(superposition,[],[f66,f173])).

fof(f188,plain,
    ( spl3_15
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f178,f171,f184])).

fof(f178,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))
    | ~ spl3_14 ),
    inference(superposition,[],[f173,f28])).

fof(f187,plain,
    ( spl3_15
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f177,f171,f184])).

fof(f177,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))
    | ~ spl3_14 ),
    inference(superposition,[],[f173,f28])).

fof(f174,plain,
    ( spl3_14
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f169,f163,f171])).

fof(f163,plain,
    ( spl3_13
  <=> r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f169,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),sK1)
    | ~ spl3_13 ),
    inference(resolution,[],[f165,f33])).

fof(f165,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),sK1)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f163])).

fof(f168,plain,
    ( spl3_12
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f155,f144,f157])).

fof(f155,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))
    | ~ spl3_11 ),
    inference(superposition,[],[f28,f146])).

fof(f167,plain,
    ( spl3_12
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f154,f144,f157])).

fof(f154,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))
    | ~ spl3_11 ),
    inference(superposition,[],[f28,f146])).

fof(f166,plain,
    ( spl3_13
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f152,f144,f163])).

fof(f152,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),sK1)
    | ~ spl3_11 ),
    inference(superposition,[],[f66,f146])).

fof(f161,plain,
    ( spl3_12
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f151,f144,f157])).

fof(f151,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))
    | ~ spl3_11 ),
    inference(superposition,[],[f146,f28])).

fof(f160,plain,
    ( spl3_12
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f150,f144,f157])).

fof(f150,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))
    | ~ spl3_11 ),
    inference(superposition,[],[f146,f28])).

fof(f147,plain,
    ( spl3_11
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f142,f136,f144])).

fof(f136,plain,
    ( spl3_10
  <=> r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f142,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),sK1)
    | ~ spl3_10 ),
    inference(resolution,[],[f138,f33])).

fof(f138,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f136])).

fof(f141,plain,
    ( spl3_9
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f128,f119,f130])).

fof(f128,plain,
    ( k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ spl3_8 ),
    inference(superposition,[],[f28,f121])).

fof(f140,plain,
    ( spl3_9
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f127,f119,f130])).

fof(f127,plain,
    ( k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ spl3_8 ),
    inference(superposition,[],[f28,f121])).

fof(f139,plain,
    ( spl3_10
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f125,f119,f136])).

fof(f125,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),sK1)
    | ~ spl3_8 ),
    inference(superposition,[],[f66,f121])).

fof(f134,plain,
    ( spl3_9
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f124,f119,f130])).

fof(f124,plain,
    ( k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ spl3_8 ),
    inference(superposition,[],[f121,f28])).

fof(f133,plain,
    ( spl3_9
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f123,f119,f130])).

fof(f123,plain,
    ( k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ spl3_8 ),
    inference(superposition,[],[f121,f28])).

fof(f122,plain,
    ( spl3_8
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f117,f102,f119])).

fof(f102,plain,
    ( spl3_6
  <=> r1_tarski(k5_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f117,plain,
    ( k5_xboole_0(sK1,sK2) = k3_xboole_0(k5_xboole_0(sK1,sK2),sK1)
    | ~ spl3_6 ),
    inference(resolution,[],[f104,f33])).

fof(f104,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK2),sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f114,plain,
    ( ~ spl3_7
    | spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f109,f96,f58,f111])).

fof(f58,plain,
    ( spl3_3
  <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f109,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))))
    | spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f108,f28])).

fof(f108,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2))))))
    | spl3_3
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f60,f98])).

fof(f60,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f107,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f94,f85,f96])).

fof(f94,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl3_4 ),
    inference(superposition,[],[f28,f87])).

fof(f106,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f93,f85,f96])).

fof(f93,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl3_4 ),
    inference(superposition,[],[f28,f87])).

fof(f105,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f91,f85,f102])).

fof(f91,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK2),sK1)
    | ~ spl3_4 ),
    inference(superposition,[],[f66,f87])).

fof(f100,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f90,f85,f96])).

fof(f90,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl3_4 ),
    inference(superposition,[],[f87,f28])).

fof(f99,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f89,f85,f96])).

fof(f89,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl3_4 ),
    inference(superposition,[],[f87,f28])).

fof(f88,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f79,f50,f85])).

fof(f50,plain,
    ( spl3_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f79,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f33,f52])).

fof(f52,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f61,plain,
    ( ~ spl3_3
    | spl3_1 ),
    inference(avatar_split_clause,[],[f56,f45,f58])).

fof(f45,plain,
    ( spl3_1
  <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f56,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f55,f28])).

fof(f55,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f54,f34])).

fof(f54,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f47,f43])).

fof(f47,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f53,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f21,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    & r1_tarski(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
        & r1_tarski(X2,X1) )
   => ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      & r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X2,X1)
       => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).

fof(f48,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f38,f45])).

fof(f38,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))) ),
    inference(definition_unfolding,[],[f22,f32,f36,f32,f32])).

fof(f22,plain,(
    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:51:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.41  % (23211)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.46  % (23204)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (23210)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.46  % (23207)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (23216)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (23208)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (23203)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (23209)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (23212)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (23215)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (23206)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (23205)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.49  % (23202)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.50  % (23217)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (23214)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.50  % (23213)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.51  % (23219)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.51  % (23218)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 4.57/1.00  % (23206)Time limit reached!
% 4.57/1.00  % (23206)------------------------------
% 4.57/1.00  % (23206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.57/1.00  % (23206)Termination reason: Time limit
% 4.57/1.00  % (23206)Termination phase: Saturation
% 4.57/1.00  
% 4.57/1.01  % (23206)Memory used [KB]: 12153
% 4.57/1.01  % (23206)Time elapsed: 0.600 s
% 4.57/1.01  % (23206)------------------------------
% 4.57/1.01  % (23206)------------------------------
% 5.79/1.09  % (23212)Refutation found. Thanks to Tanya!
% 5.79/1.09  % SZS status Theorem for theBenchmark
% 5.79/1.09  % SZS output start Proof for theBenchmark
% 5.79/1.09  fof(f17241,plain,(
% 5.79/1.09    $false),
% 5.79/1.09    inference(avatar_sat_refutation,[],[f48,f53,f61,f88,f99,f100,f105,f106,f107,f114,f122,f133,f134,f139,f140,f141,f147,f160,f161,f166,f167,f168,f174,f187,f188,f193,f194,f195,f201,f214,f215,f220,f221,f222,f228,f257,f258,f263,f264,f265,f271,f299,f378,f385,f393,f402,f412,f418,f424,f431,f439,f448,f458,f463,f476,f483,f493,f500,f506,f518,f527,f533,f589,f595,f601,f607,f613,f618,f644,f652,f658,f664,f670,f676,f682,f700,f706,f712,f718,f732,f742,f747,f757,f762,f772,f777,f796,f817,f823,f846,f854,f856,f857,f922,f927,f950,f956,f976,f1094,f1104,f1117,f1129,f1142,f1185,f1192,f1202,f1211,f1221,f1264,f1269,f1274,f1279,f1295,f1300,f1305,f1310,f1316,f1321,f1327,f1376,f1377,f1378,f1379,f1391,f1397,f1410,f1454,f1470,f1487,f1500,f1896,f1919,f2012,f2120,f3695,f17216,f17222])).
% 5.79/1.09  fof(f17222,plain,(
% 5.79/1.09    ~spl3_108 | ~spl3_5 | spl3_7),
% 5.79/1.09    inference(avatar_split_clause,[],[f17217,f111,f96,f17219])).
% 5.79/1.09  fof(f17219,plain,(
% 5.79/1.09    spl3_108 <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_108])])).
% 5.79/1.09  fof(f96,plain,(
% 5.79/1.09    spl3_5 <=> sK2 = k3_xboole_0(sK1,sK2)),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 5.79/1.09  fof(f111,plain,(
% 5.79/1.09    spl3_7 <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 5.79/1.09  fof(f17217,plain,(
% 5.79/1.09    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))) | (~spl3_5 | spl3_7)),
% 5.79/1.09    inference(forward_demodulation,[],[f17211,f23])).
% 5.79/1.09  fof(f23,plain,(
% 5.79/1.09    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.79/1.09    inference(cnf_transformation,[],[f11])).
% 5.79/1.09  fof(f11,axiom,(
% 5.79/1.09    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 5.79/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 5.79/1.09  fof(f17211,plain,(
% 5.79/1.09    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0)))) | (~spl3_5 | spl3_7)),
% 5.79/1.09    inference(backward_demodulation,[],[f113,f17208])).
% 5.79/1.09  fof(f17208,plain,(
% 5.79/1.09    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(X0,k3_xboole_0(X0,sK1)))) ) | ~spl3_5),
% 5.79/1.09    inference(forward_demodulation,[],[f17193,f1652])).
% 5.79/1.09  fof(f1652,plain,(
% 5.79/1.09    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 5.79/1.09    inference(superposition,[],[f1148,f28])).
% 5.79/1.09  fof(f28,plain,(
% 5.79/1.09    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.79/1.09    inference(cnf_transformation,[],[f2])).
% 5.79/1.09  fof(f2,axiom,(
% 5.79/1.09    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.79/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.79/1.09  fof(f1148,plain,(
% 5.79/1.09    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 5.79/1.09    inference(backward_demodulation,[],[f362,f1144])).
% 5.79/1.09  fof(f1144,plain,(
% 5.79/1.09    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 5.79/1.09    inference(forward_demodulation,[],[f1143,f23])).
% 5.79/1.09  fof(f1143,plain,(
% 5.79/1.09    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 5.79/1.09    inference(forward_demodulation,[],[f1039,f693])).
% 5.79/1.09  fof(f693,plain,(
% 5.79/1.09    ( ! [X12,X11] : (k5_xboole_0(X12,k3_xboole_0(k1_xboole_0,X11)) = X12) )),
% 5.79/1.09    inference(forward_demodulation,[],[f692,f23])).
% 5.79/1.09  fof(f692,plain,(
% 5.79/1.09    ( ! [X12,X11] : (k5_xboole_0(X12,k3_xboole_0(k1_xboole_0,X11)) = k5_xboole_0(X12,k1_xboole_0)) )),
% 5.79/1.09    inference(forward_demodulation,[],[f565,f362])).
% 5.79/1.09  fof(f565,plain,(
% 5.79/1.09    ( ! [X12,X11] : (k5_xboole_0(X12,k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X11)))) = k5_xboole_0(X12,k3_xboole_0(k1_xboole_0,X11))) )),
% 5.79/1.09    inference(superposition,[],[f274,f37])).
% 5.79/1.09  fof(f37,plain,(
% 5.79/1.09    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 5.79/1.09    inference(definition_unfolding,[],[f31,f32,f32])).
% 5.79/1.09  fof(f32,plain,(
% 5.79/1.09    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.79/1.09    inference(cnf_transformation,[],[f4])).
% 5.79/1.09  fof(f4,axiom,(
% 5.79/1.09    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.79/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 5.79/1.09  fof(f31,plain,(
% 5.79/1.09    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 5.79/1.09    inference(cnf_transformation,[],[f9])).
% 5.79/1.09  fof(f9,axiom,(
% 5.79/1.09    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.79/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 5.79/1.09  fof(f274,plain,(
% 5.79/1.09    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) )),
% 5.79/1.09    inference(superposition,[],[f34,f23])).
% 5.79/1.09  fof(f34,plain,(
% 5.79/1.09    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 5.79/1.09    inference(cnf_transformation,[],[f12])).
% 5.79/1.09  fof(f12,axiom,(
% 5.79/1.09    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 5.79/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 5.79/1.09  fof(f1039,plain,(
% 5.79/1.09    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)))) )),
% 5.79/1.09    inference(superposition,[],[f41,f39])).
% 5.79/1.09  fof(f39,plain,(
% 5.79/1.09    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 5.79/1.09    inference(definition_unfolding,[],[f24,f32])).
% 5.79/1.09  fof(f24,plain,(
% 5.79/1.09    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.79/1.09    inference(cnf_transformation,[],[f8])).
% 5.79/1.09  fof(f8,axiom,(
% 5.79/1.09    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 5.79/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 5.79/1.09  fof(f41,plain,(
% 5.79/1.09    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 5.79/1.09    inference(definition_unfolding,[],[f27,f36,f36])).
% 5.79/1.09  fof(f36,plain,(
% 5.79/1.09    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 5.79/1.09    inference(definition_unfolding,[],[f30,f32])).
% 5.79/1.09  fof(f30,plain,(
% 5.79/1.09    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 5.79/1.09    inference(cnf_transformation,[],[f13])).
% 5.79/1.09  fof(f13,axiom,(
% 5.79/1.09    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 5.79/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 5.79/1.09  fof(f27,plain,(
% 5.79/1.09    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 5.79/1.09    inference(cnf_transformation,[],[f1])).
% 5.79/1.09  fof(f1,axiom,(
% 5.79/1.09    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 5.79/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 5.79/1.09  fof(f362,plain,(
% 5.79/1.09    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 5.79/1.09    inference(superposition,[],[f42,f39])).
% 5.79/1.09  fof(f42,plain,(
% 5.79/1.09    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 5.79/1.09    inference(definition_unfolding,[],[f29,f36])).
% 5.79/1.09  fof(f29,plain,(
% 5.79/1.09    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 5.79/1.09    inference(cnf_transformation,[],[f5])).
% 5.79/1.09  fof(f5,axiom,(
% 5.79/1.09    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 5.79/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 5.79/1.09  fof(f17193,plain,(
% 5.79/1.09    ( ! [X0] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(X0,k3_xboole_0(X0,sK1))) = k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(X0,k3_xboole_0(X0,sK1))),k1_xboole_0)) ) | ~spl3_5),
% 5.79/1.09    inference(resolution,[],[f16410,f33])).
% 5.79/1.09  fof(f33,plain,(
% 5.79/1.09    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 5.79/1.09    inference(cnf_transformation,[],[f18])).
% 5.79/1.09  fof(f18,plain,(
% 5.79/1.09    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 5.79/1.09    inference(ennf_transformation,[],[f6])).
% 5.79/1.09  fof(f6,axiom,(
% 5.79/1.09    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 5.79/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 5.79/1.09  fof(f16410,plain,(
% 5.79/1.09    ( ! [X0] : (r1_tarski(k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(X0,k3_xboole_0(X0,sK1))),k1_xboole_0)) ) | ~spl3_5),
% 5.79/1.09    inference(superposition,[],[f15451,f28])).
% 5.79/1.09  fof(f15451,plain,(
% 5.79/1.09    ( ! [X61] : (r1_tarski(k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(X61,k3_xboole_0(sK1,X61))),k1_xboole_0)) ) | ~spl3_5),
% 5.79/1.09    inference(backward_demodulation,[],[f5875,f15187])).
% 5.79/1.09  fof(f15187,plain,(
% 5.79/1.09    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k3_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 5.79/1.09    inference(superposition,[],[f1787,f535])).
% 5.79/1.09  fof(f535,plain,(
% 5.79/1.09    ( ! [X2,X1] : (k3_xboole_0(X2,X1) = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1))))) )),
% 5.79/1.09    inference(superposition,[],[f37,f28])).
% 5.79/1.09  fof(f1787,plain,(
% 5.79/1.09    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 5.79/1.09    inference(superposition,[],[f43,f25])).
% 5.79/1.09  fof(f25,plain,(
% 5.79/1.09    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 5.79/1.09    inference(cnf_transformation,[],[f16])).
% 5.79/1.09  fof(f16,plain,(
% 5.79/1.09    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 5.79/1.09    inference(rectify,[],[f3])).
% 5.79/1.09  fof(f3,axiom,(
% 5.79/1.09    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 5.79/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 5.79/1.09  fof(f43,plain,(
% 5.79/1.09    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 5.79/1.09    inference(definition_unfolding,[],[f35,f32,f32])).
% 5.79/1.09  fof(f35,plain,(
% 5.79/1.09    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 5.79/1.09    inference(cnf_transformation,[],[f10])).
% 5.79/1.09  fof(f10,axiom,(
% 5.79/1.09    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 5.79/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 5.79/1.09  fof(f5875,plain,(
% 5.79/1.09    ( ! [X61] : (r1_tarski(k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(X61,k3_xboole_0(X61,k3_xboole_0(sK1,X61)))),k1_xboole_0)) ) | ~spl3_5),
% 5.79/1.09    inference(forward_demodulation,[],[f5728,f28])).
% 5.79/1.09  fof(f5728,plain,(
% 5.79/1.09    ( ! [X61] : (r1_tarski(k3_xboole_0(k5_xboole_0(X61,k3_xboole_0(X61,k3_xboole_0(sK1,X61))),k5_xboole_0(sK1,sK2)),k1_xboole_0)) ) | ~spl3_5),
% 5.79/1.09    inference(superposition,[],[f4883,f1828])).
% 5.79/1.09  fof(f1828,plain,(
% 5.79/1.09    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1))))) )),
% 5.79/1.09    inference(forward_demodulation,[],[f1799,f1668])).
% 5.79/1.09  fof(f1668,plain,(
% 5.79/1.09    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 5.79/1.09    inference(backward_demodulation,[],[f623,f1652])).
% 5.79/1.09  fof(f623,plain,(
% 5.79/1.09    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,X0)) )),
% 5.79/1.09    inference(forward_demodulation,[],[f555,f25])).
% 5.79/1.09  fof(f555,plain,(
% 5.79/1.09    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 5.79/1.09    inference(superposition,[],[f37,f39])).
% 5.79/1.09  fof(f1799,plain,(
% 5.79/1.09    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1))))) )),
% 5.79/1.09    inference(superposition,[],[f43,f25])).
% 5.79/1.09  fof(f4883,plain,(
% 5.79/1.09    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,k5_xboole_0(sK1,sK2)),k3_xboole_0(sK1,X0))) ) | ~spl3_5),
% 5.79/1.09    inference(superposition,[],[f4737,f28])).
% 5.79/1.09  fof(f4737,plain,(
% 5.79/1.09    ( ! [X43] : (r1_tarski(k3_xboole_0(X43,k5_xboole_0(sK1,sK2)),k3_xboole_0(X43,sK1))) ) | ~spl3_5),
% 5.79/1.09    inference(superposition,[],[f1810,f98])).
% 5.79/1.09  fof(f98,plain,(
% 5.79/1.09    sK2 = k3_xboole_0(sK1,sK2) | ~spl3_5),
% 5.79/1.09    inference(avatar_component_clause,[],[f96])).
% 5.79/1.09  fof(f1810,plain,(
% 5.79/1.09    ( ! [X17,X15,X16] : (r1_tarski(k3_xboole_0(X15,k5_xboole_0(X16,k3_xboole_0(X16,X17))),k3_xboole_0(X15,X16))) )),
% 5.79/1.09    inference(superposition,[],[f40,f43])).
% 5.79/1.09  fof(f40,plain,(
% 5.79/1.09    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 5.79/1.09    inference(definition_unfolding,[],[f26,f32])).
% 5.79/1.09  fof(f26,plain,(
% 5.79/1.09    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 5.79/1.09    inference(cnf_transformation,[],[f7])).
% 5.79/1.09  fof(f7,axiom,(
% 5.79/1.09    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 5.79/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 5.79/1.09  fof(f113,plain,(
% 5.79/1.09    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))) | spl3_7),
% 5.79/1.09    inference(avatar_component_clause,[],[f111])).
% 5.79/1.09  fof(f17216,plain,(
% 5.79/1.09    ~spl3_4 | ~spl3_5 | spl3_24),
% 5.79/1.09    inference(avatar_contradiction_clause,[],[f17215])).
% 5.79/1.09  fof(f17215,plain,(
% 5.79/1.09    $false | (~spl3_4 | ~spl3_5 | spl3_24)),
% 5.79/1.09    inference(trivial_inequality_removal,[],[f17214])).
% 5.79/1.09  fof(f17214,plain,(
% 5.79/1.09    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | (~spl3_4 | ~spl3_5 | spl3_24)),
% 5.79/1.09    inference(forward_demodulation,[],[f17213,f28])).
% 5.79/1.09  fof(f17213,plain,(
% 5.79/1.09    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(sK0,k3_xboole_0(sK2,sK0)) | (~spl3_4 | ~spl3_5 | spl3_24)),
% 5.79/1.09    inference(forward_demodulation,[],[f17212,f15375])).
% 5.79/1.09  fof(f15375,plain,(
% 5.79/1.09    ( ! [X19] : (k3_xboole_0(sK2,X19) = k5_xboole_0(k3_xboole_0(X19,sK1),k3_xboole_0(X19,k5_xboole_0(sK1,sK2)))) ) | (~spl3_4 | ~spl3_5)),
% 5.79/1.09    inference(backward_demodulation,[],[f13879,f15374])).
% 5.79/1.09  fof(f15374,plain,(
% 5.79/1.09    ( ! [X26] : (k3_xboole_0(X26,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k3_xboole_0(X26,sK1),k3_xboole_0(X26,k5_xboole_0(sK1,sK2)))) ) | (~spl3_4 | ~spl3_5)),
% 5.79/1.09    inference(forward_demodulation,[],[f15137,f13871])).
% 5.79/1.09  fof(f13871,plain,(
% 5.79/1.09    ( ! [X0] : (k3_xboole_0(X0,k5_xboole_0(sK1,sK2)) = k5_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(sK2,X0))) ) | (~spl3_4 | ~spl3_5)),
% 5.79/1.09    inference(forward_demodulation,[],[f13813,f98])).
% 5.79/1.09  fof(f13813,plain,(
% 5.79/1.09    ( ! [X0] : (k5_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(sK2,X0)) = k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) ) | ~spl3_4),
% 5.79/1.09    inference(superposition,[],[f43,f13317])).
% 5.79/1.09  fof(f13317,plain,(
% 5.79/1.09    ( ! [X52] : (k3_xboole_0(sK2,X52) = k3_xboole_0(k3_xboole_0(X52,sK1),sK2)) ) | ~spl3_4),
% 5.79/1.09    inference(forward_demodulation,[],[f13251,f23])).
% 5.79/1.09  fof(f13251,plain,(
% 5.79/1.09    ( ! [X52] : (k3_xboole_0(k3_xboole_0(X52,sK1),sK2) = k5_xboole_0(k3_xboole_0(sK2,X52),k1_xboole_0)) ) | ~spl3_4),
% 5.79/1.09    inference(superposition,[],[f7101,f13177])).
% 5.79/1.09  fof(f13177,plain,(
% 5.79/1.09    ( ! [X38] : (k3_xboole_0(sK2,X38) = k3_xboole_0(sK2,k3_xboole_0(X38,sK1))) ) | ~spl3_4),
% 5.79/1.09    inference(forward_demodulation,[],[f13176,f1697])).
% 5.79/1.09  fof(f1697,plain,(
% 5.79/1.09    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 5.79/1.09    inference(forward_demodulation,[],[f1686,f1144])).
% 5.79/1.09  fof(f1686,plain,(
% 5.79/1.09    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 5.79/1.09    inference(superposition,[],[f34,f1668])).
% 5.79/1.09  fof(f13176,plain,(
% 5.79/1.09    ( ! [X38] : (k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,X38))) = k3_xboole_0(sK2,k3_xboole_0(X38,sK1))) ) | ~spl3_4),
% 5.79/1.09    inference(forward_demodulation,[],[f12979,f2094])).
% 5.79/1.09  fof(f2094,plain,(
% 5.79/1.09    ( ! [X0] : (k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) = k3_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(X0,sK1)))) ) | ~spl3_4),
% 5.79/1.09    inference(superposition,[],[f1796,f28])).
% 5.79/1.09  fof(f1796,plain,(
% 5.79/1.09    ( ! [X18] : (k3_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,X18))) = k5_xboole_0(sK2,k3_xboole_0(sK2,X18))) ) | ~spl3_4),
% 5.79/1.09    inference(superposition,[],[f43,f87])).
% 5.79/1.09  fof(f87,plain,(
% 5.79/1.09    sK2 = k3_xboole_0(sK2,sK1) | ~spl3_4),
% 5.79/1.09    inference(avatar_component_clause,[],[f85])).
% 5.79/1.09  fof(f85,plain,(
% 5.79/1.09    spl3_4 <=> sK2 = k3_xboole_0(sK2,sK1)),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 5.79/1.09  fof(f12979,plain,(
% 5.79/1.09    ( ! [X38] : (k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(X38,sK1)))) = k3_xboole_0(sK2,k3_xboole_0(X38,sK1))) ) | ~spl3_4),
% 5.79/1.09    inference(superposition,[],[f1796,f535])).
% 5.79/1.09  fof(f7101,plain,(
% 5.79/1.09    ( ! [X9] : (k3_xboole_0(X9,sK2) = k5_xboole_0(k3_xboole_0(sK2,X9),k1_xboole_0)) ) | ~spl3_4),
% 5.79/1.09    inference(forward_demodulation,[],[f7100,f23])).
% 5.79/1.09  fof(f7100,plain,(
% 5.79/1.09    ( ! [X9] : (k5_xboole_0(k3_xboole_0(sK2,X9),k1_xboole_0) = k5_xboole_0(k3_xboole_0(X9,sK2),k1_xboole_0)) ) | ~spl3_4),
% 5.79/1.09    inference(forward_demodulation,[],[f7099,f5766])).
% 5.79/1.09  fof(f5766,plain,(
% 5.79/1.09    ( ! [X2,X1] : (k1_xboole_0 = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) )),
% 5.79/1.09    inference(forward_demodulation,[],[f5652,f1815])).
% 5.79/1.09  fof(f1815,plain,(
% 5.79/1.09    ( ! [X2,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 5.79/1.09    inference(backward_demodulation,[],[f556,f1787])).
% 5.79/1.09  fof(f556,plain,(
% 5.79/1.09    ( ! [X2,X1] : (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 5.79/1.09    inference(superposition,[],[f37,f37])).
% 5.79/1.09  fof(f5652,plain,(
% 5.79/1.09    ( ! [X2,X1] : (k1_xboole_0 = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(X2,X1))))) )),
% 5.79/1.09    inference(superposition,[],[f1828,f28])).
% 5.79/1.09  fof(f7099,plain,(
% 5.79/1.09    ( ! [X9] : (k5_xboole_0(k3_xboole_0(X9,sK2),k1_xboole_0) = k5_xboole_0(k3_xboole_0(sK2,X9),k3_xboole_0(X9,k5_xboole_0(sK2,k3_xboole_0(sK2,X9))))) ) | ~spl3_4),
% 5.79/1.09    inference(forward_demodulation,[],[f7098,f1815])).
% 5.79/1.09  fof(f7098,plain,(
% 5.79/1.09    ( ! [X9] : (k5_xboole_0(k3_xboole_0(X9,sK2),k1_xboole_0) = k5_xboole_0(k3_xboole_0(sK2,X9),k3_xboole_0(X9,k5_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK2,X9)))))) ) | ~spl3_4),
% 5.79/1.09    inference(forward_demodulation,[],[f7097,f43])).
% 5.79/1.09  fof(f7097,plain,(
% 5.79/1.09    ( ! [X9] : (k5_xboole_0(k3_xboole_0(X9,sK2),k1_xboole_0) = k5_xboole_0(k3_xboole_0(sK2,X9),k5_xboole_0(k3_xboole_0(X9,sK2),k3_xboole_0(k3_xboole_0(X9,sK2),k3_xboole_0(sK2,X9))))) ) | ~spl3_4),
% 5.79/1.09    inference(forward_demodulation,[],[f7046,f1668])).
% 5.79/1.09  fof(f7046,plain,(
% 5.79/1.09    ( ! [X9] : (k5_xboole_0(k3_xboole_0(sK2,X9),k5_xboole_0(k3_xboole_0(X9,sK2),k3_xboole_0(k3_xboole_0(X9,sK2),k3_xboole_0(sK2,X9)))) = k5_xboole_0(k3_xboole_0(X9,sK2),k5_xboole_0(k3_xboole_0(sK2,X9),k3_xboole_0(sK2,X9)))) ) | ~spl3_4),
% 5.79/1.09    inference(superposition,[],[f41,f5112])).
% 5.79/1.09  fof(f5112,plain,(
% 5.79/1.09    ( ! [X0] : (k3_xboole_0(sK2,X0) = k3_xboole_0(k3_xboole_0(sK2,X0),k3_xboole_0(X0,sK2))) ) | ~spl3_4),
% 5.79/1.09    inference(resolution,[],[f5051,f33])).
% 5.79/1.09  fof(f5051,plain,(
% 5.79/1.09    ( ! [X0] : (r1_tarski(k3_xboole_0(sK2,X0),k3_xboole_0(X0,sK2))) ) | ~spl3_4),
% 5.79/1.09    inference(superposition,[],[f4912,f87])).
% 5.79/1.09  fof(f4912,plain,(
% 5.79/1.09    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(k3_xboole_0(sK2,X2),X1),k3_xboole_0(X1,sK2))) ) | ~spl3_4),
% 5.79/1.09    inference(superposition,[],[f4827,f28])).
% 5.79/1.09  fof(f4827,plain,(
% 5.79/1.09    ( ! [X54,X53] : (r1_tarski(k3_xboole_0(X54,k3_xboole_0(sK2,X53)),k3_xboole_0(X54,sK2))) ) | ~spl3_4),
% 5.79/1.09    inference(forward_demodulation,[],[f4743,f1697])).
% 5.79/1.09  fof(f4743,plain,(
% 5.79/1.09    ( ! [X54,X53] : (r1_tarski(k3_xboole_0(X54,k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,X53)))),k3_xboole_0(X54,sK2))) ) | ~spl3_4),
% 5.79/1.09    inference(superposition,[],[f1810,f1796])).
% 5.79/1.09  fof(f15137,plain,(
% 5.79/1.09    ( ! [X26] : (k5_xboole_0(k3_xboole_0(X26,sK1),k3_xboole_0(sK2,X26)) = k3_xboole_0(k3_xboole_0(X26,sK1),k5_xboole_0(k3_xboole_0(X26,sK1),k3_xboole_0(sK2,X26)))) ) | ~spl3_4),
% 5.79/1.09    inference(superposition,[],[f1787,f2782])).
% 5.79/1.09  fof(f2782,plain,(
% 5.79/1.09    ( ! [X1] : (k3_xboole_0(sK2,X1) = k3_xboole_0(k3_xboole_0(X1,sK1),k3_xboole_0(sK2,X1))) ) | ~spl3_4),
% 5.79/1.09    inference(superposition,[],[f2290,f28])).
% 5.79/1.09  fof(f2290,plain,(
% 5.79/1.09    ( ! [X0] : (k3_xboole_0(sK2,X0) = k3_xboole_0(k3_xboole_0(sK2,X0),k3_xboole_0(X0,sK1))) ) | ~spl3_4),
% 5.79/1.09    inference(resolution,[],[f2267,f33])).
% 5.79/1.09  fof(f2267,plain,(
% 5.79/1.09    ( ! [X0] : (r1_tarski(k3_xboole_0(sK2,X0),k3_xboole_0(X0,sK1))) ) | ~spl3_4),
% 5.79/1.09    inference(superposition,[],[f2229,f28])).
% 5.79/1.09  fof(f2229,plain,(
% 5.79/1.09    ( ! [X2] : (r1_tarski(k3_xboole_0(sK2,X2),k3_xboole_0(sK1,X2))) ) | ~spl3_4),
% 5.79/1.09    inference(forward_demodulation,[],[f2228,f1697])).
% 5.79/1.09  fof(f2228,plain,(
% 5.79/1.09    ( ! [X2] : (r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,X2))),k3_xboole_0(sK1,X2))) ) | ~spl3_4),
% 5.79/1.09    inference(forward_demodulation,[],[f2227,f1697])).
% 5.79/1.09  fof(f2227,plain,(
% 5.79/1.09    ( ! [X2] : (r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,X2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,X2))))) ) | ~spl3_4),
% 5.79/1.09    inference(forward_demodulation,[],[f2208,f1787])).
% 5.79/1.09  fof(f2208,plain,(
% 5.79/1.09    ( ! [X2] : (r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,X2))),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,X2)))))) ) | ~spl3_4),
% 5.79/1.09    inference(superposition,[],[f2113,f1796])).
% 5.79/1.09  fof(f2113,plain,(
% 5.79/1.09    ( ! [X15] : (r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,X15)),k5_xboole_0(sK1,k3_xboole_0(sK1,X15)))) ) | ~spl3_4),
% 5.79/1.09    inference(superposition,[],[f898,f1796])).
% 5.79/1.09  fof(f898,plain,(
% 5.79/1.09    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 5.79/1.09    inference(superposition,[],[f561,f28])).
% 5.79/1.09  fof(f561,plain,(
% 5.79/1.09    ( ! [X2,X3] : (r1_tarski(k3_xboole_0(X2,X3),X2)) )),
% 5.79/1.09    inference(superposition,[],[f40,f37])).
% 5.79/1.09  fof(f13879,plain,(
% 5.79/1.09    ( ! [X19] : (k3_xboole_0(sK2,X19) = k5_xboole_0(k3_xboole_0(X19,sK1),k3_xboole_0(k3_xboole_0(X19,sK1),k3_xboole_0(X19,k5_xboole_0(sK1,sK2))))) ) | (~spl3_4 | ~spl3_5)),
% 5.79/1.09    inference(backward_demodulation,[],[f12897,f13871])).
% 5.79/1.09  fof(f12897,plain,(
% 5.79/1.09    ( ! [X19] : (k3_xboole_0(sK2,X19) = k5_xboole_0(k3_xboole_0(X19,sK1),k3_xboole_0(k3_xboole_0(X19,sK1),k5_xboole_0(k3_xboole_0(X19,sK1),k3_xboole_0(sK2,X19))))) ) | ~spl3_4),
% 5.79/1.09    inference(superposition,[],[f535,f2290])).
% 5.79/1.09  fof(f17212,plain,(
% 5.79/1.09    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)))) | (~spl3_5 | spl3_24)),
% 5.79/1.09    inference(forward_demodulation,[],[f17210,f23])).
% 5.79/1.09  fof(f17210,plain,(
% 5.79/1.09    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0))))) | (~spl3_5 | spl3_24)),
% 5.79/1.09    inference(backward_demodulation,[],[f298,f17208])).
% 5.79/1.09  fof(f298,plain,(
% 5.79/1.09    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))))) | spl3_24),
% 5.79/1.09    inference(avatar_component_clause,[],[f296])).
% 5.79/1.09  fof(f296,plain,(
% 5.79/1.09    spl3_24 <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 5.79/1.09  fof(f3695,plain,(
% 5.79/1.09    spl3_107 | ~spl3_4 | ~spl3_9 | ~spl3_106),
% 5.79/1.09    inference(avatar_split_clause,[],[f3690,f2117,f130,f85,f3692])).
% 5.79/1.09  fof(f3692,plain,(
% 5.79/1.09    spl3_107 <=> k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK1,sK2),sK2)),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_107])])).
% 5.79/1.09  fof(f130,plain,(
% 5.79/1.09    spl3_9 <=> k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 5.79/1.09  fof(f2117,plain,(
% 5.79/1.09    spl3_106 <=> k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_106])])).
% 5.79/1.09  fof(f3690,plain,(
% 5.79/1.09    k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK1,sK2),sK2) | (~spl3_4 | ~spl3_9 | ~spl3_106)),
% 5.79/1.09    inference(forward_demodulation,[],[f3689,f23])).
% 5.79/1.09  fof(f3689,plain,(
% 5.79/1.09    k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK2,k1_xboole_0)) | (~spl3_4 | ~spl3_9 | ~spl3_106)),
% 5.79/1.09    inference(forward_demodulation,[],[f3635,f2119])).
% 5.79/1.09  fof(f2119,plain,(
% 5.79/1.09    k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) | ~spl3_106),
% 5.79/1.09    inference(avatar_component_clause,[],[f2117])).
% 5.79/1.09  fof(f3635,plain,(
% 5.79/1.09    k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) | (~spl3_4 | ~spl3_9)),
% 5.79/1.09    inference(superposition,[],[f2751,f132])).
% 5.79/1.09  fof(f132,plain,(
% 5.79/1.09    k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | ~spl3_9),
% 5.79/1.09    inference(avatar_component_clause,[],[f130])).
% 5.79/1.09  fof(f2751,plain,(
% 5.79/1.09    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK1,X0))))) ) | ~spl3_4),
% 5.79/1.09    inference(forward_demodulation,[],[f2735,f1668])).
% 5.79/1.09  fof(f2735,plain,(
% 5.79/1.09    ( ! [X0] : (k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,k3_xboole_0(sK1,X0)))) = k5_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(X0,sK2))) ) | ~spl3_4),
% 5.79/1.09    inference(superposition,[],[f43,f2274])).
% 5.79/1.09  fof(f2274,plain,(
% 5.79/1.09    ( ! [X0] : (k3_xboole_0(X0,sK2) = k3_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(sK1,X0))) ) | ~spl3_4),
% 5.79/1.09    inference(resolution,[],[f2260,f33])).
% 5.79/1.09  fof(f2260,plain,(
% 5.79/1.09    ( ! [X3] : (r1_tarski(k3_xboole_0(X3,sK2),k3_xboole_0(sK1,X3))) ) | ~spl3_4),
% 5.79/1.09    inference(superposition,[],[f2229,f28])).
% 5.79/1.09  fof(f2120,plain,(
% 5.79/1.09    spl3_106 | ~spl3_4 | ~spl3_5),
% 5.79/1.09    inference(avatar_split_clause,[],[f2115,f96,f85,f2117])).
% 5.79/1.09  fof(f2115,plain,(
% 5.79/1.09    k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) | (~spl3_4 | ~spl3_5)),
% 5.79/1.09    inference(forward_demodulation,[],[f2114,f1668])).
% 5.79/1.09  fof(f2114,plain,(
% 5.79/1.09    k5_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) | (~spl3_4 | ~spl3_5)),
% 5.79/1.09    inference(forward_demodulation,[],[f2091,f25])).
% 5.79/1.09  fof(f2091,plain,(
% 5.79/1.09    k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) | (~spl3_4 | ~spl3_5)),
% 5.79/1.09    inference(superposition,[],[f1796,f98])).
% 5.79/1.09  fof(f2012,plain,(
% 5.79/1.09    spl3_105 | ~spl3_101 | ~spl3_103),
% 5.79/1.09    inference(avatar_split_clause,[],[f2005,f1893,f1484,f2009])).
% 5.79/1.09  fof(f2009,plain,(
% 5.79/1.09    spl3_105 <=> sK2 = k5_xboole_0(k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK2)),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_105])])).
% 5.79/1.09  fof(f1484,plain,(
% 5.79/1.09    spl3_101 <=> k1_xboole_0 = k5_xboole_0(sK2,sK2)),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_101])])).
% 5.79/1.09  fof(f1893,plain,(
% 5.79/1.09    spl3_103 <=> sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_103])])).
% 5.79/1.09  fof(f2005,plain,(
% 5.79/1.09    sK2 = k5_xboole_0(k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK2) | (~spl3_101 | ~spl3_103)),
% 5.79/1.09    inference(superposition,[],[f1863,f1895])).
% 5.79/1.09  fof(f1895,plain,(
% 5.79/1.09    sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_103),
% 5.79/1.09    inference(avatar_component_clause,[],[f1893])).
% 5.79/1.09  fof(f1863,plain,(
% 5.79/1.09    ( ! [X0] : (sK2 = k5_xboole_0(k3_xboole_0(sK2,X0),k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))) ) | ~spl3_101),
% 5.79/1.09    inference(superposition,[],[f1853,f28])).
% 5.79/1.09  fof(f1853,plain,(
% 5.79/1.09    ( ! [X4] : (sK2 = k5_xboole_0(k3_xboole_0(X4,sK2),k5_xboole_0(sK2,k3_xboole_0(X4,sK2)))) ) | ~spl3_101),
% 5.79/1.09    inference(forward_demodulation,[],[f1852,f23])).
% 5.79/1.09  fof(f1852,plain,(
% 5.79/1.09    ( ! [X4] : (k5_xboole_0(sK2,k1_xboole_0) = k5_xboole_0(k3_xboole_0(X4,sK2),k5_xboole_0(sK2,k3_xboole_0(X4,sK2)))) ) | ~spl3_101),
% 5.79/1.09    inference(forward_demodulation,[],[f1851,f1652])).
% 5.79/1.09  fof(f1851,plain,(
% 5.79/1.09    ( ! [X4] : (k5_xboole_0(k3_xboole_0(X4,sK2),k5_xboole_0(sK2,k3_xboole_0(X4,sK2))) = k5_xboole_0(sK2,k3_xboole_0(X4,k1_xboole_0))) ) | ~spl3_101),
% 5.79/1.09    inference(forward_demodulation,[],[f1850,f1668])).
% 5.79/1.09  fof(f1850,plain,(
% 5.79/1.09    ( ! [X4] : (k5_xboole_0(k3_xboole_0(X4,sK2),k5_xboole_0(sK2,k3_xboole_0(X4,sK2))) = k5_xboole_0(sK2,k3_xboole_0(X4,k5_xboole_0(sK2,sK2)))) ) | ~spl3_101),
% 5.79/1.09    inference(forward_demodulation,[],[f1849,f25])).
% 5.79/1.09  fof(f1849,plain,(
% 5.79/1.09    ( ! [X4] : (k5_xboole_0(k3_xboole_0(X4,sK2),k5_xboole_0(sK2,k3_xboole_0(X4,sK2))) = k5_xboole_0(sK2,k3_xboole_0(X4,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))))) ) | ~spl3_101),
% 5.79/1.09    inference(forward_demodulation,[],[f1842,f43])).
% 5.79/1.09  fof(f1842,plain,(
% 5.79/1.09    ( ! [X4] : (k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(X4,sK2),k3_xboole_0(k3_xboole_0(X4,sK2),sK2))) = k5_xboole_0(k3_xboole_0(X4,sK2),k5_xboole_0(sK2,k3_xboole_0(X4,sK2)))) ) | ~spl3_101),
% 5.79/1.09    inference(superposition,[],[f41,f1770])).
% 5.79/1.09  fof(f1770,plain,(
% 5.79/1.09    ( ! [X2] : (k3_xboole_0(X2,sK2) = k3_xboole_0(sK2,k3_xboole_0(X2,sK2))) ) | ~spl3_101),
% 5.79/1.09    inference(superposition,[],[f1743,f28])).
% 5.79/1.09  fof(f1743,plain,(
% 5.79/1.09    ( ! [X0] : (k3_xboole_0(sK2,X0) = k3_xboole_0(sK2,k3_xboole_0(sK2,X0))) ) | ~spl3_101),
% 5.79/1.09    inference(forward_demodulation,[],[f1726,f1697])).
% 5.79/1.09  fof(f1726,plain,(
% 5.79/1.09    ( ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))) = k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))))) ) | ~spl3_101),
% 5.79/1.09    inference(superposition,[],[f1510,f1510])).
% 5.79/1.09  fof(f1510,plain,(
% 5.79/1.09    ( ! [X2] : (k5_xboole_0(sK2,k3_xboole_0(sK2,X2)) = k3_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,X2)))) ) | ~spl3_101),
% 5.79/1.09    inference(superposition,[],[f1501,f37])).
% 5.79/1.09  fof(f1501,plain,(
% 5.79/1.09    ( ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(sK2,X0)) = X0) ) | ~spl3_101),
% 5.79/1.09    inference(forward_demodulation,[],[f1493,f1144])).
% 5.79/1.09  fof(f1493,plain,(
% 5.79/1.09    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK2,k5_xboole_0(sK2,X0))) ) | ~spl3_101),
% 5.79/1.09    inference(superposition,[],[f34,f1486])).
% 5.79/1.09  fof(f1486,plain,(
% 5.79/1.09    k1_xboole_0 = k5_xboole_0(sK2,sK2) | ~spl3_101),
% 5.79/1.09    inference(avatar_component_clause,[],[f1484])).
% 5.79/1.09  fof(f1919,plain,(
% 5.79/1.09    spl3_104 | ~spl3_80 | ~spl3_103),
% 5.79/1.09    inference(avatar_split_clause,[],[f1914,f1893,f1101,f1916])).
% 5.79/1.09  fof(f1916,plain,(
% 5.79/1.09    spl3_104 <=> sK1 = k5_xboole_0(sK1,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_104])])).
% 5.79/1.09  fof(f1101,plain,(
% 5.79/1.09    spl3_80 <=> sK1 = k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).
% 5.79/1.09  fof(f1914,plain,(
% 5.79/1.09    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | (~spl3_80 | ~spl3_103)),
% 5.79/1.09    inference(forward_demodulation,[],[f1908,f1103])).
% 5.79/1.09  fof(f1103,plain,(
% 5.79/1.09    sK1 = k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) | ~spl3_80),
% 5.79/1.09    inference(avatar_component_clause,[],[f1101])).
% 5.79/1.09  fof(f1908,plain,(
% 5.79/1.09    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | (~spl3_80 | ~spl3_103)),
% 5.79/1.09    inference(superposition,[],[f1351,f1895])).
% 5.79/1.09  fof(f1351,plain,(
% 5.79/1.09    ( ! [X0] : (k5_xboole_0(sK1,X0) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,X0)))) ) | ~spl3_80),
% 5.79/1.09    inference(forward_demodulation,[],[f1349,f34])).
% 5.79/1.09  fof(f1349,plain,(
% 5.79/1.09    ( ! [X0] : (k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),X0)) = k5_xboole_0(sK1,X0)) ) | ~spl3_80),
% 5.79/1.09    inference(superposition,[],[f34,f1103])).
% 5.79/1.09  fof(f1896,plain,(
% 5.79/1.09    spl3_103 | ~spl3_5 | ~spl3_101),
% 5.79/1.09    inference(avatar_split_clause,[],[f1876,f1484,f96,f1893])).
% 5.79/1.09  fof(f1876,plain,(
% 5.79/1.09    sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | (~spl3_5 | ~spl3_101)),
% 5.79/1.09    inference(superposition,[],[f1868,f98])).
% 5.79/1.09  fof(f1868,plain,(
% 5.79/1.09    ( ! [X5] : (sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(X5,k3_xboole_0(X5,sK2))))) ) | ~spl3_101),
% 5.79/1.09    inference(backward_demodulation,[],[f1783,f1863])).
% 5.79/1.09  fof(f1783,plain,(
% 5.79/1.09    ( ! [X5] : (k5_xboole_0(k3_xboole_0(sK2,X5),k5_xboole_0(sK2,k3_xboole_0(sK2,X5))) = k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(X5,k3_xboole_0(X5,sK2))))) ) | ~spl3_101),
% 5.79/1.09    inference(forward_demodulation,[],[f1777,f43])).
% 5.79/1.09  fof(f1777,plain,(
% 5.79/1.09    ( ! [X5] : (k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,X5),k3_xboole_0(k3_xboole_0(sK2,X5),sK2))) = k5_xboole_0(k3_xboole_0(sK2,X5),k5_xboole_0(sK2,k3_xboole_0(sK2,X5)))) ) | ~spl3_101),
% 5.79/1.09    inference(superposition,[],[f41,f1743])).
% 5.79/1.09  fof(f1500,plain,(
% 5.79/1.09    spl3_102 | ~spl3_45 | ~spl3_101),
% 5.79/1.09    inference(avatar_split_clause,[],[f1495,f1484,f586,f1497])).
% 5.79/1.09  fof(f1497,plain,(
% 5.79/1.09    spl3_102 <=> k1_xboole_0 = k5_xboole_0(sK1,sK1)),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_102])])).
% 5.79/1.09  fof(f586,plain,(
% 5.79/1.09    spl3_45 <=> sK2 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 5.79/1.09  fof(f1495,plain,(
% 5.79/1.09    k1_xboole_0 = k5_xboole_0(sK1,sK1) | (~spl3_45 | ~spl3_101)),
% 5.79/1.09    inference(forward_demodulation,[],[f1492,f23])).
% 5.79/1.09  fof(f1492,plain,(
% 5.79/1.09    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK1,k1_xboole_0)) | (~spl3_45 | ~spl3_101)),
% 5.79/1.09    inference(superposition,[],[f834,f1486])).
% 5.79/1.09  fof(f834,plain,(
% 5.79/1.09    ( ! [X0] : (k5_xboole_0(sK2,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,X0)))) ) | ~spl3_45),
% 5.79/1.09    inference(forward_demodulation,[],[f833,f34])).
% 5.79/1.09  fof(f833,plain,(
% 5.79/1.09    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),X0)) = k5_xboole_0(sK2,X0)) ) | ~spl3_45),
% 5.79/1.09    inference(superposition,[],[f34,f588])).
% 5.79/1.09  fof(f588,plain,(
% 5.79/1.09    sK2 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | ~spl3_45),
% 5.79/1.09    inference(avatar_component_clause,[],[f586])).
% 5.79/1.09  fof(f1487,plain,(
% 5.79/1.09    spl3_101 | ~spl3_45 | ~spl3_80 | ~spl3_100),
% 5.79/1.09    inference(avatar_split_clause,[],[f1482,f1467,f1101,f586,f1484])).
% 5.79/1.09  fof(f1467,plain,(
% 5.79/1.09    spl3_100 <=> k5_xboole_0(sK1,sK2) = k5_xboole_0(sK2,sK1)),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_100])])).
% 5.79/1.09  fof(f1482,plain,(
% 5.79/1.09    k1_xboole_0 = k5_xboole_0(sK2,sK2) | (~spl3_45 | ~spl3_80 | ~spl3_100)),
% 5.79/1.09    inference(forward_demodulation,[],[f1481,f588])).
% 5.79/1.09  fof(f1481,plain,(
% 5.79/1.09    k1_xboole_0 = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) | (~spl3_80 | ~spl3_100)),
% 5.79/1.09    inference(forward_demodulation,[],[f1480,f1148])).
% 5.79/1.09  fof(f1480,plain,(
% 5.79/1.09    k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k1_xboole_0,sK1) | (~spl3_80 | ~spl3_100)),
% 5.79/1.09    inference(forward_demodulation,[],[f1479,f28])).
% 5.79/1.09  fof(f1479,plain,(
% 5.79/1.09    k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(sK1,k1_xboole_0) | (~spl3_80 | ~spl3_100)),
% 5.79/1.09    inference(forward_demodulation,[],[f1476,f623])).
% 5.79/1.09  fof(f1476,plain,(
% 5.79/1.09    k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,sK1) | (~spl3_80 | ~spl3_100)),
% 5.79/1.09    inference(superposition,[],[f1351,f1469])).
% 5.79/1.09  fof(f1469,plain,(
% 5.79/1.09    k5_xboole_0(sK1,sK2) = k5_xboole_0(sK2,sK1) | ~spl3_100),
% 5.79/1.09    inference(avatar_component_clause,[],[f1467])).
% 5.79/1.09  fof(f1470,plain,(
% 5.79/1.09    spl3_100 | ~spl3_5 | ~spl3_98 | ~spl3_99),
% 5.79/1.09    inference(avatar_split_clause,[],[f1465,f1451,f1407,f96,f1467])).
% 5.79/1.09  fof(f1407,plain,(
% 5.79/1.09    spl3_98 <=> k5_xboole_0(sK2,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_98])])).
% 5.79/1.09  fof(f1451,plain,(
% 5.79/1.09    spl3_99 <=> sK2 = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_99])])).
% 5.79/1.09  fof(f1465,plain,(
% 5.79/1.09    k5_xboole_0(sK1,sK2) = k5_xboole_0(sK2,sK1) | (~spl3_5 | ~spl3_98 | ~spl3_99)),
% 5.79/1.09    inference(forward_demodulation,[],[f1462,f98])).
% 5.79/1.09  fof(f1462,plain,(
% 5.79/1.09    k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,sK1) | (~spl3_98 | ~spl3_99)),
% 5.79/1.09    inference(backward_demodulation,[],[f1409,f1453])).
% 5.79/1.09  fof(f1453,plain,(
% 5.79/1.09    sK2 = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) | ~spl3_99),
% 5.79/1.09    inference(avatar_component_clause,[],[f1451])).
% 5.79/1.09  fof(f1409,plain,(
% 5.79/1.09    k5_xboole_0(sK2,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))) | ~spl3_98),
% 5.79/1.09    inference(avatar_component_clause,[],[f1407])).
% 5.79/1.09  fof(f1454,plain,(
% 5.79/1.09    spl3_99 | ~spl3_80 | ~spl3_93),
% 5.79/1.09    inference(avatar_split_clause,[],[f1449,f1318,f1101,f1451])).
% 5.79/1.09  fof(f1318,plain,(
% 5.79/1.09    spl3_93 <=> sK1 = k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).
% 5.79/1.09  fof(f1449,plain,(
% 5.79/1.09    sK2 = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) | (~spl3_80 | ~spl3_93)),
% 5.79/1.09    inference(forward_demodulation,[],[f1448,f23])).
% 5.79/1.09  fof(f1448,plain,(
% 5.79/1.09    k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = k5_xboole_0(sK2,k1_xboole_0) | (~spl3_80 | ~spl3_93)),
% 5.79/1.09    inference(forward_demodulation,[],[f1447,f1148])).
% 5.79/1.09  fof(f1447,plain,(
% 5.79/1.09    k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK1)) | (~spl3_80 | ~spl3_93)),
% 5.79/1.09    inference(forward_demodulation,[],[f1446,f28])).
% 5.79/1.09  fof(f1446,plain,(
% 5.79/1.09    k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = k5_xboole_0(sK2,k3_xboole_0(sK1,k1_xboole_0)) | (~spl3_80 | ~spl3_93)),
% 5.79/1.09    inference(forward_demodulation,[],[f1433,f623])).
% 5.79/1.09  fof(f1433,plain,(
% 5.79/1.09    k5_xboole_0(sK2,k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) | (~spl3_80 | ~spl3_93)),
% 5.79/1.09    inference(superposition,[],[f1351,f1320])).
% 5.79/1.09  fof(f1320,plain,(
% 5.79/1.09    sK1 = k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)) | ~spl3_93),
% 5.79/1.09    inference(avatar_component_clause,[],[f1318])).
% 5.79/1.09  fof(f1410,plain,(
% 5.79/1.09    spl3_98 | ~spl3_95),
% 5.79/1.09    inference(avatar_split_clause,[],[f1398,f1373,f1407])).
% 5.79/1.09  fof(f1373,plain,(
% 5.79/1.09    spl3_95 <=> k5_xboole_0(sK2,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK2,sK1))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_95])])).
% 5.79/1.09  fof(f1398,plain,(
% 5.79/1.09    k5_xboole_0(sK2,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))) | ~spl3_95),
% 5.79/1.09    inference(superposition,[],[f37,f1375])).
% 5.79/1.09  fof(f1375,plain,(
% 5.79/1.09    k5_xboole_0(sK2,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK2,sK1)) | ~spl3_95),
% 5.79/1.09    inference(avatar_component_clause,[],[f1373])).
% 5.79/1.09  fof(f1397,plain,(
% 5.79/1.09    spl3_97 | ~spl3_96),
% 5.79/1.09    inference(avatar_split_clause,[],[f1392,f1388,f1394])).
% 5.79/1.09  fof(f1394,plain,(
% 5.79/1.09    spl3_97 <=> k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1)),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_97])])).
% 5.79/1.09  fof(f1388,plain,(
% 5.79/1.09    spl3_96 <=> r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1)),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).
% 5.79/1.09  fof(f1392,plain,(
% 5.79/1.09    k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1) | ~spl3_96),
% 5.79/1.09    inference(resolution,[],[f1390,f33])).
% 5.79/1.09  fof(f1390,plain,(
% 5.79/1.09    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1) | ~spl3_96),
% 5.79/1.09    inference(avatar_component_clause,[],[f1388])).
% 5.79/1.09  fof(f1391,plain,(
% 5.79/1.09    spl3_96 | ~spl3_88),
% 5.79/1.09    inference(avatar_split_clause,[],[f1369,f1292,f1388])).
% 5.79/1.09  fof(f1292,plain,(
% 5.79/1.09    spl3_88 <=> k5_xboole_0(sK2,sK1) = k3_xboole_0(k5_xboole_0(sK2,sK1),sK1)),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_88])])).
% 5.79/1.09  fof(f1369,plain,(
% 5.79/1.09    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1) | ~spl3_88),
% 5.79/1.09    inference(superposition,[],[f66,f1294])).
% 5.79/1.09  fof(f1294,plain,(
% 5.79/1.09    k5_xboole_0(sK2,sK1) = k3_xboole_0(k5_xboole_0(sK2,sK1),sK1) | ~spl3_88),
% 5.79/1.09    inference(avatar_component_clause,[],[f1292])).
% 5.79/1.09  fof(f66,plain,(
% 5.79/1.09    ( ! [X2,X1] : (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1)) )),
% 5.79/1.09    inference(superposition,[],[f40,f28])).
% 5.79/1.09  fof(f1379,plain,(
% 5.79/1.09    spl3_95 | ~spl3_88),
% 5.79/1.09    inference(avatar_split_clause,[],[f1365,f1292,f1373])).
% 5.79/1.09  fof(f1365,plain,(
% 5.79/1.09    k5_xboole_0(sK2,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK2,sK1)) | ~spl3_88),
% 5.79/1.09    inference(superposition,[],[f28,f1294])).
% 5.79/1.09  fof(f1378,plain,(
% 5.79/1.09    spl3_95 | ~spl3_88),
% 5.79/1.09    inference(avatar_split_clause,[],[f1364,f1292,f1373])).
% 5.79/1.09  fof(f1364,plain,(
% 5.79/1.09    k5_xboole_0(sK2,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK2,sK1)) | ~spl3_88),
% 5.79/1.09    inference(superposition,[],[f28,f1294])).
% 5.79/1.09  fof(f1377,plain,(
% 5.79/1.09    spl3_95 | ~spl3_88),
% 5.79/1.09    inference(avatar_split_clause,[],[f1363,f1292,f1373])).
% 5.79/1.09  fof(f1363,plain,(
% 5.79/1.09    k5_xboole_0(sK2,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK2,sK1)) | ~spl3_88),
% 5.79/1.09    inference(superposition,[],[f1294,f28])).
% 5.79/1.09  fof(f1376,plain,(
% 5.79/1.09    spl3_95 | ~spl3_88),
% 5.79/1.09    inference(avatar_split_clause,[],[f1362,f1292,f1373])).
% 5.79/1.09  fof(f1362,plain,(
% 5.79/1.09    k5_xboole_0(sK2,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK2,sK1)) | ~spl3_88),
% 5.79/1.09    inference(superposition,[],[f1294,f28])).
% 5.79/1.09  fof(f1327,plain,(
% 5.79/1.09    spl3_94 | ~spl3_79 | ~spl3_80),
% 5.79/1.09    inference(avatar_split_clause,[],[f1322,f1101,f1091,f1324])).
% 5.79/1.09  fof(f1324,plain,(
% 5.79/1.09    spl3_94 <=> sK1 = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))))))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_94])])).
% 5.79/1.09  fof(f1091,plain,(
% 5.79/1.09    spl3_79 <=> k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))))))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_79])])).
% 5.79/1.09  fof(f1322,plain,(
% 5.79/1.09    sK1 = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))))) | (~spl3_79 | ~spl3_80)),
% 5.79/1.09    inference(forward_demodulation,[],[f1093,f1103])).
% 5.79/1.09  fof(f1093,plain,(
% 5.79/1.09    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))))) | ~spl3_79),
% 5.79/1.09    inference(avatar_component_clause,[],[f1091])).
% 5.79/1.09  fof(f1321,plain,(
% 5.79/1.09    spl3_93 | ~spl3_80 | ~spl3_83),
% 5.79/1.09    inference(avatar_split_clause,[],[f1290,f1139,f1101,f1318])).
% 5.79/1.09  fof(f1139,plain,(
% 5.79/1.09    spl3_83 <=> k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).
% 5.79/1.09  fof(f1290,plain,(
% 5.79/1.09    sK1 = k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)) | (~spl3_80 | ~spl3_83)),
% 5.79/1.09    inference(backward_demodulation,[],[f1141,f1103])).
% 5.79/1.09  fof(f1141,plain,(
% 5.79/1.09    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)) | ~spl3_83),
% 5.79/1.09    inference(avatar_component_clause,[],[f1139])).
% 5.79/1.09  fof(f1316,plain,(
% 5.79/1.09    spl3_92 | ~spl3_80 | ~spl3_82),
% 5.79/1.09    inference(avatar_split_clause,[],[f1289,f1126,f1101,f1313])).
% 5.79/1.09  fof(f1313,plain,(
% 5.79/1.09    spl3_92 <=> sK1 = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_92])])).
% 5.79/1.09  fof(f1126,plain,(
% 5.79/1.09    spl3_82 <=> k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).
% 5.79/1.09  fof(f1289,plain,(
% 5.79/1.09    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))) | (~spl3_80 | ~spl3_82)),
% 5.79/1.09    inference(backward_demodulation,[],[f1128,f1103])).
% 5.79/1.09  fof(f1128,plain,(
% 5.79/1.09    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))) | ~spl3_82),
% 5.79/1.09    inference(avatar_component_clause,[],[f1126])).
% 5.79/1.09  fof(f1310,plain,(
% 5.79/1.09    spl3_91 | ~spl3_77 | ~spl3_80),
% 5.79/1.09    inference(avatar_split_clause,[],[f1287,f1101,f953,f1307])).
% 5.79/1.09  fof(f1307,plain,(
% 5.79/1.09    spl3_91 <=> k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),sK1)),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_91])])).
% 5.79/1.09  fof(f953,plain,(
% 5.79/1.09    spl3_77 <=> k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).
% 5.79/1.09  fof(f1287,plain,(
% 5.79/1.09    k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),sK1) | (~spl3_77 | ~spl3_80)),
% 5.79/1.09    inference(backward_demodulation,[],[f955,f1103])).
% 5.79/1.09  fof(f955,plain,(
% 5.79/1.09    k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_77),
% 5.79/1.09    inference(avatar_component_clause,[],[f953])).
% 5.79/1.09  fof(f1305,plain,(
% 5.79/1.09    spl3_90 | ~spl3_72 | ~spl3_80),
% 5.79/1.09    inference(avatar_split_clause,[],[f1283,f1101,f843,f1302])).
% 5.79/1.09  fof(f1302,plain,(
% 5.79/1.09    spl3_90 <=> r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),sK1)),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_90])])).
% 5.79/1.09  fof(f843,plain,(
% 5.79/1.09    spl3_72 <=> r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 5.79/1.09  fof(f1283,plain,(
% 5.79/1.09    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),sK1) | (~spl3_72 | ~spl3_80)),
% 5.79/1.09    inference(backward_demodulation,[],[f845,f1103])).
% 5.79/1.09  fof(f845,plain,(
% 5.79/1.09    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_72),
% 5.79/1.09    inference(avatar_component_clause,[],[f843])).
% 5.79/1.09  fof(f1300,plain,(
% 5.79/1.09    spl3_89 | ~spl3_60 | ~spl3_80),
% 5.79/1.09    inference(avatar_split_clause,[],[f1282,f1101,f709,f1297])).
% 5.79/1.09  fof(f1297,plain,(
% 5.79/1.09    spl3_89 <=> r1_tarski(k5_xboole_0(sK2,sK1),sK1)),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_89])])).
% 5.79/1.09  fof(f709,plain,(
% 5.79/1.09    spl3_60 <=> r1_tarski(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 5.79/1.09  fof(f1282,plain,(
% 5.79/1.09    r1_tarski(k5_xboole_0(sK2,sK1),sK1) | (~spl3_60 | ~spl3_80)),
% 5.79/1.09    inference(backward_demodulation,[],[f711,f1103])).
% 5.79/1.09  fof(f711,plain,(
% 5.79/1.09    r1_tarski(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_60),
% 5.79/1.09    inference(avatar_component_clause,[],[f709])).
% 5.79/1.09  fof(f1295,plain,(
% 5.79/1.09    spl3_88 | ~spl3_58 | ~spl3_80),
% 5.79/1.09    inference(avatar_split_clause,[],[f1281,f1101,f697,f1292])).
% 5.79/1.09  fof(f697,plain,(
% 5.79/1.09    spl3_58 <=> k5_xboole_0(sK2,sK1) = k3_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 5.79/1.09  fof(f1281,plain,(
% 5.79/1.09    k5_xboole_0(sK2,sK1) = k3_xboole_0(k5_xboole_0(sK2,sK1),sK1) | (~spl3_58 | ~spl3_80)),
% 5.79/1.09    inference(backward_demodulation,[],[f699,f1103])).
% 5.79/1.09  fof(f699,plain,(
% 5.79/1.09    k5_xboole_0(sK2,sK1) = k3_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_58),
% 5.79/1.09    inference(avatar_component_clause,[],[f697])).
% 5.79/1.09  fof(f1279,plain,(
% 5.79/1.09    spl3_87 | ~spl3_61 | ~spl3_83),
% 5.79/1.09    inference(avatar_split_clause,[],[f1259,f1139,f715,f1276])).
% 5.79/1.09  fof(f1276,plain,(
% 5.79/1.09    spl3_87 <=> r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))),sK1)),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_87])])).
% 5.79/1.09  fof(f715,plain,(
% 5.79/1.09    spl3_61 <=> r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),sK1)),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 5.79/1.09  fof(f1259,plain,(
% 5.79/1.09    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))),sK1) | (~spl3_61 | ~spl3_83)),
% 5.79/1.09    inference(backward_demodulation,[],[f717,f1141])).
% 5.79/1.09  fof(f717,plain,(
% 5.79/1.09    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),sK1) | ~spl3_61),
% 5.79/1.09    inference(avatar_component_clause,[],[f715])).
% 5.79/1.09  fof(f1274,plain,(
% 5.79/1.09    spl3_86 | ~spl3_59 | ~spl3_83),
% 5.79/1.09    inference(avatar_split_clause,[],[f1258,f1139,f703,f1271])).
% 5.79/1.09  fof(f1271,plain,(
% 5.79/1.09    spl3_86 <=> k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))),sK1)),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).
% 5.79/1.09  fof(f703,plain,(
% 5.79/1.09    spl3_59 <=> k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),sK1)),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 5.79/1.09  fof(f1258,plain,(
% 5.79/1.09    k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))),sK1) | (~spl3_59 | ~spl3_83)),
% 5.79/1.09    inference(backward_demodulation,[],[f705,f1141])).
% 5.79/1.09  fof(f705,plain,(
% 5.79/1.09    k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),sK1) | ~spl3_59),
% 5.79/1.09    inference(avatar_component_clause,[],[f703])).
% 5.79/1.09  fof(f1269,plain,(
% 5.79/1.09    spl3_85 | ~spl3_76 | ~spl3_83),
% 5.79/1.09    inference(avatar_split_clause,[],[f1257,f1139,f947,f1266])).
% 5.79/1.09  fof(f1266,plain,(
% 5.79/1.09    spl3_85 <=> r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).
% 5.79/1.09  fof(f947,plain,(
% 5.79/1.09    spl3_76 <=> r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 5.79/1.09  fof(f1257,plain,(
% 5.79/1.09    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | (~spl3_76 | ~spl3_83)),
% 5.79/1.09    inference(backward_demodulation,[],[f949,f1141])).
% 5.79/1.09  fof(f949,plain,(
% 5.79/1.09    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_76),
% 5.79/1.09    inference(avatar_component_clause,[],[f947])).
% 5.79/1.09  fof(f1264,plain,(
% 5.79/1.09    spl3_84 | ~spl3_78 | ~spl3_83),
% 5.79/1.09    inference(avatar_split_clause,[],[f1256,f1139,f973,f1261])).
% 5.79/1.09  fof(f1261,plain,(
% 5.79/1.09    spl3_84 <=> k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).
% 5.79/1.09  fof(f973,plain,(
% 5.79/1.09    spl3_78 <=> k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),
% 5.79/1.09    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).
% 5.79/1.09  fof(f1256,plain,(
% 5.79/1.09    k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | (~spl3_78 | ~spl3_83)),
% 5.79/1.09    inference(backward_demodulation,[],[f975,f1141])).
% 5.79/1.09  fof(f975,plain,(
% 5.79/1.09    k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_78),
% 5.79/1.10    inference(avatar_component_clause,[],[f973])).
% 5.79/1.10  fof(f1221,plain,(
% 5.79/1.10    spl3_83 | ~spl3_30),
% 5.79/1.10    inference(avatar_split_clause,[],[f1220,f415,f1139])).
% 5.79/1.10  fof(f415,plain,(
% 5.79/1.10    spl3_30 <=> sK2 = k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 5.79/1.10  fof(f1220,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)) | ~spl3_30),
% 5.79/1.10    inference(forward_demodulation,[],[f1219,f23])).
% 5.79/1.10  fof(f1219,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k1_xboole_0) | ~spl3_30),
% 5.79/1.10    inference(forward_demodulation,[],[f1218,f23])).
% 5.79/1.10  fof(f1218,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k1_xboole_0) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k1_xboole_0))) | ~spl3_30),
% 5.79/1.10    inference(forward_demodulation,[],[f1217,f1148])).
% 5.79/1.10  fof(f1217,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k1_xboole_0,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2)))) | ~spl3_30),
% 5.79/1.10    inference(forward_demodulation,[],[f1216,f28])).
% 5.79/1.10  fof(f1216,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(sK2,k1_xboole_0)) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0)))) | ~spl3_30),
% 5.79/1.10    inference(forward_demodulation,[],[f1215,f623])).
% 5.79/1.10  fof(f1215,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)))) | ~spl3_30),
% 5.79/1.10    inference(forward_demodulation,[],[f1214,f417])).
% 5.79/1.10  fof(f417,plain,(
% 5.79/1.10    sK2 = k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_30),
% 5.79/1.10    inference(avatar_component_clause,[],[f415])).
% 5.79/1.10  fof(f1214,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))))) | ~spl3_30),
% 5.79/1.10    inference(forward_demodulation,[],[f1213,f28])).
% 5.79/1.10  fof(f1213,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK2))))) | ~spl3_30),
% 5.79/1.10    inference(forward_demodulation,[],[f1212,f34])).
% 5.79/1.10  fof(f1212,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK2)))) | ~spl3_30),
% 5.79/1.10    inference(forward_demodulation,[],[f1051,f34])).
% 5.79/1.10  fof(f1051,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK2))) | ~spl3_30),
% 5.79/1.10    inference(superposition,[],[f41,f417])).
% 5.79/1.10  fof(f1211,plain,(
% 5.79/1.10    spl3_82 | ~spl3_73),
% 5.79/1.10    inference(avatar_split_clause,[],[f1210,f851,f1126])).
% 5.79/1.10  fof(f851,plain,(
% 5.79/1.10    spl3_73 <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).
% 5.79/1.10  fof(f1210,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))) | ~spl3_73),
% 5.79/1.10    inference(forward_demodulation,[],[f1209,f23])).
% 5.79/1.10  fof(f1209,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k1_xboole_0) | ~spl3_73),
% 5.79/1.10    inference(forward_demodulation,[],[f1208,f1148])).
% 5.79/1.10  fof(f1208,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k1_xboole_0,sK1)) | ~spl3_73),
% 5.79/1.10    inference(forward_demodulation,[],[f1207,f28])).
% 5.79/1.10  fof(f1207,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(sK1,k1_xboole_0)) | ~spl3_73),
% 5.79/1.10    inference(forward_demodulation,[],[f1206,f623])).
% 5.79/1.10  fof(f1206,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))) | ~spl3_73),
% 5.79/1.10    inference(forward_demodulation,[],[f1205,f853])).
% 5.79/1.10  fof(f853,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_73),
% 5.79/1.10    inference(avatar_component_clause,[],[f851])).
% 5.79/1.10  fof(f1205,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))))) | ~spl3_73),
% 5.79/1.10    inference(forward_demodulation,[],[f1204,f28])).
% 5.79/1.10  fof(f1204,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK1))))) | ~spl3_73),
% 5.79/1.10    inference(forward_demodulation,[],[f1203,f34])).
% 5.79/1.10  fof(f1203,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK1)))) | ~spl3_73),
% 5.79/1.10    inference(forward_demodulation,[],[f1050,f34])).
% 5.79/1.10  fof(f1050,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK1))) | ~spl3_73),
% 5.79/1.10    inference(superposition,[],[f41,f853])).
% 5.79/1.10  fof(f1202,plain,(
% 5.79/1.10    spl3_81 | ~spl3_9 | ~spl3_45),
% 5.79/1.10    inference(avatar_split_clause,[],[f1201,f586,f130,f1114])).
% 5.79/1.10  fof(f1114,plain,(
% 5.79/1.10    spl3_81 <=> sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).
% 5.79/1.10  fof(f1201,plain,(
% 5.79/1.10    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) | (~spl3_9 | ~spl3_45)),
% 5.79/1.10    inference(forward_demodulation,[],[f1200,f132])).
% 5.79/1.10  fof(f1200,plain,(
% 5.79/1.10    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) | (~spl3_9 | ~spl3_45)),
% 5.79/1.10    inference(forward_demodulation,[],[f1199,f28])).
% 5.79/1.10  fof(f1199,plain,(
% 5.79/1.10    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),sK1)))) | (~spl3_9 | ~spl3_45)),
% 5.79/1.10    inference(forward_demodulation,[],[f1198,f34])).
% 5.79/1.10  fof(f1198,plain,(
% 5.79/1.10    sK1 = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))) | (~spl3_9 | ~spl3_45)),
% 5.79/1.10    inference(forward_demodulation,[],[f1197,f23])).
% 5.79/1.10  fof(f1197,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))) = k5_xboole_0(sK1,k1_xboole_0) | (~spl3_9 | ~spl3_45)),
% 5.79/1.10    inference(forward_demodulation,[],[f1196,f1148])).
% 5.79/1.10  fof(f1196,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))) = k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2)) | (~spl3_9 | ~spl3_45)),
% 5.79/1.10    inference(forward_demodulation,[],[f1195,f28])).
% 5.79/1.10  fof(f1195,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))) = k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0)) | (~spl3_9 | ~spl3_45)),
% 5.79/1.10    inference(forward_demodulation,[],[f1194,f623])).
% 5.79/1.10  fof(f1194,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) | (~spl3_9 | ~spl3_45)),
% 5.79/1.10    inference(forward_demodulation,[],[f1193,f588])).
% 5.79/1.10  fof(f1193,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) | ~spl3_9),
% 5.79/1.10    inference(forward_demodulation,[],[f1049,f34])).
% 5.79/1.10  fof(f1049,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))) = k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) | ~spl3_9),
% 5.79/1.10    inference(superposition,[],[f41,f132])).
% 5.79/1.10  fof(f1192,plain,(
% 5.79/1.10    spl3_80 | ~spl3_5),
% 5.79/1.10    inference(avatar_split_clause,[],[f1191,f96,f1101])).
% 5.79/1.10  fof(f1191,plain,(
% 5.79/1.10    sK1 = k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) | ~spl3_5),
% 5.79/1.10    inference(forward_demodulation,[],[f1190,f23])).
% 5.79/1.10  fof(f1190,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k1_xboole_0) | ~spl3_5),
% 5.79/1.10    inference(forward_demodulation,[],[f1189,f1148])).
% 5.79/1.10  fof(f1189,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2)) | ~spl3_5),
% 5.79/1.10    inference(forward_demodulation,[],[f1188,f28])).
% 5.79/1.10  fof(f1188,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0)) | ~spl3_5),
% 5.79/1.10    inference(forward_demodulation,[],[f1187,f623])).
% 5.79/1.10  fof(f1187,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) | ~spl3_5),
% 5.79/1.10    inference(forward_demodulation,[],[f1186,f98])).
% 5.79/1.10  fof(f1186,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))) | ~spl3_5),
% 5.79/1.10    inference(forward_demodulation,[],[f1048,f28])).
% 5.79/1.10  fof(f1048,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1))) | ~spl3_5),
% 5.79/1.10    inference(superposition,[],[f41,f98])).
% 5.79/1.10  fof(f1185,plain,(
% 5.79/1.10    spl3_79 | ~spl3_58),
% 5.79/1.10    inference(avatar_split_clause,[],[f1184,f697,f1091])).
% 5.79/1.10  fof(f1184,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))))) | ~spl3_58),
% 5.79/1.10    inference(forward_demodulation,[],[f1183,f23])).
% 5.79/1.10  fof(f1183,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))))) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0))) | ~spl3_58),
% 5.79/1.10    inference(forward_demodulation,[],[f1182,f1148])).
% 5.79/1.10  fof(f1182,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,k5_xboole_0(sK2,sK1))))) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))))) | ~spl3_58),
% 5.79/1.10    inference(forward_demodulation,[],[f1181,f28])).
% 5.79/1.10  fof(f1181,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0)))) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))))) | ~spl3_58),
% 5.79/1.10    inference(forward_demodulation,[],[f1180,f34])).
% 5.79/1.10  fof(f1180,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))))) = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0))) | ~spl3_58),
% 5.79/1.10    inference(forward_demodulation,[],[f1179,f34])).
% 5.79/1.10  fof(f1179,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))))) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0)) | ~spl3_58),
% 5.79/1.10    inference(forward_demodulation,[],[f1178,f623])).
% 5.79/1.10  fof(f1178,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1))) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))))) | ~spl3_58),
% 5.79/1.10    inference(forward_demodulation,[],[f1177,f34])).
% 5.79/1.10  fof(f1177,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))))) | ~spl3_58),
% 5.79/1.10    inference(forward_demodulation,[],[f1176,f699])).
% 5.79/1.10  fof(f1176,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))))) | ~spl3_58),
% 5.79/1.10    inference(forward_demodulation,[],[f1175,f28])).
% 5.79/1.10  fof(f1175,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK1)))))) | ~spl3_58),
% 5.79/1.10    inference(forward_demodulation,[],[f1174,f34])).
% 5.79/1.10  fof(f1174,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK1))))) | ~spl3_58),
% 5.79/1.10    inference(forward_demodulation,[],[f1047,f34])).
% 5.79/1.10  fof(f1047,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK1)))) | ~spl3_58),
% 5.79/1.10    inference(superposition,[],[f41,f699])).
% 5.79/1.10  fof(f1142,plain,(
% 5.79/1.10    spl3_83 | ~spl3_30),
% 5.79/1.10    inference(avatar_split_clause,[],[f1137,f415,f1139])).
% 5.79/1.10  fof(f1137,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)) | ~spl3_30),
% 5.79/1.10    inference(forward_demodulation,[],[f1136,f693])).
% 5.79/1.10  fof(f1136,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k1_xboole_0,sK2)) | ~spl3_30),
% 5.79/1.10    inference(forward_demodulation,[],[f1135,f693])).
% 5.79/1.10  fof(f1135,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k1_xboole_0,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2)))) | ~spl3_30),
% 5.79/1.10    inference(forward_demodulation,[],[f1134,f28])).
% 5.79/1.10  fof(f1134,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(sK2,k1_xboole_0)) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0)))) | ~spl3_30),
% 5.79/1.10    inference(forward_demodulation,[],[f1133,f623])).
% 5.79/1.10  fof(f1133,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)))) | ~spl3_30),
% 5.79/1.10    inference(forward_demodulation,[],[f1132,f417])).
% 5.79/1.10  fof(f1132,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))))) | ~spl3_30),
% 5.79/1.10    inference(forward_demodulation,[],[f1131,f28])).
% 5.79/1.10  fof(f1131,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK2))))) | ~spl3_30),
% 5.79/1.10    inference(forward_demodulation,[],[f1130,f34])).
% 5.79/1.10  fof(f1130,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK2)))) | ~spl3_30),
% 5.79/1.10    inference(forward_demodulation,[],[f1038,f34])).
% 5.79/1.10  fof(f1038,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK2)) = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK2))) | ~spl3_30),
% 5.79/1.10    inference(superposition,[],[f41,f417])).
% 5.79/1.10  fof(f1129,plain,(
% 5.79/1.10    spl3_82 | ~spl3_73),
% 5.79/1.10    inference(avatar_split_clause,[],[f1124,f851,f1126])).
% 5.79/1.10  fof(f1124,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))) | ~spl3_73),
% 5.79/1.10    inference(forward_demodulation,[],[f1123,f693])).
% 5.79/1.10  fof(f1123,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k1_xboole_0,sK1)) | ~spl3_73),
% 5.79/1.10    inference(forward_demodulation,[],[f1122,f28])).
% 5.79/1.10  fof(f1122,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(sK1,k1_xboole_0)) | ~spl3_73),
% 5.79/1.10    inference(forward_demodulation,[],[f1121,f623])).
% 5.79/1.10  fof(f1121,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))) | ~spl3_73),
% 5.79/1.10    inference(forward_demodulation,[],[f1120,f853])).
% 5.79/1.10  fof(f1120,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))))) | ~spl3_73),
% 5.79/1.10    inference(forward_demodulation,[],[f1119,f28])).
% 5.79/1.10  fof(f1119,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK1))))) | ~spl3_73),
% 5.79/1.10    inference(forward_demodulation,[],[f1118,f34])).
% 5.79/1.10  fof(f1118,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK1)))) | ~spl3_73),
% 5.79/1.10    inference(forward_demodulation,[],[f1037,f34])).
% 5.79/1.10  fof(f1037,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK1))) | ~spl3_73),
% 5.79/1.10    inference(superposition,[],[f41,f853])).
% 5.79/1.10  fof(f1117,plain,(
% 5.79/1.10    spl3_81 | ~spl3_9 | ~spl3_45),
% 5.79/1.10    inference(avatar_split_clause,[],[f1112,f586,f130,f1114])).
% 5.79/1.10  fof(f1112,plain,(
% 5.79/1.10    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) | (~spl3_9 | ~spl3_45)),
% 5.79/1.10    inference(forward_demodulation,[],[f1111,f132])).
% 5.79/1.10  fof(f1111,plain,(
% 5.79/1.10    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) | (~spl3_9 | ~spl3_45)),
% 5.79/1.10    inference(forward_demodulation,[],[f1110,f28])).
% 5.79/1.10  fof(f1110,plain,(
% 5.79/1.10    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),sK1)))) | (~spl3_9 | ~spl3_45)),
% 5.79/1.10    inference(forward_demodulation,[],[f1109,f34])).
% 5.79/1.10  fof(f1109,plain,(
% 5.79/1.10    sK1 = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))) | (~spl3_9 | ~spl3_45)),
% 5.79/1.10    inference(forward_demodulation,[],[f1108,f693])).
% 5.79/1.10  fof(f1108,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))) = k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2)) | (~spl3_9 | ~spl3_45)),
% 5.79/1.10    inference(forward_demodulation,[],[f1107,f28])).
% 5.79/1.10  fof(f1107,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))) = k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0)) | (~spl3_9 | ~spl3_45)),
% 5.79/1.10    inference(forward_demodulation,[],[f1106,f623])).
% 5.79/1.10  fof(f1106,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) | (~spl3_9 | ~spl3_45)),
% 5.79/1.10    inference(forward_demodulation,[],[f1105,f588])).
% 5.79/1.10  fof(f1105,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))) = k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) | ~spl3_9),
% 5.79/1.10    inference(forward_demodulation,[],[f1036,f34])).
% 5.79/1.10  fof(f1036,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1))) = k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) | ~spl3_9),
% 5.79/1.10    inference(superposition,[],[f41,f132])).
% 5.79/1.10  fof(f1104,plain,(
% 5.79/1.10    spl3_80 | ~spl3_5),
% 5.79/1.10    inference(avatar_split_clause,[],[f1099,f96,f1101])).
% 5.79/1.10  fof(f1099,plain,(
% 5.79/1.10    sK1 = k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) | ~spl3_5),
% 5.79/1.10    inference(forward_demodulation,[],[f1098,f693])).
% 5.79/1.10  fof(f1098,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2)) | ~spl3_5),
% 5.79/1.10    inference(forward_demodulation,[],[f1097,f28])).
% 5.79/1.10  fof(f1097,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0)) | ~spl3_5),
% 5.79/1.10    inference(forward_demodulation,[],[f1096,f623])).
% 5.79/1.10  fof(f1096,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) | ~spl3_5),
% 5.79/1.10    inference(forward_demodulation,[],[f1095,f98])).
% 5.79/1.10  fof(f1095,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))) | ~spl3_5),
% 5.79/1.10    inference(forward_demodulation,[],[f1035,f28])).
% 5.79/1.10  fof(f1035,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1))) | ~spl3_5),
% 5.79/1.10    inference(superposition,[],[f41,f98])).
% 5.79/1.10  fof(f1094,plain,(
% 5.79/1.10    spl3_79 | ~spl3_58),
% 5.79/1.10    inference(avatar_split_clause,[],[f1089,f697,f1091])).
% 5.79/1.10  fof(f1089,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))))) | ~spl3_58),
% 5.79/1.10    inference(forward_demodulation,[],[f1088,f693])).
% 5.79/1.10  fof(f1088,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,k5_xboole_0(sK2,sK1))))) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))))) | ~spl3_58),
% 5.79/1.10    inference(forward_demodulation,[],[f1087,f28])).
% 5.79/1.10  fof(f1087,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0)))) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))))) | ~spl3_58),
% 5.79/1.10    inference(forward_demodulation,[],[f1086,f34])).
% 5.79/1.10  fof(f1086,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))))) = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0))) | ~spl3_58),
% 5.79/1.10    inference(forward_demodulation,[],[f1085,f34])).
% 5.79/1.10  fof(f1085,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))))) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0)) | ~spl3_58),
% 5.79/1.10    inference(forward_demodulation,[],[f1084,f623])).
% 5.79/1.10  fof(f1084,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1))) = k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))))) | ~spl3_58),
% 5.79/1.10    inference(forward_demodulation,[],[f1083,f34])).
% 5.79/1.10  fof(f1083,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))))) | ~spl3_58),
% 5.79/1.10    inference(forward_demodulation,[],[f1082,f699])).
% 5.79/1.10  fof(f1082,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))))) | ~spl3_58),
% 5.79/1.10    inference(forward_demodulation,[],[f1081,f28])).
% 5.79/1.10  fof(f1081,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK1)))))) | ~spl3_58),
% 5.79/1.10    inference(forward_demodulation,[],[f1080,f34])).
% 5.79/1.10  fof(f1080,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK1))))) | ~spl3_58),
% 5.79/1.10    inference(forward_demodulation,[],[f1034,f34])).
% 5.79/1.10  fof(f1034,plain,(
% 5.79/1.10    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK1)))) | ~spl3_58),
% 5.79/1.10    inference(superposition,[],[f41,f699])).
% 5.79/1.10  fof(f976,plain,(
% 5.79/1.10    spl3_78 | ~spl3_76),
% 5.79/1.10    inference(avatar_split_clause,[],[f971,f947,f973])).
% 5.79/1.10  fof(f971,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_76),
% 5.79/1.10    inference(resolution,[],[f949,f33])).
% 5.79/1.10  fof(f956,plain,(
% 5.79/1.10    spl3_77 | ~spl3_72),
% 5.79/1.10    inference(avatar_split_clause,[],[f951,f843,f953])).
% 5.79/1.10  fof(f951,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_72),
% 5.79/1.10    inference(resolution,[],[f845,f33])).
% 5.79/1.10  fof(f950,plain,(
% 5.79/1.10    spl3_76 | ~spl3_58),
% 5.79/1.10    inference(avatar_split_clause,[],[f945,f697,f947])).
% 5.79/1.10  fof(f945,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1)))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_58),
% 5.79/1.10    inference(forward_demodulation,[],[f944,f34])).
% 5.79/1.10  fof(f944,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK2,sK1))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_58),
% 5.79/1.10    inference(forward_demodulation,[],[f933,f34])).
% 5.79/1.10  fof(f933,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK1)),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_58),
% 5.79/1.10    inference(superposition,[],[f66,f699])).
% 5.79/1.10  fof(f927,plain,(
% 5.79/1.10    spl3_75 | ~spl3_30),
% 5.79/1.10    inference(avatar_split_clause,[],[f917,f415,f924])).
% 5.79/1.10  fof(f924,plain,(
% 5.79/1.10    spl3_75 <=> r1_tarski(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).
% 5.79/1.10  fof(f917,plain,(
% 5.79/1.10    r1_tarski(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_30),
% 5.79/1.10    inference(superposition,[],[f898,f417])).
% 5.79/1.10  fof(f922,plain,(
% 5.79/1.10    spl3_74 | ~spl3_73),
% 5.79/1.10    inference(avatar_split_clause,[],[f915,f851,f919])).
% 5.79/1.10  fof(f919,plain,(
% 5.79/1.10    spl3_74 <=> r1_tarski(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).
% 5.79/1.10  fof(f915,plain,(
% 5.79/1.10    r1_tarski(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_73),
% 5.79/1.10    inference(superposition,[],[f898,f853])).
% 5.79/1.10  fof(f857,plain,(
% 5.79/1.10    spl3_73 | ~spl3_25 | ~spl3_45),
% 5.79/1.10    inference(avatar_split_clause,[],[f840,f586,f375,f851])).
% 5.79/1.10  fof(f375,plain,(
% 5.79/1.10    spl3_25 <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 5.79/1.10  fof(f840,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | (~spl3_25 | ~spl3_45)),
% 5.79/1.10    inference(backward_demodulation,[],[f377,f834])).
% 5.79/1.10  fof(f377,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))) | ~spl3_25),
% 5.79/1.10    inference(avatar_component_clause,[],[f375])).
% 5.79/1.10  fof(f856,plain,(
% 5.79/1.10    spl3_73 | ~spl3_45 | ~spl3_67),
% 5.79/1.10    inference(avatar_split_clause,[],[f855,f769,f586,f851])).
% 5.79/1.10  fof(f769,plain,(
% 5.79/1.10    spl3_67 <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).
% 5.79/1.10  fof(f855,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | (~spl3_45 | ~spl3_67)),
% 5.79/1.10    inference(forward_demodulation,[],[f839,f834])).
% 5.79/1.10  fof(f839,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))) | (~spl3_45 | ~spl3_67)),
% 5.79/1.10    inference(backward_demodulation,[],[f771,f834])).
% 5.79/1.10  fof(f771,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))))) | ~spl3_67),
% 5.79/1.10    inference(avatar_component_clause,[],[f769])).
% 5.79/1.10  fof(f854,plain,(
% 5.79/1.10    spl3_73 | ~spl3_45 | ~spl3_71),
% 5.79/1.10    inference(avatar_split_clause,[],[f849,f820,f586,f851])).
% 5.79/1.10  fof(f820,plain,(
% 5.79/1.10    spl3_71 <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).
% 5.79/1.10  fof(f849,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | (~spl3_45 | ~spl3_71)),
% 5.79/1.10    inference(forward_demodulation,[],[f848,f834])).
% 5.79/1.10  fof(f848,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))) | (~spl3_45 | ~spl3_71)),
% 5.79/1.10    inference(forward_demodulation,[],[f838,f834])).
% 5.79/1.10  fof(f838,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))))) | (~spl3_45 | ~spl3_71)),
% 5.79/1.10    inference(backward_demodulation,[],[f822,f834])).
% 5.79/1.10  fof(f822,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))))))) | ~spl3_71),
% 5.79/1.10    inference(avatar_component_clause,[],[f820])).
% 5.79/1.10  fof(f846,plain,(
% 5.79/1.10    spl3_72 | ~spl3_43 | ~spl3_45),
% 5.79/1.10    inference(avatar_split_clause,[],[f841,f586,f524,f843])).
% 5.79/1.10  fof(f524,plain,(
% 5.79/1.10    spl3_43 <=> r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 5.79/1.10  fof(f841,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | (~spl3_43 | ~spl3_45)),
% 5.79/1.10    inference(forward_demodulation,[],[f835,f834])).
% 5.79/1.10  fof(f835,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))) | (~spl3_43 | ~spl3_45)),
% 5.79/1.10    inference(backward_demodulation,[],[f526,f834])).
% 5.79/1.10  fof(f526,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))) | ~spl3_43),
% 5.79/1.10    inference(avatar_component_clause,[],[f524])).
% 5.79/1.10  fof(f823,plain,(
% 5.79/1.10    spl3_71 | ~spl3_45 | ~spl3_63),
% 5.79/1.10    inference(avatar_split_clause,[],[f818,f739,f586,f820])).
% 5.79/1.10  fof(f739,plain,(
% 5.79/1.10    spl3_63 <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 5.79/1.10  fof(f818,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))))))) | (~spl3_45 | ~spl3_63)),
% 5.79/1.10    inference(forward_demodulation,[],[f741,f588])).
% 5.79/1.10  fof(f741,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))) | ~spl3_63),
% 5.79/1.10    inference(avatar_component_clause,[],[f739])).
% 5.79/1.10  fof(f817,plain,(
% 5.79/1.10    spl3_70 | ~spl3_45 | ~spl3_64),
% 5.79/1.10    inference(avatar_split_clause,[],[f812,f744,f586,f814])).
% 5.79/1.10  fof(f814,plain,(
% 5.79/1.10    spl3_70 <=> sK2 = k3_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 5.79/1.10  fof(f744,plain,(
% 5.79/1.10    spl3_64 <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 5.79/1.10  fof(f812,plain,(
% 5.79/1.10    sK2 = k3_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))))) | (~spl3_45 | ~spl3_64)),
% 5.79/1.10    inference(forward_demodulation,[],[f811,f588])).
% 5.79/1.10  fof(f811,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))))) | (~spl3_45 | ~spl3_64)),
% 5.79/1.10    inference(forward_demodulation,[],[f746,f588])).
% 5.79/1.10  fof(f746,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))) | ~spl3_64),
% 5.79/1.10    inference(avatar_component_clause,[],[f744])).
% 5.79/1.10  fof(f796,plain,(
% 5.79/1.10    spl3_69 | ~spl3_45 | ~spl3_68),
% 5.79/1.10    inference(avatar_split_clause,[],[f791,f774,f586,f793])).
% 5.79/1.10  fof(f793,plain,(
% 5.79/1.10    spl3_69 <=> sK2 = k3_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 5.79/1.10  fof(f774,plain,(
% 5.79/1.10    spl3_68 <=> k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 5.79/1.10  fof(f791,plain,(
% 5.79/1.10    sK2 = k3_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))) | (~spl3_45 | ~spl3_68)),
% 5.79/1.10    inference(forward_demodulation,[],[f776,f588])).
% 5.79/1.10  fof(f776,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))) | ~spl3_68),
% 5.79/1.10    inference(avatar_component_clause,[],[f774])).
% 5.79/1.10  fof(f777,plain,(
% 5.79/1.10    spl3_68 | ~spl3_32 | ~spl3_46),
% 5.79/1.10    inference(avatar_split_clause,[],[f767,f592,f428,f774])).
% 5.79/1.10  fof(f428,plain,(
% 5.79/1.10    spl3_32 <=> k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 5.79/1.10  fof(f592,plain,(
% 5.79/1.10    spl3_46 <=> k5_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 5.79/1.10  fof(f767,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))) | (~spl3_32 | ~spl3_46)),
% 5.79/1.10    inference(backward_demodulation,[],[f430,f594])).
% 5.79/1.10  fof(f594,plain,(
% 5.79/1.10    k5_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) | ~spl3_46),
% 5.79/1.10    inference(avatar_component_clause,[],[f592])).
% 5.79/1.10  fof(f430,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))) | ~spl3_32),
% 5.79/1.10    inference(avatar_component_clause,[],[f428])).
% 5.79/1.10  fof(f772,plain,(
% 5.79/1.10    spl3_67 | ~spl3_27 | ~spl3_46),
% 5.79/1.10    inference(avatar_split_clause,[],[f766,f592,f390,f769])).
% 5.79/1.10  fof(f390,plain,(
% 5.79/1.10    spl3_27 <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 5.79/1.10  fof(f766,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))))) | (~spl3_27 | ~spl3_46)),
% 5.79/1.10    inference(backward_demodulation,[],[f392,f594])).
% 5.79/1.10  fof(f392,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))) | ~spl3_27),
% 5.79/1.10    inference(avatar_component_clause,[],[f390])).
% 5.79/1.10  fof(f762,plain,(
% 5.79/1.10    spl3_66 | ~spl3_33 | ~spl3_47),
% 5.79/1.10    inference(avatar_split_clause,[],[f752,f598,f436,f759])).
% 5.79/1.10  fof(f759,plain,(
% 5.79/1.10    spl3_66 <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 5.79/1.10  fof(f436,plain,(
% 5.79/1.10    spl3_33 <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 5.79/1.10  fof(f598,plain,(
% 5.79/1.10    spl3_47 <=> k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 5.79/1.10  fof(f752,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))) | (~spl3_33 | ~spl3_47)),
% 5.79/1.10    inference(backward_demodulation,[],[f438,f600])).
% 5.79/1.10  fof(f600,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) | ~spl3_47),
% 5.79/1.10    inference(avatar_component_clause,[],[f598])).
% 5.79/1.10  fof(f438,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))) | ~spl3_33),
% 5.79/1.10    inference(avatar_component_clause,[],[f436])).
% 5.79/1.10  fof(f757,plain,(
% 5.79/1.10    spl3_65 | ~spl3_28 | ~spl3_47),
% 5.79/1.10    inference(avatar_split_clause,[],[f751,f598,f399,f754])).
% 5.79/1.10  fof(f754,plain,(
% 5.79/1.10    spl3_65 <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 5.79/1.10  fof(f399,plain,(
% 5.79/1.10    spl3_28 <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 5.79/1.10  fof(f751,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))) | (~spl3_28 | ~spl3_47)),
% 5.79/1.10    inference(backward_demodulation,[],[f401,f600])).
% 5.79/1.10  fof(f401,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))) | ~spl3_28),
% 5.79/1.10    inference(avatar_component_clause,[],[f399])).
% 5.79/1.10  fof(f747,plain,(
% 5.79/1.10    spl3_64 | ~spl3_34 | ~spl3_48),
% 5.79/1.10    inference(avatar_split_clause,[],[f737,f604,f445,f744])).
% 5.79/1.10  fof(f445,plain,(
% 5.79/1.10    spl3_34 <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 5.79/1.10  fof(f604,plain,(
% 5.79/1.10    spl3_48 <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 5.79/1.10  fof(f737,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))) | (~spl3_34 | ~spl3_48)),
% 5.79/1.10    inference(backward_demodulation,[],[f447,f606])).
% 5.79/1.10  fof(f606,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) | ~spl3_48),
% 5.79/1.10    inference(avatar_component_clause,[],[f604])).
% 5.79/1.10  fof(f447,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))) | ~spl3_34),
% 5.79/1.10    inference(avatar_component_clause,[],[f445])).
% 5.79/1.10  fof(f742,plain,(
% 5.79/1.10    spl3_63 | ~spl3_29 | ~spl3_48),
% 5.79/1.10    inference(avatar_split_clause,[],[f736,f604,f409,f739])).
% 5.79/1.10  fof(f409,plain,(
% 5.79/1.10    spl3_29 <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 5.79/1.10  fof(f736,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))) | (~spl3_29 | ~spl3_48)),
% 5.79/1.10    inference(backward_demodulation,[],[f411,f606])).
% 5.79/1.10  fof(f411,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))))) | ~spl3_29),
% 5.79/1.10    inference(avatar_component_clause,[],[f409])).
% 5.79/1.10  fof(f732,plain,(
% 5.79/1.10    spl3_62 | ~spl3_35 | ~spl3_49),
% 5.79/1.10    inference(avatar_split_clause,[],[f725,f610,f455,f729])).
% 5.79/1.10  fof(f729,plain,(
% 5.79/1.10    spl3_62 <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 5.79/1.10  fof(f455,plain,(
% 5.79/1.10    spl3_35 <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 5.79/1.10  fof(f610,plain,(
% 5.79/1.10    spl3_49 <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 5.79/1.10  fof(f725,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))) | (~spl3_35 | ~spl3_49)),
% 5.79/1.10    inference(backward_demodulation,[],[f457,f612])).
% 5.79/1.10  fof(f612,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))) | ~spl3_49),
% 5.79/1.10    inference(avatar_component_clause,[],[f610])).
% 5.79/1.10  fof(f457,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))))) | ~spl3_35),
% 5.79/1.10    inference(avatar_component_clause,[],[f455])).
% 5.79/1.10  fof(f718,plain,(
% 5.79/1.10    spl3_61 | ~spl3_54),
% 5.79/1.10    inference(avatar_split_clause,[],[f713,f661,f715])).
% 5.79/1.10  fof(f661,plain,(
% 5.79/1.10    spl3_54 <=> r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2)))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 5.79/1.10  fof(f713,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),sK1) | ~spl3_54),
% 5.79/1.10    inference(forward_demodulation,[],[f663,f693])).
% 5.79/1.10  fof(f663,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))) | ~spl3_54),
% 5.79/1.10    inference(avatar_component_clause,[],[f661])).
% 5.79/1.10  fof(f712,plain,(
% 5.79/1.10    spl3_60 | ~spl3_55),
% 5.79/1.10    inference(avatar_split_clause,[],[f707,f667,f709])).
% 5.79/1.10  fof(f667,plain,(
% 5.79/1.10    spl3_55 <=> r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 5.79/1.10  fof(f707,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_55),
% 5.79/1.10    inference(forward_demodulation,[],[f669,f693])).
% 5.79/1.10  fof(f669,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_55),
% 5.79/1.10    inference(avatar_component_clause,[],[f667])).
% 5.79/1.10  fof(f706,plain,(
% 5.79/1.10    spl3_59 | ~spl3_56),
% 5.79/1.10    inference(avatar_split_clause,[],[f701,f673,f703])).
% 5.79/1.10  fof(f673,plain,(
% 5.79/1.10    spl3_56 <=> k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2)))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 5.79/1.10  fof(f701,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),sK1) | ~spl3_56),
% 5.79/1.10    inference(forward_demodulation,[],[f675,f693])).
% 5.79/1.10  fof(f675,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))) | ~spl3_56),
% 5.79/1.10    inference(avatar_component_clause,[],[f673])).
% 5.79/1.10  fof(f700,plain,(
% 5.79/1.10    spl3_58 | ~spl3_57),
% 5.79/1.10    inference(avatar_split_clause,[],[f695,f679,f697])).
% 5.79/1.10  fof(f679,plain,(
% 5.79/1.10    spl3_57 <=> k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 5.79/1.10  fof(f695,plain,(
% 5.79/1.10    k5_xboole_0(sK2,sK1) = k3_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_57),
% 5.79/1.10    inference(forward_demodulation,[],[f681,f693])).
% 5.79/1.10  fof(f681,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_57),
% 5.79/1.10    inference(avatar_component_clause,[],[f679])).
% 5.79/1.10  fof(f682,plain,(
% 5.79/1.10    spl3_57 | ~spl3_44),
% 5.79/1.10    inference(avatar_split_clause,[],[f677,f530,f679])).
% 5.79/1.10  fof(f530,plain,(
% 5.79/1.10    spl3_44 <=> k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 5.79/1.10  fof(f677,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_44),
% 5.79/1.10    inference(forward_demodulation,[],[f638,f28])).
% 5.79/1.10  fof(f638,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_44),
% 5.79/1.10    inference(backward_demodulation,[],[f532,f623])).
% 5.79/1.10  fof(f532,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_44),
% 5.79/1.10    inference(avatar_component_clause,[],[f530])).
% 5.79/1.10  fof(f676,plain,(
% 5.79/1.10    spl3_56 | ~spl3_41),
% 5.79/1.10    inference(avatar_split_clause,[],[f671,f503,f673])).
% 5.79/1.10  fof(f503,plain,(
% 5.79/1.10    spl3_41 <=> k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 5.79/1.10  fof(f671,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))) | ~spl3_41),
% 5.79/1.10    inference(forward_demodulation,[],[f637,f28])).
% 5.79/1.10  fof(f637,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0))) | ~spl3_41),
% 5.79/1.10    inference(backward_demodulation,[],[f505,f623])).
% 5.79/1.10  fof(f505,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))) | ~spl3_41),
% 5.79/1.10    inference(avatar_component_clause,[],[f503])).
% 5.79/1.10  fof(f670,plain,(
% 5.79/1.10    spl3_55 | ~spl3_40),
% 5.79/1.10    inference(avatar_split_clause,[],[f665,f497,f667])).
% 5.79/1.10  fof(f497,plain,(
% 5.79/1.10    spl3_40 <=> r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 5.79/1.10  fof(f665,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_40),
% 5.79/1.10    inference(forward_demodulation,[],[f636,f28])).
% 5.79/1.10  fof(f636,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_40),
% 5.79/1.10    inference(backward_demodulation,[],[f499,f623])).
% 5.79/1.10  fof(f499,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_40),
% 5.79/1.10    inference(avatar_component_clause,[],[f497])).
% 5.79/1.10  fof(f664,plain,(
% 5.79/1.10    spl3_54 | ~spl3_38),
% 5.79/1.10    inference(avatar_split_clause,[],[f659,f480,f661])).
% 5.79/1.10  fof(f480,plain,(
% 5.79/1.10    spl3_38 <=> r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 5.79/1.10  fof(f659,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))) | ~spl3_38),
% 5.79/1.10    inference(forward_demodulation,[],[f635,f28])).
% 5.79/1.10  fof(f635,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0))) | ~spl3_38),
% 5.79/1.10    inference(backward_demodulation,[],[f482,f623])).
% 5.79/1.10  fof(f482,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))) | ~spl3_38),
% 5.79/1.10    inference(avatar_component_clause,[],[f480])).
% 5.79/1.10  fof(f658,plain,(
% 5.79/1.10    spl3_53 | ~spl3_36),
% 5.79/1.10    inference(avatar_split_clause,[],[f653,f460,f655])).
% 5.79/1.10  fof(f655,plain,(
% 5.79/1.10    spl3_53 <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2)))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 5.79/1.10  fof(f460,plain,(
% 5.79/1.10    spl3_36 <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 5.79/1.10  fof(f653,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2))) | ~spl3_36),
% 5.79/1.10    inference(forward_demodulation,[],[f634,f28])).
% 5.79/1.10  fof(f634,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0))) | ~spl3_36),
% 5.79/1.10    inference(backward_demodulation,[],[f462,f623])).
% 5.79/1.10  fof(f462,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))) | ~spl3_36),
% 5.79/1.10    inference(avatar_component_clause,[],[f460])).
% 5.79/1.10  fof(f652,plain,(
% 5.79/1.10    spl3_52 | ~spl3_37),
% 5.79/1.10    inference(avatar_split_clause,[],[f647,f473,f649])).
% 5.79/1.10  fof(f649,plain,(
% 5.79/1.10    spl3_52 <=> k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK1)))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 5.79/1.10  fof(f473,plain,(
% 5.79/1.10    spl3_37 <=> k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK1)))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 5.79/1.10  fof(f647,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK1))))) | ~spl3_37),
% 5.79/1.10    inference(forward_demodulation,[],[f646,f28])).
% 5.79/1.10  fof(f646,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0)) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0)),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK1))))) | ~spl3_37),
% 5.79/1.10    inference(forward_demodulation,[],[f645,f623])).
% 5.79/1.10  fof(f645,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK1))))) | ~spl3_37),
% 5.79/1.10    inference(forward_demodulation,[],[f633,f28])).
% 5.79/1.10  fof(f633,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK1,k1_xboole_0))))) | ~spl3_37),
% 5.79/1.10    inference(backward_demodulation,[],[f475,f623])).
% 5.79/1.10  fof(f475,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK1))))) | ~spl3_37),
% 5.79/1.10    inference(avatar_component_clause,[],[f473])).
% 5.79/1.10  fof(f644,plain,(
% 5.79/1.10    spl3_51 | ~spl3_42),
% 5.79/1.10    inference(avatar_split_clause,[],[f639,f515,f641])).
% 5.79/1.10  fof(f641,plain,(
% 5.79/1.10    spl3_51 <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK1)))))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 5.79/1.10  fof(f515,plain,(
% 5.79/1.10    spl3_42 <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK1)))))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 5.79/1.10  fof(f639,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK1))))))) | ~spl3_42),
% 5.79/1.10    inference(forward_demodulation,[],[f632,f28])).
% 5.79/1.10  fof(f632,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,k1_xboole_0))))))) | ~spl3_42),
% 5.79/1.10    inference(backward_demodulation,[],[f517,f623])).
% 5.79/1.10  fof(f517,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK1))))))) | ~spl3_42),
% 5.79/1.10    inference(avatar_component_clause,[],[f515])).
% 5.79/1.10  fof(f618,plain,(
% 5.79/1.10    spl3_50 | ~spl3_21),
% 5.79/1.10    inference(avatar_split_clause,[],[f550,f254,f615])).
% 5.79/1.10  fof(f615,plain,(
% 5.79/1.10    spl3_50 <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 5.79/1.10  fof(f254,plain,(
% 5.79/1.10    spl3_21 <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 5.79/1.10  fof(f550,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))) | ~spl3_21),
% 5.79/1.10    inference(superposition,[],[f37,f256])).
% 5.79/1.10  fof(f256,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))) | ~spl3_21),
% 5.79/1.10    inference(avatar_component_clause,[],[f254])).
% 5.79/1.10  fof(f613,plain,(
% 5.79/1.10    spl3_49 | ~spl3_18 | ~spl3_21),
% 5.79/1.10    inference(avatar_split_clause,[],[f608,f254,f211,f610])).
% 5.79/1.10  fof(f211,plain,(
% 5.79/1.10    spl3_18 <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 5.79/1.10  fof(f608,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))) | (~spl3_18 | ~spl3_21)),
% 5.79/1.10    inference(forward_demodulation,[],[f549,f256])).
% 5.79/1.10  fof(f549,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))) | ~spl3_18),
% 5.79/1.10    inference(superposition,[],[f37,f213])).
% 5.79/1.10  fof(f213,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) | ~spl3_18),
% 5.79/1.10    inference(avatar_component_clause,[],[f211])).
% 5.79/1.10  fof(f607,plain,(
% 5.79/1.10    spl3_48 | ~spl3_15 | ~spl3_18),
% 5.79/1.10    inference(avatar_split_clause,[],[f602,f211,f184,f604])).
% 5.79/1.10  fof(f184,plain,(
% 5.79/1.10    spl3_15 <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 5.79/1.10  fof(f602,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) | (~spl3_15 | ~spl3_18)),
% 5.79/1.10    inference(forward_demodulation,[],[f548,f213])).
% 5.79/1.10  fof(f548,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))) | ~spl3_15),
% 5.79/1.10    inference(superposition,[],[f37,f186])).
% 5.79/1.10  fof(f186,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) | ~spl3_15),
% 5.79/1.10    inference(avatar_component_clause,[],[f184])).
% 5.79/1.10  fof(f601,plain,(
% 5.79/1.10    spl3_47 | ~spl3_12 | ~spl3_15),
% 5.79/1.10    inference(avatar_split_clause,[],[f596,f184,f157,f598])).
% 5.79/1.10  fof(f157,plain,(
% 5.79/1.10    spl3_12 <=> k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 5.79/1.10  fof(f596,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) | (~spl3_12 | ~spl3_15)),
% 5.79/1.10    inference(forward_demodulation,[],[f547,f186])).
% 5.79/1.10  fof(f547,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) | ~spl3_12),
% 5.79/1.10    inference(superposition,[],[f37,f159])).
% 5.79/1.10  fof(f159,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) | ~spl3_12),
% 5.79/1.10    inference(avatar_component_clause,[],[f157])).
% 5.79/1.10  fof(f595,plain,(
% 5.79/1.10    spl3_46 | ~spl3_9 | ~spl3_12),
% 5.79/1.10    inference(avatar_split_clause,[],[f590,f157,f130,f592])).
% 5.79/1.10  fof(f590,plain,(
% 5.79/1.10    k5_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) | (~spl3_9 | ~spl3_12)),
% 5.79/1.10    inference(forward_demodulation,[],[f546,f159])).
% 5.79/1.10  fof(f546,plain,(
% 5.79/1.10    k5_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) | ~spl3_9),
% 5.79/1.10    inference(superposition,[],[f37,f132])).
% 5.79/1.10  fof(f589,plain,(
% 5.79/1.10    spl3_45 | ~spl3_5 | ~spl3_9),
% 5.79/1.10    inference(avatar_split_clause,[],[f584,f130,f96,f586])).
% 5.79/1.10  fof(f584,plain,(
% 5.79/1.10    sK2 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | (~spl3_5 | ~spl3_9)),
% 5.79/1.10    inference(forward_demodulation,[],[f545,f132])).
% 5.79/1.10  fof(f545,plain,(
% 5.79/1.10    sK2 = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))) | ~spl3_5),
% 5.79/1.10    inference(superposition,[],[f37,f98])).
% 5.79/1.10  fof(f533,plain,(
% 5.79/1.10    spl3_44 | ~spl3_40),
% 5.79/1.10    inference(avatar_split_clause,[],[f528,f497,f530])).
% 5.79/1.10  fof(f528,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_40),
% 5.79/1.10    inference(resolution,[],[f499,f33])).
% 5.79/1.10  fof(f527,plain,(
% 5.79/1.10    spl3_43 | ~spl3_25),
% 5.79/1.10    inference(avatar_split_clause,[],[f522,f375,f524])).
% 5.79/1.10  fof(f522,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))) | ~spl3_25),
% 5.79/1.10    inference(forward_demodulation,[],[f521,f34])).
% 5.79/1.10  fof(f521,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))) | ~spl3_25),
% 5.79/1.10    inference(forward_demodulation,[],[f520,f34])).
% 5.79/1.10  fof(f520,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK1))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))) | ~spl3_25),
% 5.79/1.10    inference(forward_demodulation,[],[f519,f34])).
% 5.79/1.10  fof(f519,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))),sK1)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))) | ~spl3_25),
% 5.79/1.10    inference(forward_demodulation,[],[f508,f34])).
% 5.79/1.10  fof(f508,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),sK1),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))) | ~spl3_25),
% 5.79/1.10    inference(superposition,[],[f66,f377])).
% 5.79/1.10  fof(f518,plain,(
% 5.79/1.10    spl3_42 | ~spl3_25),
% 5.79/1.10    inference(avatar_split_clause,[],[f513,f375,f515])).
% 5.79/1.10  fof(f513,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK1))))))) | ~spl3_25),
% 5.79/1.10    inference(forward_demodulation,[],[f512,f34])).
% 5.79/1.10  fof(f512,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK1)))))) | ~spl3_25),
% 5.79/1.10    inference(forward_demodulation,[],[f511,f34])).
% 5.79/1.10  fof(f511,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK1))))) | ~spl3_25),
% 5.79/1.10    inference(forward_demodulation,[],[f510,f34])).
% 5.79/1.10  fof(f510,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,sK1)))) | ~spl3_25),
% 5.79/1.10    inference(forward_demodulation,[],[f507,f34])).
% 5.79/1.10  fof(f507,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,sK1))) | ~spl3_25),
% 5.79/1.10    inference(superposition,[],[f42,f377])).
% 5.79/1.10  fof(f506,plain,(
% 5.79/1.10    spl3_41 | ~spl3_38),
% 5.79/1.10    inference(avatar_split_clause,[],[f501,f480,f503])).
% 5.79/1.10  fof(f501,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))) | ~spl3_38),
% 5.79/1.10    inference(resolution,[],[f482,f33])).
% 5.79/1.10  fof(f500,plain,(
% 5.79/1.10    spl3_40 | ~spl3_30),
% 5.79/1.10    inference(avatar_split_clause,[],[f495,f415,f497])).
% 5.79/1.10  fof(f495,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_30),
% 5.79/1.10    inference(forward_demodulation,[],[f494,f34])).
% 5.79/1.10  fof(f494,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),sK2)),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_30),
% 5.79/1.10    inference(forward_demodulation,[],[f485,f34])).
% 5.79/1.10  fof(f485,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),sK2),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_30),
% 5.79/1.10    inference(superposition,[],[f66,f417])).
% 5.79/1.10  fof(f493,plain,(
% 5.79/1.10    spl3_39 | ~spl3_30),
% 5.79/1.10    inference(avatar_split_clause,[],[f488,f415,f490])).
% 5.79/1.10  fof(f490,plain,(
% 5.79/1.10    spl3_39 <=> k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK2)))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 5.79/1.10  fof(f488,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK2))))) | ~spl3_30),
% 5.79/1.10    inference(forward_demodulation,[],[f487,f34])).
% 5.79/1.10  fof(f487,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK2,sK2)))) | ~spl3_30),
% 5.79/1.10    inference(forward_demodulation,[],[f484,f34])).
% 5.79/1.10  fof(f484,plain,(
% 5.79/1.10    k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,sK2))) | ~spl3_30),
% 5.79/1.10    inference(superposition,[],[f42,f417])).
% 5.79/1.10  fof(f483,plain,(
% 5.79/1.10    spl3_38 | ~spl3_36),
% 5.79/1.10    inference(avatar_split_clause,[],[f478,f460,f480])).
% 5.79/1.10  fof(f478,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,sK1))),k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))) | ~spl3_36),
% 5.79/1.10    inference(forward_demodulation,[],[f477,f34])).
% 5.79/1.10  fof(f477,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,sK2),sK1)),k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))) | ~spl3_36),
% 5.79/1.10    inference(forward_demodulation,[],[f468,f34])).
% 5.79/1.10  fof(f468,plain,(
% 5.79/1.10    r1_tarski(k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)),sK1),k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))) | ~spl3_36),
% 5.79/1.10    inference(superposition,[],[f66,f462])).
% 5.79/1.10  fof(f476,plain,(
% 5.79/1.10    spl3_37 | ~spl3_36),
% 5.79/1.10    inference(avatar_split_clause,[],[f471,f460,f473])).
% 5.79/1.10  fof(f471,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK1))))) | ~spl3_36),
% 5.79/1.10    inference(forward_demodulation,[],[f470,f34])).
% 5.79/1.10  fof(f470,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(sK1,sK1)))) | ~spl3_36),
% 5.79/1.10    inference(forward_demodulation,[],[f467,f34])).
% 5.79/1.10  fof(f467,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)),k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)),k5_xboole_0(sK1,sK1))) | ~spl3_36),
% 5.79/1.10    inference(superposition,[],[f42,f462])).
% 5.79/1.10  fof(f463,plain,(
% 5.79/1.10    spl3_36 | ~spl3_4),
% 5.79/1.10    inference(avatar_split_clause,[],[f361,f85,f460])).
% 5.79/1.10  fof(f361,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))) | ~spl3_4),
% 5.79/1.10    inference(superposition,[],[f42,f87])).
% 5.79/1.10  fof(f458,plain,(
% 5.79/1.10    spl3_35 | ~spl3_21),
% 5.79/1.10    inference(avatar_split_clause,[],[f453,f254,f455])).
% 5.79/1.10  fof(f453,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))))) | ~spl3_21),
% 5.79/1.10    inference(forward_demodulation,[],[f452,f34])).
% 5.79/1.10  fof(f452,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))))) | ~spl3_21),
% 5.79/1.10    inference(forward_demodulation,[],[f451,f34])).
% 5.79/1.10  fof(f451,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))) | ~spl3_21),
% 5.79/1.10    inference(forward_demodulation,[],[f450,f34])).
% 5.79/1.10  fof(f450,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))) | ~spl3_21),
% 5.79/1.10    inference(forward_demodulation,[],[f449,f34])).
% 5.79/1.10  fof(f449,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))) | ~spl3_21),
% 5.79/1.10    inference(forward_demodulation,[],[f360,f34])).
% 5.79/1.10  fof(f360,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))) | ~spl3_21),
% 5.79/1.10    inference(superposition,[],[f42,f256])).
% 5.79/1.10  fof(f448,plain,(
% 5.79/1.10    spl3_34 | ~spl3_18),
% 5.79/1.10    inference(avatar_split_clause,[],[f443,f211,f445])).
% 5.79/1.10  fof(f443,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))) | ~spl3_18),
% 5.79/1.10    inference(forward_demodulation,[],[f442,f34])).
% 5.79/1.10  fof(f442,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))) | ~spl3_18),
% 5.79/1.10    inference(forward_demodulation,[],[f441,f34])).
% 5.79/1.10  fof(f441,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))) | ~spl3_18),
% 5.79/1.10    inference(forward_demodulation,[],[f440,f34])).
% 5.79/1.10  fof(f440,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))) | ~spl3_18),
% 5.79/1.10    inference(forward_demodulation,[],[f359,f34])).
% 5.79/1.10  fof(f359,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))) | ~spl3_18),
% 5.79/1.10    inference(superposition,[],[f42,f213])).
% 5.79/1.10  fof(f439,plain,(
% 5.79/1.10    spl3_33 | ~spl3_15),
% 5.79/1.10    inference(avatar_split_clause,[],[f434,f184,f436])).
% 5.79/1.10  fof(f434,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))) | ~spl3_15),
% 5.79/1.10    inference(forward_demodulation,[],[f433,f34])).
% 5.79/1.10  fof(f433,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))) | ~spl3_15),
% 5.79/1.10    inference(forward_demodulation,[],[f432,f34])).
% 5.79/1.10  fof(f432,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))) | ~spl3_15),
% 5.79/1.10    inference(forward_demodulation,[],[f358,f34])).
% 5.79/1.10  fof(f358,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))) | ~spl3_15),
% 5.79/1.10    inference(superposition,[],[f42,f186])).
% 5.79/1.10  fof(f431,plain,(
% 5.79/1.10    spl3_32 | ~spl3_12),
% 5.79/1.10    inference(avatar_split_clause,[],[f426,f157,f428])).
% 5.79/1.10  fof(f426,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))) | ~spl3_12),
% 5.79/1.10    inference(forward_demodulation,[],[f425,f34])).
% 5.79/1.10  fof(f425,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))) | ~spl3_12),
% 5.79/1.10    inference(forward_demodulation,[],[f357,f34])).
% 5.79/1.10  fof(f357,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) | ~spl3_12),
% 5.79/1.10    inference(superposition,[],[f42,f159])).
% 5.79/1.10  fof(f424,plain,(
% 5.79/1.10    spl3_31 | ~spl3_9),
% 5.79/1.10    inference(avatar_split_clause,[],[f419,f130,f421])).
% 5.79/1.10  fof(f421,plain,(
% 5.79/1.10    spl3_31 <=> k5_xboole_0(sK1,sK2) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 5.79/1.10  fof(f419,plain,(
% 5.79/1.10    k5_xboole_0(sK1,sK2) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) | ~spl3_9),
% 5.79/1.10    inference(forward_demodulation,[],[f356,f34])).
% 5.79/1.10  fof(f356,plain,(
% 5.79/1.10    k5_xboole_0(sK1,sK2) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) | ~spl3_9),
% 5.79/1.10    inference(superposition,[],[f42,f132])).
% 5.79/1.10  fof(f418,plain,(
% 5.79/1.10    spl3_30 | ~spl3_5),
% 5.79/1.10    inference(avatar_split_clause,[],[f355,f96,f415])).
% 5.79/1.10  fof(f355,plain,(
% 5.79/1.10    sK2 = k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_5),
% 5.79/1.10    inference(superposition,[],[f42,f98])).
% 5.79/1.10  fof(f412,plain,(
% 5.79/1.10    spl3_29 | ~spl3_20),
% 5.79/1.10    inference(avatar_split_clause,[],[f407,f225,f409])).
% 5.79/1.10  fof(f225,plain,(
% 5.79/1.10    spl3_20 <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),sK1)),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 5.79/1.10  fof(f407,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))))) | ~spl3_20),
% 5.79/1.10    inference(forward_demodulation,[],[f406,f34])).
% 5.79/1.10  fof(f406,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))))) | ~spl3_20),
% 5.79/1.10    inference(forward_demodulation,[],[f405,f34])).
% 5.79/1.10  fof(f405,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))) | ~spl3_20),
% 5.79/1.10    inference(forward_demodulation,[],[f404,f34])).
% 5.79/1.10  fof(f404,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))) | ~spl3_20),
% 5.79/1.10    inference(forward_demodulation,[],[f403,f34])).
% 5.79/1.10  fof(f403,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))) | ~spl3_20),
% 5.79/1.10    inference(forward_demodulation,[],[f353,f34])).
% 5.79/1.10  fof(f353,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))) | ~spl3_20),
% 5.79/1.10    inference(superposition,[],[f42,f227])).
% 5.79/1.10  fof(f227,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),sK1) | ~spl3_20),
% 5.79/1.10    inference(avatar_component_clause,[],[f225])).
% 5.79/1.10  fof(f402,plain,(
% 5.79/1.10    spl3_28 | ~spl3_17),
% 5.79/1.10    inference(avatar_split_clause,[],[f397,f198,f399])).
% 5.79/1.10  fof(f198,plain,(
% 5.79/1.10    spl3_17 <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),sK1)),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 5.79/1.10  fof(f397,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))))) | ~spl3_17),
% 5.79/1.10    inference(forward_demodulation,[],[f396,f34])).
% 5.79/1.10  fof(f396,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))))) | ~spl3_17),
% 5.79/1.10    inference(forward_demodulation,[],[f395,f34])).
% 5.79/1.10  fof(f395,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))) | ~spl3_17),
% 5.79/1.10    inference(forward_demodulation,[],[f394,f34])).
% 5.79/1.10  fof(f394,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))) | ~spl3_17),
% 5.79/1.10    inference(forward_demodulation,[],[f352,f34])).
% 5.79/1.10  fof(f352,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))) | ~spl3_17),
% 5.79/1.10    inference(superposition,[],[f42,f200])).
% 5.79/1.10  fof(f200,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),sK1) | ~spl3_17),
% 5.79/1.10    inference(avatar_component_clause,[],[f198])).
% 5.79/1.10  fof(f393,plain,(
% 5.79/1.10    spl3_27 | ~spl3_14),
% 5.79/1.10    inference(avatar_split_clause,[],[f388,f171,f390])).
% 5.79/1.10  fof(f171,plain,(
% 5.79/1.10    spl3_14 <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),sK1)),
% 5.79/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 5.79/1.10  fof(f388,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))))) | ~spl3_14),
% 5.79/1.10    inference(forward_demodulation,[],[f387,f34])).
% 5.79/1.10  fof(f387,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))) | ~spl3_14),
% 5.79/1.10    inference(forward_demodulation,[],[f386,f34])).
% 5.79/1.10  fof(f386,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))) | ~spl3_14),
% 5.79/1.10    inference(forward_demodulation,[],[f351,f34])).
% 5.79/1.10  fof(f351,plain,(
% 5.79/1.10    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))) | ~spl3_14),
% 5.79/1.10    inference(superposition,[],[f42,f173])).
% 5.79/1.10  fof(f173,plain,(
% 5.79/1.10    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),sK1) | ~spl3_14),
% 5.79/1.10    inference(avatar_component_clause,[],[f171])).
% 5.79/1.10  fof(f385,plain,(
% 5.79/1.10    spl3_26 | ~spl3_11),
% 5.79/1.10    inference(avatar_split_clause,[],[f380,f144,f382])).
% 5.79/1.10  fof(f382,plain,(
% 5.79/1.10    spl3_26 <=> sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))))),
% 5.79/1.11    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 5.79/1.11  fof(f144,plain,(
% 5.79/1.11    spl3_11 <=> k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),sK1)),
% 5.79/1.11    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 5.79/1.11  fof(f380,plain,(
% 5.79/1.11    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))) | ~spl3_11),
% 5.79/1.11    inference(forward_demodulation,[],[f379,f34])).
% 5.79/1.11  fof(f379,plain,(
% 5.79/1.11    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))) | ~spl3_11),
% 5.79/1.11    inference(forward_demodulation,[],[f350,f34])).
% 5.79/1.11  fof(f350,plain,(
% 5.79/1.11    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) | ~spl3_11),
% 5.79/1.11    inference(superposition,[],[f42,f146])).
% 5.79/1.11  fof(f146,plain,(
% 5.79/1.11    k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),sK1) | ~spl3_11),
% 5.79/1.11    inference(avatar_component_clause,[],[f144])).
% 5.79/1.11  fof(f378,plain,(
% 5.79/1.11    spl3_25 | ~spl3_8),
% 5.79/1.11    inference(avatar_split_clause,[],[f373,f119,f375])).
% 5.79/1.11  fof(f119,plain,(
% 5.79/1.11    spl3_8 <=> k5_xboole_0(sK1,sK2) = k3_xboole_0(k5_xboole_0(sK1,sK2),sK1)),
% 5.79/1.11    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 5.79/1.11  fof(f373,plain,(
% 5.79/1.11    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))) | ~spl3_8),
% 5.79/1.11    inference(forward_demodulation,[],[f349,f34])).
% 5.79/1.11  fof(f349,plain,(
% 5.79/1.11    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)))) | ~spl3_8),
% 5.79/1.11    inference(superposition,[],[f42,f121])).
% 5.79/1.11  fof(f121,plain,(
% 5.79/1.11    k5_xboole_0(sK1,sK2) = k3_xboole_0(k5_xboole_0(sK1,sK2),sK1) | ~spl3_8),
% 5.79/1.11    inference(avatar_component_clause,[],[f119])).
% 5.79/1.11  fof(f299,plain,(
% 5.79/1.11    ~spl3_24 | spl3_7),
% 5.79/1.11    inference(avatar_split_clause,[],[f281,f111,f296])).
% 5.79/1.11  fof(f281,plain,(
% 5.79/1.11    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))))) | spl3_7),
% 5.79/1.11    inference(superposition,[],[f113,f34])).
% 5.79/1.11  fof(f271,plain,(
% 5.79/1.11    spl3_23 | ~spl3_22),
% 5.79/1.11    inference(avatar_split_clause,[],[f266,f260,f268])).
% 5.79/1.11  fof(f268,plain,(
% 5.79/1.11    spl3_23 <=> k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))),sK1)),
% 5.79/1.11    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 5.79/1.11  fof(f260,plain,(
% 5.79/1.11    spl3_22 <=> r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))),sK1)),
% 5.79/1.11    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 5.79/1.11  fof(f266,plain,(
% 5.79/1.11    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))),sK1) | ~spl3_22),
% 5.79/1.11    inference(resolution,[],[f262,f33])).
% 5.79/1.11  fof(f262,plain,(
% 5.79/1.11    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))),sK1) | ~spl3_22),
% 5.79/1.11    inference(avatar_component_clause,[],[f260])).
% 5.79/1.11  fof(f265,plain,(
% 5.79/1.11    spl3_21 | ~spl3_20),
% 5.79/1.11    inference(avatar_split_clause,[],[f252,f225,f254])).
% 5.79/1.11  fof(f252,plain,(
% 5.79/1.11    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))) | ~spl3_20),
% 5.79/1.11    inference(superposition,[],[f28,f227])).
% 5.79/1.11  fof(f264,plain,(
% 5.79/1.11    spl3_21 | ~spl3_20),
% 5.79/1.11    inference(avatar_split_clause,[],[f251,f225,f254])).
% 5.79/1.11  fof(f251,plain,(
% 5.79/1.11    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))) | ~spl3_20),
% 5.79/1.11    inference(superposition,[],[f28,f227])).
% 5.79/1.11  fof(f263,plain,(
% 5.79/1.11    spl3_22 | ~spl3_20),
% 5.79/1.11    inference(avatar_split_clause,[],[f249,f225,f260])).
% 5.79/1.11  fof(f249,plain,(
% 5.79/1.11    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))),sK1) | ~spl3_20),
% 5.79/1.11    inference(superposition,[],[f66,f227])).
% 5.79/1.11  fof(f258,plain,(
% 5.79/1.11    spl3_21 | ~spl3_20),
% 5.79/1.11    inference(avatar_split_clause,[],[f248,f225,f254])).
% 5.79/1.11  fof(f248,plain,(
% 5.79/1.11    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))) | ~spl3_20),
% 5.79/1.11    inference(superposition,[],[f227,f28])).
% 5.79/1.11  fof(f257,plain,(
% 5.79/1.11    spl3_21 | ~spl3_20),
% 5.79/1.11    inference(avatar_split_clause,[],[f247,f225,f254])).
% 5.79/1.11  fof(f247,plain,(
% 5.79/1.11    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))) | ~spl3_20),
% 5.79/1.11    inference(superposition,[],[f227,f28])).
% 5.79/1.11  fof(f228,plain,(
% 5.79/1.11    spl3_20 | ~spl3_19),
% 5.79/1.11    inference(avatar_split_clause,[],[f223,f217,f225])).
% 5.79/1.11  fof(f217,plain,(
% 5.79/1.11    spl3_19 <=> r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),sK1)),
% 5.79/1.11    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 5.79/1.11  fof(f223,plain,(
% 5.79/1.11    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),sK1) | ~spl3_19),
% 5.79/1.11    inference(resolution,[],[f219,f33])).
% 5.79/1.11  fof(f219,plain,(
% 5.79/1.11    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),sK1) | ~spl3_19),
% 5.79/1.11    inference(avatar_component_clause,[],[f217])).
% 5.79/1.11  fof(f222,plain,(
% 5.79/1.11    spl3_18 | ~spl3_17),
% 5.79/1.11    inference(avatar_split_clause,[],[f209,f198,f211])).
% 5.79/1.11  fof(f209,plain,(
% 5.79/1.11    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) | ~spl3_17),
% 5.79/1.11    inference(superposition,[],[f28,f200])).
% 5.79/1.11  fof(f221,plain,(
% 5.79/1.11    spl3_18 | ~spl3_17),
% 5.79/1.11    inference(avatar_split_clause,[],[f208,f198,f211])).
% 5.79/1.11  fof(f208,plain,(
% 5.79/1.11    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) | ~spl3_17),
% 5.79/1.11    inference(superposition,[],[f28,f200])).
% 5.79/1.11  fof(f220,plain,(
% 5.79/1.11    spl3_19 | ~spl3_17),
% 5.79/1.11    inference(avatar_split_clause,[],[f206,f198,f217])).
% 5.79/1.11  fof(f206,plain,(
% 5.79/1.11    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))),sK1) | ~spl3_17),
% 5.79/1.11    inference(superposition,[],[f66,f200])).
% 5.79/1.11  fof(f215,plain,(
% 5.79/1.11    spl3_18 | ~spl3_17),
% 5.79/1.11    inference(avatar_split_clause,[],[f205,f198,f211])).
% 5.79/1.11  fof(f205,plain,(
% 5.79/1.11    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) | ~spl3_17),
% 5.79/1.11    inference(superposition,[],[f200,f28])).
% 5.79/1.11  fof(f214,plain,(
% 5.79/1.11    spl3_18 | ~spl3_17),
% 5.79/1.11    inference(avatar_split_clause,[],[f204,f198,f211])).
% 5.79/1.11  fof(f204,plain,(
% 5.79/1.11    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) | ~spl3_17),
% 5.79/1.11    inference(superposition,[],[f200,f28])).
% 5.79/1.11  fof(f201,plain,(
% 5.79/1.11    spl3_17 | ~spl3_16),
% 5.79/1.11    inference(avatar_split_clause,[],[f196,f190,f198])).
% 5.79/1.11  fof(f190,plain,(
% 5.79/1.11    spl3_16 <=> r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),sK1)),
% 5.79/1.11    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 5.79/1.11  fof(f196,plain,(
% 5.79/1.11    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),sK1) | ~spl3_16),
% 5.79/1.11    inference(resolution,[],[f192,f33])).
% 5.79/1.11  fof(f192,plain,(
% 5.79/1.11    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),sK1) | ~spl3_16),
% 5.79/1.11    inference(avatar_component_clause,[],[f190])).
% 5.79/1.11  fof(f195,plain,(
% 5.79/1.11    spl3_15 | ~spl3_14),
% 5.79/1.11    inference(avatar_split_clause,[],[f182,f171,f184])).
% 5.79/1.11  fof(f182,plain,(
% 5.79/1.11    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) | ~spl3_14),
% 5.79/1.11    inference(superposition,[],[f28,f173])).
% 5.79/1.11  fof(f194,plain,(
% 5.79/1.11    spl3_15 | ~spl3_14),
% 5.79/1.11    inference(avatar_split_clause,[],[f181,f171,f184])).
% 5.79/1.11  fof(f181,plain,(
% 5.79/1.11    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) | ~spl3_14),
% 5.79/1.11    inference(superposition,[],[f28,f173])).
% 5.79/1.11  fof(f193,plain,(
% 5.79/1.11    spl3_16 | ~spl3_14),
% 5.79/1.11    inference(avatar_split_clause,[],[f179,f171,f190])).
% 5.79/1.11  fof(f179,plain,(
% 5.79/1.11    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))),sK1) | ~spl3_14),
% 5.79/1.11    inference(superposition,[],[f66,f173])).
% 5.79/1.11  fof(f188,plain,(
% 5.79/1.11    spl3_15 | ~spl3_14),
% 5.79/1.11    inference(avatar_split_clause,[],[f178,f171,f184])).
% 5.79/1.11  fof(f178,plain,(
% 5.79/1.11    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) | ~spl3_14),
% 5.79/1.11    inference(superposition,[],[f173,f28])).
% 5.79/1.11  fof(f187,plain,(
% 5.79/1.11    spl3_15 | ~spl3_14),
% 5.79/1.11    inference(avatar_split_clause,[],[f177,f171,f184])).
% 5.79/1.11  fof(f177,plain,(
% 5.79/1.11    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) | ~spl3_14),
% 5.79/1.11    inference(superposition,[],[f173,f28])).
% 5.79/1.11  fof(f174,plain,(
% 5.79/1.11    spl3_14 | ~spl3_13),
% 5.79/1.11    inference(avatar_split_clause,[],[f169,f163,f171])).
% 5.79/1.11  fof(f163,plain,(
% 5.79/1.11    spl3_13 <=> r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),sK1)),
% 5.79/1.11    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 5.79/1.11  fof(f169,plain,(
% 5.79/1.11    k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),sK1) | ~spl3_13),
% 5.79/1.11    inference(resolution,[],[f165,f33])).
% 5.79/1.11  fof(f165,plain,(
% 5.79/1.11    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),sK1) | ~spl3_13),
% 5.79/1.11    inference(avatar_component_clause,[],[f163])).
% 5.79/1.11  fof(f168,plain,(
% 5.79/1.11    spl3_12 | ~spl3_11),
% 5.79/1.11    inference(avatar_split_clause,[],[f155,f144,f157])).
% 5.79/1.11  fof(f155,plain,(
% 5.79/1.11    k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) | ~spl3_11),
% 5.79/1.11    inference(superposition,[],[f28,f146])).
% 5.79/1.11  fof(f167,plain,(
% 5.79/1.11    spl3_12 | ~spl3_11),
% 5.79/1.11    inference(avatar_split_clause,[],[f154,f144,f157])).
% 5.79/1.11  fof(f154,plain,(
% 5.79/1.11    k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) | ~spl3_11),
% 5.79/1.11    inference(superposition,[],[f28,f146])).
% 5.79/1.11  fof(f166,plain,(
% 5.79/1.11    spl3_13 | ~spl3_11),
% 5.79/1.11    inference(avatar_split_clause,[],[f152,f144,f163])).
% 5.79/1.11  fof(f152,plain,(
% 5.79/1.11    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),sK1) | ~spl3_11),
% 5.79/1.11    inference(superposition,[],[f66,f146])).
% 5.79/1.11  fof(f161,plain,(
% 5.79/1.11    spl3_12 | ~spl3_11),
% 5.79/1.11    inference(avatar_split_clause,[],[f151,f144,f157])).
% 5.79/1.11  fof(f151,plain,(
% 5.79/1.11    k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) | ~spl3_11),
% 5.79/1.11    inference(superposition,[],[f146,f28])).
% 5.79/1.11  fof(f160,plain,(
% 5.79/1.11    spl3_12 | ~spl3_11),
% 5.79/1.11    inference(avatar_split_clause,[],[f150,f144,f157])).
% 5.79/1.11  fof(f150,plain,(
% 5.79/1.11    k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))) | ~spl3_11),
% 5.79/1.11    inference(superposition,[],[f146,f28])).
% 5.79/1.11  fof(f147,plain,(
% 5.79/1.11    spl3_11 | ~spl3_10),
% 5.79/1.11    inference(avatar_split_clause,[],[f142,f136,f144])).
% 5.79/1.11  fof(f136,plain,(
% 5.79/1.11    spl3_10 <=> r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),sK1)),
% 5.79/1.11    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 5.79/1.11  fof(f142,plain,(
% 5.79/1.11    k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),sK1) | ~spl3_10),
% 5.79/1.11    inference(resolution,[],[f138,f33])).
% 5.79/1.11  fof(f138,plain,(
% 5.79/1.11    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),sK1) | ~spl3_10),
% 5.79/1.11    inference(avatar_component_clause,[],[f136])).
% 5.79/1.11  fof(f141,plain,(
% 5.79/1.11    spl3_9 | ~spl3_8),
% 5.79/1.11    inference(avatar_split_clause,[],[f128,f119,f130])).
% 5.79/1.11  fof(f128,plain,(
% 5.79/1.11    k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | ~spl3_8),
% 5.79/1.11    inference(superposition,[],[f28,f121])).
% 5.79/1.11  fof(f140,plain,(
% 5.79/1.11    spl3_9 | ~spl3_8),
% 5.79/1.11    inference(avatar_split_clause,[],[f127,f119,f130])).
% 5.79/1.11  fof(f127,plain,(
% 5.79/1.11    k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | ~spl3_8),
% 5.79/1.11    inference(superposition,[],[f28,f121])).
% 5.79/1.11  fof(f139,plain,(
% 5.79/1.11    spl3_10 | ~spl3_8),
% 5.79/1.11    inference(avatar_split_clause,[],[f125,f119,f136])).
% 5.79/1.11  fof(f125,plain,(
% 5.79/1.11    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),sK1) | ~spl3_8),
% 5.79/1.11    inference(superposition,[],[f66,f121])).
% 5.79/1.11  fof(f134,plain,(
% 5.79/1.11    spl3_9 | ~spl3_8),
% 5.79/1.11    inference(avatar_split_clause,[],[f124,f119,f130])).
% 5.79/1.11  fof(f124,plain,(
% 5.79/1.11    k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | ~spl3_8),
% 5.79/1.11    inference(superposition,[],[f121,f28])).
% 5.79/1.11  fof(f133,plain,(
% 5.79/1.11    spl3_9 | ~spl3_8),
% 5.79/1.11    inference(avatar_split_clause,[],[f123,f119,f130])).
% 5.79/1.11  fof(f123,plain,(
% 5.79/1.11    k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | ~spl3_8),
% 5.79/1.11    inference(superposition,[],[f121,f28])).
% 5.79/1.11  fof(f122,plain,(
% 5.79/1.11    spl3_8 | ~spl3_6),
% 5.79/1.11    inference(avatar_split_clause,[],[f117,f102,f119])).
% 5.79/1.11  fof(f102,plain,(
% 5.79/1.11    spl3_6 <=> r1_tarski(k5_xboole_0(sK1,sK2),sK1)),
% 5.79/1.11    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 5.79/1.11  fof(f117,plain,(
% 5.79/1.11    k5_xboole_0(sK1,sK2) = k3_xboole_0(k5_xboole_0(sK1,sK2),sK1) | ~spl3_6),
% 5.79/1.11    inference(resolution,[],[f104,f33])).
% 5.79/1.11  fof(f104,plain,(
% 5.79/1.11    r1_tarski(k5_xboole_0(sK1,sK2),sK1) | ~spl3_6),
% 5.79/1.11    inference(avatar_component_clause,[],[f102])).
% 5.79/1.11  fof(f114,plain,(
% 5.79/1.11    ~spl3_7 | spl3_3 | ~spl3_5),
% 5.79/1.11    inference(avatar_split_clause,[],[f109,f96,f58,f111])).
% 5.79/1.11  fof(f58,plain,(
% 5.79/1.11    spl3_3 <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))))),
% 5.79/1.11    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 5.79/1.11  fof(f109,plain,(
% 5.79/1.11    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))) | (spl3_3 | ~spl3_5)),
% 5.79/1.11    inference(forward_demodulation,[],[f108,f28])).
% 5.79/1.11  fof(f108,plain,(
% 5.79/1.11    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2)))))) | (spl3_3 | ~spl3_5)),
% 5.79/1.11    inference(backward_demodulation,[],[f60,f98])).
% 5.79/1.11  fof(f60,plain,(
% 5.79/1.11    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))))) | spl3_3),
% 5.79/1.11    inference(avatar_component_clause,[],[f58])).
% 5.79/1.11  fof(f107,plain,(
% 5.79/1.11    spl3_5 | ~spl3_4),
% 5.79/1.11    inference(avatar_split_clause,[],[f94,f85,f96])).
% 5.79/1.11  fof(f94,plain,(
% 5.79/1.11    sK2 = k3_xboole_0(sK1,sK2) | ~spl3_4),
% 5.79/1.11    inference(superposition,[],[f28,f87])).
% 5.79/1.11  fof(f106,plain,(
% 5.79/1.11    spl3_5 | ~spl3_4),
% 5.79/1.11    inference(avatar_split_clause,[],[f93,f85,f96])).
% 5.79/1.11  fof(f93,plain,(
% 5.79/1.11    sK2 = k3_xboole_0(sK1,sK2) | ~spl3_4),
% 5.79/1.11    inference(superposition,[],[f28,f87])).
% 5.79/1.11  fof(f105,plain,(
% 5.79/1.11    spl3_6 | ~spl3_4),
% 5.79/1.11    inference(avatar_split_clause,[],[f91,f85,f102])).
% 5.79/1.11  fof(f91,plain,(
% 5.79/1.11    r1_tarski(k5_xboole_0(sK1,sK2),sK1) | ~spl3_4),
% 5.79/1.11    inference(superposition,[],[f66,f87])).
% 5.79/1.11  fof(f100,plain,(
% 5.79/1.11    spl3_5 | ~spl3_4),
% 5.79/1.11    inference(avatar_split_clause,[],[f90,f85,f96])).
% 5.79/1.11  fof(f90,plain,(
% 5.79/1.11    sK2 = k3_xboole_0(sK1,sK2) | ~spl3_4),
% 5.79/1.11    inference(superposition,[],[f87,f28])).
% 5.79/1.11  fof(f99,plain,(
% 5.79/1.11    spl3_5 | ~spl3_4),
% 5.79/1.11    inference(avatar_split_clause,[],[f89,f85,f96])).
% 5.79/1.11  fof(f89,plain,(
% 5.79/1.11    sK2 = k3_xboole_0(sK1,sK2) | ~spl3_4),
% 5.79/1.11    inference(superposition,[],[f87,f28])).
% 5.79/1.11  fof(f88,plain,(
% 5.79/1.11    spl3_4 | ~spl3_2),
% 5.79/1.11    inference(avatar_split_clause,[],[f79,f50,f85])).
% 5.79/1.11  fof(f50,plain,(
% 5.79/1.11    spl3_2 <=> r1_tarski(sK2,sK1)),
% 5.79/1.11    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 5.79/1.11  fof(f79,plain,(
% 5.79/1.11    sK2 = k3_xboole_0(sK2,sK1) | ~spl3_2),
% 5.79/1.11    inference(resolution,[],[f33,f52])).
% 5.79/1.11  fof(f52,plain,(
% 5.79/1.11    r1_tarski(sK2,sK1) | ~spl3_2),
% 5.79/1.11    inference(avatar_component_clause,[],[f50])).
% 5.79/1.11  fof(f61,plain,(
% 5.79/1.11    ~spl3_3 | spl3_1),
% 5.79/1.11    inference(avatar_split_clause,[],[f56,f45,f58])).
% 5.79/1.11  fof(f45,plain,(
% 5.79/1.11    spl3_1 <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))),
% 5.79/1.11    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 5.79/1.11  fof(f56,plain,(
% 5.79/1.11    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))))) | spl3_1),
% 5.79/1.11    inference(forward_demodulation,[],[f55,f28])).
% 5.79/1.11  fof(f55,plain,(
% 5.79/1.11    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))) | spl3_1),
% 5.79/1.11    inference(forward_demodulation,[],[f54,f34])).
% 5.79/1.11  fof(f54,plain,(
% 5.79/1.11    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))) | spl3_1),
% 5.79/1.11    inference(forward_demodulation,[],[f47,f43])).
% 5.79/1.11  fof(f47,plain,(
% 5.79/1.11    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))) | spl3_1),
% 5.79/1.11    inference(avatar_component_clause,[],[f45])).
% 5.79/1.11  fof(f53,plain,(
% 5.79/1.11    spl3_2),
% 5.79/1.11    inference(avatar_split_clause,[],[f21,f50])).
% 5.79/1.11  fof(f21,plain,(
% 5.79/1.11    r1_tarski(sK2,sK1)),
% 5.79/1.11    inference(cnf_transformation,[],[f20])).
% 5.79/1.11  fof(f20,plain,(
% 5.79/1.11    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1)),
% 5.79/1.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19])).
% 5.79/1.11  fof(f19,plain,(
% 5.79/1.11    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1)) => (k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1))),
% 5.79/1.11    introduced(choice_axiom,[])).
% 5.79/1.11  fof(f17,plain,(
% 5.79/1.11    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1))),
% 5.79/1.11    inference(ennf_transformation,[],[f15])).
% 5.79/1.11  fof(f15,negated_conjecture,(
% 5.79/1.11    ~! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 5.79/1.11    inference(negated_conjecture,[],[f14])).
% 5.79/1.11  fof(f14,conjecture,(
% 5.79/1.11    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 5.79/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).
% 5.79/1.11  fof(f48,plain,(
% 5.79/1.11    ~spl3_1),
% 5.79/1.11    inference(avatar_split_clause,[],[f38,f45])).
% 5.79/1.11  fof(f38,plain,(
% 5.79/1.11    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))),
% 5.79/1.11    inference(definition_unfolding,[],[f22,f32,f36,f32,f32])).
% 5.79/1.11  fof(f22,plain,(
% 5.79/1.11    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 5.79/1.11    inference(cnf_transformation,[],[f20])).
% 5.79/1.11  % SZS output end Proof for theBenchmark
% 5.79/1.11  % (23212)------------------------------
% 5.79/1.11  % (23212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.79/1.11  % (23212)Termination reason: Refutation
% 5.79/1.11  
% 5.79/1.11  % (23212)Memory used [KB]: 15095
% 5.79/1.11  % (23212)Time elapsed: 0.682 s
% 5.79/1.11  % (23212)------------------------------
% 5.79/1.11  % (23212)------------------------------
% 5.79/1.11  % (23201)Success in time 0.753 s
%------------------------------------------------------------------------------
