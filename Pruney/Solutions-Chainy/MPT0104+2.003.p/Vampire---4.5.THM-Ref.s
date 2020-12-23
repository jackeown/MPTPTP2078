%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:02 EST 2020

% Result     : Theorem 14.92s
% Output     : Refutation 14.92s
% Verified   : 
% Statistics : Number of formulae       : 1183 (20551 expanded)
%              Number of leaves         :  220 (6474 expanded)
%              Depth                    :   25
%              Number of atoms          : 2446 (29395 expanded)
%              Number of equality atoms :  564 (15063 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f51033,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f69,f93,f122,f168,f173,f188,f193,f198,f203,f208,f213,f351,f356,f369,f374,f379,f384,f389,f394,f672,f702,f709,f714,f965,f970,f999,f1004,f1041,f1046,f1057,f1065,f3801,f3909,f4234,f4243,f4415,f4420,f4495,f4500,f4696,f4701,f4783,f4788,f5138,f5143,f9075,f9083,f9090,f9095,f9178,f9252,f9265,f9367,f9379,f9964,f9972,f9979,f10057,f10070,f10178,f10190,f11687,f11692,f11807,f11815,f11850,f11858,f11865,f11870,f12548,f12592,f12835,f12919,f13360,f13366,f13483,f13489,f13666,f13671,f14839,f14845,f15053,f15059,f15789,f15794,f19238,f19243,f19254,f19259,f19268,f19273,f19284,f19289,f19390,f19525,f19530,f19544,f25699,f25705,f25712,f25717,f25723,f25729,f25734,f25743,f25749,f25756,f25761,f25767,f25776,f26365,f26372,f26377,f26383,f43207,f43216,f43225,f43230,f43239,f43248,f43787,f43792,f43797,f43802,f45000,f45001,f45005,f45011,f45015,f45068,f45086,f45585,f45586,f45590,f45598,f45606,f45650,f45755,f45760,f45806,f45811,f45813,f45815,f45817,f45819,f45821,f45823,f45825,f45828,f45830,f45834,f45842,f45851,f46268,f46272,f46342,f46349,f46365,f46371,f46376,f46380,f46388,f46396,f46816,f47040,f47045,f47056,f47061,f47070,f47229,f47249,f47257,f47588,f47789,f47972,f48201,f48309,f48314,f48361,f48588,f48592,f48596,f48600,f48604,f48608,f48612,f48616,f48620,f48622,f48624,f48626,f48634,f48864,f48868,f48872,f48876,f48877,f48878,f48882,f48886,f48890,f48894,f48898,f48899,f48900,f48901,f48905,f48906,f48907,f48908,f48975,f49319,f49325,f49329,f49333,f49337,f49341,f49342,f49347,f49351,f49356,f49360,f49466,f49470,f49474,f49478,f49482,f49486,f50365,f50373,f50458,f50466,f51031])).

fof(f51031,plain,
    ( ~ spl3_1
    | spl3_3
    | ~ spl3_51 ),
    inference(avatar_contradiction_clause,[],[f51030])).

fof(f51030,plain,
    ( $false
    | ~ spl3_1
    | spl3_3
    | ~ spl3_51 ),
    inference(subsumption_resolution,[],[f51029,f68])).

fof(f68,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_3
  <=> r1_tarski(k5_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f51029,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK1),sK2)
    | ~ spl3_1
    | ~ spl3_51 ),
    inference(forward_demodulation,[],[f51019,f9625])).

fof(f9625,plain,(
    ! [X17,X18] : k5_xboole_0(X17,X18) = k5_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(X18,X17)) ),
    inference(forward_demodulation,[],[f9624,f47])).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f9624,plain,(
    ! [X17,X18] : k5_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(X18,X17)) = k2_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(X18,X17)) ),
    inference(forward_demodulation,[],[f9578,f113])).

fof(f113,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(resolution,[],[f48,f42])).

fof(f42,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f9578,plain,(
    ! [X17,X18] : k5_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(X18,X17)) = k2_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(X17,X18))) ),
    inference(superposition,[],[f47,f113])).

fof(f51019,plain,
    ( r1_tarski(k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2)
    | ~ spl3_1
    | ~ spl3_51 ),
    inference(superposition,[],[f50320,f9094])).

fof(f9094,plain,
    ( sK2 = k2_xboole_0(k4_xboole_0(sK1,sK0),sK2)
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f9092])).

fof(f9092,plain,
    ( spl3_51
  <=> sK2 = k2_xboole_0(k4_xboole_0(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f50320,plain,
    ( ! [X0] : r1_tarski(k5_xboole_0(k4_xboole_0(sK0,sK1),X0),k2_xboole_0(X0,sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f50232,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f50232,plain,
    ( ! [X2] : r1_tarski(k4_xboole_0(k5_xboole_0(k4_xboole_0(sK0,sK1),X2),X2),sK2)
    | ~ spl3_1 ),
    inference(superposition,[],[f49995,f3066])).

fof(f3066,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f3042,f3042])).

fof(f3042,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f3034,f41])).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f3034,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f3008,f78])).

fof(f78,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f41,f37])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f3008,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f52,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f52,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f49995,plain,
    ( ! [X226] : r1_tarski(k4_xboole_0(X226,k5_xboole_0(X226,k4_xboole_0(sK0,sK1))),sK2)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f49615,f1111])).

fof(f1111,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f1110,f37])).

fof(f1110,plain,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1084,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f1084,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f46,f37])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f49615,plain,
    ( ! [X226] : r1_tarski(k4_xboole_0(X226,k5_xboole_0(X226,k4_xboole_0(sK0,sK1))),k2_xboole_0(sK2,k1_xboole_0))
    | ~ spl3_1 ),
    inference(superposition,[],[f918,f3054])).

fof(f3054,plain,(
    ! [X14,X13] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X13,k5_xboole_0(X13,X14)),X14) ),
    inference(superposition,[],[f143,f3034])).

fof(f143,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(resolution,[],[f50,f43])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f918,plain,
    ( ! [X7] : r1_tarski(X7,k2_xboole_0(sK2,k4_xboole_0(X7,k4_xboole_0(sK0,sK1))))
    | ~ spl3_1 ),
    inference(resolution,[],[f54,f513])).

fof(f513,plain,
    ( ! [X10] : r1_tarski(k4_xboole_0(X10,sK2),k4_xboole_0(X10,k4_xboole_0(sK0,sK1)))
    | ~ spl3_1 ),
    inference(resolution,[],[f53,f58])).

fof(f58,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_1
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f50466,plain,
    ( spl3_200
    | ~ spl3_199 ),
    inference(avatar_split_clause,[],[f50459,f50455,f50463])).

fof(f50463,plain,
    ( spl3_200
  <=> r1_tarski(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_200])])).

fof(f50455,plain,
    ( spl3_199
  <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_199])])).

fof(f50459,plain,
    ( r1_tarski(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))
    | ~ spl3_199 ),
    inference(resolution,[],[f50457,f54])).

fof(f50457,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),sK0),sK2)
    | ~ spl3_199 ),
    inference(avatar_component_clause,[],[f50455])).

fof(f50458,plain,
    ( spl3_199
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f50440,f61,f50455])).

fof(f61,plain,
    ( spl3_2
  <=> r1_tarski(k4_xboole_0(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f50440,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),sK0),sK2)
    | ~ spl3_2 ),
    inference(superposition,[],[f50253,f3037])).

fof(f3037,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f3015,f1609])).

fof(f1609,plain,(
    ! [X14,X15] : k5_xboole_0(X15,k3_xboole_0(X14,X15)) = k4_xboole_0(X15,X14) ),
    inference(forward_demodulation,[],[f1608,f1111])).

fof(f1608,plain,(
    ! [X14,X15] : k5_xboole_0(X15,k3_xboole_0(X14,X15)) = k2_xboole_0(k4_xboole_0(X15,X14),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1526,f395])).

fof(f395,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f45,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f1526,plain,(
    ! [X14,X15] : k5_xboole_0(X15,k3_xboole_0(X14,X15)) = k2_xboole_0(k4_xboole_0(X15,k3_xboole_0(X14,X15)),k1_xboole_0) ),
    inference(superposition,[],[f47,f560])).

fof(f560,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X3,X4),X4) ),
    inference(resolution,[],[f550,f50])).

fof(f550,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f538,f40])).

fof(f538,plain,(
    ! [X4,X5] : r1_tarski(k3_xboole_0(X4,X5),X4) ),
    inference(superposition,[],[f524,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f524,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f523,f38])).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f523,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f509,f284])).

fof(f284,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f245,f48])).

fof(f245,plain,(
    ! [X3] : r1_xboole_0(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f241,f114])).

fof(f114,plain,(
    ! [X2] : k4_xboole_0(X2,k4_xboole_0(k1_xboole_0,X2)) = X2 ),
    inference(resolution,[],[f48,f86])).

fof(f86,plain,(
    ! [X0] : r1_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f42,f38])).

fof(f241,plain,(
    ! [X3] : r1_xboole_0(k1_xboole_0,k4_xboole_0(X3,k4_xboole_0(k1_xboole_0,X3))) ),
    inference(superposition,[],[f42,f142])).

fof(f142,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0) ),
    inference(resolution,[],[f50,f100])).

fof(f100,plain,(
    ! [X6] : r1_tarski(k4_xboole_0(k1_xboole_0,X6),X6) ),
    inference(superposition,[],[f43,f78])).

fof(f509,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) ),
    inference(resolution,[],[f53,f100])).

fof(f3015,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f52,f46])).

fof(f50253,plain,
    ( ! [X3] : r1_tarski(k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(sK1,sK0)),X3),sK2)
    | ~ spl3_2 ),
    inference(superposition,[],[f49997,f3065])).

fof(f3065,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5 ),
    inference(superposition,[],[f3042,f3034])).

fof(f49997,plain,
    ( ! [X230] : r1_tarski(k4_xboole_0(X230,k5_xboole_0(X230,k4_xboole_0(sK1,sK0))),sK2)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f49619,f1111])).

fof(f49619,plain,
    ( ! [X230] : r1_tarski(k4_xboole_0(X230,k5_xboole_0(X230,k4_xboole_0(sK1,sK0))),k2_xboole_0(sK2,k1_xboole_0))
    | ~ spl3_2 ),
    inference(superposition,[],[f919,f3054])).

fof(f919,plain,
    ( ! [X8] : r1_tarski(X8,k2_xboole_0(sK2,k4_xboole_0(X8,k4_xboole_0(sK1,sK0))))
    | ~ spl3_2 ),
    inference(resolution,[],[f54,f514])).

fof(f514,plain,
    ( ! [X11] : r1_tarski(k4_xboole_0(X11,sK2),k4_xboole_0(X11,k4_xboole_0(sK1,sK0)))
    | ~ spl3_2 ),
    inference(resolution,[],[f53,f63])).

fof(f63,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK0),sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f50373,plain,
    ( spl3_198
    | ~ spl3_197 ),
    inference(avatar_split_clause,[],[f50366,f50362,f50370])).

fof(f50370,plain,
    ( spl3_198
  <=> r1_tarski(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_198])])).

fof(f50362,plain,
    ( spl3_197
  <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_197])])).

fof(f50366,plain,
    ( r1_tarski(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2))
    | ~ spl3_197 ),
    inference(resolution,[],[f50364,f54])).

fof(f50364,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),sK1),sK2)
    | ~ spl3_197 ),
    inference(avatar_component_clause,[],[f50362])).

fof(f50365,plain,
    ( spl3_197
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f50358,f56,f50362])).

fof(f50358,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),sK1),sK2)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f50346,f11923])).

fof(f11923,plain,(
    ! [X4,X3] : k2_xboole_0(X3,X4) = k2_xboole_0(X4,X3) ),
    inference(superposition,[],[f1090,f1085])).

fof(f1085,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k5_xboole_0(k5_xboole_0(X3,X2),k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f46,f41])).

fof(f1090,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f46,f40])).

fof(f50346,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(sK1,sK0),sK1),sK2)
    | ~ spl3_1 ),
    inference(superposition,[],[f50233,f3037])).

fof(f50233,plain,
    ( ! [X3] : r1_tarski(k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(sK0,sK1)),X3),sK2)
    | ~ spl3_1 ),
    inference(superposition,[],[f49995,f3065])).

fof(f49486,plain,
    ( ~ spl3_129
    | spl3_196
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f43129,f10067,f49484,f43241])).

fof(f43241,plain,
    ( spl3_129
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_129])])).

fof(f49484,plain,
    ( spl3_196
  <=> ! [X70] : r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK2),X70),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_196])])).

fof(f10067,plain,
    ( spl3_61
  <=> sK1 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f43129,plain,
    ( ! [X70] :
        ( r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK2),X70),k1_xboole_0)
        | k1_xboole_0 != sK1 )
    | ~ spl3_61 ),
    inference(superposition,[],[f22558,f10790])).

fof(f10790,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK2),X3),sK1)
    | ~ spl3_61 ),
    inference(resolution,[],[f10742,f50])).

fof(f10742,plain,
    ( ! [X3] : r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK2),X3),sK1)
    | ~ spl3_61 ),
    inference(superposition,[],[f10713,f268])).

fof(f268,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f248,f45])).

fof(f248,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f44,f44])).

fof(f10713,plain,
    ( ! [X32] : r1_tarski(k3_xboole_0(k4_xboole_0(sK0,sK2),X32),sK1)
    | ~ spl3_61 ),
    inference(superposition,[],[f9016,f10069])).

fof(f10069,plain,
    ( sK1 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_61 ),
    inference(avatar_component_clause,[],[f10067])).

fof(f9016,plain,(
    ! [X24,X23,X22] : r1_tarski(k3_xboole_0(X22,X23),k2_xboole_0(X24,X22)) ),
    inference(superposition,[],[f1268,f8900])).

fof(f8900,plain,(
    ! [X2,X1] : k2_xboole_0(k3_xboole_0(X1,X2),X1) = X1 ),
    inference(forward_demodulation,[],[f8816,f7437])).

fof(f7437,plain,(
    ! [X8,X7] : k5_xboole_0(k3_xboole_0(X7,X8),k4_xboole_0(X7,X8)) = X7 ),
    inference(forward_demodulation,[],[f7436,f4330])).

fof(f4330,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k4_xboole_0(X8,X9)) = X8 ),
    inference(superposition,[],[f4322,f268])).

fof(f4322,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k3_xboole_0(X6,X7)) = X6 ),
    inference(forward_demodulation,[],[f4296,f3065])).

fof(f4296,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k3_xboole_0(X6,X7)) = k5_xboole_0(k5_xboole_0(X6,k3_xboole_0(X6,X7)),k3_xboole_0(X6,X7)) ),
    inference(superposition,[],[f46,f422])).

fof(f422,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f402,f44])).

fof(f402,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f44,f45])).

fof(f7436,plain,(
    ! [X8,X7] : k2_xboole_0(X7,k4_xboole_0(X7,X8)) = k5_xboole_0(k3_xboole_0(X7,X8),k4_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f7360,f268])).

fof(f7360,plain,(
    ! [X8,X7] : k2_xboole_0(X7,k4_xboole_0(X7,X8)) = k5_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X7,k4_xboole_0(X7,X8))) ),
    inference(superposition,[],[f46,f1559])).

fof(f1559,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k5_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f1558,f1111])).

fof(f1558,plain,(
    ! [X4,X5] : k5_xboole_0(X4,k4_xboole_0(X4,X5)) = k2_xboole_0(k3_xboole_0(X4,X5),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1498,f534])).

fof(f534,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),X3) ),
    inference(resolution,[],[f524,f50])).

fof(f1498,plain,(
    ! [X4,X5] : k5_xboole_0(X4,k4_xboole_0(X4,X5)) = k2_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X4,X5),X4)) ),
    inference(superposition,[],[f47,f44])).

fof(f8816,plain,(
    ! [X2,X1] : k5_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X2),X1) ),
    inference(superposition,[],[f3037,f45])).

fof(f1268,plain,(
    ! [X2,X0,X1] : r1_tarski(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(resolution,[],[f953,f54])).

fof(f953,plain,(
    ! [X21,X22,X20] : r1_tarski(k4_xboole_0(X20,X21),k2_xboole_0(X20,X22)) ),
    inference(subsumption_resolution,[],[f936,f294])).

fof(f294,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(superposition,[],[f100,f284])).

fof(f936,plain,(
    ! [X21,X22,X20] :
      ( ~ r1_tarski(k1_xboole_0,X22)
      | r1_tarski(k4_xboole_0(X20,X21),k2_xboole_0(X20,X22)) ) ),
    inference(superposition,[],[f54,f534])).

fof(f22558,plain,(
    ! [X8,X9] :
      ( r1_tarski(X9,k4_xboole_0(X9,X8))
      | k1_xboole_0 != X8 ) ),
    inference(forward_demodulation,[],[f22557,f38])).

fof(f22557,plain,(
    ! [X8,X9] :
      ( r1_tarski(k4_xboole_0(X9,k1_xboole_0),k4_xboole_0(X9,X8))
      | k1_xboole_0 != X8 ) ),
    inference(forward_demodulation,[],[f22397,f284])).

fof(f22397,plain,(
    ! [X8,X9] :
      ( k1_xboole_0 != X8
      | r1_tarski(k4_xboole_0(X9,k4_xboole_0(k1_xboole_0,X8)),k4_xboole_0(X9,X8)) ) ),
    inference(superposition,[],[f516,f114])).

fof(f516,plain,(
    ! [X14,X15,X16] :
      ( k1_xboole_0 != k4_xboole_0(X16,X15)
      | r1_tarski(k4_xboole_0(X14,X15),k4_xboole_0(X14,X16)) ) ),
    inference(resolution,[],[f53,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f49482,plain,
    ( ~ spl3_127
    | spl3_195
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f43127,f9262,f49480,f43232])).

fof(f43232,plain,
    ( spl3_127
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_127])])).

fof(f49480,plain,
    ( spl3_195
  <=> ! [X69] : r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK2),X69),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_195])])).

fof(f9262,plain,
    ( spl3_54
  <=> sK0 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f43127,plain,
    ( ! [X69] :
        ( r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK2),X69),k1_xboole_0)
        | k1_xboole_0 != sK0 )
    | ~ spl3_54 ),
    inference(superposition,[],[f22558,f10760])).

fof(f10760,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X3),sK0)
    | ~ spl3_54 ),
    inference(resolution,[],[f10727,f50])).

fof(f10727,plain,
    ( ! [X3] : r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK2),X3),sK0)
    | ~ spl3_54 ),
    inference(superposition,[],[f10712,f268])).

fof(f10712,plain,
    ( ! [X31] : r1_tarski(k3_xboole_0(k4_xboole_0(sK1,sK2),X31),sK0)
    | ~ spl3_54 ),
    inference(superposition,[],[f9016,f9264])).

fof(f9264,plain,
    ( sK0 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f9262])).

fof(f49478,plain,
    ( ~ spl3_124
    | spl3_194
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f43100,f9072,f49476,f43218])).

fof(f43218,plain,
    ( spl3_124
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_124])])).

fof(f49476,plain,
    ( spl3_194
  <=> ! [X48] : r1_tarski(k3_xboole_0(sK1,k4_xboole_0(X48,sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_194])])).

fof(f9072,plain,
    ( spl3_48
  <=> r1_tarski(k4_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f43100,plain,
    ( ! [X48] :
        ( r1_tarski(k3_xboole_0(sK1,k4_xboole_0(X48,sK0)),k1_xboole_0)
        | k1_xboole_0 != sK2 )
    | ~ spl3_48 ),
    inference(superposition,[],[f22558,f26335])).

fof(f26335,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,k4_xboole_0(X3,sK0)),sK2)
    | ~ spl3_48 ),
    inference(resolution,[],[f26012,f50])).

fof(f26012,plain,
    ( ! [X103] : r1_tarski(k3_xboole_0(sK1,k4_xboole_0(X103,sK0)),sK2)
    | ~ spl3_48 ),
    inference(forward_demodulation,[],[f26011,f40])).

fof(f26011,plain,
    ( ! [X103] : r1_tarski(k3_xboole_0(k4_xboole_0(X103,sK0),sK1),sK2)
    | ~ spl3_48 ),
    inference(forward_demodulation,[],[f25822,f1111])).

fof(f25822,plain,
    ( ! [X103] : r1_tarski(k3_xboole_0(k4_xboole_0(X103,sK0),sK1),k2_xboole_0(sK2,k1_xboole_0))
    | ~ spl3_48 ),
    inference(resolution,[],[f1982,f12622])).

fof(f12622,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k4_xboole_0(X0,sK0),k4_xboole_0(sK1,sK2)),k1_xboole_0)
    | ~ spl3_48 ),
    inference(superposition,[],[f11798,f40])).

fof(f11798,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,sK0)),k1_xboole_0)
    | ~ spl3_48 ),
    inference(forward_demodulation,[],[f11789,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f11789,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(k3_xboole_0(k4_xboole_0(sK1,sK2),X0),sK0),k1_xboole_0)
    | ~ spl3_48 ),
    inference(superposition,[],[f9077,f548])).

fof(f548,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X3,X4),X3) ),
    inference(resolution,[],[f538,f50])).

fof(f9077,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(X0,sK0),k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_48 ),
    inference(resolution,[],[f9074,f53])).

fof(f9074,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f9072])).

fof(f1982,plain,(
    ! [X30,X28,X31,X29] :
      ( ~ r1_tarski(k3_xboole_0(X28,k4_xboole_0(X29,X30)),X31)
      | r1_tarski(k3_xboole_0(X28,X29),k2_xboole_0(X30,X31)) ) ),
    inference(superposition,[],[f54,f51])).

fof(f49474,plain,
    ( ~ spl3_124
    | spl3_193
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f43096,f9961,f49472,f43218])).

fof(f49472,plain,
    ( spl3_193
  <=> ! [X44] : r1_tarski(k3_xboole_0(sK0,k4_xboole_0(X44,sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_193])])).

fof(f9961,plain,
    ( spl3_57
  <=> r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f43096,plain,
    ( ! [X44] :
        ( r1_tarski(k3_xboole_0(sK0,k4_xboole_0(X44,sK1)),k1_xboole_0)
        | k1_xboole_0 != sK2 )
    | ~ spl3_57 ),
    inference(superposition,[],[f22558,f26307])).

fof(f26307,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,k4_xboole_0(X3,sK1)),sK2)
    | ~ spl3_57 ),
    inference(resolution,[],[f26008,f50])).

fof(f26008,plain,
    ( ! [X101] : r1_tarski(k3_xboole_0(sK0,k4_xboole_0(X101,sK1)),sK2)
    | ~ spl3_57 ),
    inference(forward_demodulation,[],[f26007,f40])).

fof(f26007,plain,
    ( ! [X101] : r1_tarski(k3_xboole_0(k4_xboole_0(X101,sK1),sK0),sK2)
    | ~ spl3_57 ),
    inference(forward_demodulation,[],[f25820,f1111])).

fof(f25820,plain,
    ( ! [X101] : r1_tarski(k3_xboole_0(k4_xboole_0(X101,sK1),sK0),k2_xboole_0(sK2,k1_xboole_0))
    | ~ spl3_57 ),
    inference(resolution,[],[f1982,f12655])).

fof(f12655,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(sK0,sK2)),k1_xboole_0)
    | ~ spl3_57 ),
    inference(superposition,[],[f11841,f40])).

fof(f11841,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(X0,sK1)),k1_xboole_0)
    | ~ spl3_57 ),
    inference(forward_demodulation,[],[f11832,f51])).

fof(f11832,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK2),X0),sK1),k1_xboole_0)
    | ~ spl3_57 ),
    inference(superposition,[],[f9966,f548])).

fof(f9966,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(X0,sK1),k4_xboole_0(X0,k4_xboole_0(sK0,sK2)))
    | ~ spl3_57 ),
    inference(resolution,[],[f9963,f53])).

fof(f9963,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f9961])).

fof(f49470,plain,
    ( ~ spl3_129
    | spl3_192
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f43084,f10067,f49468,f43241])).

fof(f49468,plain,
    ( spl3_192
  <=> ! [X32] : r1_tarski(k3_xboole_0(X32,k4_xboole_0(sK0,sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_192])])).

fof(f43084,plain,
    ( ! [X32] :
        ( r1_tarski(k3_xboole_0(X32,k4_xboole_0(sK0,sK2)),k1_xboole_0)
        | k1_xboole_0 != sK1 )
    | ~ spl3_61 ),
    inference(superposition,[],[f22558,f10778])).

fof(f10778,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,k4_xboole_0(sK0,sK2)),sK1)
    | ~ spl3_61 ),
    inference(resolution,[],[f10738,f50])).

fof(f10738,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(X0,k4_xboole_0(sK0,sK2)),sK1)
    | ~ spl3_61 ),
    inference(superposition,[],[f10713,f40])).

fof(f49466,plain,
    ( ~ spl3_127
    | spl3_191
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f43083,f9262,f49464,f43232])).

fof(f49464,plain,
    ( spl3_191
  <=> ! [X31] : r1_tarski(k3_xboole_0(X31,k4_xboole_0(sK1,sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_191])])).

fof(f43083,plain,
    ( ! [X31] :
        ( r1_tarski(k3_xboole_0(X31,k4_xboole_0(sK1,sK2)),k1_xboole_0)
        | k1_xboole_0 != sK0 )
    | ~ spl3_54 ),
    inference(superposition,[],[f22558,f10748])).

fof(f10748,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl3_54 ),
    inference(resolution,[],[f10723,f50])).

fof(f10723,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(X0,k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl3_54 ),
    inference(superposition,[],[f10712,f40])).

fof(f49360,plain,
    ( spl3_190
    | spl3_123
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f43162,f9175,f43213,f49358])).

fof(f49358,plain,
    ( spl3_190
  <=> ! [X93] : k1_xboole_0 != k2_xboole_0(sK2,k2_xboole_0(sK0,X93)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_190])])).

fof(f43213,plain,
    ( spl3_123
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_123])])).

fof(f9175,plain,
    ( spl3_52
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f43162,plain,
    ( ! [X93] :
        ( r1_tarski(sK1,k1_xboole_0)
        | k1_xboole_0 != k2_xboole_0(sK2,k2_xboole_0(sK0,X93)) )
    | ~ spl3_52 ),
    inference(superposition,[],[f22558,f9356])).

fof(f9356,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK0,X2)))
    | ~ spl3_52 ),
    inference(resolution,[],[f9253,f50])).

fof(f9253,plain,
    ( ! [X0] : r1_tarski(sK1,k2_xboole_0(sK2,k2_xboole_0(sK0,X0)))
    | ~ spl3_52 ),
    inference(resolution,[],[f9235,f54])).

fof(f9235,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK1,sK2),k2_xboole_0(sK0,X0))
    | ~ spl3_52 ),
    inference(subsumption_resolution,[],[f9189,f294])).

fof(f9189,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | r1_tarski(k4_xboole_0(sK1,sK2),k2_xboole_0(sK0,X0)) )
    | ~ spl3_52 ),
    inference(superposition,[],[f54,f9177])).

fof(f9177,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f9175])).

fof(f49356,plain,
    ( ~ spl3_189
    | spl3_123
    | ~ spl3_86 ),
    inference(avatar_split_clause,[],[f43159,f15786,f43213,f49353])).

fof(f49353,plain,
    ( spl3_189
  <=> k1_xboole_0 = k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_189])])).

fof(f15786,plain,
    ( spl3_86
  <=> k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).

fof(f43159,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_86 ),
    inference(superposition,[],[f22558,f15788])).

fof(f15788,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl3_86 ),
    inference(avatar_component_clause,[],[f15786])).

fof(f49351,plain,
    ( spl3_188
    | spl3_121
    | ~ spl3_59 ),
    inference(avatar_split_clause,[],[f43146,f9976,f43204,f49349])).

fof(f49349,plain,
    ( spl3_188
  <=> ! [X81] : k1_xboole_0 != k2_xboole_0(sK2,k2_xboole_0(sK1,X81)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_188])])).

fof(f43204,plain,
    ( spl3_121
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_121])])).

fof(f9976,plain,
    ( spl3_59
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f43146,plain,
    ( ! [X81] :
        ( r1_tarski(sK0,k1_xboole_0)
        | k1_xboole_0 != k2_xboole_0(sK2,k2_xboole_0(sK1,X81)) )
    | ~ spl3_59 ),
    inference(superposition,[],[f22558,f10167])).

fof(f10167,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,X2)))
    | ~ spl3_59 ),
    inference(resolution,[],[f10058,f50])).

fof(f10058,plain,
    ( ! [X0] : r1_tarski(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,X0)))
    | ~ spl3_59 ),
    inference(resolution,[],[f10040,f54])).

fof(f10040,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(sK1,X0))
    | ~ spl3_59 ),
    inference(subsumption_resolution,[],[f9990,f294])).

fof(f9990,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(sK1,X0)) )
    | ~ spl3_59 ),
    inference(superposition,[],[f54,f9978])).

fof(f9978,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f9976])).

fof(f49347,plain,
    ( ~ spl3_187
    | spl3_121
    | ~ spl3_87 ),
    inference(avatar_split_clause,[],[f43143,f15791,f43204,f49344])).

fof(f49344,plain,
    ( spl3_187
  <=> k1_xboole_0 = k2_xboole_0(sK1,k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_187])])).

fof(f15791,plain,
    ( spl3_87
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,k3_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_87])])).

fof(f43143,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | k1_xboole_0 != k2_xboole_0(sK1,k3_xboole_0(sK0,sK2))
    | ~ spl3_87 ),
    inference(superposition,[],[f22558,f15793])).

fof(f15793,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,k3_xboole_0(sK0,sK2)))
    | ~ spl3_87 ),
    inference(avatar_component_clause,[],[f15791])).

fof(f49342,plain,
    ( spl3_186
    | spl3_126
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f43114,f61,f43227,f49339])).

fof(f49339,plain,
    ( spl3_186
  <=> ! [X56] : k1_xboole_0 != k2_xboole_0(X56,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_186])])).

fof(f43227,plain,
    ( spl3_126
  <=> r1_tarski(k4_xboole_0(sK1,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_126])])).

fof(f43114,plain,
    ( ! [X57] :
        ( r1_tarski(k4_xboole_0(sK1,sK0),k1_xboole_0)
        | k1_xboole_0 != k2_xboole_0(X57,sK2) )
    | ~ spl3_2 ),
    inference(superposition,[],[f22558,f1667])).

fof(f1667,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(X3,sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f1651,f50])).

fof(f1651,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK1,sK0),k2_xboole_0(X0,sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f1639,f54])).

fof(f1639,plain,
    ( ! [X2] : r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK0),X2),sK2)
    | ~ spl3_2 ),
    inference(superposition,[],[f1491,f268])).

fof(f1491,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k4_xboole_0(sK1,sK0),X0),sK2)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f1485,f1111])).

fof(f1485,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k4_xboole_0(sK1,sK0),X0),k2_xboole_0(sK2,k1_xboole_0))
    | ~ spl3_2 ),
    inference(superposition,[],[f919,f548])).

fof(f49341,plain,
    ( spl3_186
    | spl3_125
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f43113,f56,f43222,f49339])).

fof(f43222,plain,
    ( spl3_125
  <=> r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_125])])).

fof(f43113,plain,
    ( ! [X56] :
        ( r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0)
        | k1_xboole_0 != k2_xboole_0(X56,sK2) )
    | ~ spl3_1 ),
    inference(superposition,[],[f22558,f1473])).

fof(f1473,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(X3,sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f1457,f50])).

fof(f1457,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK0,sK1),k2_xboole_0(X0,sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f1445,f54])).

fof(f1445,plain,
    ( ! [X2] : r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),X2),sK2)
    | ~ spl3_1 ),
    inference(superposition,[],[f1434,f268])).

fof(f1434,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k4_xboole_0(sK0,sK1),X0),sK2)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f1429,f1111])).

fof(f1429,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k4_xboole_0(sK0,sK1),X0),k2_xboole_0(sK2,k1_xboole_0))
    | ~ spl3_1 ),
    inference(superposition,[],[f918,f548])).

fof(f49337,plain,
    ( ~ spl3_127
    | spl3_185
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f43099,f61,f49335,f43232])).

fof(f49335,plain,
    ( spl3_185
  <=> ! [X47] : r1_tarski(k3_xboole_0(sK1,k4_xboole_0(X47,sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_185])])).

fof(f43099,plain,
    ( ! [X47] :
        ( r1_tarski(k3_xboole_0(sK1,k4_xboole_0(X47,sK2)),k1_xboole_0)
        | k1_xboole_0 != sK0 )
    | ~ spl3_2 ),
    inference(superposition,[],[f22558,f26268])).

fof(f26268,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,k4_xboole_0(X3,sK2)),sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f26010,f50])).

fof(f26010,plain,
    ( ! [X102] : r1_tarski(k3_xboole_0(sK1,k4_xboole_0(X102,sK2)),sK0)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f26009,f40])).

fof(f26009,plain,
    ( ! [X102] : r1_tarski(k3_xboole_0(k4_xboole_0(X102,sK2),sK1),sK0)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f25821,f1111])).

fof(f25821,plain,
    ( ! [X102] : r1_tarski(k3_xboole_0(k4_xboole_0(X102,sK2),sK1),k2_xboole_0(sK0,k1_xboole_0))
    | ~ spl3_2 ),
    inference(resolution,[],[f1982,f790])).

fof(f790,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(sK1,sK0)),k1_xboole_0)
    | ~ spl3_2 ),
    inference(superposition,[],[f694,f40])).

fof(f694,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(X0,sK2)),k1_xboole_0)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f687,f51])).

fof(f687,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(k3_xboole_0(k4_xboole_0(sK1,sK0),X0),sK2),k1_xboole_0)
    | ~ spl3_2 ),
    inference(superposition,[],[f514,f548])).

fof(f49333,plain,
    ( ~ spl3_129
    | spl3_184
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f43095,f56,f49331,f43241])).

fof(f49331,plain,
    ( spl3_184
  <=> ! [X43] : r1_tarski(k3_xboole_0(sK0,k4_xboole_0(X43,sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_184])])).

fof(f43095,plain,
    ( ! [X43] :
        ( r1_tarski(k3_xboole_0(sK0,k4_xboole_0(X43,sK2)),k1_xboole_0)
        | k1_xboole_0 != sK1 )
    | ~ spl3_1 ),
    inference(superposition,[],[f22558,f26229])).

fof(f26229,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,k4_xboole_0(X3,sK2)),sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f26006,f50])).

fof(f26006,plain,
    ( ! [X100] : r1_tarski(k3_xboole_0(sK0,k4_xboole_0(X100,sK2)),sK1)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f26005,f40])).

fof(f26005,plain,
    ( ! [X100] : r1_tarski(k3_xboole_0(k4_xboole_0(X100,sK2),sK0),sK1)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f25819,f1111])).

fof(f25819,plain,
    ( ! [X100] : r1_tarski(k3_xboole_0(k4_xboole_0(X100,sK2),sK0),k2_xboole_0(sK1,k1_xboole_0))
    | ~ spl3_1 ),
    inference(resolution,[],[f1982,f777])).

fof(f777,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ spl3_1 ),
    inference(superposition,[],[f664,f40])).

fof(f664,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(X0,sK2)),k1_xboole_0)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f658,f51])).

fof(f658,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK1),X0),sK2),k1_xboole_0)
    | ~ spl3_1 ),
    inference(superposition,[],[f513,f548])).

fof(f49329,plain,
    ( ~ spl3_129
    | spl3_183
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f43092,f10067,f49327,f43241])).

fof(f49327,plain,
    ( spl3_183
  <=> ! [X40] : r1_tarski(k3_xboole_0(k4_xboole_0(sK0,sK2),X40),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_183])])).

fof(f43092,plain,
    ( ! [X40] :
        ( r1_tarski(k3_xboole_0(k4_xboole_0(sK0,sK2),X40),k1_xboole_0)
        | k1_xboole_0 != sK1 )
    | ~ spl3_61 ),
    inference(superposition,[],[f22558,f10733])).

fof(f10733,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK2),X2),sK1)
    | ~ spl3_61 ),
    inference(resolution,[],[f10713,f50])).

fof(f49325,plain,
    ( ~ spl3_127
    | spl3_182
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f43091,f9262,f49323,f43232])).

fof(f49323,plain,
    ( spl3_182
  <=> ! [X39] : r1_tarski(k3_xboole_0(k4_xboole_0(sK1,sK2),X39),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_182])])).

fof(f43091,plain,
    ( ! [X39] :
        ( r1_tarski(k3_xboole_0(k4_xboole_0(sK1,sK2),X39),k1_xboole_0)
        | k1_xboole_0 != sK0 )
    | ~ spl3_54 ),
    inference(superposition,[],[f22558,f10718])).

fof(f10718,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(k4_xboole_0(sK1,sK2),X2),sK0)
    | ~ spl3_54 ),
    inference(resolution,[],[f10712,f50])).

fof(f49319,plain,
    ( spl3_181
    | ~ spl3_27
    | ~ spl3_85 ),
    inference(avatar_split_clause,[],[f16558,f15056,f967,f49316])).

fof(f49316,plain,
    ( spl3_181
  <=> r1_tarski(k5_xboole_0(sK1,k4_xboole_0(sK0,sK2)),k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_181])])).

fof(f967,plain,
    ( spl3_27
  <=> r1_tarski(sK1,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f15056,plain,
    ( spl3_85
  <=> k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK1,k4_xboole_0(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).

fof(f16558,plain,
    ( r1_tarski(k5_xboole_0(sK1,k4_xboole_0(sK0,sK2)),k2_xboole_0(sK0,sK2))
    | ~ spl3_27
    | ~ spl3_85 ),
    inference(forward_demodulation,[],[f16493,f1111])).

fof(f16493,plain,
    ( r1_tarski(k5_xboole_0(sK1,k4_xboole_0(sK0,sK2)),k2_xboole_0(k2_xboole_0(sK0,sK2),k1_xboole_0))
    | ~ spl3_27
    | ~ spl3_85 ),
    inference(superposition,[],[f1697,f15058])).

fof(f15058,plain,
    ( k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK1,k4_xboole_0(sK0,sK2)),sK1)
    | ~ spl3_85 ),
    inference(avatar_component_clause,[],[f15056])).

fof(f1697,plain,
    ( ! [X0] : r1_tarski(X0,k2_xboole_0(k2_xboole_0(sK0,sK2),k4_xboole_0(X0,sK1)))
    | ~ spl3_27 ),
    inference(resolution,[],[f973,f54])).

fof(f973,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(X0,k2_xboole_0(sK0,sK2)),k4_xboole_0(X0,sK1))
    | ~ spl3_27 ),
    inference(resolution,[],[f969,f53])).

fof(f969,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK0,sK2))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f967])).

fof(f48975,plain,
    ( spl3_180
    | ~ spl3_26
    | ~ spl3_83 ),
    inference(avatar_split_clause,[],[f16466,f14842,f962,f48972])).

fof(f48972,plain,
    ( spl3_180
  <=> r1_tarski(k5_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_180])])).

fof(f962,plain,
    ( spl3_26
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f14842,plain,
    ( spl3_83
  <=> k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).

fof(f16466,plain,
    ( r1_tarski(k5_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | ~ spl3_26
    | ~ spl3_83 ),
    inference(forward_demodulation,[],[f16401,f1111])).

fof(f16401,plain,
    ( r1_tarski(k5_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k2_xboole_0(k2_xboole_0(sK1,sK2),k1_xboole_0))
    | ~ spl3_26
    | ~ spl3_83 ),
    inference(superposition,[],[f1674,f14844])).

fof(f14844,plain,
    ( k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl3_83 ),
    inference(avatar_component_clause,[],[f14842])).

fof(f1674,plain,
    ( ! [X0] : r1_tarski(X0,k2_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(X0,sK0)))
    | ~ spl3_26 ),
    inference(resolution,[],[f971,f54])).

fof(f971,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(X0,k2_xboole_0(sK1,sK2)),k4_xboole_0(X0,sK0))
    | ~ spl3_26 ),
    inference(resolution,[],[f964,f53])).

fof(f964,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f962])).

fof(f48908,plain,
    ( ~ spl3_146
    | spl3_179
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f44177,f4240,f48903,f46373])).

fof(f46373,plain,
    ( spl3_146
  <=> k1_xboole_0 = k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_146])])).

fof(f48903,plain,
    ( spl3_179
  <=> ! [X96] : r1_tarski(sK1,X96) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_179])])).

fof(f4240,plain,
    ( spl3_37
  <=> sK1 = k3_xboole_0(sK1,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f44177,plain,
    ( ! [X105] :
        ( r1_tarski(sK1,X105)
        | k1_xboole_0 != k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)) )
    | ~ spl3_37 ),
    inference(superposition,[],[f44055,f4242])).

fof(f4242,plain,
    ( sK1 = k3_xboole_0(sK1,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f4240])).

fof(f44055,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k3_xboole_0(X3,X2),X4)
      | k1_xboole_0 != X2 ) ),
    inference(superposition,[],[f43879,f40])).

fof(f43879,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X2)
      | k1_xboole_0 != X0 ) ),
    inference(forward_demodulation,[],[f43813,f1111])).

fof(f43813,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X2,k1_xboole_0)) ) ),
    inference(resolution,[],[f43076,f1982])).

fof(f43076,plain,(
    ! [X17,X16] :
      ( r1_tarski(k3_xboole_0(X16,X17),k1_xboole_0)
      | k1_xboole_0 != X16 ) ),
    inference(superposition,[],[f22558,f548])).

fof(f48907,plain,
    ( spl3_161
    | spl3_179
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f44174,f170,f48903,f48199])).

fof(f48199,plain,
    ( spl3_161
  <=> ! [X91] : k1_xboole_0 != k2_xboole_0(sK0,k2_xboole_0(sK2,X91)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_161])])).

fof(f170,plain,
    ( spl3_7
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f44174,plain,
    ( ! [X101,X100] :
        ( r1_tarski(sK1,X101)
        | k1_xboole_0 != k2_xboole_0(sK0,k2_xboole_0(sK2,X100)) )
    | ~ spl3_7 ),
    inference(superposition,[],[f44055,f1917])).

fof(f1917,plain,
    ( ! [X4] : sK1 = k3_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK2,X4)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f1904,f38])).

fof(f1904,plain,
    ( ! [X4] : k4_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK2,X4)))
    | ~ spl3_7 ),
    inference(superposition,[],[f44,f1051])).

fof(f1051,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK2,X2)))
    | ~ spl3_7 ),
    inference(resolution,[],[f991,f50])).

fof(f991,plain,
    ( ! [X0] : r1_tarski(sK1,k2_xboole_0(sK0,k2_xboole_0(sK2,X0)))
    | ~ spl3_7 ),
    inference(resolution,[],[f960,f54])).

fof(f960,plain,
    ( ! [X31] : r1_tarski(k4_xboole_0(sK1,sK0),k2_xboole_0(sK2,X31))
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f942,f294])).

fof(f942,plain,
    ( ! [X31] :
        ( ~ r1_tarski(k1_xboole_0,X31)
        | r1_tarski(k4_xboole_0(sK1,sK0),k2_xboole_0(sK2,X31)) )
    | ~ spl3_7 ),
    inference(superposition,[],[f54,f172])).

fof(f172,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f170])).

fof(f48906,plain,
    ( spl3_147
    | spl3_179
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f44172,f1001,f48903,f46378])).

fof(f46378,plain,
    ( spl3_147
  <=> ! [X89] : k1_xboole_0 != k2_xboole_0(k2_xboole_0(sK0,sK2),X89) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_147])])).

fof(f1001,plain,
    ( spl3_29
  <=> k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f44172,plain,
    ( ! [X97,X98] :
        ( r1_tarski(sK1,X98)
        | k1_xboole_0 != k2_xboole_0(k2_xboole_0(sK0,sK2),X97) )
    | ~ spl3_29 ),
    inference(superposition,[],[f44055,f3787])).

fof(f3787,plain,
    ( ! [X8] : sK1 = k3_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK0,sK2),X8))
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f3750,f38])).

fof(f3750,plain,
    ( ! [X8] : k4_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK0,sK2),X8))
    | ~ spl3_29 ),
    inference(superposition,[],[f44,f1067])).

fof(f1067,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK0,sK2),X2))
    | ~ spl3_29 ),
    inference(resolution,[],[f1034,f50])).

fof(f1034,plain,
    ( ! [X0] : r1_tarski(sK1,k2_xboole_0(k2_xboole_0(sK0,sK2),X0))
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f1025,f294])).

fof(f1025,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | r1_tarski(sK1,k2_xboole_0(k2_xboole_0(sK0,sK2),X0)) )
    | ~ spl3_29 ),
    inference(superposition,[],[f54,f1003])).

fof(f1003,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f1001])).

fof(f48905,plain,
    ( spl3_169
    | spl3_179
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f44171,f967,f48903,f48618])).

fof(f48618,plain,
    ( spl3_169
  <=> ! [X87] : k1_xboole_0 != k2_xboole_0(X87,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_169])])).

fof(f44171,plain,
    ( ! [X95,X96] :
        ( r1_tarski(sK1,X96)
        | k1_xboole_0 != k2_xboole_0(X95,k2_xboole_0(sK0,sK2)) )
    | ~ spl3_27 ),
    inference(superposition,[],[f44055,f5705])).

fof(f5705,plain,
    ( ! [X10] : sK1 = k3_xboole_0(sK1,k2_xboole_0(X10,k2_xboole_0(sK0,sK2)))
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f5665,f38])).

fof(f5665,plain,
    ( ! [X10] : k4_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,k2_xboole_0(X10,k2_xboole_0(sK0,sK2)))
    | ~ spl3_27 ),
    inference(superposition,[],[f44,f1855])).

fof(f1855,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(X2,k2_xboole_0(sK0,sK2)))
    | ~ spl3_27 ),
    inference(resolution,[],[f1831,f50])).

fof(f1831,plain,
    ( ! [X0] : r1_tarski(sK1,k2_xboole_0(X0,k2_xboole_0(sK0,sK2)))
    | ~ spl3_27 ),
    inference(resolution,[],[f1830,f54])).

fof(f1830,plain,
    ( ! [X2] : r1_tarski(k4_xboole_0(sK1,X2),k2_xboole_0(sK0,sK2))
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f1824,f1111])).

fof(f1824,plain,
    ( ! [X2] : r1_tarski(k4_xboole_0(sK1,X2),k2_xboole_0(k2_xboole_0(sK0,sK2),k1_xboole_0))
    | ~ spl3_27 ),
    inference(superposition,[],[f1697,f534])).

fof(f48901,plain,
    ( ~ spl3_146
    | spl3_178
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f44163,f4231,f48896,f46373])).

fof(f48896,plain,
    ( spl3_178
  <=> ! [X73] : r1_tarski(sK0,X73) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_178])])).

fof(f4231,plain,
    ( spl3_36
  <=> sK0 = k3_xboole_0(sK0,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f44163,plain,
    ( ! [X82] :
        ( r1_tarski(sK0,X82)
        | k1_xboole_0 != k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)) )
    | ~ spl3_36 ),
    inference(superposition,[],[f44055,f4233])).

fof(f4233,plain,
    ( sK0 = k3_xboole_0(sK0,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f4231])).

fof(f48900,plain,
    ( spl3_141
    | spl3_178
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f44160,f165,f48896,f45648])).

fof(f45648,plain,
    ( spl3_141
  <=> ! [X79] : k1_xboole_0 != k2_xboole_0(sK1,k2_xboole_0(sK2,X79)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_141])])).

fof(f165,plain,
    ( spl3_6
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f44160,plain,
    ( ! [X78,X77] :
        ( r1_tarski(sK0,X78)
        | k1_xboole_0 != k2_xboole_0(sK1,k2_xboole_0(sK2,X77)) )
    | ~ spl3_6 ),
    inference(superposition,[],[f44055,f1893])).

fof(f1893,plain,
    ( ! [X4] : sK0 = k3_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,X4)))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f1880,f38])).

fof(f1880,plain,
    ( ! [X4] : k4_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,X4)))
    | ~ spl3_6 ),
    inference(superposition,[],[f44,f1048])).

fof(f1048,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,X2)))
    | ~ spl3_6 ),
    inference(resolution,[],[f987,f50])).

fof(f987,plain,
    ( ! [X0] : r1_tarski(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,X0)))
    | ~ spl3_6 ),
    inference(resolution,[],[f959,f54])).

fof(f959,plain,
    ( ! [X30] : r1_tarski(k4_xboole_0(sK0,sK1),k2_xboole_0(sK2,X30))
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f941,f294])).

fof(f941,plain,
    ( ! [X30] :
        ( ~ r1_tarski(k1_xboole_0,X30)
        | r1_tarski(k4_xboole_0(sK0,sK1),k2_xboole_0(sK2,X30)) )
    | ~ spl3_6 ),
    inference(superposition,[],[f54,f167])).

fof(f167,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f165])).

fof(f48899,plain,
    ( spl3_139
    | spl3_178
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f44158,f996,f48896,f45588])).

fof(f45588,plain,
    ( spl3_139
  <=> ! [X77] : k1_xboole_0 != k2_xboole_0(k2_xboole_0(sK1,sK2),X77) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_139])])).

fof(f996,plain,
    ( spl3_28
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f44158,plain,
    ( ! [X74,X75] :
        ( r1_tarski(sK0,X75)
        | k1_xboole_0 != k2_xboole_0(k2_xboole_0(sK1,sK2),X74) )
    | ~ spl3_28 ),
    inference(superposition,[],[f44055,f1941])).

fof(f1941,plain,
    ( ! [X4] : sK0 = k3_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X4))
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f1928,f38])).

fof(f1928,plain,
    ( ! [X4] : k4_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X4))
    | ~ spl3_28 ),
    inference(superposition,[],[f44,f1059])).

fof(f1059,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X2))
    | ~ spl3_28 ),
    inference(resolution,[],[f1018,f50])).

fof(f1018,plain,
    ( ! [X0] : r1_tarski(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0))
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f1009,f294])).

fof(f1009,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | r1_tarski(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) )
    | ~ spl3_28 ),
    inference(superposition,[],[f54,f998])).

fof(f998,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f996])).

fof(f48898,plain,
    ( spl3_168
    | spl3_178
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f44157,f962,f48896,f48614])).

fof(f48614,plain,
    ( spl3_168
  <=> ! [X75] : k1_xboole_0 != k2_xboole_0(X75,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_168])])).

fof(f44157,plain,
    ( ! [X72,X73] :
        ( r1_tarski(sK0,X73)
        | k1_xboole_0 != k2_xboole_0(X72,k2_xboole_0(sK1,sK2)) )
    | ~ spl3_26 ),
    inference(superposition,[],[f44055,f5565])).

fof(f5565,plain,
    ( ! [X10] : sK0 = k3_xboole_0(sK0,k2_xboole_0(X10,k2_xboole_0(sK1,sK2)))
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f5525,f38])).

fof(f5525,plain,
    ( ! [X10] : k4_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(X10,k2_xboole_0(sK1,sK2)))
    | ~ spl3_26 ),
    inference(superposition,[],[f44,f1808])).

fof(f1808,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X2,k2_xboole_0(sK1,sK2)))
    | ~ spl3_26 ),
    inference(resolution,[],[f1784,f50])).

fof(f1784,plain,
    ( ! [X0] : r1_tarski(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,sK2)))
    | ~ spl3_26 ),
    inference(resolution,[],[f1783,f54])).

fof(f1783,plain,
    ( ! [X2] : r1_tarski(k4_xboole_0(sK0,X2),k2_xboole_0(sK1,sK2))
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f1777,f1111])).

fof(f1777,plain,
    ( ! [X2] : r1_tarski(k4_xboole_0(sK0,X2),k2_xboole_0(k2_xboole_0(sK1,sK2),k1_xboole_0))
    | ~ spl3_26 ),
    inference(superposition,[],[f1674,f534])).

fof(f48894,plain,
    ( ~ spl3_124
    | spl3_177
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f43133,f61,f48892,f43218])).

fof(f48892,plain,
    ( spl3_177
  <=> ! [X72] : r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK0),X72),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_177])])).

fof(f43133,plain,
    ( ! [X72] :
        ( r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK0),X72),k1_xboole_0)
        | k1_xboole_0 != sK2 )
    | ~ spl3_2 ),
    inference(superposition,[],[f22558,f1653])).

fof(f1653,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),X3),sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f1639,f50])).

fof(f48890,plain,
    ( ~ spl3_124
    | spl3_176
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f43132,f56,f48888,f43218])).

fof(f48888,plain,
    ( spl3_176
  <=> ! [X71] : r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),X71),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_176])])).

fof(f43132,plain,
    ( ! [X71] :
        ( r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),X71),k1_xboole_0)
        | k1_xboole_0 != sK2 )
    | ~ spl3_1 ),
    inference(superposition,[],[f22558,f1459])).

fof(f1459,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),X3),sK2)
    | ~ spl3_1 ),
    inference(resolution,[],[f1445,f50])).

fof(f48886,plain,
    ( spl3_175
    | spl3_130
    | ~ spl3_59 ),
    inference(avatar_split_clause,[],[f43120,f9976,f43245,f48884])).

fof(f48884,plain,
    ( spl3_175
  <=> ! [X63] : k1_xboole_0 != k2_xboole_0(sK1,X63) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_175])])).

fof(f43245,plain,
    ( spl3_130
  <=> r1_tarski(k4_xboole_0(sK0,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_130])])).

fof(f43120,plain,
    ( ! [X63] :
        ( r1_tarski(k4_xboole_0(sK0,sK2),k1_xboole_0)
        | k1_xboole_0 != k2_xboole_0(sK1,X63) )
    | ~ spl3_59 ),
    inference(superposition,[],[f22558,f10060])).

fof(f10060,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(sK1,X3))
    | ~ spl3_59 ),
    inference(resolution,[],[f10040,f50])).

fof(f48882,plain,
    ( spl3_174
    | spl3_128
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f43118,f9175,f43236,f48880])).

fof(f48880,plain,
    ( spl3_174
  <=> ! [X61] : k1_xboole_0 != k2_xboole_0(sK0,X61) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_174])])).

fof(f43236,plain,
    ( spl3_128
  <=> r1_tarski(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_128])])).

fof(f43118,plain,
    ( ! [X61] :
        ( r1_tarski(k4_xboole_0(sK1,sK2),k1_xboole_0)
        | k1_xboole_0 != k2_xboole_0(sK0,X61) )
    | ~ spl3_52 ),
    inference(superposition,[],[f22558,f9255])).

fof(f9255,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK0,X3))
    | ~ spl3_52 ),
    inference(resolution,[],[f9235,f50])).

fof(f48878,plain,
    ( ~ spl3_134
    | spl3_125
    | ~ spl3_81 ),
    inference(avatar_split_clause,[],[f43110,f13668,f43222,f43799])).

fof(f43799,plain,
    ( spl3_134
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_134])])).

fof(f13668,plain,
    ( spl3_81
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).

fof(f43110,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | ~ spl3_81 ),
    inference(superposition,[],[f22558,f13670])).

fof(f13670,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))
    | ~ spl3_81 ),
    inference(avatar_component_clause,[],[f13668])).

fof(f48877,plain,
    ( ~ spl3_133
    | spl3_126
    | ~ spl3_80 ),
    inference(avatar_split_clause,[],[f43109,f13663,f43227,f43794])).

fof(f43794,plain,
    ( spl3_133
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_133])])).

fof(f13663,plain,
    ( spl3_80
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).

fof(f43109,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK0),k1_xboole_0)
    | k1_xboole_0 != k3_xboole_0(sK1,sK2)
    | ~ spl3_80 ),
    inference(superposition,[],[f22558,f13665])).

fof(f13665,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2))
    | ~ spl3_80 ),
    inference(avatar_component_clause,[],[f13663])).

fof(f48876,plain,
    ( ~ spl3_122
    | spl3_173
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f43087,f967,f48874,f43209])).

fof(f43209,plain,
    ( spl3_122
  <=> k1_xboole_0 = k2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_122])])).

fof(f48874,plain,
    ( spl3_173
  <=> ! [X35] : r1_tarski(k3_xboole_0(X35,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_173])])).

fof(f43087,plain,
    ( ! [X35] :
        ( r1_tarski(k3_xboole_0(X35,sK1),k1_xboole_0)
        | k1_xboole_0 != k2_xboole_0(sK0,sK2) )
    | ~ spl3_27 ),
    inference(superposition,[],[f22558,f1859])).

fof(f1859,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,sK1),k2_xboole_0(sK0,sK2))
    | ~ spl3_27 ),
    inference(resolution,[],[f1827,f50])).

fof(f1827,plain,
    ( ! [X1] : r1_tarski(k3_xboole_0(X1,sK1),k2_xboole_0(sK0,sK2))
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f1822,f1111])).

fof(f1822,plain,
    ( ! [X1] : r1_tarski(k3_xboole_0(X1,sK1),k2_xboole_0(k2_xboole_0(sK0,sK2),k1_xboole_0))
    | ~ spl3_27 ),
    inference(superposition,[],[f1697,f560])).

fof(f48872,plain,
    ( ~ spl3_120
    | spl3_172
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f43085,f962,f48870,f43200])).

fof(f43200,plain,
    ( spl3_120
  <=> k1_xboole_0 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_120])])).

fof(f48870,plain,
    ( spl3_172
  <=> ! [X33] : r1_tarski(k3_xboole_0(X33,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_172])])).

fof(f43085,plain,
    ( ! [X33] :
        ( r1_tarski(k3_xboole_0(X33,sK0),k1_xboole_0)
        | k1_xboole_0 != k2_xboole_0(sK1,sK2) )
    | ~ spl3_26 ),
    inference(superposition,[],[f22558,f1812])).

fof(f1812,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,sK0),k2_xboole_0(sK1,sK2))
    | ~ spl3_26 ),
    inference(resolution,[],[f1780,f50])).

fof(f1780,plain,
    ( ! [X1] : r1_tarski(k3_xboole_0(X1,sK0),k2_xboole_0(sK1,sK2))
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f1775,f1111])).

fof(f1775,plain,
    ( ! [X1] : r1_tarski(k3_xboole_0(X1,sK0),k2_xboole_0(k2_xboole_0(sK1,sK2),k1_xboole_0))
    | ~ spl3_26 ),
    inference(superposition,[],[f1674,f560])).

fof(f48868,plain,
    ( ~ spl3_124
    | spl3_171
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f43082,f61,f48866,f43218])).

fof(f48866,plain,
    ( spl3_171
  <=> ! [X30] : r1_tarski(k3_xboole_0(X30,k4_xboole_0(sK1,sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_171])])).

fof(f43082,plain,
    ( ! [X30] :
        ( r1_tarski(k3_xboole_0(X30,k4_xboole_0(sK1,sK0)),k1_xboole_0)
        | k1_xboole_0 != sK2 )
    | ~ spl3_2 ),
    inference(superposition,[],[f22558,f1644])).

fof(f1644,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,k4_xboole_0(sK1,sK0)),sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f1492,f50])).

fof(f1492,plain,
    ( ! [X1] : r1_tarski(k3_xboole_0(X1,k4_xboole_0(sK1,sK0)),sK2)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f1486,f1111])).

fof(f1486,plain,
    ( ! [X1] : r1_tarski(k3_xboole_0(X1,k4_xboole_0(sK1,sK0)),k2_xboole_0(sK2,k1_xboole_0))
    | ~ spl3_2 ),
    inference(superposition,[],[f919,f560])).

fof(f48864,plain,
    ( ~ spl3_124
    | spl3_170
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f43081,f56,f48862,f43218])).

fof(f48862,plain,
    ( spl3_170
  <=> ! [X29] : r1_tarski(k3_xboole_0(X29,k4_xboole_0(sK0,sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_170])])).

fof(f43081,plain,
    ( ! [X29] :
        ( r1_tarski(k3_xboole_0(X29,k4_xboole_0(sK0,sK1)),k1_xboole_0)
        | k1_xboole_0 != sK2 )
    | ~ spl3_1 ),
    inference(superposition,[],[f22558,f1450])).

fof(f1450,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,k4_xboole_0(sK0,sK1)),sK2)
    | ~ spl3_1 ),
    inference(resolution,[],[f1435,f50])).

fof(f1435,plain,
    ( ! [X1] : r1_tarski(k3_xboole_0(X1,k4_xboole_0(sK0,sK1)),sK2)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f1430,f1111])).

fof(f1430,plain,
    ( ! [X1] : r1_tarski(k3_xboole_0(X1,k4_xboole_0(sK0,sK1)),k2_xboole_0(sK2,k1_xboole_0))
    | ~ spl3_1 ),
    inference(superposition,[],[f918,f560])).

fof(f48634,plain,
    ( ~ spl3_129
    | spl3_128 ),
    inference(avatar_split_clause,[],[f46350,f43236,f43241])).

fof(f46350,plain,
    ( k1_xboole_0 != sK1
    | spl3_128 ),
    inference(superposition,[],[f46276,f8902])).

fof(f8902,plain,(
    ! [X6,X7] : k2_xboole_0(k4_xboole_0(X6,X7),X6) = X6 ),
    inference(forward_demodulation,[],[f8819,f7367])).

fof(f7367,plain,(
    ! [X23,X22] : k5_xboole_0(k4_xboole_0(X22,X23),k3_xboole_0(X22,X23)) = X22 ),
    inference(superposition,[],[f3042,f1559])).

fof(f8819,plain,(
    ! [X6,X7] : k2_xboole_0(k4_xboole_0(X6,X7),X6) = k5_xboole_0(k4_xboole_0(X6,X7),k3_xboole_0(X6,X7)) ),
    inference(superposition,[],[f3037,f44])).

fof(f46276,plain,
    ( ! [X1] : k1_xboole_0 != k2_xboole_0(k4_xboole_0(sK1,sK2),X1)
    | spl3_128 ),
    inference(resolution,[],[f43237,f43073])).

fof(f43073,plain,(
    ! [X12,X11] :
      ( r1_tarski(X11,k1_xboole_0)
      | k1_xboole_0 != k2_xboole_0(X11,X12) ) ),
    inference(superposition,[],[f22558,f980])).

fof(f980,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X3,X4)) ),
    inference(resolution,[],[f947,f50])).

fof(f947,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(subsumption_resolution,[],[f928,f294])).

fof(f928,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | r1_tarski(X0,k2_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f54,f148])).

fof(f148,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(X6,X6) ),
    inference(resolution,[],[f50,f101])).

fof(f101,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(forward_demodulation,[],[f95,f37])).

fof(f95,plain,(
    ! [X0] : r1_tarski(X0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f43,f38])).

fof(f43237,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),k1_xboole_0)
    | spl3_128 ),
    inference(avatar_component_clause,[],[f43236])).

fof(f48626,plain,
    ( spl3_128
    | ~ spl3_148 ),
    inference(avatar_contradiction_clause,[],[f48625])).

fof(f48625,plain,
    ( $false
    | spl3_128
    | ~ spl3_148 ),
    inference(subsumption_resolution,[],[f48205,f46350])).

fof(f48205,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_148 ),
    inference(superposition,[],[f46387,f38])).

fof(f46387,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_148 ),
    inference(avatar_component_clause,[],[f46385])).

fof(f46385,plain,
    ( spl3_148
  <=> k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_148])])).

fof(f48624,plain,
    ( spl3_128
    | ~ spl3_148 ),
    inference(avatar_contradiction_clause,[],[f48623])).

fof(f48623,plain,
    ( $false
    | spl3_128
    | ~ spl3_148 ),
    inference(subsumption_resolution,[],[f48228,f46350])).

fof(f48228,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_148 ),
    inference(superposition,[],[f38,f46387])).

fof(f48622,plain,
    ( spl3_128
    | ~ spl3_148 ),
    inference(avatar_contradiction_clause,[],[f48621])).

fof(f48621,plain,
    ( $false
    | spl3_128
    | ~ spl3_148 ),
    inference(subsumption_resolution,[],[f48359,f46350])).

fof(f48359,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_148 ),
    inference(forward_demodulation,[],[f48358,f78])).

fof(f48358,plain,
    ( sK1 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_148 ),
    inference(forward_demodulation,[],[f48290,f1113])).

fof(f1113,plain,(
    ! [X6] : k2_xboole_0(k1_xboole_0,X6) = X6 ),
    inference(forward_demodulation,[],[f1112,f37])).

fof(f1112,plain,(
    ! [X6] : k5_xboole_0(X6,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X6) ),
    inference(forward_demodulation,[],[f1087,f70])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f40,f35])).

fof(f1087,plain,(
    ! [X6] : k2_xboole_0(k1_xboole_0,X6) = k5_xboole_0(X6,k3_xboole_0(k1_xboole_0,X6)) ),
    inference(superposition,[],[f46,f78])).

fof(f48290,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,sK1)
    | ~ spl3_148 ),
    inference(superposition,[],[f3037,f46387])).

fof(f48620,plain,
    ( spl3_169
    | spl3_123
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f43152,f967,f43213,f48618])).

fof(f43152,plain,
    ( ! [X87] :
        ( r1_tarski(sK1,k1_xboole_0)
        | k1_xboole_0 != k2_xboole_0(X87,k2_xboole_0(sK0,sK2)) )
    | ~ spl3_27 ),
    inference(superposition,[],[f22558,f1855])).

fof(f48616,plain,
    ( spl3_168
    | spl3_121
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f43136,f962,f43204,f48614])).

fof(f43136,plain,
    ( ! [X75] :
        ( r1_tarski(sK0,k1_xboole_0)
        | k1_xboole_0 != k2_xboole_0(X75,k2_xboole_0(sK1,sK2)) )
    | ~ spl3_26 ),
    inference(superposition,[],[f22558,f1808])).

fof(f48612,plain,
    ( ~ spl3_122
    | spl3_167
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f43097,f967,f48610,f43209])).

fof(f48610,plain,
    ( spl3_167
  <=> ! [X45] : r1_tarski(k3_xboole_0(sK1,X45),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_167])])).

fof(f43097,plain,
    ( ! [X45] :
        ( r1_tarski(k3_xboole_0(sK1,X45),k1_xboole_0)
        | k1_xboole_0 != k2_xboole_0(sK0,sK2) )
    | ~ spl3_27 ),
    inference(superposition,[],[f22558,f1844])).

fof(f1844,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,X2),k2_xboole_0(sK0,sK2))
    | ~ spl3_27 ),
    inference(resolution,[],[f1826,f50])).

fof(f1826,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),k2_xboole_0(sK0,sK2))
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f1821,f1111])).

fof(f1821,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),k2_xboole_0(k2_xboole_0(sK0,sK2),k1_xboole_0))
    | ~ spl3_27 ),
    inference(superposition,[],[f1697,f548])).

fof(f48608,plain,
    ( ~ spl3_120
    | spl3_166
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f43093,f962,f48606,f43200])).

fof(f48606,plain,
    ( spl3_166
  <=> ! [X41] : r1_tarski(k3_xboole_0(sK0,X41),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_166])])).

fof(f43093,plain,
    ( ! [X41] :
        ( r1_tarski(k3_xboole_0(sK0,X41),k1_xboole_0)
        | k1_xboole_0 != k2_xboole_0(sK1,sK2) )
    | ~ spl3_26 ),
    inference(superposition,[],[f22558,f1797])).

fof(f1797,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,X2),k2_xboole_0(sK1,sK2))
    | ~ spl3_26 ),
    inference(resolution,[],[f1779,f50])).

fof(f1779,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),k2_xboole_0(sK1,sK2))
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f1774,f1111])).

fof(f1774,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),k2_xboole_0(k2_xboole_0(sK1,sK2),k1_xboole_0))
    | ~ spl3_26 ),
    inference(superposition,[],[f1674,f548])).

fof(f48604,plain,
    ( ~ spl3_124
    | spl3_165
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f43090,f61,f48602,f43218])).

fof(f48602,plain,
    ( spl3_165
  <=> ! [X38] : r1_tarski(k3_xboole_0(k4_xboole_0(sK1,sK0),X38),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_165])])).

fof(f43090,plain,
    ( ! [X38] :
        ( r1_tarski(k3_xboole_0(k4_xboole_0(sK1,sK0),X38),k1_xboole_0)
        | k1_xboole_0 != sK2 )
    | ~ spl3_2 ),
    inference(superposition,[],[f22558,f1633])).

fof(f1633,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(k4_xboole_0(sK1,sK0),X2),sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f1491,f50])).

fof(f48600,plain,
    ( ~ spl3_124
    | spl3_164
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f43089,f56,f48598,f43218])).

fof(f48598,plain,
    ( spl3_164
  <=> ! [X37] : r1_tarski(k3_xboole_0(k4_xboole_0(sK0,sK1),X37),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_164])])).

fof(f43089,plain,
    ( ! [X37] :
        ( r1_tarski(k3_xboole_0(k4_xboole_0(sK0,sK1),X37),k1_xboole_0)
        | k1_xboole_0 != sK2 )
    | ~ spl3_1 ),
    inference(superposition,[],[f22558,f1439])).

fof(f1439,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK1),X2),sK2)
    | ~ spl3_1 ),
    inference(resolution,[],[f1434,f50])).

fof(f48596,plain,
    ( ~ spl3_120
    | spl3_163
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f43119,f962,f48594,f43200])).

fof(f48594,plain,
    ( spl3_163
  <=> ! [X62] : r1_tarski(k4_xboole_0(sK0,X62),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_163])])).

fof(f43119,plain,
    ( ! [X62] :
        ( r1_tarski(k4_xboole_0(sK0,X62),k1_xboole_0)
        | k1_xboole_0 != k2_xboole_0(sK1,sK2) )
    | ~ spl3_26 ),
    inference(superposition,[],[f22558,f1786])).

fof(f1786,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X3),k2_xboole_0(sK1,sK2))
    | ~ spl3_26 ),
    inference(resolution,[],[f1783,f50])).

fof(f48592,plain,
    ( ~ spl3_122
    | spl3_162
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f43117,f967,f48590,f43209])).

fof(f48590,plain,
    ( spl3_162
  <=> ! [X60] : r1_tarski(k4_xboole_0(sK1,X60),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_162])])).

fof(f43117,plain,
    ( ! [X60] :
        ( r1_tarski(k4_xboole_0(sK1,X60),k1_xboole_0)
        | k1_xboole_0 != k2_xboole_0(sK0,sK2) )
    | ~ spl3_27 ),
    inference(superposition,[],[f22558,f1833])).

fof(f1833,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,X3),k2_xboole_0(sK0,sK2))
    | ~ spl3_27 ),
    inference(resolution,[],[f1830,f50])).

fof(f48588,plain,
    ( ~ spl3_146
    | spl3_123
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f43160,f3906,f43213,f46373])).

fof(f3906,plain,
    ( spl3_35
  <=> k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f43160,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 != k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl3_35 ),
    inference(superposition,[],[f22558,f3908])).

fof(f3908,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f3906])).

fof(f48361,plain,
    ( spl3_129
    | ~ spl3_148 ),
    inference(avatar_contradiction_clause,[],[f48360])).

fof(f48360,plain,
    ( $false
    | spl3_129
    | ~ spl3_148 ),
    inference(subsumption_resolution,[],[f48359,f43243])).

fof(f43243,plain,
    ( k1_xboole_0 != sK1
    | spl3_129 ),
    inference(avatar_component_clause,[],[f43241])).

fof(f48314,plain,
    ( spl3_129
    | ~ spl3_148 ),
    inference(avatar_contradiction_clause,[],[f48313])).

fof(f48313,plain,
    ( $false
    | spl3_129
    | ~ spl3_148 ),
    inference(subsumption_resolution,[],[f48228,f43243])).

fof(f48309,plain,
    ( spl3_129
    | ~ spl3_148 ),
    inference(avatar_contradiction_clause,[],[f48308])).

fof(f48308,plain,
    ( $false
    | spl3_129
    | ~ spl3_148 ),
    inference(subsumption_resolution,[],[f48205,f43243])).

fof(f48201,plain,
    ( spl3_161
    | spl3_123
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f43157,f170,f43213,f48199])).

fof(f43157,plain,
    ( ! [X91] :
        ( r1_tarski(sK1,k1_xboole_0)
        | k1_xboole_0 != k2_xboole_0(sK0,k2_xboole_0(sK2,X91)) )
    | ~ spl3_7 ),
    inference(superposition,[],[f22558,f1051])).

fof(f47972,plain,
    ( spl3_160
    | ~ spl3_159 ),
    inference(avatar_split_clause,[],[f47907,f47786,f47969])).

fof(f47969,plain,
    ( spl3_160
  <=> sK0 = k3_xboole_0(sK0,k2_xboole_0(sK2,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_160])])).

fof(f47786,plain,
    ( spl3_159
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_159])])).

fof(f47907,plain,
    ( sK0 = k3_xboole_0(sK0,k2_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_159 ),
    inference(forward_demodulation,[],[f47829,f38])).

fof(f47829,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_159 ),
    inference(superposition,[],[f44,f47788])).

fof(f47788,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_159 ),
    inference(avatar_component_clause,[],[f47786])).

fof(f47789,plain,
    ( spl3_159
    | ~ spl3_157 ),
    inference(avatar_split_clause,[],[f47259,f47254,f47786])).

fof(f47254,plain,
    ( spl3_157
  <=> r1_tarski(sK0,k2_xboole_0(sK2,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_157])])).

fof(f47259,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_157 ),
    inference(resolution,[],[f47256,f50])).

fof(f47256,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_157 ),
    inference(avatar_component_clause,[],[f47254])).

fof(f47588,plain,
    ( spl3_158
    | ~ spl3_156 ),
    inference(avatar_split_clause,[],[f47252,f47246,f47585])).

fof(f47585,plain,
    ( spl3_158
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_158])])).

fof(f47246,plain,
    ( spl3_156
  <=> r1_tarski(k4_xboole_0(sK0,sK2),k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_156])])).

fof(f47252,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k5_xboole_0(sK1,sK2))
    | ~ spl3_156 ),
    inference(resolution,[],[f47248,f50])).

fof(f47248,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k5_xboole_0(sK1,sK2))
    | ~ spl3_156 ),
    inference(avatar_component_clause,[],[f47246])).

fof(f47257,plain,
    ( spl3_157
    | ~ spl3_156 ),
    inference(avatar_split_clause,[],[f47250,f47246,f47254])).

fof(f47250,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK2,k5_xboole_0(sK1,sK2)))
    | ~ spl3_156 ),
    inference(resolution,[],[f47248,f54])).

fof(f47249,plain,
    ( spl3_156
    | ~ spl3_154 ),
    inference(avatar_split_clause,[],[f47235,f47067,f47246])).

fof(f47067,plain,
    ( spl3_154
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_154])])).

fof(f47235,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k5_xboole_0(sK1,sK2))
    | ~ spl3_154 ),
    inference(superposition,[],[f47181,f47])).

fof(f47181,plain,
    ( ! [X7] : r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(k4_xboole_0(sK1,sK2),X7))
    | ~ spl3_154 ),
    inference(subsumption_resolution,[],[f47101,f294])).

fof(f47101,plain,
    ( ! [X7] :
        ( ~ r1_tarski(k1_xboole_0,X7)
        | r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(k4_xboole_0(sK1,sK2),X7)) )
    | ~ spl3_154 ),
    inference(superposition,[],[f54,f47069])).

fof(f47069,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))
    | ~ spl3_154 ),
    inference(avatar_component_clause,[],[f47067])).

fof(f47229,plain,
    ( spl3_155
    | ~ spl3_154 ),
    inference(avatar_split_clause,[],[f47094,f47067,f47226])).

fof(f47226,plain,
    ( spl3_155
  <=> r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK2),k5_xboole_0(sK1,sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_155])])).

fof(f47094,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK2),k5_xboole_0(sK1,sK2)),k1_xboole_0)
    | ~ spl3_154 ),
    inference(superposition,[],[f510,f47069])).

fof(f510,plain,(
    ! [X4,X2,X3] : r1_tarski(k4_xboole_0(X2,k5_xboole_0(X3,X4)),k4_xboole_0(X2,k4_xboole_0(X3,X4))) ),
    inference(resolution,[],[f53,f43])).

fof(f47070,plain,
    ( spl3_154
    | ~ spl3_149 ),
    inference(avatar_split_clause,[],[f46819,f46813,f47067])).

fof(f46813,plain,
    ( spl3_149
  <=> r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_149])])).

fof(f46819,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))
    | ~ spl3_149 ),
    inference(resolution,[],[f46815,f50])).

fof(f46815,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))
    | ~ spl3_149 ),
    inference(avatar_component_clause,[],[f46813])).

fof(f47061,plain,
    ( spl3_153
    | ~ spl3_151 ),
    inference(avatar_split_clause,[],[f47049,f47042,f47058])).

fof(f47058,plain,
    ( spl3_153
  <=> r1_tarski(sK1,k2_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(sK2,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_153])])).

fof(f47042,plain,
    ( spl3_151
  <=> r1_tarski(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,k4_xboole_0(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_151])])).

fof(f47049,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(sK2,sK0))))
    | ~ spl3_151 ),
    inference(resolution,[],[f47044,f54])).

fof(f47044,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,k4_xboole_0(sK2,sK0)))
    | ~ spl3_151 ),
    inference(avatar_component_clause,[],[f47042])).

fof(f47056,plain,
    ( spl3_152
    | ~ spl3_150 ),
    inference(avatar_split_clause,[],[f47046,f47037,f47053])).

fof(f47053,plain,
    ( spl3_152
  <=> r1_tarski(sK0,k2_xboole_0(sK1,k3_xboole_0(sK0,k4_xboole_0(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_152])])).

fof(f47037,plain,
    ( spl3_150
  <=> r1_tarski(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_150])])).

fof(f47046,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,k3_xboole_0(sK0,k4_xboole_0(sK2,sK1))))
    | ~ spl3_150 ),
    inference(resolution,[],[f47039,f54])).

fof(f47039,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK2,sK1)))
    | ~ spl3_150 ),
    inference(avatar_component_clause,[],[f47037])).

fof(f47045,plain,
    ( spl3_151
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f46600,f353,f47042])).

fof(f353,plain,
    ( spl3_15
  <=> k4_xboole_0(sK1,sK0) = k3_xboole_0(k4_xboole_0(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f46600,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,k4_xboole_0(sK2,sK0)))
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f46599,f15339])).

fof(f15339,plain,(
    ! [X8,X7,X9] : k3_xboole_0(X7,k4_xboole_0(X8,X9)) = k3_xboole_0(X8,k4_xboole_0(X7,X9)) ),
    inference(superposition,[],[f1947,f51])).

fof(f1947,plain,(
    ! [X4,X2,X3] : k3_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(k3_xboole_0(X3,X2),X4) ),
    inference(superposition,[],[f51,f40])).

fof(f46599,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK0),k3_xboole_0(sK2,k4_xboole_0(sK1,sK0)))
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f46598,f40])).

fof(f46598,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK0),k3_xboole_0(k4_xboole_0(sK1,sK0),sK2))
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f46431,f1559])).

fof(f46431,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK0),k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k4_xboole_0(sK1,sK0),sK2)))
    | ~ spl3_15 ),
    inference(superposition,[],[f274,f355])).

fof(f355,plain,
    ( k4_xboole_0(sK1,sK0) = k3_xboole_0(k4_xboole_0(sK1,sK0),sK2)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f353])).

fof(f274,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f256,f41])).

fof(f256,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(superposition,[],[f98,f44])).

fof(f98,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X2,X3),k5_xboole_0(X3,X2)) ),
    inference(superposition,[],[f43,f41])).

fof(f47040,plain,
    ( spl3_150
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f46597,f348,f47037])).

fof(f348,plain,
    ( spl3_14
  <=> k4_xboole_0(sK0,sK1) = k3_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f46597,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK2,sK1)))
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f46596,f15339])).

fof(f46596,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),k3_xboole_0(sK2,k4_xboole_0(sK0,sK1)))
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f46595,f40])).

fof(f46595,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),k3_xboole_0(k4_xboole_0(sK0,sK1),sK2))
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f46430,f1559])).

fof(f46430,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)))
    | ~ spl3_14 ),
    inference(superposition,[],[f274,f350])).

fof(f350,plain,
    ( k4_xboole_0(sK0,sK1) = k3_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f348])).

fof(f46816,plain,
    ( spl3_149
    | ~ spl3_72
    | ~ spl3_79 ),
    inference(avatar_split_clause,[],[f46594,f13486,f12545,f46813])).

fof(f12545,plain,
    ( spl3_72
  <=> k4_xboole_0(sK1,sK2) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f13486,plain,
    ( spl3_79
  <=> k4_xboole_0(sK0,sK2) = k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_79])])).

fof(f46594,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))
    | ~ spl3_72
    | ~ spl3_79 ),
    inference(forward_demodulation,[],[f46593,f12547])).

fof(f12547,plain,
    ( k4_xboole_0(sK1,sK2) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_72 ),
    inference(avatar_component_clause,[],[f12545])).

fof(f46593,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_79 ),
    inference(forward_demodulation,[],[f46592,f15339])).

fof(f46592,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)))
    | ~ spl3_79 ),
    inference(forward_demodulation,[],[f46591,f40])).

fof(f46591,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1))
    | ~ spl3_79 ),
    inference(forward_demodulation,[],[f46426,f1559])).

fof(f46426,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k5_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)))
    | ~ spl3_79 ),
    inference(superposition,[],[f274,f13488])).

fof(f13488,plain,
    ( k4_xboole_0(sK0,sK2) = k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl3_79 ),
    inference(avatar_component_clause,[],[f13486])).

fof(f46396,plain,
    ( ~ spl3_148
    | spl3_123 ),
    inference(avatar_split_clause,[],[f46395,f43213,f46385])).

fof(f46395,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k1_xboole_0)
    | spl3_123 ),
    inference(resolution,[],[f43214,f49])).

fof(f43214,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl3_123 ),
    inference(avatar_component_clause,[],[f43213])).

fof(f46388,plain,
    ( spl3_148
    | ~ spl3_123 ),
    inference(avatar_split_clause,[],[f46382,f43213,f46385])).

fof(f46382,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_123 ),
    inference(resolution,[],[f43215,f50])).

fof(f43215,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_123 ),
    inference(avatar_component_clause,[],[f43213])).

fof(f46380,plain,
    ( spl3_147
    | spl3_123
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f43154,f1001,f43213,f46378])).

fof(f43154,plain,
    ( ! [X89] :
        ( r1_tarski(sK1,k1_xboole_0)
        | k1_xboole_0 != k2_xboole_0(k2_xboole_0(sK0,sK2),X89) )
    | ~ spl3_29 ),
    inference(superposition,[],[f22558,f1067])).

fof(f46376,plain,
    ( ~ spl3_146
    | spl3_121
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f43144,f3798,f43204,f46373])).

fof(f3798,plain,
    ( spl3_34
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f43144,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | k1_xboole_0 != k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl3_34 ),
    inference(superposition,[],[f22558,f3800])).

fof(f3800,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f3798])).

fof(f46371,plain,
    ( ~ spl3_145
    | spl3_128 ),
    inference(avatar_split_clause,[],[f46333,f43236,f46368])).

fof(f46368,plain,
    ( spl3_145
  <=> k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_145])])).

fof(f46333,plain,
    ( k1_xboole_0 != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))
    | spl3_128 ),
    inference(superposition,[],[f46275,f1592])).

fof(f1592,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f1591,f41])).

fof(f1591,plain,(
    ! [X2,X1] : k5_xboole_0(k3_xboole_0(X1,X2),X1) = k2_xboole_0(k3_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f1518,f51])).

fof(f1518,plain,(
    ! [X2,X1] : k5_xboole_0(k3_xboole_0(X1,X2),X1) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X1,X2),X1),k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f47,f45])).

fof(f46275,plain,
    ( ! [X0] : k1_xboole_0 != k2_xboole_0(X0,k4_xboole_0(sK1,sK2))
    | spl3_128 ),
    inference(resolution,[],[f43237,f43074])).

fof(f43074,plain,(
    ! [X14,X13] :
      ( r1_tarski(X13,k1_xboole_0)
      | k1_xboole_0 != k2_xboole_0(X14,X13) ) ),
    inference(superposition,[],[f22558,f984])).

fof(f984,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,X3)) ),
    inference(resolution,[],[f913,f50])).

fof(f913,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(resolution,[],[f54,f524])).

fof(f46365,plain,
    ( ~ spl3_144
    | spl3_128 ),
    inference(avatar_split_clause,[],[f46281,f43236,f46362])).

fof(f46362,plain,
    ( spl3_144
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_144])])).

fof(f46281,plain,
    ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)
    | spl3_128 ),
    inference(resolution,[],[f43237,f49])).

fof(f46349,plain,
    ( ~ spl3_143
    | spl3_142 ),
    inference(avatar_split_clause,[],[f46343,f46339,f46346])).

fof(f46346,plain,
    ( spl3_143
  <=> k1_xboole_0 = k5_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_143])])).

fof(f46339,plain,
    ( spl3_142
  <=> k1_xboole_0 = k5_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_142])])).

fof(f46343,plain,
    ( k1_xboole_0 != k5_xboole_0(sK1,sK2)
    | spl3_142 ),
    inference(superposition,[],[f46341,f41])).

fof(f46341,plain,
    ( k1_xboole_0 != k5_xboole_0(sK2,sK1)
    | spl3_142 ),
    inference(avatar_component_clause,[],[f46339])).

fof(f46342,plain,
    ( ~ spl3_142
    | spl3_128 ),
    inference(avatar_split_clause,[],[f46334,f43236,f46339])).

fof(f46334,plain,
    ( k1_xboole_0 != k5_xboole_0(sK2,sK1)
    | spl3_128 ),
    inference(superposition,[],[f46275,f47])).

fof(f46272,plain,
    ( spl3_106
    | ~ spl3_107 ),
    inference(avatar_contradiction_clause,[],[f46271])).

fof(f46271,plain,
    ( $false
    | spl3_106
    | ~ spl3_107 ),
    inference(subsumption_resolution,[],[f46270,f25728])).

fof(f25728,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK2)
    | spl3_106 ),
    inference(avatar_component_clause,[],[f25726])).

fof(f25726,plain,
    ( spl3_106
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_106])])).

fof(f46270,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl3_107 ),
    inference(resolution,[],[f25733,f50])).

fof(f25733,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_107 ),
    inference(avatar_component_clause,[],[f25731])).

fof(f25731,plain,
    ( spl3_107
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_107])])).

fof(f46268,plain,
    ( spl3_107
    | ~ spl3_128 ),
    inference(avatar_split_clause,[],[f45879,f43236,f25731])).

fof(f45879,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_128 ),
    inference(forward_demodulation,[],[f45876,f1111])).

fof(f45876,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK2,k1_xboole_0))
    | ~ spl3_128 ),
    inference(resolution,[],[f43238,f54])).

fof(f43238,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),k1_xboole_0)
    | ~ spl3_128 ),
    inference(avatar_component_clause,[],[f43236])).

fof(f45851,plain,
    ( ~ spl3_127
    | ~ spl3_74
    | spl3_106 ),
    inference(avatar_split_clause,[],[f45843,f25726,f12832,f43232])).

fof(f12832,plain,
    ( spl3_74
  <=> sK0 = k2_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).

fof(f45843,plain,
    ( k1_xboole_0 != sK0
    | ~ spl3_74
    | spl3_106 ),
    inference(subsumption_resolution,[],[f43896,f25728])).

fof(f43896,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl3_74 ),
    inference(superposition,[],[f43661,f12834])).

fof(f12834,plain,
    ( sK0 = k2_xboole_0(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl3_74 ),
    inference(avatar_component_clause,[],[f12832])).

fof(f43661,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 != k2_xboole_0(X3,X4)
      | k1_xboole_0 = X3 ) ),
    inference(forward_demodulation,[],[f43656,f38])).

fof(f43656,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 != k2_xboole_0(X3,X4)
      | k1_xboole_0 = k4_xboole_0(X3,k1_xboole_0) ) ),
    inference(resolution,[],[f43073,f50])).

fof(f45842,plain,
    ( ~ spl3_74
    | spl3_106
    | ~ spl3_140 ),
    inference(avatar_contradiction_clause,[],[f45841])).

fof(f45841,plain,
    ( $false
    | ~ spl3_74
    | spl3_106
    | ~ spl3_140 ),
    inference(subsumption_resolution,[],[f45840,f25728])).

fof(f45840,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl3_74
    | ~ spl3_140 ),
    inference(subsumption_resolution,[],[f43896,f45804])).

fof(f45804,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_140 ),
    inference(forward_demodulation,[],[f45803,f78])).

fof(f45803,plain,
    ( sK0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_140 ),
    inference(forward_demodulation,[],[f45736,f1113])).

fof(f45736,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,sK0)
    | ~ spl3_140 ),
    inference(superposition,[],[f3037,f45597])).

fof(f45597,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_140 ),
    inference(avatar_component_clause,[],[f45595])).

fof(f45595,plain,
    ( spl3_140
  <=> k1_xboole_0 = k4_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_140])])).

fof(f45834,plain,
    ( ~ spl3_54
    | spl3_106
    | ~ spl3_140 ),
    inference(avatar_contradiction_clause,[],[f45833])).

fof(f45833,plain,
    ( $false
    | ~ spl3_54
    | spl3_106
    | ~ spl3_140 ),
    inference(subsumption_resolution,[],[f45832,f25728])).

fof(f45832,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl3_54
    | ~ spl3_140 ),
    inference(subsumption_resolution,[],[f44026,f45804])).

fof(f44026,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl3_54 ),
    inference(superposition,[],[f43810,f9264])).

fof(f43810,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 != k2_xboole_0(X3,X4)
      | k1_xboole_0 = X4 ) ),
    inference(forward_demodulation,[],[f43805,f38])).

fof(f43805,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 != k2_xboole_0(X3,X4)
      | k1_xboole_0 = k4_xboole_0(X4,k1_xboole_0) ) ),
    inference(resolution,[],[f43074,f50])).

fof(f45830,plain,
    ( spl3_114
    | ~ spl3_140 ),
    inference(avatar_contradiction_clause,[],[f45829])).

fof(f45829,plain,
    ( $false
    | spl3_114
    | ~ spl3_140 ),
    inference(subsumption_resolution,[],[f44050,f45804])).

fof(f44050,plain,
    ( k1_xboole_0 != sK0
    | spl3_114 ),
    inference(resolution,[],[f43879,f25771])).

fof(f25771,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
    | spl3_114 ),
    inference(avatar_component_clause,[],[f25769])).

fof(f25769,plain,
    ( spl3_114
  <=> r1_tarski(k3_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_114])])).

fof(f45828,plain,
    ( spl3_100
    | ~ spl3_140 ),
    inference(avatar_contradiction_clause,[],[f45827])).

fof(f45827,plain,
    ( $false
    | spl3_100
    | ~ spl3_140 ),
    inference(subsumption_resolution,[],[f44051,f45804])).

fof(f44051,plain,
    ( k1_xboole_0 != sK0
    | spl3_100 ),
    inference(resolution,[],[f43879,f25694])).

fof(f25694,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK2)
    | spl3_100 ),
    inference(avatar_component_clause,[],[f25692])).

fof(f25692,plain,
    ( spl3_100
  <=> r1_tarski(k3_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_100])])).

fof(f45825,plain,
    ( spl3_114
    | ~ spl3_140 ),
    inference(avatar_contradiction_clause,[],[f45824])).

fof(f45824,plain,
    ( $false
    | spl3_114
    | ~ spl3_140 ),
    inference(subsumption_resolution,[],[f44932,f45804])).

fof(f44932,plain,
    ( k1_xboole_0 != sK0
    | spl3_114 ),
    inference(superposition,[],[f44918,f8900])).

fof(f44918,plain,
    ( ! [X13] : k1_xboole_0 != k2_xboole_0(k3_xboole_0(sK0,sK2),X13)
    | spl3_114 ),
    inference(resolution,[],[f44134,f25771])).

fof(f44134,plain,(
    ! [X28,X29,X27] :
      ( r1_tarski(X27,X29)
      | k1_xboole_0 != k2_xboole_0(X27,X28) ) ),
    inference(superposition,[],[f44055,f1263])).

fof(f1263,plain,(
    ! [X8,X7] : k3_xboole_0(X7,k2_xboole_0(X7,X8)) = X7 ),
    inference(forward_demodulation,[],[f1241,f38])).

fof(f1241,plain,(
    ! [X8,X7] : k3_xboole_0(X7,k2_xboole_0(X7,X8)) = k4_xboole_0(X7,k1_xboole_0) ),
    inference(superposition,[],[f44,f980])).

fof(f45823,plain,
    ( spl3_100
    | ~ spl3_140 ),
    inference(avatar_contradiction_clause,[],[f45822])).

fof(f45822,plain,
    ( $false
    | spl3_100
    | ~ spl3_140 ),
    inference(subsumption_resolution,[],[f44941,f45804])).

fof(f44941,plain,
    ( k1_xboole_0 != sK0
    | spl3_100 ),
    inference(superposition,[],[f44919,f8900])).

fof(f44919,plain,
    ( ! [X14] : k1_xboole_0 != k2_xboole_0(k3_xboole_0(sK0,sK1),X14)
    | spl3_100 ),
    inference(resolution,[],[f44134,f25694])).

fof(f45821,plain,
    ( spl3_114
    | ~ spl3_140 ),
    inference(avatar_contradiction_clause,[],[f45820])).

fof(f45820,plain,
    ( $false
    | spl3_114
    | ~ spl3_140 ),
    inference(subsumption_resolution,[],[f44966,f45804])).

fof(f44966,plain,
    ( k1_xboole_0 != sK0
    | spl3_114 ),
    inference(superposition,[],[f44935,f4322])).

fof(f44935,plain,
    ( ! [X0] : k1_xboole_0 != k2_xboole_0(X0,k3_xboole_0(sK0,sK2))
    | spl3_114 ),
    inference(superposition,[],[f44918,f11923])).

fof(f45819,plain,
    ( spl3_100
    | ~ spl3_140 ),
    inference(avatar_contradiction_clause,[],[f45818])).

fof(f45818,plain,
    ( $false
    | spl3_100
    | ~ spl3_140 ),
    inference(subsumption_resolution,[],[f44975,f45804])).

fof(f44975,plain,
    ( k1_xboole_0 != sK0
    | spl3_100 ),
    inference(superposition,[],[f44944,f4322])).

fof(f44944,plain,
    ( ! [X0] : k1_xboole_0 != k2_xboole_0(X0,k3_xboole_0(sK0,sK1))
    | spl3_100 ),
    inference(superposition,[],[f44919,f11923])).

fof(f45817,plain,
    ( spl3_125
    | ~ spl3_140 ),
    inference(avatar_contradiction_clause,[],[f45816])).

fof(f45816,plain,
    ( $false
    | spl3_125
    | ~ spl3_140 ),
    inference(subsumption_resolution,[],[f45044,f45804])).

fof(f45044,plain,
    ( k1_xboole_0 != sK0
    | spl3_125 ),
    inference(resolution,[],[f43223,f43106])).

fof(f43106,plain,(
    ! [X50,X51] :
      ( r1_tarski(k4_xboole_0(X50,X51),k1_xboole_0)
      | k1_xboole_0 != X50 ) ),
    inference(superposition,[],[f22558,f534])).

fof(f43223,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | spl3_125 ),
    inference(avatar_component_clause,[],[f43222])).

fof(f45815,plain,
    ( spl3_125
    | ~ spl3_140 ),
    inference(avatar_contradiction_clause,[],[f45814])).

fof(f45814,plain,
    ( $false
    | spl3_125
    | ~ spl3_140 ),
    inference(subsumption_resolution,[],[f45045,f45804])).

fof(f45045,plain,
    ( k1_xboole_0 != sK0
    | spl3_125 ),
    inference(resolution,[],[f43223,f44059])).

fof(f44059,plain,(
    ! [X14,X15,X13] :
      ( r1_tarski(k4_xboole_0(X13,X14),X15)
      | k1_xboole_0 != X13 ) ),
    inference(superposition,[],[f43879,f268])).

fof(f45813,plain,
    ( spl3_125
    | ~ spl3_140 ),
    inference(avatar_contradiction_clause,[],[f45812])).

fof(f45812,plain,
    ( $false
    | spl3_125
    | ~ spl3_140 ),
    inference(subsumption_resolution,[],[f45053,f45804])).

fof(f45053,plain,
    ( k1_xboole_0 != sK0
    | spl3_125 ),
    inference(superposition,[],[f45046,f4330])).

fof(f45046,plain,
    ( ! [X0] : k1_xboole_0 != k2_xboole_0(X0,k4_xboole_0(sK0,sK1))
    | spl3_125 ),
    inference(resolution,[],[f43223,f43074])).

fof(f45811,plain,
    ( spl3_125
    | ~ spl3_140 ),
    inference(avatar_contradiction_clause,[],[f45810])).

fof(f45810,plain,
    ( $false
    | spl3_125
    | ~ spl3_140 ),
    inference(subsumption_resolution,[],[f45071,f45804])).

fof(f45071,plain,
    ( k1_xboole_0 != sK0
    | spl3_125 ),
    inference(superposition,[],[f45047,f8902])).

fof(f45047,plain,
    ( ! [X1] : k1_xboole_0 != k2_xboole_0(k4_xboole_0(sK0,sK1),X1)
    | spl3_125 ),
    inference(resolution,[],[f43223,f43073])).

fof(f45806,plain,
    ( spl3_127
    | ~ spl3_140 ),
    inference(avatar_contradiction_clause,[],[f45805])).

fof(f45805,plain,
    ( $false
    | spl3_127
    | ~ spl3_140 ),
    inference(subsumption_resolution,[],[f45804,f43234])).

fof(f43234,plain,
    ( k1_xboole_0 != sK0
    | spl3_127 ),
    inference(avatar_component_clause,[],[f43232])).

fof(f45760,plain,
    ( spl3_127
    | ~ spl3_140 ),
    inference(avatar_contradiction_clause,[],[f45759])).

fof(f45759,plain,
    ( $false
    | spl3_127
    | ~ spl3_140 ),
    inference(subsumption_resolution,[],[f45677,f43234])).

fof(f45677,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_140 ),
    inference(superposition,[],[f38,f45597])).

fof(f45755,plain,
    ( spl3_127
    | ~ spl3_140 ),
    inference(avatar_contradiction_clause,[],[f45754])).

fof(f45754,plain,
    ( $false
    | spl3_127
    | ~ spl3_140 ),
    inference(subsumption_resolution,[],[f45654,f43234])).

fof(f45654,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_140 ),
    inference(superposition,[],[f45597,f38])).

fof(f45650,plain,
    ( spl3_141
    | spl3_121
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f43141,f165,f43204,f45648])).

fof(f43141,plain,
    ( ! [X79] :
        ( r1_tarski(sK0,k1_xboole_0)
        | k1_xboole_0 != k2_xboole_0(sK1,k2_xboole_0(sK2,X79)) )
    | ~ spl3_6 ),
    inference(superposition,[],[f22558,f1048])).

fof(f45606,plain,
    ( ~ spl3_140
    | spl3_121 ),
    inference(avatar_split_clause,[],[f45605,f43204,f45595])).

fof(f45605,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k1_xboole_0)
    | spl3_121 ),
    inference(resolution,[],[f43205,f49])).

fof(f43205,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | spl3_121 ),
    inference(avatar_component_clause,[],[f43204])).

fof(f45598,plain,
    ( spl3_140
    | ~ spl3_121 ),
    inference(avatar_split_clause,[],[f45592,f43204,f45595])).

fof(f45592,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_121 ),
    inference(resolution,[],[f43206,f50])).

fof(f43206,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl3_121 ),
    inference(avatar_component_clause,[],[f43204])).

fof(f45590,plain,
    ( spl3_139
    | spl3_121
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f43138,f996,f43204,f45588])).

fof(f43138,plain,
    ( ! [X77] :
        ( r1_tarski(sK0,k1_xboole_0)
        | k1_xboole_0 != k2_xboole_0(k2_xboole_0(sK1,sK2),X77) )
    | ~ spl3_28 ),
    inference(superposition,[],[f22558,f1059])).

fof(f45586,plain,
    ( spl3_135
    | spl3_126
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f43122,f170,f43227,f45003])).

fof(f45003,plain,
    ( spl3_135
  <=> ! [X64] : k1_xboole_0 != k2_xboole_0(sK2,X64) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_135])])).

fof(f43122,plain,
    ( ! [X65] :
        ( r1_tarski(k4_xboole_0(sK1,sK0),k1_xboole_0)
        | k1_xboole_0 != k2_xboole_0(sK2,X65) )
    | ~ spl3_7 ),
    inference(superposition,[],[f22558,f993])).

fof(f993,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK2,X3))
    | ~ spl3_7 ),
    inference(resolution,[],[f960,f50])).

fof(f45585,plain,
    ( ~ spl3_138
    | spl3_125 ),
    inference(avatar_split_clause,[],[f45059,f43222,f45582])).

fof(f45582,plain,
    ( spl3_138
  <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_138])])).

fof(f45059,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | spl3_125 ),
    inference(superposition,[],[f45046,f1592])).

fof(f45086,plain,
    ( ~ spl3_137
    | spl3_125 ),
    inference(avatar_split_clause,[],[f45052,f43222,f45083])).

fof(f45083,plain,
    ( spl3_137
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_137])])).

fof(f45052,plain,
    ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | spl3_125 ),
    inference(resolution,[],[f43223,f49])).

fof(f45068,plain,
    ( ~ spl3_136
    | spl3_125 ),
    inference(avatar_split_clause,[],[f45060,f43222,f45065])).

fof(f45065,plain,
    ( spl3_136
  <=> k1_xboole_0 = k5_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_136])])).

fof(f45060,plain,
    ( k1_xboole_0 != k5_xboole_0(sK1,sK0)
    | spl3_125 ),
    inference(superposition,[],[f45046,f47])).

fof(f45015,plain,
    ( ~ spl3_115
    | spl3_119 ),
    inference(avatar_contradiction_clause,[],[f45014])).

fof(f45014,plain,
    ( $false
    | ~ spl3_115
    | spl3_119 ),
    inference(subsumption_resolution,[],[f45013,f26382])).

fof(f26382,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_119 ),
    inference(avatar_component_clause,[],[f26380])).

fof(f26380,plain,
    ( spl3_119
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_119])])).

fof(f45013,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_115 ),
    inference(resolution,[],[f25775,f50])).

fof(f25775,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_115 ),
    inference(avatar_component_clause,[],[f25773])).

fof(f25773,plain,
    ( spl3_115
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_115])])).

fof(f45011,plain,
    ( spl3_115
    | ~ spl3_125 ),
    inference(avatar_split_clause,[],[f45009,f43222,f25773])).

fof(f45009,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_125 ),
    inference(forward_demodulation,[],[f45006,f1111])).

fof(f45006,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,k1_xboole_0))
    | ~ spl3_125 ),
    inference(resolution,[],[f43224,f54])).

fof(f43224,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl3_125 ),
    inference(avatar_component_clause,[],[f43222])).

fof(f45005,plain,
    ( spl3_135
    | spl3_125
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f43121,f165,f43222,f45003])).

fof(f43121,plain,
    ( ! [X64] :
        ( r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0)
        | k1_xboole_0 != k2_xboole_0(sK2,X64) )
    | ~ spl3_6 ),
    inference(superposition,[],[f22558,f989])).

fof(f989,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK2,X3))
    | ~ spl3_6 ),
    inference(resolution,[],[f959,f50])).

fof(f45001,plain,
    ( ~ spl3_131
    | spl3_128
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f43108,f711,f43236,f43784])).

fof(f43784,plain,
    ( spl3_131
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_131])])).

fof(f711,plain,
    ( spl3_25
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f43108,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),k1_xboole_0)
    | k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | ~ spl3_25 ),
    inference(superposition,[],[f22558,f713])).

fof(f713,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k3_xboole_0(sK0,sK1))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f711])).

fof(f45000,plain,
    ( ~ spl3_131
    | spl3_130
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f43107,f706,f43245,f43784])).

fof(f706,plain,
    ( spl3_24
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f43107,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k1_xboole_0)
    | k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | ~ spl3_24 ),
    inference(superposition,[],[f22558,f708])).

fof(f708,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK1))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f706])).

fof(f43802,plain,
    ( ~ spl3_134
    | spl3_114 ),
    inference(avatar_split_clause,[],[f43778,f25769,f43799])).

fof(f43778,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | spl3_114 ),
    inference(resolution,[],[f43772,f25771])).

fof(f43772,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(forward_demodulation,[],[f43664,f1111])).

fof(f43664,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k2_xboole_0(X1,k1_xboole_0)) ) ),
    inference(resolution,[],[f43106,f54])).

fof(f43797,plain,
    ( ~ spl3_133
    | spl3_108 ),
    inference(avatar_split_clause,[],[f43777,f25736,f43794])).

fof(f25736,plain,
    ( spl3_108
  <=> r1_tarski(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_108])])).

fof(f43777,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK2)
    | spl3_108 ),
    inference(resolution,[],[f43772,f25738])).

fof(f25738,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK0)
    | spl3_108 ),
    inference(avatar_component_clause,[],[f25736])).

fof(f43792,plain,
    ( ~ spl3_132
    | spl3_3 ),
    inference(avatar_split_clause,[],[f43780,f66,f43789])).

fof(f43789,plain,
    ( spl3_132
  <=> k1_xboole_0 = k5_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_132])])).

fof(f43780,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK1)
    | spl3_3 ),
    inference(resolution,[],[f43772,f68])).

fof(f43787,plain,
    ( ~ spl3_131
    | spl3_100 ),
    inference(avatar_split_clause,[],[f43779,f25692,f43784])).

fof(f43779,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | spl3_100 ),
    inference(resolution,[],[f43772,f25694])).

fof(f43248,plain,
    ( ~ spl3_129
    | spl3_130
    | ~ spl3_85 ),
    inference(avatar_split_clause,[],[f43183,f15056,f43245,f43241])).

fof(f43183,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k1_xboole_0)
    | k1_xboole_0 != sK1
    | ~ spl3_85 ),
    inference(forward_demodulation,[],[f43182,f78])).

fof(f43182,plain,
    ( r1_tarski(k5_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)),k1_xboole_0)
    | k1_xboole_0 != sK1
    | ~ spl3_85 ),
    inference(inner_rewriting,[],[f43104])).

fof(f43104,plain,
    ( r1_tarski(k5_xboole_0(sK1,k4_xboole_0(sK0,sK2)),k1_xboole_0)
    | k1_xboole_0 != sK1
    | ~ spl3_85 ),
    inference(superposition,[],[f22558,f15058])).

fof(f43239,plain,
    ( ~ spl3_127
    | spl3_128
    | ~ spl3_83 ),
    inference(avatar_split_clause,[],[f43181,f14842,f43236,f43232])).

fof(f43181,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),k1_xboole_0)
    | k1_xboole_0 != sK0
    | ~ spl3_83 ),
    inference(forward_demodulation,[],[f43180,f78])).

fof(f43180,plain,
    ( r1_tarski(k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)),k1_xboole_0)
    | k1_xboole_0 != sK0
    | ~ spl3_83 ),
    inference(inner_rewriting,[],[f43103])).

fof(f43103,plain,
    ( r1_tarski(k5_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k1_xboole_0)
    | k1_xboole_0 != sK0
    | ~ spl3_83 ),
    inference(superposition,[],[f22558,f14844])).

fof(f43230,plain,
    ( ~ spl3_124
    | spl3_126
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f43179,f5140,f43227,f43218])).

fof(f5140,plain,
    ( spl3_47
  <=> k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(sK1,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f43179,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK0),k1_xboole_0)
    | k1_xboole_0 != sK2
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f43178,f78])).

fof(f43178,plain,
    ( r1_tarski(k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)),k1_xboole_0)
    | k1_xboole_0 != sK2
    | ~ spl3_47 ),
    inference(inner_rewriting,[],[f43102])).

fof(f43102,plain,
    ( r1_tarski(k5_xboole_0(sK2,k4_xboole_0(sK1,sK0)),k1_xboole_0)
    | k1_xboole_0 != sK2
    | ~ spl3_47 ),
    inference(superposition,[],[f22558,f5142])).

fof(f5142,plain,
    ( k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(sK1,sK0)),sK2)
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f5140])).

fof(f43225,plain,
    ( ~ spl3_124
    | spl3_125
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f43177,f5135,f43222,f43218])).

fof(f5135,plain,
    ( spl3_46
  <=> k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f43177,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 != sK2
    | ~ spl3_46 ),
    inference(forward_demodulation,[],[f43176,f78])).

fof(f43176,plain,
    ( r1_tarski(k5_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)),k1_xboole_0)
    | k1_xboole_0 != sK2
    | ~ spl3_46 ),
    inference(inner_rewriting,[],[f43101])).

fof(f43101,plain,
    ( r1_tarski(k5_xboole_0(sK2,k4_xboole_0(sK0,sK1)),k1_xboole_0)
    | k1_xboole_0 != sK2
    | ~ spl3_46 ),
    inference(superposition,[],[f22558,f5137])).

fof(f5137,plain,
    ( k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(sK0,sK1)),sK2)
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f5135])).

fof(f43216,plain,
    ( ~ spl3_122
    | spl3_123
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f43156,f1001,f43213,f43209])).

fof(f43156,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 != k2_xboole_0(sK0,sK2)
    | ~ spl3_29 ),
    inference(superposition,[],[f22558,f1003])).

fof(f43207,plain,
    ( ~ spl3_120
    | spl3_121
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f43140,f996,f43204,f43200])).

fof(f43140,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | k1_xboole_0 != k2_xboole_0(sK1,sK2)
    | ~ spl3_28 ),
    inference(superposition,[],[f22558,f998])).

fof(f26383,plain,
    ( ~ spl3_119
    | ~ spl3_20
    | spl3_117 ),
    inference(avatar_split_clause,[],[f26378,f26369,f386,f26380])).

fof(f386,plain,
    ( spl3_20
  <=> k4_xboole_0(sK0,sK1) = k3_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f26369,plain,
    ( spl3_117
  <=> k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_117])])).

fof(f26378,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | ~ spl3_20
    | spl3_117 ),
    inference(superposition,[],[f26371,f388])).

fof(f388,plain,
    ( k4_xboole_0(sK0,sK1) = k3_xboole_0(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f386])).

fof(f26371,plain,
    ( k1_xboole_0 != k3_xboole_0(sK2,k4_xboole_0(sK0,sK1))
    | spl3_117 ),
    inference(avatar_component_clause,[],[f26369])).

fof(f26377,plain,
    ( ~ spl3_118
    | spl3_116 ),
    inference(avatar_split_clause,[],[f26367,f26362,f26374])).

fof(f26374,plain,
    ( spl3_118
  <=> k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_118])])).

fof(f26362,plain,
    ( spl3_116
  <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_116])])).

fof(f26367,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,k4_xboole_0(sK2,sK1))
    | spl3_116 ),
    inference(superposition,[],[f26364,f51])).

fof(f26364,plain,
    ( k1_xboole_0 != k4_xboole_0(k3_xboole_0(sK0,sK2),sK1)
    | spl3_116 ),
    inference(avatar_component_clause,[],[f26362])).

fof(f26372,plain,
    ( ~ spl3_117
    | spl3_116 ),
    inference(avatar_split_clause,[],[f26366,f26362,f26369])).

fof(f26366,plain,
    ( k1_xboole_0 != k3_xboole_0(sK2,k4_xboole_0(sK0,sK1))
    | spl3_116 ),
    inference(superposition,[],[f26364,f1947])).

fof(f26365,plain,
    ( ~ spl3_116
    | spl3_114 ),
    inference(avatar_split_clause,[],[f26226,f25769,f26362])).

fof(f26226,plain,
    ( k1_xboole_0 != k4_xboole_0(k3_xboole_0(sK0,sK2),sK1)
    | spl3_114 ),
    inference(resolution,[],[f25771,f49])).

fof(f25776,plain,
    ( ~ spl3_114
    | spl3_115
    | ~ spl3_75 ),
    inference(avatar_split_clause,[],[f25486,f12916,f25773,f25769])).

fof(f12916,plain,
    ( spl3_75
  <=> sK1 = k2_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).

fof(f25486,plain,
    ( r1_tarski(sK0,sK1)
    | ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
    | ~ spl3_75 ),
    inference(superposition,[],[f931,f12918])).

fof(f12918,plain,
    ( sK1 = k2_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl3_75 ),
    inference(avatar_component_clause,[],[f12916])).

fof(f931,plain,(
    ! [X8,X7,X9] :
      ( r1_tarski(X7,k2_xboole_0(k4_xboole_0(X7,X8),X9))
      | ~ r1_tarski(k3_xboole_0(X7,X8),X9) ) ),
    inference(superposition,[],[f54,f44])).

fof(f25767,plain,
    ( ~ spl3_113
    | ~ spl3_21
    | spl3_111 ),
    inference(avatar_split_clause,[],[f25762,f25753,f391,f25764])).

fof(f25764,plain,
    ( spl3_113
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_113])])).

fof(f391,plain,
    ( spl3_21
  <=> k4_xboole_0(sK1,sK0) = k3_xboole_0(sK2,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f25753,plain,
    ( spl3_111
  <=> k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_111])])).

fof(f25762,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK0)
    | ~ spl3_21
    | spl3_111 ),
    inference(superposition,[],[f25755,f393])).

fof(f393,plain,
    ( k4_xboole_0(sK1,sK0) = k3_xboole_0(sK2,k4_xboole_0(sK1,sK0))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f391])).

fof(f25755,plain,
    ( k1_xboole_0 != k3_xboole_0(sK2,k4_xboole_0(sK1,sK0))
    | spl3_111 ),
    inference(avatar_component_clause,[],[f25753])).

fof(f25761,plain,
    ( ~ spl3_112
    | spl3_110 ),
    inference(avatar_split_clause,[],[f25751,f25746,f25758])).

fof(f25758,plain,
    ( spl3_112
  <=> k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_112])])).

fof(f25746,plain,
    ( spl3_110
  <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_110])])).

fof(f25751,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,k4_xboole_0(sK2,sK0))
    | spl3_110 ),
    inference(superposition,[],[f25748,f51])).

fof(f25748,plain,
    ( k1_xboole_0 != k4_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | spl3_110 ),
    inference(avatar_component_clause,[],[f25746])).

fof(f25756,plain,
    ( ~ spl3_111
    | spl3_110 ),
    inference(avatar_split_clause,[],[f25750,f25746,f25753])).

fof(f25750,plain,
    ( k1_xboole_0 != k3_xboole_0(sK2,k4_xboole_0(sK1,sK0))
    | spl3_110 ),
    inference(superposition,[],[f25748,f1947])).

fof(f25749,plain,
    ( ~ spl3_110
    | spl3_108 ),
    inference(avatar_split_clause,[],[f25744,f25736,f25746])).

fof(f25744,plain,
    ( k1_xboole_0 != k4_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | spl3_108 ),
    inference(resolution,[],[f25738,f49])).

fof(f25743,plain,
    ( ~ spl3_108
    | spl3_109
    | ~ spl3_74 ),
    inference(avatar_split_clause,[],[f25485,f12832,f25740,f25736])).

fof(f25740,plain,
    ( spl3_109
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_109])])).

fof(f25485,plain,
    ( r1_tarski(sK1,sK0)
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl3_74 ),
    inference(superposition,[],[f931,f12834])).

fof(f25734,plain,
    ( spl3_107
    | ~ spl3_100
    | ~ spl3_51 ),
    inference(avatar_split_clause,[],[f25690,f9092,f25692,f25731])).

fof(f25690,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK2)
    | r1_tarski(sK1,sK2)
    | ~ spl3_51 ),
    inference(forward_demodulation,[],[f25488,f40])).

fof(f25488,plain,
    ( r1_tarski(sK1,sK2)
    | ~ r1_tarski(k3_xboole_0(sK1,sK0),sK2)
    | ~ spl3_51 ),
    inference(superposition,[],[f931,f9094])).

fof(f25729,plain,
    ( ~ spl3_106
    | ~ spl3_72
    | spl3_104 ),
    inference(avatar_split_clause,[],[f25724,f25714,f12545,f25726])).

fof(f25714,plain,
    ( spl3_104
  <=> k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_104])])).

fof(f25724,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK2)
    | ~ spl3_72
    | spl3_104 ),
    inference(superposition,[],[f25716,f12547])).

fof(f25716,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl3_104 ),
    inference(avatar_component_clause,[],[f25714])).

fof(f25723,plain,
    ( ~ spl3_105
    | ~ spl3_73
    | spl3_103 ),
    inference(avatar_split_clause,[],[f25718,f25709,f12589,f25720])).

fof(f25720,plain,
    ( spl3_105
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_105])])).

fof(f12589,plain,
    ( spl3_73
  <=> k4_xboole_0(sK0,sK2) = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).

fof(f25709,plain,
    ( spl3_103
  <=> k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_103])])).

fof(f25718,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK2)
    | ~ spl3_73
    | spl3_103 ),
    inference(superposition,[],[f25711,f12591])).

fof(f12591,plain,
    ( k4_xboole_0(sK0,sK2) = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_73 ),
    inference(avatar_component_clause,[],[f12589])).

fof(f25711,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl3_103 ),
    inference(avatar_component_clause,[],[f25709])).

fof(f25717,plain,
    ( ~ spl3_104
    | spl3_102 ),
    inference(avatar_split_clause,[],[f25707,f25702,f25714])).

fof(f25702,plain,
    ( spl3_102
  <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_102])])).

fof(f25707,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl3_102 ),
    inference(superposition,[],[f25704,f51])).

fof(f25704,plain,
    ( k1_xboole_0 != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | spl3_102 ),
    inference(avatar_component_clause,[],[f25702])).

fof(f25712,plain,
    ( ~ spl3_103
    | spl3_102 ),
    inference(avatar_split_clause,[],[f25706,f25702,f25709])).

fof(f25706,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl3_102 ),
    inference(superposition,[],[f25704,f1947])).

fof(f25705,plain,
    ( ~ spl3_102
    | spl3_100 ),
    inference(avatar_split_clause,[],[f25700,f25692,f25702])).

fof(f25700,plain,
    ( k1_xboole_0 != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | spl3_100 ),
    inference(resolution,[],[f25694,f49])).

fof(f25699,plain,
    ( ~ spl3_100
    | spl3_101
    | ~ spl3_50 ),
    inference(avatar_split_clause,[],[f25487,f9087,f25696,f25692])).

fof(f25696,plain,
    ( spl3_101
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_101])])).

fof(f9087,plain,
    ( spl3_50
  <=> sK2 = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f25487,plain,
    ( r1_tarski(sK0,sK2)
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl3_50 ),
    inference(superposition,[],[f931,f9089])).

fof(f9089,plain,
    ( sK2 = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f9087])).

fof(f19544,plain,
    ( spl3_99
    | ~ spl3_87 ),
    inference(avatar_split_clause,[],[f16740,f15791,f19541])).

fof(f19541,plain,
    ( spl3_99
  <=> sK0 = k3_xboole_0(sK0,k2_xboole_0(sK1,k3_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_99])])).

fof(f16740,plain,
    ( sK0 = k3_xboole_0(sK0,k2_xboole_0(sK1,k3_xboole_0(sK0,sK2)))
    | ~ spl3_87 ),
    inference(forward_demodulation,[],[f16686,f38])).

fof(f16686,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(sK1,k3_xboole_0(sK0,sK2)))
    | ~ spl3_87 ),
    inference(superposition,[],[f44,f15793])).

fof(f19530,plain,
    ( spl3_98
    | ~ spl3_86 ),
    inference(avatar_split_clause,[],[f16652,f15786,f19527])).

fof(f19527,plain,
    ( spl3_98
  <=> sK1 = k3_xboole_0(sK1,k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_98])])).

fof(f16652,plain,
    ( sK1 = k3_xboole_0(sK1,k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl3_86 ),
    inference(forward_demodulation,[],[f16598,f38])).

fof(f16598,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl3_86 ),
    inference(superposition,[],[f44,f15788])).

fof(f19525,plain,
    ( spl3_97
    | ~ spl3_85 ),
    inference(avatar_split_clause,[],[f16579,f15056,f19522])).

fof(f19522,plain,
    ( spl3_97
  <=> sK1 = k2_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_97])])).

fof(f16579,plain,
    ( sK1 = k2_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK0,sK2)))
    | ~ spl3_85 ),
    inference(forward_demodulation,[],[f16546,f37])).

fof(f16546,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK0,sK2)))
    | ~ spl3_85 ),
    inference(superposition,[],[f3037,f15058])).

fof(f19390,plain,
    ( spl3_96
    | ~ spl3_83 ),
    inference(avatar_split_clause,[],[f16487,f14842,f19387])).

fof(f19387,plain,
    ( spl3_96
  <=> sK0 = k2_xboole_0(sK0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).

fof(f16487,plain,
    ( sK0 = k2_xboole_0(sK0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_83 ),
    inference(forward_demodulation,[],[f16454,f37])).

fof(f16454,plain,
    ( k5_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_83 ),
    inference(superposition,[],[f3037,f14844])).

fof(f19289,plain,
    ( spl3_95
    | ~ spl3_93 ),
    inference(avatar_split_clause,[],[f19277,f19270,f19286])).

fof(f19286,plain,
    ( spl3_95
  <=> r1_tarski(sK0,k2_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_95])])).

fof(f19270,plain,
    ( spl3_93
  <=> r1_tarski(k4_xboole_0(sK0,sK2),k5_xboole_0(sK2,k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).

fof(f19277,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK0,sK1))))
    | ~ spl3_93 ),
    inference(resolution,[],[f19272,f54])).

fof(f19272,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k5_xboole_0(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl3_93 ),
    inference(avatar_component_clause,[],[f19270])).

fof(f19284,plain,
    ( spl3_94
    | ~ spl3_92 ),
    inference(avatar_split_clause,[],[f19274,f19265,f19281])).

fof(f19281,plain,
    ( spl3_94
  <=> r1_tarski(sK1,k2_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_94])])).

fof(f19265,plain,
    ( spl3_92
  <=> r1_tarski(k4_xboole_0(sK1,sK2),k5_xboole_0(sK2,k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_92])])).

fof(f19274,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK0,sK1))))
    | ~ spl3_92 ),
    inference(resolution,[],[f19267,f54])).

fof(f19267,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),k5_xboole_0(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl3_92 ),
    inference(avatar_component_clause,[],[f19265])).

fof(f19273,plain,
    ( spl3_93
    | ~ spl3_73 ),
    inference(avatar_split_clause,[],[f19175,f12589,f19270])).

fof(f19175,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k5_xboole_0(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f19174,f40])).

fof(f19174,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k5_xboole_0(sK2,k3_xboole_0(sK1,sK0)))
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f18985,f41])).

fof(f18985,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k5_xboole_0(k3_xboole_0(sK1,sK0),sK2))
    | ~ spl3_73 ),
    inference(superposition,[],[f1978,f12591])).

fof(f1978,plain,(
    ! [X17,X18,X16] : r1_tarski(k3_xboole_0(X16,k4_xboole_0(X17,X18)),k5_xboole_0(k3_xboole_0(X16,X17),X18)) ),
    inference(superposition,[],[f43,f51])).

fof(f19268,plain,
    ( spl3_92
    | ~ spl3_72 ),
    inference(avatar_split_clause,[],[f19173,f12545,f19265])).

fof(f19173,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),k5_xboole_0(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl3_72 ),
    inference(forward_demodulation,[],[f18983,f41])).

fof(f18983,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),k5_xboole_0(k3_xboole_0(sK0,sK1),sK2))
    | ~ spl3_72 ),
    inference(superposition,[],[f1978,f12547])).

fof(f19259,plain,
    ( spl3_91
    | ~ spl3_89 ),
    inference(avatar_split_clause,[],[f19247,f19240,f19256])).

fof(f19256,plain,
    ( spl3_91
  <=> r1_tarski(sK1,k2_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_91])])).

fof(f19240,plain,
    ( spl3_89
  <=> r1_tarski(k4_xboole_0(sK1,sK0),k5_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_89])])).

fof(f19247,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK1,sK2))))
    | ~ spl3_89 ),
    inference(resolution,[],[f19242,f54])).

fof(f19242,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK0),k5_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl3_89 ),
    inference(avatar_component_clause,[],[f19240])).

fof(f19254,plain,
    ( spl3_90
    | ~ spl3_88 ),
    inference(avatar_split_clause,[],[f19244,f19235,f19251])).

fof(f19251,plain,
    ( spl3_90
  <=> r1_tarski(sK0,k2_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_90])])).

fof(f19235,plain,
    ( spl3_88
  <=> r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_88])])).

fof(f19244,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK0,sK2))))
    | ~ spl3_88 ),
    inference(resolution,[],[f19237,f54])).

fof(f19237,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK0,sK2)))
    | ~ spl3_88 ),
    inference(avatar_component_clause,[],[f19235])).

fof(f19243,plain,
    ( spl3_89
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f19179,f391,f19240])).

fof(f19179,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK0),k5_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f19178,f40])).

fof(f19178,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK0),k5_xboole_0(sK0,k3_xboole_0(sK2,sK1)))
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f18987,f41])).

fof(f18987,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK0),k5_xboole_0(k3_xboole_0(sK2,sK1),sK0))
    | ~ spl3_21 ),
    inference(superposition,[],[f1978,f393])).

fof(f19238,plain,
    ( spl3_88
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f19177,f386,f19235])).

fof(f19177,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK0,sK2)))
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f19176,f40])).

fof(f19176,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK2,sK0)))
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f18986,f41])).

fof(f18986,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK2,sK0),sK1))
    | ~ spl3_20 ),
    inference(superposition,[],[f1978,f388])).

fof(f15794,plain,
    ( spl3_87
    | ~ spl3_69 ),
    inference(avatar_split_clause,[],[f11860,f11855,f15791])).

fof(f11855,plain,
    ( spl3_69
  <=> r1_tarski(sK0,k2_xboole_0(sK1,k3_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f11860,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,k3_xboole_0(sK0,sK2)))
    | ~ spl3_69 ),
    inference(resolution,[],[f11857,f50])).

fof(f11857,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,k3_xboole_0(sK0,sK2)))
    | ~ spl3_69 ),
    inference(avatar_component_clause,[],[f11855])).

fof(f15789,plain,
    ( spl3_86
    | ~ spl3_67 ),
    inference(avatar_split_clause,[],[f11817,f11812,f15786])).

fof(f11812,plain,
    ( spl3_67
  <=> r1_tarski(sK1,k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f11817,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl3_67 ),
    inference(resolution,[],[f11814,f50])).

fof(f11814,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl3_67 ),
    inference(avatar_component_clause,[],[f11812])).

fof(f15059,plain,
    ( spl3_85
    | ~ spl3_63 ),
    inference(avatar_split_clause,[],[f10223,f10187,f15056])).

fof(f10187,plain,
    ( spl3_63
  <=> r1_tarski(k5_xboole_0(sK1,k4_xboole_0(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f10223,plain,
    ( k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK1,k4_xboole_0(sK0,sK2)),sK1)
    | ~ spl3_63 ),
    inference(resolution,[],[f10189,f50])).

fof(f10189,plain,
    ( r1_tarski(k5_xboole_0(sK1,k4_xboole_0(sK0,sK2)),sK1)
    | ~ spl3_63 ),
    inference(avatar_component_clause,[],[f10187])).

fof(f15053,plain,
    ( spl3_84
    | ~ spl3_62 ),
    inference(avatar_split_clause,[],[f10219,f10175,f15050])).

fof(f15050,plain,
    ( spl3_84
  <=> k2_xboole_0(sK2,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).

fof(f10175,plain,
    ( spl3_62
  <=> sK0 = k3_xboole_0(sK0,k2_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f10219,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK2,sK1))
    | ~ spl3_62 ),
    inference(forward_demodulation,[],[f10195,f3066])).

fof(f10195,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(sK2,sK1)) = k5_xboole_0(k5_xboole_0(sK0,k2_xboole_0(sK2,sK1)),sK0)
    | ~ spl3_62 ),
    inference(superposition,[],[f46,f10177])).

fof(f10177,plain,
    ( sK0 = k3_xboole_0(sK0,k2_xboole_0(sK2,sK1))
    | ~ spl3_62 ),
    inference(avatar_component_clause,[],[f10175])).

fof(f14845,plain,
    ( spl3_83
    | ~ spl3_56 ),
    inference(avatar_split_clause,[],[f9411,f9376,f14842])).

fof(f9376,plain,
    ( spl3_56
  <=> r1_tarski(k5_xboole_0(sK0,k4_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f9411,plain,
    ( k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl3_56 ),
    inference(resolution,[],[f9378,f50])).

fof(f9378,plain,
    ( r1_tarski(k5_xboole_0(sK0,k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f9376])).

fof(f14839,plain,
    ( spl3_82
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f9407,f9364,f14836])).

fof(f14836,plain,
    ( spl3_82
  <=> k2_xboole_0(sK2,sK0) = k2_xboole_0(sK1,k2_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).

fof(f9364,plain,
    ( spl3_55
  <=> sK1 = k3_xboole_0(sK1,k2_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f9407,plain,
    ( k2_xboole_0(sK2,sK0) = k2_xboole_0(sK1,k2_xboole_0(sK2,sK0))
    | ~ spl3_55 ),
    inference(forward_demodulation,[],[f9384,f3066])).

fof(f9384,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK2,sK0)) = k5_xboole_0(k5_xboole_0(sK1,k2_xboole_0(sK2,sK0)),sK1)
    | ~ spl3_55 ),
    inference(superposition,[],[f46,f9366])).

fof(f9366,plain,
    ( sK1 = k3_xboole_0(sK1,k2_xboole_0(sK2,sK0))
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f9364])).

fof(f13671,plain,
    ( spl3_81
    | ~ spl3_68 ),
    inference(avatar_split_clause,[],[f11853,f11847,f13668])).

fof(f11847,plain,
    ( spl3_68
  <=> r1_tarski(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f11853,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))
    | ~ spl3_68 ),
    inference(resolution,[],[f11849,f50])).

fof(f11849,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))
    | ~ spl3_68 ),
    inference(avatar_component_clause,[],[f11847])).

fof(f13666,plain,
    ( spl3_80
    | ~ spl3_66 ),
    inference(avatar_split_clause,[],[f11810,f11804,f13663])).

fof(f11804,plain,
    ( spl3_66
  <=> r1_tarski(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f11810,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2))
    | ~ spl3_66 ),
    inference(resolution,[],[f11806,f50])).

fof(f11806,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2))
    | ~ spl3_66 ),
    inference(avatar_component_clause,[],[f11804])).

fof(f13489,plain,
    ( spl3_79
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f10155,f10067,f13486])).

fof(f10155,plain,
    ( k4_xboole_0(sK0,sK2) = k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl3_61 ),
    inference(superposition,[],[f1325,f10069])).

fof(f1325,plain,(
    ! [X8,X7] : k3_xboole_0(X7,k2_xboole_0(X8,X7)) = X7 ),
    inference(forward_demodulation,[],[f1302,f38])).

fof(f1302,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k1_xboole_0) = k3_xboole_0(X7,k2_xboole_0(X8,X7)) ),
    inference(superposition,[],[f44,f984])).

fof(f13483,plain,
    ( spl3_78
    | ~ spl3_60 ),
    inference(avatar_split_clause,[],[f10143,f10054,f13480])).

fof(f13480,plain,
    ( spl3_78
  <=> k2_xboole_0(sK2,sK1) = k2_xboole_0(k2_xboole_0(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).

fof(f10054,plain,
    ( spl3_60
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f10143,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(k2_xboole_0(sK2,sK1),sK0)
    | ~ spl3_60 ),
    inference(forward_demodulation,[],[f10122,f37])).

fof(f10122,plain,
    ( k5_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0) = k2_xboole_0(k2_xboole_0(sK2,sK1),sK0)
    | ~ spl3_60 ),
    inference(superposition,[],[f3037,f10056])).

fof(f10056,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))
    | ~ spl3_60 ),
    inference(avatar_component_clause,[],[f10054])).

fof(f13366,plain,
    ( spl3_77
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f9346,f9262,f13363])).

fof(f13363,plain,
    ( spl3_77
  <=> k4_xboole_0(sK1,sK2) = k3_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).

fof(f9346,plain,
    ( k4_xboole_0(sK1,sK2) = k3_xboole_0(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl3_54 ),
    inference(superposition,[],[f1325,f9264])).

fof(f13360,plain,
    ( spl3_76
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f9334,f9249,f13357])).

fof(f13357,plain,
    ( spl3_76
  <=> k2_xboole_0(sK2,sK0) = k2_xboole_0(k2_xboole_0(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f9249,plain,
    ( spl3_53
  <=> k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f9334,plain,
    ( k2_xboole_0(sK2,sK0) = k2_xboole_0(k2_xboole_0(sK2,sK0),sK1)
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f9315,f37])).

fof(f9315,plain,
    ( k5_xboole_0(k2_xboole_0(sK2,sK0),k1_xboole_0) = k2_xboole_0(k2_xboole_0(sK2,sK0),sK1)
    | ~ spl3_53 ),
    inference(superposition,[],[f3037,f9251])).

fof(f9251,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f9249])).

fof(f12919,plain,
    ( spl3_75
    | ~ spl3_73 ),
    inference(avatar_split_clause,[],[f12914,f12589,f12916])).

fof(f12914,plain,
    ( sK1 = k2_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f12892,f3066])).

fof(f12892,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK2),sK1) = k5_xboole_0(k5_xboole_0(k4_xboole_0(sK0,sK2),sK1),k4_xboole_0(sK0,sK2))
    | ~ spl3_73 ),
    inference(superposition,[],[f1090,f12591])).

fof(f12835,plain,
    ( spl3_74
    | ~ spl3_72 ),
    inference(avatar_split_clause,[],[f12830,f12545,f12832])).

fof(f12830,plain,
    ( sK0 = k2_xboole_0(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl3_72 ),
    inference(forward_demodulation,[],[f12808,f3066])).

fof(f12808,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),sK0) = k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,sK2),sK0),k4_xboole_0(sK1,sK2))
    | ~ spl3_72 ),
    inference(superposition,[],[f1090,f12547])).

fof(f12592,plain,
    ( spl3_73
    | ~ spl3_59 ),
    inference(avatar_split_clause,[],[f10038,f9976,f12589])).

fof(f10038,plain,
    ( k4_xboole_0(sK0,sK2) = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_59 ),
    inference(forward_demodulation,[],[f10037,f38])).

fof(f10037,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_59 ),
    inference(forward_demodulation,[],[f9987,f40])).

fof(f9987,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) = k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl3_59 ),
    inference(superposition,[],[f44,f9978])).

fof(f12548,plain,
    ( spl3_72
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f9233,f9175,f12545])).

fof(f9233,plain,
    ( k4_xboole_0(sK1,sK2) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f9232,f38])).

fof(f9232,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f9186,f40])).

fof(f9186,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) = k3_xboole_0(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl3_52 ),
    inference(superposition,[],[f44,f9177])).

fof(f11870,plain,
    ( spl3_71
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f8919,f5140,f11867])).

fof(f11867,plain,
    ( spl3_71
  <=> sK2 = k2_xboole_0(sK2,k5_xboole_0(sK2,k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).

fof(f8919,plain,
    ( sK2 = k2_xboole_0(sK2,k5_xboole_0(sK2,k4_xboole_0(sK1,sK0)))
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f8837,f37])).

fof(f8837,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,k5_xboole_0(sK2,k4_xboole_0(sK1,sK0)))
    | ~ spl3_47 ),
    inference(superposition,[],[f3037,f5142])).

fof(f11865,plain,
    ( spl3_70
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f8918,f5135,f11862])).

fof(f11862,plain,
    ( spl3_70
  <=> sK2 = k2_xboole_0(sK2,k5_xboole_0(sK2,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f8918,plain,
    ( sK2 = k2_xboole_0(sK2,k5_xboole_0(sK2,k4_xboole_0(sK0,sK1)))
    | ~ spl3_46 ),
    inference(forward_demodulation,[],[f8836,f37])).

fof(f8836,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,k5_xboole_0(sK2,k4_xboole_0(sK0,sK1)))
    | ~ spl3_46 ),
    inference(superposition,[],[f3037,f5137])).

fof(f11858,plain,
    ( spl3_69
    | ~ spl3_68 ),
    inference(avatar_split_clause,[],[f11851,f11847,f11855])).

fof(f11851,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,k3_xboole_0(sK0,sK2)))
    | ~ spl3_68 ),
    inference(resolution,[],[f11849,f54])).

fof(f11850,plain,
    ( spl3_68
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f11829,f9961,f11847])).

fof(f11829,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))
    | ~ spl3_57 ),
    inference(superposition,[],[f9966,f44])).

fof(f11815,plain,
    ( spl3_67
    | ~ spl3_66 ),
    inference(avatar_split_clause,[],[f11808,f11804,f11812])).

fof(f11808,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl3_66 ),
    inference(resolution,[],[f11806,f54])).

fof(f11807,plain,
    ( spl3_66
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f11786,f9072,f11804])).

fof(f11786,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2))
    | ~ spl3_48 ),
    inference(superposition,[],[f9077,f44])).

fof(f11692,plain,
    ( spl3_65
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f9882,f1062,f11689])).

fof(f11689,plain,
    ( spl3_65
  <=> k2_xboole_0(sK0,sK2) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f1062,plain,
    ( spl3_33
  <=> sK1 = k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f9882,plain,
    ( k2_xboole_0(sK0,sK2) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | ~ spl3_33 ),
    inference(superposition,[],[f8969,f1064])).

fof(f1064,plain,
    ( sK1 = k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f1062])).

fof(f8969,plain,(
    ! [X2,X1] : k2_xboole_0(k3_xboole_0(X2,X1),X1) = X1 ),
    inference(superposition,[],[f8900,f40])).

fof(f11687,plain,
    ( spl3_64
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f9875,f1054,f11684])).

fof(f11684,plain,
    ( spl3_64
  <=> k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f1054,plain,
    ( spl3_32
  <=> sK0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f9875,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_32 ),
    inference(superposition,[],[f8969,f1056])).

fof(f1056,plain,
    ( sK0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f1054])).

fof(f10190,plain,
    ( spl3_63
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f10161,f10067,f10187])).

fof(f10161,plain,
    ( r1_tarski(k5_xboole_0(sK1,k4_xboole_0(sK0,sK2)),sK1)
    | ~ spl3_61 ),
    inference(superposition,[],[f3056,f10069])).

fof(f3056,plain,(
    ! [X17,X18] : r1_tarski(k5_xboole_0(X17,X18),k2_xboole_0(X17,X18)) ),
    inference(superposition,[],[f917,f3034])).

fof(f917,plain,(
    ! [X6,X5] : r1_tarski(X5,k2_xboole_0(X6,k5_xboole_0(X6,X5))) ),
    inference(resolution,[],[f54,f98])).

fof(f10178,plain,
    ( spl3_62
    | ~ spl3_60 ),
    inference(avatar_split_clause,[],[f10130,f10054,f10175])).

fof(f10130,plain,
    ( sK0 = k3_xboole_0(sK0,k2_xboole_0(sK2,sK1))
    | ~ spl3_60 ),
    inference(forward_demodulation,[],[f10082,f38])).

fof(f10082,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(sK2,sK1))
    | ~ spl3_60 ),
    inference(superposition,[],[f44,f10056])).

fof(f10070,plain,
    ( spl3_61
    | ~ spl3_59 ),
    inference(avatar_split_clause,[],[f10052,f9976,f10067])).

fof(f10052,plain,
    ( sK1 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_59 ),
    inference(forward_demodulation,[],[f10027,f37])).

fof(f10027,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_59 ),
    inference(superposition,[],[f3037,f9978])).

fof(f10057,plain,
    ( spl3_60
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f9974,f9969,f10054])).

fof(f9969,plain,
    ( spl3_58
  <=> r1_tarski(sK0,k2_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f9974,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))
    | ~ spl3_58 ),
    inference(resolution,[],[f9971,f50])).

fof(f9971,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK2,sK1))
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f9969])).

fof(f9979,plain,
    ( spl3_59
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f9967,f9961,f9976])).

fof(f9967,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl3_57 ),
    inference(resolution,[],[f9963,f50])).

fof(f9972,plain,
    ( spl3_58
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f9892,f706,f9969])).

fof(f9892,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK2,sK1))
    | ~ spl3_24 ),
    inference(superposition,[],[f1864,f8969])).

fof(f1864,plain,
    ( ! [X0] : r1_tarski(sK0,k2_xboole_0(sK2,k2_xboole_0(k3_xboole_0(sK0,sK1),X0)))
    | ~ spl3_24 ),
    inference(resolution,[],[f954,f54])).

fof(f954,plain,
    ( ! [X23] : r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),X23))
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f937,f294])).

fof(f937,plain,
    ( ! [X23] :
        ( ~ r1_tarski(k1_xboole_0,X23)
        | r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),X23)) )
    | ~ spl3_24 ),
    inference(superposition,[],[f54,f708])).

fof(f9964,plain,
    ( spl3_57
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f9894,f706,f9961])).

fof(f9894,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl3_24 ),
    inference(superposition,[],[f954,f8969])).

fof(f9379,plain,
    ( spl3_56
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f9352,f9262,f9376])).

fof(f9352,plain,
    ( r1_tarski(k5_xboole_0(sK0,k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl3_54 ),
    inference(superposition,[],[f3056,f9264])).

fof(f9367,plain,
    ( spl3_55
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f9321,f9249,f9364])).

fof(f9321,plain,
    ( sK1 = k3_xboole_0(sK1,k2_xboole_0(sK2,sK0))
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f9277,f38])).

fof(f9277,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,k2_xboole_0(sK2,sK0))
    | ~ spl3_53 ),
    inference(superposition,[],[f44,f9251])).

fof(f9265,plain,
    ( spl3_54
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f9247,f9175,f9262])).

fof(f9247,plain,
    ( sK0 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f9224,f37])).

fof(f9224,plain,
    ( k5_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_52 ),
    inference(superposition,[],[f3037,f9177])).

fof(f9252,plain,
    ( spl3_53
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f9085,f9080,f9249])).

fof(f9080,plain,
    ( spl3_49
  <=> r1_tarski(sK1,k2_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f9085,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))
    | ~ spl3_49 ),
    inference(resolution,[],[f9082,f50])).

fof(f9082,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK2,sK0))
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f9080])).

fof(f9178,plain,
    ( spl3_52
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f9078,f9072,f9175])).

fof(f9078,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl3_48 ),
    inference(resolution,[],[f9074,f50])).

fof(f9095,plain,
    ( spl3_51
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f9001,f391,f9092])).

fof(f9001,plain,
    ( sK2 = k2_xboole_0(k4_xboole_0(sK1,sK0),sK2)
    | ~ spl3_21 ),
    inference(superposition,[],[f8900,f393])).

fof(f9090,plain,
    ( spl3_50
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f9000,f386,f9087])).

fof(f9000,plain,
    ( sK2 = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_20 ),
    inference(superposition,[],[f8900,f388])).

fof(f9083,plain,
    ( spl3_49
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f9003,f711,f9080])).

fof(f9003,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK2,sK0))
    | ~ spl3_25 ),
    inference(superposition,[],[f1869,f8900])).

fof(f1869,plain,
    ( ! [X0] : r1_tarski(sK1,k2_xboole_0(sK2,k2_xboole_0(k3_xboole_0(sK0,sK1),X0)))
    | ~ spl3_25 ),
    inference(resolution,[],[f955,f54])).

fof(f955,plain,
    ( ! [X24] : r1_tarski(k4_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),X24))
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f938,f294])).

fof(f938,plain,
    ( ! [X24] :
        ( ~ r1_tarski(k1_xboole_0,X24)
        | r1_tarski(k4_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),X24)) )
    | ~ spl3_25 ),
    inference(superposition,[],[f54,f713])).

fof(f9075,plain,
    ( spl3_48
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f9005,f711,f9072])).

fof(f9005,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl3_25 ),
    inference(superposition,[],[f955,f8900])).

fof(f5143,plain,
    ( spl3_47
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f4504,f4497,f5140])).

fof(f4497,plain,
    ( spl3_41
  <=> r1_tarski(k5_xboole_0(sK2,k4_xboole_0(sK1,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f4504,plain,
    ( k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(sK1,sK0)),sK2)
    | ~ spl3_41 ),
    inference(resolution,[],[f4499,f50])).

fof(f4499,plain,
    ( r1_tarski(k5_xboole_0(sK2,k4_xboole_0(sK1,sK0)),sK2)
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f4497])).

fof(f5138,plain,
    ( spl3_46
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f4502,f4492,f5135])).

fof(f4492,plain,
    ( spl3_40
  <=> r1_tarski(k5_xboole_0(sK2,k4_xboole_0(sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f4502,plain,
    ( k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(sK0,sK1)),sK2)
    | ~ spl3_40 ),
    inference(resolution,[],[f4494,f50])).

fof(f4494,plain,
    ( r1_tarski(k5_xboole_0(sK2,k4_xboole_0(sK0,sK1)),sK2)
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f4492])).

fof(f4788,plain,
    ( spl3_45
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f4751,f4698,f4785])).

fof(f4785,plain,
    ( spl3_45
  <=> r1_tarski(k5_xboole_0(sK1,k2_xboole_0(sK0,sK2)),k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f4698,plain,
    ( spl3_43
  <=> k2_xboole_0(sK0,sK2) = k2_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f4751,plain,
    ( r1_tarski(k5_xboole_0(sK1,k2_xboole_0(sK0,sK2)),k2_xboole_0(sK0,sK2))
    | ~ spl3_43 ),
    inference(forward_demodulation,[],[f4749,f41])).

fof(f4749,plain,
    ( r1_tarski(k5_xboole_0(k2_xboole_0(sK0,sK2),sK1),k2_xboole_0(sK0,sK2))
    | ~ spl3_43 ),
    inference(superposition,[],[f3056,f4700])).

fof(f4700,plain,
    ( k2_xboole_0(sK0,sK2) = k2_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f4698])).

fof(f4783,plain,
    ( spl3_44
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f4726,f4693,f4780])).

fof(f4780,plain,
    ( spl3_44
  <=> r1_tarski(k5_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f4693,plain,
    ( spl3_42
  <=> k2_xboole_0(sK1,sK2) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f4726,plain,
    ( r1_tarski(k5_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f4724,f41])).

fof(f4724,plain,
    ( r1_tarski(k5_xboole_0(k2_xboole_0(sK1,sK2),sK0),k2_xboole_0(sK1,sK2))
    | ~ spl3_42 ),
    inference(superposition,[],[f3056,f4695])).

fof(f4695,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f4693])).

fof(f4701,plain,
    ( spl3_43
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f4523,f1062,f4698])).

fof(f4523,plain,
    ( k2_xboole_0(sK0,sK2) = k2_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | ~ spl3_33 ),
    inference(superposition,[],[f4326,f1064])).

fof(f4326,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(superposition,[],[f4322,f40])).

fof(f4696,plain,
    ( spl3_42
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f4519,f1054,f4693])).

fof(f4519,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl3_32 ),
    inference(superposition,[],[f4326,f1056])).

fof(f4500,plain,
    ( spl3_41
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f4488,f4417,f4497])).

fof(f4417,plain,
    ( spl3_39
  <=> sK2 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f4488,plain,
    ( r1_tarski(k5_xboole_0(sK2,k4_xboole_0(sK1,sK0)),sK2)
    | ~ spl3_39 ),
    inference(superposition,[],[f3056,f4419])).

fof(f4419,plain,
    ( sK2 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK0))
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f4417])).

fof(f4495,plain,
    ( spl3_40
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f4453,f4412,f4492])).

fof(f4412,plain,
    ( spl3_38
  <=> sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f4453,plain,
    ( r1_tarski(k5_xboole_0(sK2,k4_xboole_0(sK0,sK1)),sK2)
    | ~ spl3_38 ),
    inference(superposition,[],[f3056,f4414])).

fof(f4414,plain,
    ( sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f4412])).

fof(f4420,plain,
    ( spl3_39
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f4347,f391,f4417])).

fof(f4347,plain,
    ( sK2 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK0))
    | ~ spl3_21 ),
    inference(superposition,[],[f4322,f393])).

fof(f4415,plain,
    ( spl3_38
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f4346,f386,f4412])).

fof(f4346,plain,
    ( sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl3_20 ),
    inference(superposition,[],[f4322,f388])).

fof(f4243,plain,
    ( spl3_37
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f4024,f3906,f4240])).

fof(f4024,plain,
    ( sK1 = k3_xboole_0(sK1,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f3987,f38])).

fof(f3987,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl3_35 ),
    inference(superposition,[],[f44,f3908])).

fof(f4234,plain,
    ( spl3_36
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f3969,f3798,f4231])).

fof(f3969,plain,
    ( sK0 = k3_xboole_0(sK0,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f3932,f38])).

fof(f3932,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl3_34 ),
    inference(superposition,[],[f44,f3800])).

fof(f3909,plain,
    ( spl3_35
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f1072,f1043,f3906])).

fof(f1043,plain,
    ( spl3_31
  <=> r1_tarski(sK1,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f1072,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl3_31 ),
    inference(resolution,[],[f1045,f50])).

fof(f1045,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f1043])).

fof(f3801,plain,
    ( spl3_34
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f1070,f1038,f3798])).

fof(f1038,plain,
    ( spl3_30
  <=> r1_tarski(sK0,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f1070,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl3_30 ),
    inference(resolution,[],[f1040,f50])).

fof(f1040,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f1038])).

fof(f1065,plain,
    ( spl3_33
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f1033,f1001,f1062])).

fof(f1033,plain,
    ( sK1 = k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f1024,f38])).

fof(f1024,plain,
    ( k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_29 ),
    inference(superposition,[],[f44,f1003])).

fof(f1057,plain,
    ( spl3_32
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f1017,f996,f1054])).

fof(f1017,plain,
    ( sK0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f1008,f38])).

fof(f1008,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_28 ),
    inference(superposition,[],[f44,f998])).

fof(f1046,plain,
    ( spl3_31
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f915,f699,f1043])).

fof(f699,plain,
    ( spl3_23
  <=> r1_tarski(k4_xboole_0(sK1,sK2),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f915,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl3_23 ),
    inference(resolution,[],[f54,f701])).

fof(f701,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),k3_xboole_0(sK0,sK1))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f699])).

fof(f1041,plain,
    ( spl3_30
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f914,f669,f1038])).

fof(f669,plain,
    ( spl3_22
  <=> r1_tarski(k4_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f914,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl3_22 ),
    inference(resolution,[],[f54,f671])).

fof(f671,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK1))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f669])).

fof(f1004,plain,
    ( spl3_29
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f974,f967,f1001])).

fof(f974,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | ~ spl3_27 ),
    inference(resolution,[],[f969,f50])).

fof(f999,plain,
    ( spl3_28
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f972,f962,f996])).

fof(f972,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_26 ),
    inference(resolution,[],[f964,f50])).

fof(f970,plain,
    ( spl3_27
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f924,f61,f967])).

fof(f924,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK0,sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f54,f63])).

fof(f965,plain,
    ( spl3_26
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f923,f56,f962])).

fof(f923,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f54,f58])).

fof(f714,plain,
    ( spl3_25
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f704,f699,f711])).

fof(f704,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k3_xboole_0(sK0,sK1))
    | ~ spl3_23 ),
    inference(resolution,[],[f701,f50])).

fof(f709,plain,
    ( spl3_24
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f674,f669,f706])).

fof(f674,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK1))
    | ~ spl3_22 ),
    inference(resolution,[],[f671,f50])).

fof(f702,plain,
    ( spl3_23
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f692,f61,f699])).

fof(f692,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),k3_xboole_0(sK0,sK1))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f685,f40])).

fof(f685,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK0))
    | ~ spl3_2 ),
    inference(superposition,[],[f514,f44])).

fof(f672,plain,
    ( spl3_22
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f656,f56,f669])).

fof(f656,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK1))
    | ~ spl3_1 ),
    inference(superposition,[],[f513,f44])).

fof(f394,plain,
    ( spl3_21
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f361,f353,f391])).

fof(f361,plain,
    ( k4_xboole_0(sK1,sK0) = k3_xboole_0(sK2,k4_xboole_0(sK1,sK0))
    | ~ spl3_15 ),
    inference(superposition,[],[f355,f40])).

fof(f389,plain,
    ( spl3_20
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f357,f348,f386])).

fof(f357,plain,
    ( k4_xboole_0(sK0,sK1) = k3_xboole_0(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl3_14 ),
    inference(superposition,[],[f350,f40])).

fof(f384,plain,
    ( spl3_19
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f219,f210,f381])).

fof(f381,plain,
    ( spl3_19
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f210,plain,
    ( spl3_13
  <=> r1_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f219,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK1,sK0)))
    | ~ spl3_13 ),
    inference(resolution,[],[f212,f48])).

fof(f212,plain,
    ( r1_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK1,sK0)))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f210])).

fof(f379,plain,
    ( spl3_18
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f217,f200,f376])).

fof(f376,plain,
    ( spl3_18
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f200,plain,
    ( spl3_11
  <=> r1_tarski(k1_xboole_0,k5_xboole_0(sK2,k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f217,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k4_xboole_0(sK1,sK0)))
    | ~ spl3_11 ),
    inference(resolution,[],[f202,f50])).

fof(f202,plain,
    ( r1_tarski(k1_xboole_0,k5_xboole_0(sK2,k4_xboole_0(sK1,sK0)))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f200])).

fof(f374,plain,
    ( spl3_17
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f216,f195,f371])).

fof(f371,plain,
    ( spl3_17
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f195,plain,
    ( spl3_10
  <=> r1_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f216,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)))
    | ~ spl3_10 ),
    inference(resolution,[],[f197,f48])).

fof(f197,plain,
    ( r1_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f195])).

fof(f369,plain,
    ( spl3_16
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f214,f185,f366])).

fof(f366,plain,
    ( spl3_16
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f185,plain,
    ( spl3_8
  <=> r1_tarski(k1_xboole_0,k5_xboole_0(sK2,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f214,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k4_xboole_0(sK0,sK1)))
    | ~ spl3_8 ),
    inference(resolution,[],[f187,f50])).

fof(f187,plain,
    ( r1_tarski(k1_xboole_0,k5_xboole_0(sK2,k4_xboole_0(sK0,sK1)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f185])).

fof(f356,plain,
    ( spl3_15
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f271,f170,f353])).

fof(f271,plain,
    ( k4_xboole_0(sK1,sK0) = k3_xboole_0(k4_xboole_0(sK1,sK0),sK2)
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f251,f38])).

fof(f251,plain,
    ( k3_xboole_0(k4_xboole_0(sK1,sK0),sK2) = k4_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0)
    | ~ spl3_7 ),
    inference(superposition,[],[f44,f172])).

fof(f351,plain,
    ( spl3_14
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f270,f165,f348])).

fof(f270,plain,
    ( k4_xboole_0(sK0,sK1) = k3_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f250,f38])).

fof(f250,plain,
    ( k3_xboole_0(k4_xboole_0(sK0,sK1),sK2) = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl3_6 ),
    inference(superposition,[],[f44,f167])).

fof(f213,plain,
    ( spl3_13
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f182,f170,f210])).

fof(f182,plain,
    ( r1_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK1,sK0)))
    | ~ spl3_7 ),
    inference(superposition,[],[f42,f172])).

fof(f208,plain,
    ( spl3_12
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f181,f170,f205])).

fof(f205,plain,
    ( spl3_12
  <=> r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f181,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,sK0)),k1_xboole_0)
    | ~ spl3_7 ),
    inference(superposition,[],[f42,f172])).

fof(f203,plain,
    ( spl3_11
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f179,f170,f200])).

fof(f179,plain,
    ( r1_tarski(k1_xboole_0,k5_xboole_0(sK2,k4_xboole_0(sK1,sK0)))
    | ~ spl3_7 ),
    inference(superposition,[],[f98,f172])).

fof(f198,plain,
    ( spl3_10
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f177,f165,f195])).

fof(f177,plain,
    ( r1_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)))
    | ~ spl3_6 ),
    inference(superposition,[],[f42,f167])).

fof(f193,plain,
    ( spl3_9
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f176,f165,f190])).

fof(f190,plain,
    ( spl3_9
  <=> r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f176,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ spl3_6 ),
    inference(superposition,[],[f42,f167])).

fof(f188,plain,
    ( spl3_8
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f174,f165,f185])).

fof(f174,plain,
    ( r1_tarski(k1_xboole_0,k5_xboole_0(sK2,k4_xboole_0(sK0,sK1)))
    | ~ spl3_6 ),
    inference(superposition,[],[f98,f167])).

fof(f173,plain,
    ( spl3_7
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f147,f61,f170])).

fof(f147,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f50,f63])).

fof(f168,plain,
    ( spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f146,f56,f165])).

fof(f146,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_1 ),
    inference(resolution,[],[f50,f58])).

fof(f122,plain,
    ( ~ spl3_5
    | spl3_3 ),
    inference(avatar_split_clause,[],[f117,f66,f119])).

fof(f119,plain,
    ( spl3_5
  <=> k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f117,plain,
    ( k1_xboole_0 != k4_xboole_0(k5_xboole_0(sK0,sK1),sK2)
    | spl3_3 ),
    inference(resolution,[],[f49,f68])).

fof(f93,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f88,f90])).

fof(f90,plain,
    ( spl3_4
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f88,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f86,f38])).

fof(f69,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f34,f66])).

fof(f34,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2)
    & r1_tarski(k4_xboole_0(sK1,sK0),sK2)
    & r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
        & r1_tarski(k4_xboole_0(X1,X0),X2)
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
   => ( ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2)
      & r1_tarski(k4_xboole_0(sK1,sK0),sK2)
      & r1_tarski(k4_xboole_0(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
      & r1_tarski(k4_xboole_0(X1,X0),X2)
      & r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
      & r1_tarski(k4_xboole_0(X1,X0),X2)
      & r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(k4_xboole_0(X1,X0),X2)
          & r1_tarski(k4_xboole_0(X0,X1),X2) )
       => r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k4_xboole_0(X1,X0),X2)
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
     => r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_xboole_1)).

fof(f64,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f33,f61])).

fof(f33,plain,(
    r1_tarski(k4_xboole_0(sK1,sK0),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f32,f56])).

fof(f32,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:19:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (21680)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (21691)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (21686)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (21677)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (21689)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (21692)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (21683)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (21695)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (21694)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (21681)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (21679)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (21678)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (21688)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (21676)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (21687)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.51  % (21684)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.52  % (21690)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.53  % (21693)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 5.36/1.04  % (21680)Time limit reached!
% 5.36/1.04  % (21680)------------------------------
% 5.36/1.04  % (21680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.36/1.04  % (21680)Termination reason: Time limit
% 5.36/1.04  % (21680)Termination phase: Saturation
% 5.36/1.04  
% 5.36/1.04  % (21680)Memory used [KB]: 19701
% 5.36/1.04  % (21680)Time elapsed: 0.600 s
% 5.36/1.04  % (21680)------------------------------
% 5.36/1.04  % (21680)------------------------------
% 12.47/1.92  % (21681)Time limit reached!
% 12.47/1.92  % (21681)------------------------------
% 12.47/1.92  % (21681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.47/1.92  % (21681)Termination reason: Time limit
% 12.47/1.92  % (21681)Termination phase: Saturation
% 12.47/1.92  
% 12.47/1.92  % (21681)Memory used [KB]: 30319
% 12.47/1.92  % (21681)Time elapsed: 1.500 s
% 12.47/1.92  % (21681)------------------------------
% 12.47/1.92  % (21681)------------------------------
% 12.47/1.97  % (21683)Time limit reached!
% 12.47/1.97  % (21683)------------------------------
% 12.47/1.97  % (21683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.47/1.97  % (21683)Termination reason: Time limit
% 12.47/1.97  % (21683)Termination phase: Saturation
% 12.47/1.97  
% 12.47/1.97  % (21683)Memory used [KB]: 45542
% 12.47/1.97  % (21683)Time elapsed: 1.500 s
% 12.47/1.97  % (21683)------------------------------
% 12.47/1.97  % (21683)------------------------------
% 14.92/2.24  % (21678)Time limit reached!
% 14.92/2.24  % (21678)------------------------------
% 14.92/2.24  % (21678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.92/2.24  % (21678)Termination reason: Time limit
% 14.92/2.24  
% 14.92/2.24  % (21678)Memory used [KB]: 36459
% 14.92/2.24  % (21678)Time elapsed: 1.821 s
% 14.92/2.24  % (21678)------------------------------
% 14.92/2.24  % (21678)------------------------------
% 14.92/2.24  % (21676)Refutation found. Thanks to Tanya!
% 14.92/2.24  % SZS status Theorem for theBenchmark
% 14.92/2.24  % SZS output start Proof for theBenchmark
% 14.92/2.24  fof(f51033,plain,(
% 14.92/2.24    $false),
% 14.92/2.24    inference(avatar_sat_refutation,[],[f59,f64,f69,f93,f122,f168,f173,f188,f193,f198,f203,f208,f213,f351,f356,f369,f374,f379,f384,f389,f394,f672,f702,f709,f714,f965,f970,f999,f1004,f1041,f1046,f1057,f1065,f3801,f3909,f4234,f4243,f4415,f4420,f4495,f4500,f4696,f4701,f4783,f4788,f5138,f5143,f9075,f9083,f9090,f9095,f9178,f9252,f9265,f9367,f9379,f9964,f9972,f9979,f10057,f10070,f10178,f10190,f11687,f11692,f11807,f11815,f11850,f11858,f11865,f11870,f12548,f12592,f12835,f12919,f13360,f13366,f13483,f13489,f13666,f13671,f14839,f14845,f15053,f15059,f15789,f15794,f19238,f19243,f19254,f19259,f19268,f19273,f19284,f19289,f19390,f19525,f19530,f19544,f25699,f25705,f25712,f25717,f25723,f25729,f25734,f25743,f25749,f25756,f25761,f25767,f25776,f26365,f26372,f26377,f26383,f43207,f43216,f43225,f43230,f43239,f43248,f43787,f43792,f43797,f43802,f45000,f45001,f45005,f45011,f45015,f45068,f45086,f45585,f45586,f45590,f45598,f45606,f45650,f45755,f45760,f45806,f45811,f45813,f45815,f45817,f45819,f45821,f45823,f45825,f45828,f45830,f45834,f45842,f45851,f46268,f46272,f46342,f46349,f46365,f46371,f46376,f46380,f46388,f46396,f46816,f47040,f47045,f47056,f47061,f47070,f47229,f47249,f47257,f47588,f47789,f47972,f48201,f48309,f48314,f48361,f48588,f48592,f48596,f48600,f48604,f48608,f48612,f48616,f48620,f48622,f48624,f48626,f48634,f48864,f48868,f48872,f48876,f48877,f48878,f48882,f48886,f48890,f48894,f48898,f48899,f48900,f48901,f48905,f48906,f48907,f48908,f48975,f49319,f49325,f49329,f49333,f49337,f49341,f49342,f49347,f49351,f49356,f49360,f49466,f49470,f49474,f49478,f49482,f49486,f50365,f50373,f50458,f50466,f51031])).
% 14.92/2.24  fof(f51031,plain,(
% 14.92/2.24    ~spl3_1 | spl3_3 | ~spl3_51),
% 14.92/2.24    inference(avatar_contradiction_clause,[],[f51030])).
% 14.92/2.24  fof(f51030,plain,(
% 14.92/2.24    $false | (~spl3_1 | spl3_3 | ~spl3_51)),
% 14.92/2.24    inference(subsumption_resolution,[],[f51029,f68])).
% 14.92/2.24  fof(f68,plain,(
% 14.92/2.24    ~r1_tarski(k5_xboole_0(sK0,sK1),sK2) | spl3_3),
% 14.92/2.24    inference(avatar_component_clause,[],[f66])).
% 14.92/2.24  fof(f66,plain,(
% 14.92/2.24    spl3_3 <=> r1_tarski(k5_xboole_0(sK0,sK1),sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 14.92/2.24  fof(f51029,plain,(
% 14.92/2.24    r1_tarski(k5_xboole_0(sK0,sK1),sK2) | (~spl3_1 | ~spl3_51)),
% 14.92/2.24    inference(forward_demodulation,[],[f51019,f9625])).
% 14.92/2.24  fof(f9625,plain,(
% 14.92/2.24    ( ! [X17,X18] : (k5_xboole_0(X17,X18) = k5_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(X18,X17))) )),
% 14.92/2.24    inference(forward_demodulation,[],[f9624,f47])).
% 14.92/2.24  fof(f47,plain,(
% 14.92/2.24    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 14.92/2.24    inference(cnf_transformation,[],[f3])).
% 14.92/2.24  fof(f3,axiom,(
% 14.92/2.24    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 14.92/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 14.92/2.24  fof(f9624,plain,(
% 14.92/2.24    ( ! [X17,X18] : (k5_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(X18,X17)) = k2_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(X18,X17))) )),
% 14.92/2.24    inference(forward_demodulation,[],[f9578,f113])).
% 14.92/2.24  fof(f113,plain,(
% 14.92/2.24    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 14.92/2.24    inference(resolution,[],[f48,f42])).
% 14.92/2.24  fof(f42,plain,(
% 14.92/2.24    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 14.92/2.24    inference(cnf_transformation,[],[f14])).
% 14.92/2.24  fof(f14,axiom,(
% 14.92/2.24    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 14.92/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).
% 14.92/2.24  fof(f48,plain,(
% 14.92/2.24    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 14.92/2.24    inference(cnf_transformation,[],[f26])).
% 14.92/2.24  fof(f26,plain,(
% 14.92/2.24    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 14.92/2.24    inference(ennf_transformation,[],[f23])).
% 14.92/2.24  fof(f23,plain,(
% 14.92/2.24    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 14.92/2.24    inference(unused_predicate_definition_removal,[],[f15])).
% 14.92/2.24  fof(f15,axiom,(
% 14.92/2.24    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 14.92/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 14.92/2.24  fof(f9578,plain,(
% 14.92/2.24    ( ! [X17,X18] : (k5_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(X18,X17)) = k2_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(X17,X18)))) )),
% 14.92/2.24    inference(superposition,[],[f47,f113])).
% 14.92/2.24  fof(f51019,plain,(
% 14.92/2.24    r1_tarski(k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) | (~spl3_1 | ~spl3_51)),
% 14.92/2.24    inference(superposition,[],[f50320,f9094])).
% 14.92/2.24  fof(f9094,plain,(
% 14.92/2.24    sK2 = k2_xboole_0(k4_xboole_0(sK1,sK0),sK2) | ~spl3_51),
% 14.92/2.24    inference(avatar_component_clause,[],[f9092])).
% 14.92/2.24  fof(f9092,plain,(
% 14.92/2.24    spl3_51 <=> sK2 = k2_xboole_0(k4_xboole_0(sK1,sK0),sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 14.92/2.24  fof(f50320,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k5_xboole_0(k4_xboole_0(sK0,sK1),X0),k2_xboole_0(X0,sK2))) ) | ~spl3_1),
% 14.92/2.24    inference(resolution,[],[f50232,f54])).
% 14.92/2.24  fof(f54,plain,(
% 14.92/2.24    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 14.92/2.24    inference(cnf_transformation,[],[f28])).
% 14.92/2.24  fof(f28,plain,(
% 14.92/2.24    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 14.92/2.24    inference(ennf_transformation,[],[f9])).
% 14.92/2.24  fof(f9,axiom,(
% 14.92/2.24    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 14.92/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 14.92/2.24  fof(f50232,plain,(
% 14.92/2.24    ( ! [X2] : (r1_tarski(k4_xboole_0(k5_xboole_0(k4_xboole_0(sK0,sK1),X2),X2),sK2)) ) | ~spl3_1),
% 14.92/2.24    inference(superposition,[],[f49995,f3066])).
% 14.92/2.24  fof(f3066,plain,(
% 14.92/2.24    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 14.92/2.24    inference(superposition,[],[f3042,f3042])).
% 14.92/2.24  fof(f3042,plain,(
% 14.92/2.24    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 14.92/2.24    inference(superposition,[],[f3034,f41])).
% 14.92/2.24  fof(f41,plain,(
% 14.92/2.24    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 14.92/2.24    inference(cnf_transformation,[],[f2])).
% 14.92/2.24  fof(f2,axiom,(
% 14.92/2.24    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 14.92/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 14.92/2.24  fof(f3034,plain,(
% 14.92/2.24    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 14.92/2.24    inference(forward_demodulation,[],[f3008,f78])).
% 14.92/2.24  fof(f78,plain,(
% 14.92/2.24    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 14.92/2.24    inference(superposition,[],[f41,f37])).
% 14.92/2.24  fof(f37,plain,(
% 14.92/2.24    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 14.92/2.24    inference(cnf_transformation,[],[f13])).
% 14.92/2.24  fof(f13,axiom,(
% 14.92/2.24    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 14.92/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 14.92/2.24  fof(f3008,plain,(
% 14.92/2.24    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 14.92/2.24    inference(superposition,[],[f52,f36])).
% 14.92/2.24  fof(f36,plain,(
% 14.92/2.24    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 14.92/2.24    inference(cnf_transformation,[],[f17])).
% 14.92/2.24  fof(f17,axiom,(
% 14.92/2.24    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 14.92/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 14.92/2.24  fof(f52,plain,(
% 14.92/2.24    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 14.92/2.24    inference(cnf_transformation,[],[f16])).
% 14.92/2.24  fof(f16,axiom,(
% 14.92/2.24    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 14.92/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 14.92/2.24  fof(f49995,plain,(
% 14.92/2.24    ( ! [X226] : (r1_tarski(k4_xboole_0(X226,k5_xboole_0(X226,k4_xboole_0(sK0,sK1))),sK2)) ) | ~spl3_1),
% 14.92/2.24    inference(forward_demodulation,[],[f49615,f1111])).
% 14.92/2.24  fof(f1111,plain,(
% 14.92/2.24    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 14.92/2.24    inference(forward_demodulation,[],[f1110,f37])).
% 14.92/2.24  fof(f1110,plain,(
% 14.92/2.24    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,k1_xboole_0)) )),
% 14.92/2.24    inference(forward_demodulation,[],[f1084,f35])).
% 14.92/2.24  fof(f35,plain,(
% 14.92/2.24    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 14.92/2.24    inference(cnf_transformation,[],[f5])).
% 14.92/2.24  fof(f5,axiom,(
% 14.92/2.24    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 14.92/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 14.92/2.24  fof(f1084,plain,(
% 14.92/2.24    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) )),
% 14.92/2.24    inference(superposition,[],[f46,f37])).
% 14.92/2.24  fof(f46,plain,(
% 14.92/2.24    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 14.92/2.24    inference(cnf_transformation,[],[f18])).
% 14.92/2.24  fof(f18,axiom,(
% 14.92/2.24    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 14.92/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 14.92/2.24  fof(f49615,plain,(
% 14.92/2.24    ( ! [X226] : (r1_tarski(k4_xboole_0(X226,k5_xboole_0(X226,k4_xboole_0(sK0,sK1))),k2_xboole_0(sK2,k1_xboole_0))) ) | ~spl3_1),
% 14.92/2.24    inference(superposition,[],[f918,f3054])).
% 14.92/2.24  fof(f3054,plain,(
% 14.92/2.24    ( ! [X14,X13] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X13,k5_xboole_0(X13,X14)),X14)) )),
% 14.92/2.24    inference(superposition,[],[f143,f3034])).
% 14.92/2.24  fof(f143,plain,(
% 14.92/2.24    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2))) )),
% 14.92/2.24    inference(resolution,[],[f50,f43])).
% 14.92/2.24  fof(f43,plain,(
% 14.92/2.24    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 14.92/2.24    inference(cnf_transformation,[],[f19])).
% 14.92/2.24  fof(f19,axiom,(
% 14.92/2.24    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 14.92/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).
% 14.92/2.24  fof(f50,plain,(
% 14.92/2.24    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 14.92/2.24    inference(cnf_transformation,[],[f31])).
% 14.92/2.24  fof(f31,plain,(
% 14.92/2.24    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 14.92/2.24    inference(nnf_transformation,[],[f7])).
% 14.92/2.24  fof(f7,axiom,(
% 14.92/2.24    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 14.92/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 14.92/2.24  fof(f918,plain,(
% 14.92/2.24    ( ! [X7] : (r1_tarski(X7,k2_xboole_0(sK2,k4_xboole_0(X7,k4_xboole_0(sK0,sK1))))) ) | ~spl3_1),
% 14.92/2.24    inference(resolution,[],[f54,f513])).
% 14.92/2.24  fof(f513,plain,(
% 14.92/2.24    ( ! [X10] : (r1_tarski(k4_xboole_0(X10,sK2),k4_xboole_0(X10,k4_xboole_0(sK0,sK1)))) ) | ~spl3_1),
% 14.92/2.24    inference(resolution,[],[f53,f58])).
% 14.92/2.24  fof(f58,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK0,sK1),sK2) | ~spl3_1),
% 14.92/2.24    inference(avatar_component_clause,[],[f56])).
% 14.92/2.24  fof(f56,plain,(
% 14.92/2.24    spl3_1 <=> r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 14.92/2.24  fof(f53,plain,(
% 14.92/2.24    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))) )),
% 14.92/2.24    inference(cnf_transformation,[],[f27])).
% 14.92/2.24  fof(f27,plain,(
% 14.92/2.24    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 14.92/2.24    inference(ennf_transformation,[],[f6])).
% 14.92/2.24  fof(f6,axiom,(
% 14.92/2.24    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 14.92/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).
% 14.92/2.24  fof(f50466,plain,(
% 14.92/2.24    spl3_200 | ~spl3_199),
% 14.92/2.24    inference(avatar_split_clause,[],[f50459,f50455,f50463])).
% 14.92/2.24  fof(f50463,plain,(
% 14.92/2.24    spl3_200 <=> r1_tarski(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_200])])).
% 14.92/2.24  fof(f50455,plain,(
% 14.92/2.24    spl3_199 <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),sK0),sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_199])])).
% 14.92/2.24  fof(f50459,plain,(
% 14.92/2.24    r1_tarski(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) | ~spl3_199),
% 14.92/2.24    inference(resolution,[],[f50457,f54])).
% 14.92/2.24  fof(f50457,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),sK0),sK2) | ~spl3_199),
% 14.92/2.24    inference(avatar_component_clause,[],[f50455])).
% 14.92/2.24  fof(f50458,plain,(
% 14.92/2.24    spl3_199 | ~spl3_2),
% 14.92/2.24    inference(avatar_split_clause,[],[f50440,f61,f50455])).
% 14.92/2.24  fof(f61,plain,(
% 14.92/2.24    spl3_2 <=> r1_tarski(k4_xboole_0(sK1,sK0),sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 14.92/2.24  fof(f50440,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),sK0),sK2) | ~spl3_2),
% 14.92/2.24    inference(superposition,[],[f50253,f3037])).
% 14.92/2.24  fof(f3037,plain,(
% 14.92/2.24    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 14.92/2.24    inference(forward_demodulation,[],[f3015,f1609])).
% 14.92/2.24  fof(f1609,plain,(
% 14.92/2.24    ( ! [X14,X15] : (k5_xboole_0(X15,k3_xboole_0(X14,X15)) = k4_xboole_0(X15,X14)) )),
% 14.92/2.24    inference(forward_demodulation,[],[f1608,f1111])).
% 14.92/2.24  fof(f1608,plain,(
% 14.92/2.24    ( ! [X14,X15] : (k5_xboole_0(X15,k3_xboole_0(X14,X15)) = k2_xboole_0(k4_xboole_0(X15,X14),k1_xboole_0)) )),
% 14.92/2.24    inference(forward_demodulation,[],[f1526,f395])).
% 14.92/2.24  fof(f395,plain,(
% 14.92/2.24    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 14.92/2.24    inference(superposition,[],[f45,f40])).
% 14.92/2.24  fof(f40,plain,(
% 14.92/2.24    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 14.92/2.24    inference(cnf_transformation,[],[f1])).
% 14.92/2.24  fof(f1,axiom,(
% 14.92/2.24    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 14.92/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 14.92/2.24  fof(f45,plain,(
% 14.92/2.24    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 14.92/2.24    inference(cnf_transformation,[],[f10])).
% 14.92/2.24  fof(f10,axiom,(
% 14.92/2.24    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 14.92/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 14.92/2.24  fof(f1526,plain,(
% 14.92/2.24    ( ! [X14,X15] : (k5_xboole_0(X15,k3_xboole_0(X14,X15)) = k2_xboole_0(k4_xboole_0(X15,k3_xboole_0(X14,X15)),k1_xboole_0)) )),
% 14.92/2.24    inference(superposition,[],[f47,f560])).
% 14.92/2.24  fof(f560,plain,(
% 14.92/2.24    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X3,X4),X4)) )),
% 14.92/2.24    inference(resolution,[],[f550,f50])).
% 14.92/2.24  fof(f550,plain,(
% 14.92/2.24    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 14.92/2.24    inference(superposition,[],[f538,f40])).
% 14.92/2.24  fof(f538,plain,(
% 14.92/2.24    ( ! [X4,X5] : (r1_tarski(k3_xboole_0(X4,X5),X4)) )),
% 14.92/2.24    inference(superposition,[],[f524,f44])).
% 14.92/2.24  fof(f44,plain,(
% 14.92/2.24    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 14.92/2.24    inference(cnf_transformation,[],[f11])).
% 14.92/2.24  fof(f11,axiom,(
% 14.92/2.24    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 14.92/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 14.92/2.24  fof(f524,plain,(
% 14.92/2.24    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 14.92/2.24    inference(forward_demodulation,[],[f523,f38])).
% 14.92/2.24  fof(f38,plain,(
% 14.92/2.24    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 14.92/2.24    inference(cnf_transformation,[],[f8])).
% 14.92/2.24  fof(f8,axiom,(
% 14.92/2.24    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 14.92/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 14.92/2.24  fof(f523,plain,(
% 14.92/2.24    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0))) )),
% 14.92/2.24    inference(forward_demodulation,[],[f509,f284])).
% 14.92/2.24  fof(f284,plain,(
% 14.92/2.24    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 14.92/2.24    inference(resolution,[],[f245,f48])).
% 14.92/2.24  fof(f245,plain,(
% 14.92/2.24    ( ! [X3] : (r1_xboole_0(k1_xboole_0,X3)) )),
% 14.92/2.24    inference(forward_demodulation,[],[f241,f114])).
% 14.92/2.24  fof(f114,plain,(
% 14.92/2.24    ( ! [X2] : (k4_xboole_0(X2,k4_xboole_0(k1_xboole_0,X2)) = X2) )),
% 14.92/2.24    inference(resolution,[],[f48,f86])).
% 14.92/2.24  fof(f86,plain,(
% 14.92/2.24    ( ! [X0] : (r1_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0))) )),
% 14.92/2.24    inference(superposition,[],[f42,f38])).
% 14.92/2.24  fof(f241,plain,(
% 14.92/2.24    ( ! [X3] : (r1_xboole_0(k1_xboole_0,k4_xboole_0(X3,k4_xboole_0(k1_xboole_0,X3)))) )),
% 14.92/2.24    inference(superposition,[],[f42,f142])).
% 14.92/2.24  fof(f142,plain,(
% 14.92/2.24    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0)) )),
% 14.92/2.24    inference(resolution,[],[f50,f100])).
% 14.92/2.24  fof(f100,plain,(
% 14.92/2.24    ( ! [X6] : (r1_tarski(k4_xboole_0(k1_xboole_0,X6),X6)) )),
% 14.92/2.24    inference(superposition,[],[f43,f78])).
% 14.92/2.24  fof(f509,plain,(
% 14.92/2.24    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)))) )),
% 14.92/2.24    inference(resolution,[],[f53,f100])).
% 14.92/2.24  fof(f3015,plain,(
% 14.92/2.24    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 14.92/2.24    inference(superposition,[],[f52,f46])).
% 14.92/2.24  fof(f50253,plain,(
% 14.92/2.24    ( ! [X3] : (r1_tarski(k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(sK1,sK0)),X3),sK2)) ) | ~spl3_2),
% 14.92/2.24    inference(superposition,[],[f49997,f3065])).
% 14.92/2.24  fof(f3065,plain,(
% 14.92/2.24    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5) )),
% 14.92/2.24    inference(superposition,[],[f3042,f3034])).
% 14.92/2.24  fof(f49997,plain,(
% 14.92/2.24    ( ! [X230] : (r1_tarski(k4_xboole_0(X230,k5_xboole_0(X230,k4_xboole_0(sK1,sK0))),sK2)) ) | ~spl3_2),
% 14.92/2.24    inference(forward_demodulation,[],[f49619,f1111])).
% 14.92/2.24  fof(f49619,plain,(
% 14.92/2.24    ( ! [X230] : (r1_tarski(k4_xboole_0(X230,k5_xboole_0(X230,k4_xboole_0(sK1,sK0))),k2_xboole_0(sK2,k1_xboole_0))) ) | ~spl3_2),
% 14.92/2.24    inference(superposition,[],[f919,f3054])).
% 14.92/2.24  fof(f919,plain,(
% 14.92/2.24    ( ! [X8] : (r1_tarski(X8,k2_xboole_0(sK2,k4_xboole_0(X8,k4_xboole_0(sK1,sK0))))) ) | ~spl3_2),
% 14.92/2.24    inference(resolution,[],[f54,f514])).
% 14.92/2.24  fof(f514,plain,(
% 14.92/2.24    ( ! [X11] : (r1_tarski(k4_xboole_0(X11,sK2),k4_xboole_0(X11,k4_xboole_0(sK1,sK0)))) ) | ~spl3_2),
% 14.92/2.24    inference(resolution,[],[f53,f63])).
% 14.92/2.24  fof(f63,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK1,sK0),sK2) | ~spl3_2),
% 14.92/2.24    inference(avatar_component_clause,[],[f61])).
% 14.92/2.24  fof(f50373,plain,(
% 14.92/2.24    spl3_198 | ~spl3_197),
% 14.92/2.24    inference(avatar_split_clause,[],[f50366,f50362,f50370])).
% 14.92/2.24  fof(f50370,plain,(
% 14.92/2.24    spl3_198 <=> r1_tarski(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_198])])).
% 14.92/2.24  fof(f50362,plain,(
% 14.92/2.24    spl3_197 <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),sK1),sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_197])])).
% 14.92/2.24  fof(f50366,plain,(
% 14.92/2.24    r1_tarski(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)) | ~spl3_197),
% 14.92/2.24    inference(resolution,[],[f50364,f54])).
% 14.92/2.24  fof(f50364,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),sK1),sK2) | ~spl3_197),
% 14.92/2.24    inference(avatar_component_clause,[],[f50362])).
% 14.92/2.24  fof(f50365,plain,(
% 14.92/2.24    spl3_197 | ~spl3_1),
% 14.92/2.24    inference(avatar_split_clause,[],[f50358,f56,f50362])).
% 14.92/2.24  fof(f50358,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),sK1),sK2) | ~spl3_1),
% 14.92/2.24    inference(forward_demodulation,[],[f50346,f11923])).
% 14.92/2.24  fof(f11923,plain,(
% 14.92/2.24    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k2_xboole_0(X4,X3)) )),
% 14.92/2.24    inference(superposition,[],[f1090,f1085])).
% 14.92/2.24  fof(f1085,plain,(
% 14.92/2.24    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k5_xboole_0(k5_xboole_0(X3,X2),k3_xboole_0(X2,X3))) )),
% 14.92/2.24    inference(superposition,[],[f46,f41])).
% 14.92/2.24  fof(f1090,plain,(
% 14.92/2.24    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X2,X1))) )),
% 14.92/2.24    inference(superposition,[],[f46,f40])).
% 14.92/2.24  fof(f50346,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(k2_xboole_0(sK1,sK0),sK1),sK2) | ~spl3_1),
% 14.92/2.24    inference(superposition,[],[f50233,f3037])).
% 14.92/2.24  fof(f50233,plain,(
% 14.92/2.24    ( ! [X3] : (r1_tarski(k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(sK0,sK1)),X3),sK2)) ) | ~spl3_1),
% 14.92/2.24    inference(superposition,[],[f49995,f3065])).
% 14.92/2.24  fof(f49486,plain,(
% 14.92/2.24    ~spl3_129 | spl3_196 | ~spl3_61),
% 14.92/2.24    inference(avatar_split_clause,[],[f43129,f10067,f49484,f43241])).
% 14.92/2.24  fof(f43241,plain,(
% 14.92/2.24    spl3_129 <=> k1_xboole_0 = sK1),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_129])])).
% 14.92/2.24  fof(f49484,plain,(
% 14.92/2.24    spl3_196 <=> ! [X70] : r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK2),X70),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_196])])).
% 14.92/2.24  fof(f10067,plain,(
% 14.92/2.24    spl3_61 <=> sK1 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 14.92/2.24  fof(f43129,plain,(
% 14.92/2.24    ( ! [X70] : (r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK2),X70),k1_xboole_0) | k1_xboole_0 != sK1) ) | ~spl3_61),
% 14.92/2.24    inference(superposition,[],[f22558,f10790])).
% 14.92/2.24  fof(f10790,plain,(
% 14.92/2.24    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK2),X3),sK1)) ) | ~spl3_61),
% 14.92/2.24    inference(resolution,[],[f10742,f50])).
% 14.92/2.24  fof(f10742,plain,(
% 14.92/2.24    ( ! [X3] : (r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK2),X3),sK1)) ) | ~spl3_61),
% 14.92/2.24    inference(superposition,[],[f10713,f268])).
% 14.92/2.24  fof(f268,plain,(
% 14.92/2.24    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 14.92/2.24    inference(forward_demodulation,[],[f248,f45])).
% 14.92/2.24  fof(f248,plain,(
% 14.92/2.24    ( ! [X2,X3] : (k3_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 14.92/2.24    inference(superposition,[],[f44,f44])).
% 14.92/2.24  fof(f10713,plain,(
% 14.92/2.24    ( ! [X32] : (r1_tarski(k3_xboole_0(k4_xboole_0(sK0,sK2),X32),sK1)) ) | ~spl3_61),
% 14.92/2.24    inference(superposition,[],[f9016,f10069])).
% 14.92/2.24  fof(f10069,plain,(
% 14.92/2.24    sK1 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl3_61),
% 14.92/2.24    inference(avatar_component_clause,[],[f10067])).
% 14.92/2.24  fof(f9016,plain,(
% 14.92/2.24    ( ! [X24,X23,X22] : (r1_tarski(k3_xboole_0(X22,X23),k2_xboole_0(X24,X22))) )),
% 14.92/2.24    inference(superposition,[],[f1268,f8900])).
% 14.92/2.24  fof(f8900,plain,(
% 14.92/2.24    ( ! [X2,X1] : (k2_xboole_0(k3_xboole_0(X1,X2),X1) = X1) )),
% 14.92/2.24    inference(forward_demodulation,[],[f8816,f7437])).
% 14.92/2.24  fof(f7437,plain,(
% 14.92/2.24    ( ! [X8,X7] : (k5_xboole_0(k3_xboole_0(X7,X8),k4_xboole_0(X7,X8)) = X7) )),
% 14.92/2.24    inference(forward_demodulation,[],[f7436,f4330])).
% 14.92/2.24  fof(f4330,plain,(
% 14.92/2.24    ( ! [X8,X9] : (k2_xboole_0(X8,k4_xboole_0(X8,X9)) = X8) )),
% 14.92/2.24    inference(superposition,[],[f4322,f268])).
% 14.92/2.24  fof(f4322,plain,(
% 14.92/2.24    ( ! [X6,X7] : (k2_xboole_0(X6,k3_xboole_0(X6,X7)) = X6) )),
% 14.92/2.24    inference(forward_demodulation,[],[f4296,f3065])).
% 14.92/2.24  fof(f4296,plain,(
% 14.92/2.24    ( ! [X6,X7] : (k2_xboole_0(X6,k3_xboole_0(X6,X7)) = k5_xboole_0(k5_xboole_0(X6,k3_xboole_0(X6,X7)),k3_xboole_0(X6,X7))) )),
% 14.92/2.24    inference(superposition,[],[f46,f422])).
% 14.92/2.24  fof(f422,plain,(
% 14.92/2.24    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 14.92/2.24    inference(forward_demodulation,[],[f402,f44])).
% 14.92/2.24  fof(f402,plain,(
% 14.92/2.24    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 14.92/2.24    inference(superposition,[],[f44,f45])).
% 14.92/2.24  fof(f7436,plain,(
% 14.92/2.24    ( ! [X8,X7] : (k2_xboole_0(X7,k4_xboole_0(X7,X8)) = k5_xboole_0(k3_xboole_0(X7,X8),k4_xboole_0(X7,X8))) )),
% 14.92/2.24    inference(forward_demodulation,[],[f7360,f268])).
% 14.92/2.24  fof(f7360,plain,(
% 14.92/2.24    ( ! [X8,X7] : (k2_xboole_0(X7,k4_xboole_0(X7,X8)) = k5_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X7,k4_xboole_0(X7,X8)))) )),
% 14.92/2.24    inference(superposition,[],[f46,f1559])).
% 14.92/2.24  fof(f1559,plain,(
% 14.92/2.24    ( ! [X4,X5] : (k3_xboole_0(X4,X5) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) )),
% 14.92/2.24    inference(forward_demodulation,[],[f1558,f1111])).
% 14.92/2.24  fof(f1558,plain,(
% 14.92/2.24    ( ! [X4,X5] : (k5_xboole_0(X4,k4_xboole_0(X4,X5)) = k2_xboole_0(k3_xboole_0(X4,X5),k1_xboole_0)) )),
% 14.92/2.24    inference(forward_demodulation,[],[f1498,f534])).
% 14.92/2.24  fof(f534,plain,(
% 14.92/2.24    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),X3)) )),
% 14.92/2.24    inference(resolution,[],[f524,f50])).
% 14.92/2.24  fof(f1498,plain,(
% 14.92/2.24    ( ! [X4,X5] : (k5_xboole_0(X4,k4_xboole_0(X4,X5)) = k2_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X4,X5),X4))) )),
% 14.92/2.24    inference(superposition,[],[f47,f44])).
% 14.92/2.24  fof(f8816,plain,(
% 14.92/2.24    ( ! [X2,X1] : (k5_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X2),X1)) )),
% 14.92/2.24    inference(superposition,[],[f3037,f45])).
% 14.92/2.24  fof(f1268,plain,(
% 14.92/2.24    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2)))) )),
% 14.92/2.24    inference(resolution,[],[f953,f54])).
% 14.92/2.24  fof(f953,plain,(
% 14.92/2.24    ( ! [X21,X22,X20] : (r1_tarski(k4_xboole_0(X20,X21),k2_xboole_0(X20,X22))) )),
% 14.92/2.24    inference(subsumption_resolution,[],[f936,f294])).
% 14.92/2.24  fof(f294,plain,(
% 14.92/2.24    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 14.92/2.24    inference(superposition,[],[f100,f284])).
% 14.92/2.24  fof(f936,plain,(
% 14.92/2.24    ( ! [X21,X22,X20] : (~r1_tarski(k1_xboole_0,X22) | r1_tarski(k4_xboole_0(X20,X21),k2_xboole_0(X20,X22))) )),
% 14.92/2.24    inference(superposition,[],[f54,f534])).
% 14.92/2.24  fof(f22558,plain,(
% 14.92/2.24    ( ! [X8,X9] : (r1_tarski(X9,k4_xboole_0(X9,X8)) | k1_xboole_0 != X8) )),
% 14.92/2.24    inference(forward_demodulation,[],[f22557,f38])).
% 14.92/2.24  fof(f22557,plain,(
% 14.92/2.24    ( ! [X8,X9] : (r1_tarski(k4_xboole_0(X9,k1_xboole_0),k4_xboole_0(X9,X8)) | k1_xboole_0 != X8) )),
% 14.92/2.24    inference(forward_demodulation,[],[f22397,f284])).
% 14.92/2.24  fof(f22397,plain,(
% 14.92/2.24    ( ! [X8,X9] : (k1_xboole_0 != X8 | r1_tarski(k4_xboole_0(X9,k4_xboole_0(k1_xboole_0,X8)),k4_xboole_0(X9,X8))) )),
% 14.92/2.24    inference(superposition,[],[f516,f114])).
% 14.92/2.24  fof(f516,plain,(
% 14.92/2.24    ( ! [X14,X15,X16] : (k1_xboole_0 != k4_xboole_0(X16,X15) | r1_tarski(k4_xboole_0(X14,X15),k4_xboole_0(X14,X16))) )),
% 14.92/2.24    inference(resolution,[],[f53,f49])).
% 14.92/2.24  fof(f49,plain,(
% 14.92/2.24    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 14.92/2.24    inference(cnf_transformation,[],[f31])).
% 14.92/2.24  fof(f49482,plain,(
% 14.92/2.24    ~spl3_127 | spl3_195 | ~spl3_54),
% 14.92/2.24    inference(avatar_split_clause,[],[f43127,f9262,f49480,f43232])).
% 14.92/2.24  fof(f43232,plain,(
% 14.92/2.24    spl3_127 <=> k1_xboole_0 = sK0),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_127])])).
% 14.92/2.24  fof(f49480,plain,(
% 14.92/2.24    spl3_195 <=> ! [X69] : r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK2),X69),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_195])])).
% 14.92/2.24  fof(f9262,plain,(
% 14.92/2.24    spl3_54 <=> sK0 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 14.92/2.24  fof(f43127,plain,(
% 14.92/2.24    ( ! [X69] : (r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK2),X69),k1_xboole_0) | k1_xboole_0 != sK0) ) | ~spl3_54),
% 14.92/2.24    inference(superposition,[],[f22558,f10760])).
% 14.92/2.24  fof(f10760,plain,(
% 14.92/2.24    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X3),sK0)) ) | ~spl3_54),
% 14.92/2.24    inference(resolution,[],[f10727,f50])).
% 14.92/2.24  fof(f10727,plain,(
% 14.92/2.24    ( ! [X3] : (r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK2),X3),sK0)) ) | ~spl3_54),
% 14.92/2.24    inference(superposition,[],[f10712,f268])).
% 14.92/2.24  fof(f10712,plain,(
% 14.92/2.24    ( ! [X31] : (r1_tarski(k3_xboole_0(k4_xboole_0(sK1,sK2),X31),sK0)) ) | ~spl3_54),
% 14.92/2.24    inference(superposition,[],[f9016,f9264])).
% 14.92/2.24  fof(f9264,plain,(
% 14.92/2.24    sK0 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_54),
% 14.92/2.24    inference(avatar_component_clause,[],[f9262])).
% 14.92/2.24  fof(f49478,plain,(
% 14.92/2.24    ~spl3_124 | spl3_194 | ~spl3_48),
% 14.92/2.24    inference(avatar_split_clause,[],[f43100,f9072,f49476,f43218])).
% 14.92/2.24  fof(f43218,plain,(
% 14.92/2.24    spl3_124 <=> k1_xboole_0 = sK2),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_124])])).
% 14.92/2.24  fof(f49476,plain,(
% 14.92/2.24    spl3_194 <=> ! [X48] : r1_tarski(k3_xboole_0(sK1,k4_xboole_0(X48,sK0)),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_194])])).
% 14.92/2.24  fof(f9072,plain,(
% 14.92/2.24    spl3_48 <=> r1_tarski(k4_xboole_0(sK1,sK2),sK0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 14.92/2.24  fof(f43100,plain,(
% 14.92/2.24    ( ! [X48] : (r1_tarski(k3_xboole_0(sK1,k4_xboole_0(X48,sK0)),k1_xboole_0) | k1_xboole_0 != sK2) ) | ~spl3_48),
% 14.92/2.24    inference(superposition,[],[f22558,f26335])).
% 14.92/2.24  fof(f26335,plain,(
% 14.92/2.24    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,k4_xboole_0(X3,sK0)),sK2)) ) | ~spl3_48),
% 14.92/2.24    inference(resolution,[],[f26012,f50])).
% 14.92/2.24  fof(f26012,plain,(
% 14.92/2.24    ( ! [X103] : (r1_tarski(k3_xboole_0(sK1,k4_xboole_0(X103,sK0)),sK2)) ) | ~spl3_48),
% 14.92/2.24    inference(forward_demodulation,[],[f26011,f40])).
% 14.92/2.24  fof(f26011,plain,(
% 14.92/2.24    ( ! [X103] : (r1_tarski(k3_xboole_0(k4_xboole_0(X103,sK0),sK1),sK2)) ) | ~spl3_48),
% 14.92/2.24    inference(forward_demodulation,[],[f25822,f1111])).
% 14.92/2.24  fof(f25822,plain,(
% 14.92/2.24    ( ! [X103] : (r1_tarski(k3_xboole_0(k4_xboole_0(X103,sK0),sK1),k2_xboole_0(sK2,k1_xboole_0))) ) | ~spl3_48),
% 14.92/2.24    inference(resolution,[],[f1982,f12622])).
% 14.92/2.24  fof(f12622,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k3_xboole_0(k4_xboole_0(X0,sK0),k4_xboole_0(sK1,sK2)),k1_xboole_0)) ) | ~spl3_48),
% 14.92/2.24    inference(superposition,[],[f11798,f40])).
% 14.92/2.24  fof(f11798,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k3_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,sK0)),k1_xboole_0)) ) | ~spl3_48),
% 14.92/2.24    inference(forward_demodulation,[],[f11789,f51])).
% 14.92/2.24  fof(f51,plain,(
% 14.92/2.24    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 14.92/2.24    inference(cnf_transformation,[],[f12])).
% 14.92/2.24  fof(f12,axiom,(
% 14.92/2.24    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 14.92/2.24    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 14.92/2.24  fof(f11789,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k4_xboole_0(k3_xboole_0(k4_xboole_0(sK1,sK2),X0),sK0),k1_xboole_0)) ) | ~spl3_48),
% 14.92/2.24    inference(superposition,[],[f9077,f548])).
% 14.92/2.24  fof(f548,plain,(
% 14.92/2.24    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X3,X4),X3)) )),
% 14.92/2.24    inference(resolution,[],[f538,f50])).
% 14.92/2.24  fof(f9077,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,sK0),k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))) ) | ~spl3_48),
% 14.92/2.24    inference(resolution,[],[f9074,f53])).
% 14.92/2.24  fof(f9074,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK1,sK2),sK0) | ~spl3_48),
% 14.92/2.24    inference(avatar_component_clause,[],[f9072])).
% 14.92/2.24  fof(f1982,plain,(
% 14.92/2.24    ( ! [X30,X28,X31,X29] : (~r1_tarski(k3_xboole_0(X28,k4_xboole_0(X29,X30)),X31) | r1_tarski(k3_xboole_0(X28,X29),k2_xboole_0(X30,X31))) )),
% 14.92/2.24    inference(superposition,[],[f54,f51])).
% 14.92/2.24  fof(f49474,plain,(
% 14.92/2.24    ~spl3_124 | spl3_193 | ~spl3_57),
% 14.92/2.24    inference(avatar_split_clause,[],[f43096,f9961,f49472,f43218])).
% 14.92/2.24  fof(f49472,plain,(
% 14.92/2.24    spl3_193 <=> ! [X44] : r1_tarski(k3_xboole_0(sK0,k4_xboole_0(X44,sK1)),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_193])])).
% 14.92/2.24  fof(f9961,plain,(
% 14.92/2.24    spl3_57 <=> r1_tarski(k4_xboole_0(sK0,sK2),sK1)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 14.92/2.24  fof(f43096,plain,(
% 14.92/2.24    ( ! [X44] : (r1_tarski(k3_xboole_0(sK0,k4_xboole_0(X44,sK1)),k1_xboole_0) | k1_xboole_0 != sK2) ) | ~spl3_57),
% 14.92/2.24    inference(superposition,[],[f22558,f26307])).
% 14.92/2.24  fof(f26307,plain,(
% 14.92/2.24    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,k4_xboole_0(X3,sK1)),sK2)) ) | ~spl3_57),
% 14.92/2.24    inference(resolution,[],[f26008,f50])).
% 14.92/2.24  fof(f26008,plain,(
% 14.92/2.24    ( ! [X101] : (r1_tarski(k3_xboole_0(sK0,k4_xboole_0(X101,sK1)),sK2)) ) | ~spl3_57),
% 14.92/2.24    inference(forward_demodulation,[],[f26007,f40])).
% 14.92/2.24  fof(f26007,plain,(
% 14.92/2.24    ( ! [X101] : (r1_tarski(k3_xboole_0(k4_xboole_0(X101,sK1),sK0),sK2)) ) | ~spl3_57),
% 14.92/2.24    inference(forward_demodulation,[],[f25820,f1111])).
% 14.92/2.24  fof(f25820,plain,(
% 14.92/2.24    ( ! [X101] : (r1_tarski(k3_xboole_0(k4_xboole_0(X101,sK1),sK0),k2_xboole_0(sK2,k1_xboole_0))) ) | ~spl3_57),
% 14.92/2.24    inference(resolution,[],[f1982,f12655])).
% 14.92/2.24  fof(f12655,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k3_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(sK0,sK2)),k1_xboole_0)) ) | ~spl3_57),
% 14.92/2.24    inference(superposition,[],[f11841,f40])).
% 14.92/2.24  fof(f11841,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k3_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(X0,sK1)),k1_xboole_0)) ) | ~spl3_57),
% 14.92/2.24    inference(forward_demodulation,[],[f11832,f51])).
% 14.92/2.24  fof(f11832,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k4_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK2),X0),sK1),k1_xboole_0)) ) | ~spl3_57),
% 14.92/2.24    inference(superposition,[],[f9966,f548])).
% 14.92/2.24  fof(f9966,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,sK1),k4_xboole_0(X0,k4_xboole_0(sK0,sK2)))) ) | ~spl3_57),
% 14.92/2.24    inference(resolution,[],[f9963,f53])).
% 14.92/2.24  fof(f9963,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK0,sK2),sK1) | ~spl3_57),
% 14.92/2.24    inference(avatar_component_clause,[],[f9961])).
% 14.92/2.24  fof(f49470,plain,(
% 14.92/2.24    ~spl3_129 | spl3_192 | ~spl3_61),
% 14.92/2.24    inference(avatar_split_clause,[],[f43084,f10067,f49468,f43241])).
% 14.92/2.24  fof(f49468,plain,(
% 14.92/2.24    spl3_192 <=> ! [X32] : r1_tarski(k3_xboole_0(X32,k4_xboole_0(sK0,sK2)),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_192])])).
% 14.92/2.24  fof(f43084,plain,(
% 14.92/2.24    ( ! [X32] : (r1_tarski(k3_xboole_0(X32,k4_xboole_0(sK0,sK2)),k1_xboole_0) | k1_xboole_0 != sK1) ) | ~spl3_61),
% 14.92/2.24    inference(superposition,[],[f22558,f10778])).
% 14.92/2.24  fof(f10778,plain,(
% 14.92/2.24    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,k4_xboole_0(sK0,sK2)),sK1)) ) | ~spl3_61),
% 14.92/2.24    inference(resolution,[],[f10738,f50])).
% 14.92/2.24  fof(f10738,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,k4_xboole_0(sK0,sK2)),sK1)) ) | ~spl3_61),
% 14.92/2.24    inference(superposition,[],[f10713,f40])).
% 14.92/2.24  fof(f49466,plain,(
% 14.92/2.24    ~spl3_127 | spl3_191 | ~spl3_54),
% 14.92/2.24    inference(avatar_split_clause,[],[f43083,f9262,f49464,f43232])).
% 14.92/2.24  fof(f49464,plain,(
% 14.92/2.24    spl3_191 <=> ! [X31] : r1_tarski(k3_xboole_0(X31,k4_xboole_0(sK1,sK2)),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_191])])).
% 14.92/2.24  fof(f43083,plain,(
% 14.92/2.24    ( ! [X31] : (r1_tarski(k3_xboole_0(X31,k4_xboole_0(sK1,sK2)),k1_xboole_0) | k1_xboole_0 != sK0) ) | ~spl3_54),
% 14.92/2.24    inference(superposition,[],[f22558,f10748])).
% 14.92/2.24  fof(f10748,plain,(
% 14.92/2.24    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,k4_xboole_0(sK1,sK2)),sK0)) ) | ~spl3_54),
% 14.92/2.24    inference(resolution,[],[f10723,f50])).
% 14.92/2.24  fof(f10723,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,k4_xboole_0(sK1,sK2)),sK0)) ) | ~spl3_54),
% 14.92/2.24    inference(superposition,[],[f10712,f40])).
% 14.92/2.24  fof(f49360,plain,(
% 14.92/2.24    spl3_190 | spl3_123 | ~spl3_52),
% 14.92/2.24    inference(avatar_split_clause,[],[f43162,f9175,f43213,f49358])).
% 14.92/2.24  fof(f49358,plain,(
% 14.92/2.24    spl3_190 <=> ! [X93] : k1_xboole_0 != k2_xboole_0(sK2,k2_xboole_0(sK0,X93))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_190])])).
% 14.92/2.24  fof(f43213,plain,(
% 14.92/2.24    spl3_123 <=> r1_tarski(sK1,k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_123])])).
% 14.92/2.24  fof(f9175,plain,(
% 14.92/2.24    spl3_52 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 14.92/2.24  fof(f43162,plain,(
% 14.92/2.24    ( ! [X93] : (r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 != k2_xboole_0(sK2,k2_xboole_0(sK0,X93))) ) | ~spl3_52),
% 14.92/2.24    inference(superposition,[],[f22558,f9356])).
% 14.92/2.24  fof(f9356,plain,(
% 14.92/2.24    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK0,X2)))) ) | ~spl3_52),
% 14.92/2.24    inference(resolution,[],[f9253,f50])).
% 14.92/2.24  fof(f9253,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(sK1,k2_xboole_0(sK2,k2_xboole_0(sK0,X0)))) ) | ~spl3_52),
% 14.92/2.24    inference(resolution,[],[f9235,f54])).
% 14.92/2.24  fof(f9235,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,sK2),k2_xboole_0(sK0,X0))) ) | ~spl3_52),
% 14.92/2.24    inference(subsumption_resolution,[],[f9189,f294])).
% 14.92/2.24  fof(f9189,plain,(
% 14.92/2.24    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | r1_tarski(k4_xboole_0(sK1,sK2),k2_xboole_0(sK0,X0))) ) | ~spl3_52),
% 14.92/2.24    inference(superposition,[],[f54,f9177])).
% 14.92/2.24  fof(f9177,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0) | ~spl3_52),
% 14.92/2.24    inference(avatar_component_clause,[],[f9175])).
% 14.92/2.24  fof(f49356,plain,(
% 14.92/2.24    ~spl3_189 | spl3_123 | ~spl3_86),
% 14.92/2.24    inference(avatar_split_clause,[],[f43159,f15786,f43213,f49353])).
% 14.92/2.24  fof(f49353,plain,(
% 14.92/2.24    spl3_189 <=> k1_xboole_0 = k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_189])])).
% 14.92/2.24  fof(f15786,plain,(
% 14.92/2.24    spl3_86 <=> k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).
% 14.92/2.24  fof(f43159,plain,(
% 14.92/2.24    r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_86),
% 14.92/2.24    inference(superposition,[],[f22558,f15788])).
% 14.92/2.24  fof(f15788,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))) | ~spl3_86),
% 14.92/2.24    inference(avatar_component_clause,[],[f15786])).
% 14.92/2.24  fof(f49351,plain,(
% 14.92/2.24    spl3_188 | spl3_121 | ~spl3_59),
% 14.92/2.24    inference(avatar_split_clause,[],[f43146,f9976,f43204,f49349])).
% 14.92/2.24  fof(f49349,plain,(
% 14.92/2.24    spl3_188 <=> ! [X81] : k1_xboole_0 != k2_xboole_0(sK2,k2_xboole_0(sK1,X81))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_188])])).
% 14.92/2.24  fof(f43204,plain,(
% 14.92/2.24    spl3_121 <=> r1_tarski(sK0,k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_121])])).
% 14.92/2.24  fof(f9976,plain,(
% 14.92/2.24    spl3_59 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 14.92/2.24  fof(f43146,plain,(
% 14.92/2.24    ( ! [X81] : (r1_tarski(sK0,k1_xboole_0) | k1_xboole_0 != k2_xboole_0(sK2,k2_xboole_0(sK1,X81))) ) | ~spl3_59),
% 14.92/2.24    inference(superposition,[],[f22558,f10167])).
% 14.92/2.24  fof(f10167,plain,(
% 14.92/2.24    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,X2)))) ) | ~spl3_59),
% 14.92/2.24    inference(resolution,[],[f10058,f50])).
% 14.92/2.24  fof(f10058,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,X0)))) ) | ~spl3_59),
% 14.92/2.24    inference(resolution,[],[f10040,f54])).
% 14.92/2.24  fof(f10040,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(sK1,X0))) ) | ~spl3_59),
% 14.92/2.24    inference(subsumption_resolution,[],[f9990,f294])).
% 14.92/2.24  fof(f9990,plain,(
% 14.92/2.24    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(sK1,X0))) ) | ~spl3_59),
% 14.92/2.24    inference(superposition,[],[f54,f9978])).
% 14.92/2.24  fof(f9978,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) | ~spl3_59),
% 14.92/2.24    inference(avatar_component_clause,[],[f9976])).
% 14.92/2.24  fof(f49347,plain,(
% 14.92/2.24    ~spl3_187 | spl3_121 | ~spl3_87),
% 14.92/2.24    inference(avatar_split_clause,[],[f43143,f15791,f43204,f49344])).
% 14.92/2.24  fof(f49344,plain,(
% 14.92/2.24    spl3_187 <=> k1_xboole_0 = k2_xboole_0(sK1,k3_xboole_0(sK0,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_187])])).
% 14.92/2.24  fof(f15791,plain,(
% 14.92/2.24    spl3_87 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,k3_xboole_0(sK0,sK2)))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_87])])).
% 14.92/2.24  fof(f43143,plain,(
% 14.92/2.24    r1_tarski(sK0,k1_xboole_0) | k1_xboole_0 != k2_xboole_0(sK1,k3_xboole_0(sK0,sK2)) | ~spl3_87),
% 14.92/2.24    inference(superposition,[],[f22558,f15793])).
% 14.92/2.24  fof(f15793,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,k3_xboole_0(sK0,sK2))) | ~spl3_87),
% 14.92/2.24    inference(avatar_component_clause,[],[f15791])).
% 14.92/2.24  fof(f49342,plain,(
% 14.92/2.24    spl3_186 | spl3_126 | ~spl3_2),
% 14.92/2.24    inference(avatar_split_clause,[],[f43114,f61,f43227,f49339])).
% 14.92/2.24  fof(f49339,plain,(
% 14.92/2.24    spl3_186 <=> ! [X56] : k1_xboole_0 != k2_xboole_0(X56,sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_186])])).
% 14.92/2.24  fof(f43227,plain,(
% 14.92/2.24    spl3_126 <=> r1_tarski(k4_xboole_0(sK1,sK0),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_126])])).
% 14.92/2.24  fof(f43114,plain,(
% 14.92/2.24    ( ! [X57] : (r1_tarski(k4_xboole_0(sK1,sK0),k1_xboole_0) | k1_xboole_0 != k2_xboole_0(X57,sK2)) ) | ~spl3_2),
% 14.92/2.24    inference(superposition,[],[f22558,f1667])).
% 14.92/2.24  fof(f1667,plain,(
% 14.92/2.24    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(X3,sK2))) ) | ~spl3_2),
% 14.92/2.24    inference(resolution,[],[f1651,f50])).
% 14.92/2.24  fof(f1651,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,sK0),k2_xboole_0(X0,sK2))) ) | ~spl3_2),
% 14.92/2.24    inference(resolution,[],[f1639,f54])).
% 14.92/2.24  fof(f1639,plain,(
% 14.92/2.24    ( ! [X2] : (r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK0),X2),sK2)) ) | ~spl3_2),
% 14.92/2.24    inference(superposition,[],[f1491,f268])).
% 14.92/2.24  fof(f1491,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k3_xboole_0(k4_xboole_0(sK1,sK0),X0),sK2)) ) | ~spl3_2),
% 14.92/2.24    inference(forward_demodulation,[],[f1485,f1111])).
% 14.92/2.24  fof(f1485,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k3_xboole_0(k4_xboole_0(sK1,sK0),X0),k2_xboole_0(sK2,k1_xboole_0))) ) | ~spl3_2),
% 14.92/2.24    inference(superposition,[],[f919,f548])).
% 14.92/2.24  fof(f49341,plain,(
% 14.92/2.24    spl3_186 | spl3_125 | ~spl3_1),
% 14.92/2.24    inference(avatar_split_clause,[],[f43113,f56,f43222,f49339])).
% 14.92/2.24  fof(f43222,plain,(
% 14.92/2.24    spl3_125 <=> r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_125])])).
% 14.92/2.24  fof(f43113,plain,(
% 14.92/2.24    ( ! [X56] : (r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) | k1_xboole_0 != k2_xboole_0(X56,sK2)) ) | ~spl3_1),
% 14.92/2.24    inference(superposition,[],[f22558,f1473])).
% 14.92/2.24  fof(f1473,plain,(
% 14.92/2.24    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(X3,sK2))) ) | ~spl3_1),
% 14.92/2.24    inference(resolution,[],[f1457,f50])).
% 14.92/2.24  fof(f1457,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,sK1),k2_xboole_0(X0,sK2))) ) | ~spl3_1),
% 14.92/2.24    inference(resolution,[],[f1445,f54])).
% 14.92/2.24  fof(f1445,plain,(
% 14.92/2.24    ( ! [X2] : (r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),X2),sK2)) ) | ~spl3_1),
% 14.92/2.24    inference(superposition,[],[f1434,f268])).
% 14.92/2.24  fof(f1434,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k3_xboole_0(k4_xboole_0(sK0,sK1),X0),sK2)) ) | ~spl3_1),
% 14.92/2.24    inference(forward_demodulation,[],[f1429,f1111])).
% 14.92/2.24  fof(f1429,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k3_xboole_0(k4_xboole_0(sK0,sK1),X0),k2_xboole_0(sK2,k1_xboole_0))) ) | ~spl3_1),
% 14.92/2.24    inference(superposition,[],[f918,f548])).
% 14.92/2.24  fof(f49337,plain,(
% 14.92/2.24    ~spl3_127 | spl3_185 | ~spl3_2),
% 14.92/2.24    inference(avatar_split_clause,[],[f43099,f61,f49335,f43232])).
% 14.92/2.24  fof(f49335,plain,(
% 14.92/2.24    spl3_185 <=> ! [X47] : r1_tarski(k3_xboole_0(sK1,k4_xboole_0(X47,sK2)),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_185])])).
% 14.92/2.24  fof(f43099,plain,(
% 14.92/2.24    ( ! [X47] : (r1_tarski(k3_xboole_0(sK1,k4_xboole_0(X47,sK2)),k1_xboole_0) | k1_xboole_0 != sK0) ) | ~spl3_2),
% 14.92/2.24    inference(superposition,[],[f22558,f26268])).
% 14.92/2.24  fof(f26268,plain,(
% 14.92/2.24    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,k4_xboole_0(X3,sK2)),sK0)) ) | ~spl3_2),
% 14.92/2.24    inference(resolution,[],[f26010,f50])).
% 14.92/2.24  fof(f26010,plain,(
% 14.92/2.24    ( ! [X102] : (r1_tarski(k3_xboole_0(sK1,k4_xboole_0(X102,sK2)),sK0)) ) | ~spl3_2),
% 14.92/2.24    inference(forward_demodulation,[],[f26009,f40])).
% 14.92/2.24  fof(f26009,plain,(
% 14.92/2.24    ( ! [X102] : (r1_tarski(k3_xboole_0(k4_xboole_0(X102,sK2),sK1),sK0)) ) | ~spl3_2),
% 14.92/2.24    inference(forward_demodulation,[],[f25821,f1111])).
% 14.92/2.24  fof(f25821,plain,(
% 14.92/2.24    ( ! [X102] : (r1_tarski(k3_xboole_0(k4_xboole_0(X102,sK2),sK1),k2_xboole_0(sK0,k1_xboole_0))) ) | ~spl3_2),
% 14.92/2.24    inference(resolution,[],[f1982,f790])).
% 14.92/2.24  fof(f790,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k3_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(sK1,sK0)),k1_xboole_0)) ) | ~spl3_2),
% 14.92/2.24    inference(superposition,[],[f694,f40])).
% 14.92/2.24  fof(f694,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k3_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(X0,sK2)),k1_xboole_0)) ) | ~spl3_2),
% 14.92/2.24    inference(forward_demodulation,[],[f687,f51])).
% 14.92/2.24  fof(f687,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k4_xboole_0(k3_xboole_0(k4_xboole_0(sK1,sK0),X0),sK2),k1_xboole_0)) ) | ~spl3_2),
% 14.92/2.24    inference(superposition,[],[f514,f548])).
% 14.92/2.24  fof(f49333,plain,(
% 14.92/2.24    ~spl3_129 | spl3_184 | ~spl3_1),
% 14.92/2.24    inference(avatar_split_clause,[],[f43095,f56,f49331,f43241])).
% 14.92/2.24  fof(f49331,plain,(
% 14.92/2.24    spl3_184 <=> ! [X43] : r1_tarski(k3_xboole_0(sK0,k4_xboole_0(X43,sK2)),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_184])])).
% 14.92/2.24  fof(f43095,plain,(
% 14.92/2.24    ( ! [X43] : (r1_tarski(k3_xboole_0(sK0,k4_xboole_0(X43,sK2)),k1_xboole_0) | k1_xboole_0 != sK1) ) | ~spl3_1),
% 14.92/2.24    inference(superposition,[],[f22558,f26229])).
% 14.92/2.24  fof(f26229,plain,(
% 14.92/2.24    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,k4_xboole_0(X3,sK2)),sK1)) ) | ~spl3_1),
% 14.92/2.24    inference(resolution,[],[f26006,f50])).
% 14.92/2.24  fof(f26006,plain,(
% 14.92/2.24    ( ! [X100] : (r1_tarski(k3_xboole_0(sK0,k4_xboole_0(X100,sK2)),sK1)) ) | ~spl3_1),
% 14.92/2.24    inference(forward_demodulation,[],[f26005,f40])).
% 14.92/2.24  fof(f26005,plain,(
% 14.92/2.24    ( ! [X100] : (r1_tarski(k3_xboole_0(k4_xboole_0(X100,sK2),sK0),sK1)) ) | ~spl3_1),
% 14.92/2.24    inference(forward_demodulation,[],[f25819,f1111])).
% 14.92/2.24  fof(f25819,plain,(
% 14.92/2.24    ( ! [X100] : (r1_tarski(k3_xboole_0(k4_xboole_0(X100,sK2),sK0),k2_xboole_0(sK1,k1_xboole_0))) ) | ~spl3_1),
% 14.92/2.24    inference(resolution,[],[f1982,f777])).
% 14.92/2.24  fof(f777,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k3_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(sK0,sK1)),k1_xboole_0)) ) | ~spl3_1),
% 14.92/2.24    inference(superposition,[],[f664,f40])).
% 14.92/2.24  fof(f664,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(X0,sK2)),k1_xboole_0)) ) | ~spl3_1),
% 14.92/2.24    inference(forward_demodulation,[],[f658,f51])).
% 14.92/2.24  fof(f658,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k4_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK1),X0),sK2),k1_xboole_0)) ) | ~spl3_1),
% 14.92/2.24    inference(superposition,[],[f513,f548])).
% 14.92/2.24  fof(f49329,plain,(
% 14.92/2.24    ~spl3_129 | spl3_183 | ~spl3_61),
% 14.92/2.24    inference(avatar_split_clause,[],[f43092,f10067,f49327,f43241])).
% 14.92/2.24  fof(f49327,plain,(
% 14.92/2.24    spl3_183 <=> ! [X40] : r1_tarski(k3_xboole_0(k4_xboole_0(sK0,sK2),X40),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_183])])).
% 14.92/2.24  fof(f43092,plain,(
% 14.92/2.24    ( ! [X40] : (r1_tarski(k3_xboole_0(k4_xboole_0(sK0,sK2),X40),k1_xboole_0) | k1_xboole_0 != sK1) ) | ~spl3_61),
% 14.92/2.24    inference(superposition,[],[f22558,f10733])).
% 14.92/2.24  fof(f10733,plain,(
% 14.92/2.24    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK2),X2),sK1)) ) | ~spl3_61),
% 14.92/2.24    inference(resolution,[],[f10713,f50])).
% 14.92/2.24  fof(f49325,plain,(
% 14.92/2.24    ~spl3_127 | spl3_182 | ~spl3_54),
% 14.92/2.24    inference(avatar_split_clause,[],[f43091,f9262,f49323,f43232])).
% 14.92/2.24  fof(f49323,plain,(
% 14.92/2.24    spl3_182 <=> ! [X39] : r1_tarski(k3_xboole_0(k4_xboole_0(sK1,sK2),X39),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_182])])).
% 14.92/2.24  fof(f43091,plain,(
% 14.92/2.24    ( ! [X39] : (r1_tarski(k3_xboole_0(k4_xboole_0(sK1,sK2),X39),k1_xboole_0) | k1_xboole_0 != sK0) ) | ~spl3_54),
% 14.92/2.24    inference(superposition,[],[f22558,f10718])).
% 14.92/2.24  fof(f10718,plain,(
% 14.92/2.24    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(k4_xboole_0(sK1,sK2),X2),sK0)) ) | ~spl3_54),
% 14.92/2.24    inference(resolution,[],[f10712,f50])).
% 14.92/2.24  fof(f49319,plain,(
% 14.92/2.24    spl3_181 | ~spl3_27 | ~spl3_85),
% 14.92/2.24    inference(avatar_split_clause,[],[f16558,f15056,f967,f49316])).
% 14.92/2.24  fof(f49316,plain,(
% 14.92/2.24    spl3_181 <=> r1_tarski(k5_xboole_0(sK1,k4_xboole_0(sK0,sK2)),k2_xboole_0(sK0,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_181])])).
% 14.92/2.24  fof(f967,plain,(
% 14.92/2.24    spl3_27 <=> r1_tarski(sK1,k2_xboole_0(sK0,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 14.92/2.24  fof(f15056,plain,(
% 14.92/2.24    spl3_85 <=> k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK1,k4_xboole_0(sK0,sK2)),sK1)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).
% 14.92/2.24  fof(f16558,plain,(
% 14.92/2.24    r1_tarski(k5_xboole_0(sK1,k4_xboole_0(sK0,sK2)),k2_xboole_0(sK0,sK2)) | (~spl3_27 | ~spl3_85)),
% 14.92/2.24    inference(forward_demodulation,[],[f16493,f1111])).
% 14.92/2.24  fof(f16493,plain,(
% 14.92/2.24    r1_tarski(k5_xboole_0(sK1,k4_xboole_0(sK0,sK2)),k2_xboole_0(k2_xboole_0(sK0,sK2),k1_xboole_0)) | (~spl3_27 | ~spl3_85)),
% 14.92/2.24    inference(superposition,[],[f1697,f15058])).
% 14.92/2.24  fof(f15058,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK1,k4_xboole_0(sK0,sK2)),sK1) | ~spl3_85),
% 14.92/2.24    inference(avatar_component_clause,[],[f15056])).
% 14.92/2.24  fof(f1697,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(X0,k2_xboole_0(k2_xboole_0(sK0,sK2),k4_xboole_0(X0,sK1)))) ) | ~spl3_27),
% 14.92/2.24    inference(resolution,[],[f973,f54])).
% 14.92/2.24  fof(f973,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,k2_xboole_0(sK0,sK2)),k4_xboole_0(X0,sK1))) ) | ~spl3_27),
% 14.92/2.24    inference(resolution,[],[f969,f53])).
% 14.92/2.24  fof(f969,plain,(
% 14.92/2.24    r1_tarski(sK1,k2_xboole_0(sK0,sK2)) | ~spl3_27),
% 14.92/2.24    inference(avatar_component_clause,[],[f967])).
% 14.92/2.24  fof(f48975,plain,(
% 14.92/2.24    spl3_180 | ~spl3_26 | ~spl3_83),
% 14.92/2.24    inference(avatar_split_clause,[],[f16466,f14842,f962,f48972])).
% 14.92/2.24  fof(f48972,plain,(
% 14.92/2.24    spl3_180 <=> r1_tarski(k5_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_180])])).
% 14.92/2.24  fof(f962,plain,(
% 14.92/2.24    spl3_26 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 14.92/2.24  fof(f14842,plain,(
% 14.92/2.24    spl3_83 <=> k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK2)),sK0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).
% 14.92/2.24  fof(f16466,plain,(
% 14.92/2.24    r1_tarski(k5_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) | (~spl3_26 | ~spl3_83)),
% 14.92/2.24    inference(forward_demodulation,[],[f16401,f1111])).
% 14.92/2.24  fof(f16401,plain,(
% 14.92/2.24    r1_tarski(k5_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k2_xboole_0(k2_xboole_0(sK1,sK2),k1_xboole_0)) | (~spl3_26 | ~spl3_83)),
% 14.92/2.24    inference(superposition,[],[f1674,f14844])).
% 14.92/2.24  fof(f14844,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK2)),sK0) | ~spl3_83),
% 14.92/2.24    inference(avatar_component_clause,[],[f14842])).
% 14.92/2.24  fof(f1674,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(X0,k2_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(X0,sK0)))) ) | ~spl3_26),
% 14.92/2.24    inference(resolution,[],[f971,f54])).
% 14.92/2.24  fof(f971,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,k2_xboole_0(sK1,sK2)),k4_xboole_0(X0,sK0))) ) | ~spl3_26),
% 14.92/2.24    inference(resolution,[],[f964,f53])).
% 14.92/2.24  fof(f964,plain,(
% 14.92/2.24    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_26),
% 14.92/2.24    inference(avatar_component_clause,[],[f962])).
% 14.92/2.24  fof(f48908,plain,(
% 14.92/2.24    ~spl3_146 | spl3_179 | ~spl3_37),
% 14.92/2.24    inference(avatar_split_clause,[],[f44177,f4240,f48903,f46373])).
% 14.92/2.24  fof(f46373,plain,(
% 14.92/2.24    spl3_146 <=> k1_xboole_0 = k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_146])])).
% 14.92/2.24  fof(f48903,plain,(
% 14.92/2.24    spl3_179 <=> ! [X96] : r1_tarski(sK1,X96)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_179])])).
% 14.92/2.24  fof(f4240,plain,(
% 14.92/2.24    spl3_37 <=> sK1 = k3_xboole_0(sK1,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 14.92/2.24  fof(f44177,plain,(
% 14.92/2.24    ( ! [X105] : (r1_tarski(sK1,X105) | k1_xboole_0 != k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))) ) | ~spl3_37),
% 14.92/2.24    inference(superposition,[],[f44055,f4242])).
% 14.92/2.24  fof(f4242,plain,(
% 14.92/2.24    sK1 = k3_xboole_0(sK1,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))) | ~spl3_37),
% 14.92/2.24    inference(avatar_component_clause,[],[f4240])).
% 14.92/2.24  fof(f44055,plain,(
% 14.92/2.24    ( ! [X4,X2,X3] : (r1_tarski(k3_xboole_0(X3,X2),X4) | k1_xboole_0 != X2) )),
% 14.92/2.24    inference(superposition,[],[f43879,f40])).
% 14.92/2.24  fof(f43879,plain,(
% 14.92/2.24    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X2) | k1_xboole_0 != X0) )),
% 14.92/2.24    inference(forward_demodulation,[],[f43813,f1111])).
% 14.92/2.24  fof(f43813,plain,(
% 14.92/2.24    ( ! [X2,X0,X1] : (k1_xboole_0 != X0 | r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X2,k1_xboole_0))) )),
% 14.92/2.24    inference(resolution,[],[f43076,f1982])).
% 14.92/2.24  fof(f43076,plain,(
% 14.92/2.24    ( ! [X17,X16] : (r1_tarski(k3_xboole_0(X16,X17),k1_xboole_0) | k1_xboole_0 != X16) )),
% 14.92/2.24    inference(superposition,[],[f22558,f548])).
% 14.92/2.24  fof(f48907,plain,(
% 14.92/2.24    spl3_161 | spl3_179 | ~spl3_7),
% 14.92/2.24    inference(avatar_split_clause,[],[f44174,f170,f48903,f48199])).
% 14.92/2.24  fof(f48199,plain,(
% 14.92/2.24    spl3_161 <=> ! [X91] : k1_xboole_0 != k2_xboole_0(sK0,k2_xboole_0(sK2,X91))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_161])])).
% 14.92/2.24  fof(f170,plain,(
% 14.92/2.24    spl3_7 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 14.92/2.24  fof(f44174,plain,(
% 14.92/2.24    ( ! [X101,X100] : (r1_tarski(sK1,X101) | k1_xboole_0 != k2_xboole_0(sK0,k2_xboole_0(sK2,X100))) ) | ~spl3_7),
% 14.92/2.24    inference(superposition,[],[f44055,f1917])).
% 14.92/2.24  fof(f1917,plain,(
% 14.92/2.24    ( ! [X4] : (sK1 = k3_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK2,X4)))) ) | ~spl3_7),
% 14.92/2.24    inference(forward_demodulation,[],[f1904,f38])).
% 14.92/2.24  fof(f1904,plain,(
% 14.92/2.24    ( ! [X4] : (k4_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK2,X4)))) ) | ~spl3_7),
% 14.92/2.24    inference(superposition,[],[f44,f1051])).
% 14.92/2.24  fof(f1051,plain,(
% 14.92/2.24    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK2,X2)))) ) | ~spl3_7),
% 14.92/2.24    inference(resolution,[],[f991,f50])).
% 14.92/2.24  fof(f991,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(sK1,k2_xboole_0(sK0,k2_xboole_0(sK2,X0)))) ) | ~spl3_7),
% 14.92/2.24    inference(resolution,[],[f960,f54])).
% 14.92/2.24  fof(f960,plain,(
% 14.92/2.24    ( ! [X31] : (r1_tarski(k4_xboole_0(sK1,sK0),k2_xboole_0(sK2,X31))) ) | ~spl3_7),
% 14.92/2.24    inference(subsumption_resolution,[],[f942,f294])).
% 14.92/2.24  fof(f942,plain,(
% 14.92/2.24    ( ! [X31] : (~r1_tarski(k1_xboole_0,X31) | r1_tarski(k4_xboole_0(sK1,sK0),k2_xboole_0(sK2,X31))) ) | ~spl3_7),
% 14.92/2.24    inference(superposition,[],[f54,f172])).
% 14.92/2.24  fof(f172,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK2) | ~spl3_7),
% 14.92/2.24    inference(avatar_component_clause,[],[f170])).
% 14.92/2.24  fof(f48906,plain,(
% 14.92/2.24    spl3_147 | spl3_179 | ~spl3_29),
% 14.92/2.24    inference(avatar_split_clause,[],[f44172,f1001,f48903,f46378])).
% 14.92/2.24  fof(f46378,plain,(
% 14.92/2.24    spl3_147 <=> ! [X89] : k1_xboole_0 != k2_xboole_0(k2_xboole_0(sK0,sK2),X89)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_147])])).
% 14.92/2.24  fof(f1001,plain,(
% 14.92/2.24    spl3_29 <=> k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 14.92/2.24  fof(f44172,plain,(
% 14.92/2.24    ( ! [X97,X98] : (r1_tarski(sK1,X98) | k1_xboole_0 != k2_xboole_0(k2_xboole_0(sK0,sK2),X97)) ) | ~spl3_29),
% 14.92/2.24    inference(superposition,[],[f44055,f3787])).
% 14.92/2.24  fof(f3787,plain,(
% 14.92/2.24    ( ! [X8] : (sK1 = k3_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK0,sK2),X8))) ) | ~spl3_29),
% 14.92/2.24    inference(forward_demodulation,[],[f3750,f38])).
% 14.92/2.24  fof(f3750,plain,(
% 14.92/2.24    ( ! [X8] : (k4_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK0,sK2),X8))) ) | ~spl3_29),
% 14.92/2.24    inference(superposition,[],[f44,f1067])).
% 14.92/2.24  fof(f1067,plain,(
% 14.92/2.24    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK0,sK2),X2))) ) | ~spl3_29),
% 14.92/2.24    inference(resolution,[],[f1034,f50])).
% 14.92/2.24  fof(f1034,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(sK1,k2_xboole_0(k2_xboole_0(sK0,sK2),X0))) ) | ~spl3_29),
% 14.92/2.24    inference(subsumption_resolution,[],[f1025,f294])).
% 14.92/2.24  fof(f1025,plain,(
% 14.92/2.24    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | r1_tarski(sK1,k2_xboole_0(k2_xboole_0(sK0,sK2),X0))) ) | ~spl3_29),
% 14.92/2.24    inference(superposition,[],[f54,f1003])).
% 14.92/2.24  fof(f1003,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | ~spl3_29),
% 14.92/2.24    inference(avatar_component_clause,[],[f1001])).
% 14.92/2.24  fof(f48905,plain,(
% 14.92/2.24    spl3_169 | spl3_179 | ~spl3_27),
% 14.92/2.24    inference(avatar_split_clause,[],[f44171,f967,f48903,f48618])).
% 14.92/2.24  fof(f48618,plain,(
% 14.92/2.24    spl3_169 <=> ! [X87] : k1_xboole_0 != k2_xboole_0(X87,k2_xboole_0(sK0,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_169])])).
% 14.92/2.24  fof(f44171,plain,(
% 14.92/2.24    ( ! [X95,X96] : (r1_tarski(sK1,X96) | k1_xboole_0 != k2_xboole_0(X95,k2_xboole_0(sK0,sK2))) ) | ~spl3_27),
% 14.92/2.24    inference(superposition,[],[f44055,f5705])).
% 14.92/2.24  fof(f5705,plain,(
% 14.92/2.24    ( ! [X10] : (sK1 = k3_xboole_0(sK1,k2_xboole_0(X10,k2_xboole_0(sK0,sK2)))) ) | ~spl3_27),
% 14.92/2.24    inference(forward_demodulation,[],[f5665,f38])).
% 14.92/2.24  fof(f5665,plain,(
% 14.92/2.24    ( ! [X10] : (k4_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,k2_xboole_0(X10,k2_xboole_0(sK0,sK2)))) ) | ~spl3_27),
% 14.92/2.24    inference(superposition,[],[f44,f1855])).
% 14.92/2.24  fof(f1855,plain,(
% 14.92/2.24    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(X2,k2_xboole_0(sK0,sK2)))) ) | ~spl3_27),
% 14.92/2.24    inference(resolution,[],[f1831,f50])).
% 14.92/2.24  fof(f1831,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(sK1,k2_xboole_0(X0,k2_xboole_0(sK0,sK2)))) ) | ~spl3_27),
% 14.92/2.24    inference(resolution,[],[f1830,f54])).
% 14.92/2.24  fof(f1830,plain,(
% 14.92/2.24    ( ! [X2] : (r1_tarski(k4_xboole_0(sK1,X2),k2_xboole_0(sK0,sK2))) ) | ~spl3_27),
% 14.92/2.24    inference(forward_demodulation,[],[f1824,f1111])).
% 14.92/2.24  fof(f1824,plain,(
% 14.92/2.24    ( ! [X2] : (r1_tarski(k4_xboole_0(sK1,X2),k2_xboole_0(k2_xboole_0(sK0,sK2),k1_xboole_0))) ) | ~spl3_27),
% 14.92/2.24    inference(superposition,[],[f1697,f534])).
% 14.92/2.24  fof(f48901,plain,(
% 14.92/2.24    ~spl3_146 | spl3_178 | ~spl3_36),
% 14.92/2.24    inference(avatar_split_clause,[],[f44163,f4231,f48896,f46373])).
% 14.92/2.24  fof(f48896,plain,(
% 14.92/2.24    spl3_178 <=> ! [X73] : r1_tarski(sK0,X73)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_178])])).
% 14.92/2.24  fof(f4231,plain,(
% 14.92/2.24    spl3_36 <=> sK0 = k3_xboole_0(sK0,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 14.92/2.24  fof(f44163,plain,(
% 14.92/2.24    ( ! [X82] : (r1_tarski(sK0,X82) | k1_xboole_0 != k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))) ) | ~spl3_36),
% 14.92/2.24    inference(superposition,[],[f44055,f4233])).
% 14.92/2.24  fof(f4233,plain,(
% 14.92/2.24    sK0 = k3_xboole_0(sK0,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))) | ~spl3_36),
% 14.92/2.24    inference(avatar_component_clause,[],[f4231])).
% 14.92/2.24  fof(f48900,plain,(
% 14.92/2.24    spl3_141 | spl3_178 | ~spl3_6),
% 14.92/2.24    inference(avatar_split_clause,[],[f44160,f165,f48896,f45648])).
% 14.92/2.24  fof(f45648,plain,(
% 14.92/2.24    spl3_141 <=> ! [X79] : k1_xboole_0 != k2_xboole_0(sK1,k2_xboole_0(sK2,X79))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_141])])).
% 14.92/2.24  fof(f165,plain,(
% 14.92/2.24    spl3_6 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 14.92/2.24  fof(f44160,plain,(
% 14.92/2.24    ( ! [X78,X77] : (r1_tarski(sK0,X78) | k1_xboole_0 != k2_xboole_0(sK1,k2_xboole_0(sK2,X77))) ) | ~spl3_6),
% 14.92/2.24    inference(superposition,[],[f44055,f1893])).
% 14.92/2.24  fof(f1893,plain,(
% 14.92/2.24    ( ! [X4] : (sK0 = k3_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,X4)))) ) | ~spl3_6),
% 14.92/2.24    inference(forward_demodulation,[],[f1880,f38])).
% 14.92/2.24  fof(f1880,plain,(
% 14.92/2.24    ( ! [X4] : (k4_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,X4)))) ) | ~spl3_6),
% 14.92/2.24    inference(superposition,[],[f44,f1048])).
% 14.92/2.24  fof(f1048,plain,(
% 14.92/2.24    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,X2)))) ) | ~spl3_6),
% 14.92/2.24    inference(resolution,[],[f987,f50])).
% 14.92/2.24  fof(f987,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,X0)))) ) | ~spl3_6),
% 14.92/2.24    inference(resolution,[],[f959,f54])).
% 14.92/2.24  fof(f959,plain,(
% 14.92/2.24    ( ! [X30] : (r1_tarski(k4_xboole_0(sK0,sK1),k2_xboole_0(sK2,X30))) ) | ~spl3_6),
% 14.92/2.24    inference(subsumption_resolution,[],[f941,f294])).
% 14.92/2.24  fof(f941,plain,(
% 14.92/2.24    ( ! [X30] : (~r1_tarski(k1_xboole_0,X30) | r1_tarski(k4_xboole_0(sK0,sK1),k2_xboole_0(sK2,X30))) ) | ~spl3_6),
% 14.92/2.24    inference(superposition,[],[f54,f167])).
% 14.92/2.24  fof(f167,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) | ~spl3_6),
% 14.92/2.24    inference(avatar_component_clause,[],[f165])).
% 14.92/2.24  fof(f48899,plain,(
% 14.92/2.24    spl3_139 | spl3_178 | ~spl3_28),
% 14.92/2.24    inference(avatar_split_clause,[],[f44158,f996,f48896,f45588])).
% 14.92/2.24  fof(f45588,plain,(
% 14.92/2.24    spl3_139 <=> ! [X77] : k1_xboole_0 != k2_xboole_0(k2_xboole_0(sK1,sK2),X77)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_139])])).
% 14.92/2.24  fof(f996,plain,(
% 14.92/2.24    spl3_28 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 14.92/2.24  fof(f44158,plain,(
% 14.92/2.24    ( ! [X74,X75] : (r1_tarski(sK0,X75) | k1_xboole_0 != k2_xboole_0(k2_xboole_0(sK1,sK2),X74)) ) | ~spl3_28),
% 14.92/2.24    inference(superposition,[],[f44055,f1941])).
% 14.92/2.24  fof(f1941,plain,(
% 14.92/2.24    ( ! [X4] : (sK0 = k3_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X4))) ) | ~spl3_28),
% 14.92/2.24    inference(forward_demodulation,[],[f1928,f38])).
% 14.92/2.24  fof(f1928,plain,(
% 14.92/2.24    ( ! [X4] : (k4_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X4))) ) | ~spl3_28),
% 14.92/2.24    inference(superposition,[],[f44,f1059])).
% 14.92/2.24  fof(f1059,plain,(
% 14.92/2.24    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X2))) ) | ~spl3_28),
% 14.92/2.24    inference(resolution,[],[f1018,f50])).
% 14.92/2.24  fof(f1018,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0))) ) | ~spl3_28),
% 14.92/2.24    inference(subsumption_resolution,[],[f1009,f294])).
% 14.92/2.24  fof(f1009,plain,(
% 14.92/2.24    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | r1_tarski(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0))) ) | ~spl3_28),
% 14.92/2.24    inference(superposition,[],[f54,f998])).
% 14.92/2.24  fof(f998,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_28),
% 14.92/2.24    inference(avatar_component_clause,[],[f996])).
% 14.92/2.24  fof(f48898,plain,(
% 14.92/2.24    spl3_168 | spl3_178 | ~spl3_26),
% 14.92/2.24    inference(avatar_split_clause,[],[f44157,f962,f48896,f48614])).
% 14.92/2.24  fof(f48614,plain,(
% 14.92/2.24    spl3_168 <=> ! [X75] : k1_xboole_0 != k2_xboole_0(X75,k2_xboole_0(sK1,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_168])])).
% 14.92/2.24  fof(f44157,plain,(
% 14.92/2.24    ( ! [X72,X73] : (r1_tarski(sK0,X73) | k1_xboole_0 != k2_xboole_0(X72,k2_xboole_0(sK1,sK2))) ) | ~spl3_26),
% 14.92/2.24    inference(superposition,[],[f44055,f5565])).
% 14.92/2.24  fof(f5565,plain,(
% 14.92/2.24    ( ! [X10] : (sK0 = k3_xboole_0(sK0,k2_xboole_0(X10,k2_xboole_0(sK1,sK2)))) ) | ~spl3_26),
% 14.92/2.24    inference(forward_demodulation,[],[f5525,f38])).
% 14.92/2.24  fof(f5525,plain,(
% 14.92/2.24    ( ! [X10] : (k4_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(X10,k2_xboole_0(sK1,sK2)))) ) | ~spl3_26),
% 14.92/2.24    inference(superposition,[],[f44,f1808])).
% 14.92/2.24  fof(f1808,plain,(
% 14.92/2.24    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X2,k2_xboole_0(sK1,sK2)))) ) | ~spl3_26),
% 14.92/2.24    inference(resolution,[],[f1784,f50])).
% 14.92/2.24  fof(f1784,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(X0,k2_xboole_0(sK1,sK2)))) ) | ~spl3_26),
% 14.92/2.24    inference(resolution,[],[f1783,f54])).
% 14.92/2.24  fof(f1783,plain,(
% 14.92/2.24    ( ! [X2] : (r1_tarski(k4_xboole_0(sK0,X2),k2_xboole_0(sK1,sK2))) ) | ~spl3_26),
% 14.92/2.24    inference(forward_demodulation,[],[f1777,f1111])).
% 14.92/2.24  fof(f1777,plain,(
% 14.92/2.24    ( ! [X2] : (r1_tarski(k4_xboole_0(sK0,X2),k2_xboole_0(k2_xboole_0(sK1,sK2),k1_xboole_0))) ) | ~spl3_26),
% 14.92/2.24    inference(superposition,[],[f1674,f534])).
% 14.92/2.24  fof(f48894,plain,(
% 14.92/2.24    ~spl3_124 | spl3_177 | ~spl3_2),
% 14.92/2.24    inference(avatar_split_clause,[],[f43133,f61,f48892,f43218])).
% 14.92/2.24  fof(f48892,plain,(
% 14.92/2.24    spl3_177 <=> ! [X72] : r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK0),X72),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_177])])).
% 14.92/2.24  fof(f43133,plain,(
% 14.92/2.24    ( ! [X72] : (r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK0),X72),k1_xboole_0) | k1_xboole_0 != sK2) ) | ~spl3_2),
% 14.92/2.24    inference(superposition,[],[f22558,f1653])).
% 14.92/2.24  fof(f1653,plain,(
% 14.92/2.24    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),X3),sK2)) ) | ~spl3_2),
% 14.92/2.24    inference(resolution,[],[f1639,f50])).
% 14.92/2.24  fof(f48890,plain,(
% 14.92/2.24    ~spl3_124 | spl3_176 | ~spl3_1),
% 14.92/2.24    inference(avatar_split_clause,[],[f43132,f56,f48888,f43218])).
% 14.92/2.24  fof(f48888,plain,(
% 14.92/2.24    spl3_176 <=> ! [X71] : r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),X71),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_176])])).
% 14.92/2.24  fof(f43132,plain,(
% 14.92/2.24    ( ! [X71] : (r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),X71),k1_xboole_0) | k1_xboole_0 != sK2) ) | ~spl3_1),
% 14.92/2.24    inference(superposition,[],[f22558,f1459])).
% 14.92/2.24  fof(f1459,plain,(
% 14.92/2.24    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),X3),sK2)) ) | ~spl3_1),
% 14.92/2.24    inference(resolution,[],[f1445,f50])).
% 14.92/2.24  fof(f48886,plain,(
% 14.92/2.24    spl3_175 | spl3_130 | ~spl3_59),
% 14.92/2.24    inference(avatar_split_clause,[],[f43120,f9976,f43245,f48884])).
% 14.92/2.24  fof(f48884,plain,(
% 14.92/2.24    spl3_175 <=> ! [X63] : k1_xboole_0 != k2_xboole_0(sK1,X63)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_175])])).
% 14.92/2.24  fof(f43245,plain,(
% 14.92/2.24    spl3_130 <=> r1_tarski(k4_xboole_0(sK0,sK2),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_130])])).
% 14.92/2.24  fof(f43120,plain,(
% 14.92/2.24    ( ! [X63] : (r1_tarski(k4_xboole_0(sK0,sK2),k1_xboole_0) | k1_xboole_0 != k2_xboole_0(sK1,X63)) ) | ~spl3_59),
% 14.92/2.24    inference(superposition,[],[f22558,f10060])).
% 14.92/2.24  fof(f10060,plain,(
% 14.92/2.24    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(sK1,X3))) ) | ~spl3_59),
% 14.92/2.24    inference(resolution,[],[f10040,f50])).
% 14.92/2.24  fof(f48882,plain,(
% 14.92/2.24    spl3_174 | spl3_128 | ~spl3_52),
% 14.92/2.24    inference(avatar_split_clause,[],[f43118,f9175,f43236,f48880])).
% 14.92/2.24  fof(f48880,plain,(
% 14.92/2.24    spl3_174 <=> ! [X61] : k1_xboole_0 != k2_xboole_0(sK0,X61)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_174])])).
% 14.92/2.24  fof(f43236,plain,(
% 14.92/2.24    spl3_128 <=> r1_tarski(k4_xboole_0(sK1,sK2),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_128])])).
% 14.92/2.24  fof(f43118,plain,(
% 14.92/2.24    ( ! [X61] : (r1_tarski(k4_xboole_0(sK1,sK2),k1_xboole_0) | k1_xboole_0 != k2_xboole_0(sK0,X61)) ) | ~spl3_52),
% 14.92/2.24    inference(superposition,[],[f22558,f9255])).
% 14.92/2.24  fof(f9255,plain,(
% 14.92/2.24    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK0,X3))) ) | ~spl3_52),
% 14.92/2.24    inference(resolution,[],[f9235,f50])).
% 14.92/2.24  fof(f48878,plain,(
% 14.92/2.24    ~spl3_134 | spl3_125 | ~spl3_81),
% 14.92/2.24    inference(avatar_split_clause,[],[f43110,f13668,f43222,f43799])).
% 14.92/2.24  fof(f43799,plain,(
% 14.92/2.24    spl3_134 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_134])])).
% 14.92/2.24  fof(f13668,plain,(
% 14.92/2.24    spl3_81 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).
% 14.92/2.24  fof(f43110,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) | k1_xboole_0 != k3_xboole_0(sK0,sK2) | ~spl3_81),
% 14.92/2.24    inference(superposition,[],[f22558,f13670])).
% 14.92/2.24  fof(f13670,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) | ~spl3_81),
% 14.92/2.24    inference(avatar_component_clause,[],[f13668])).
% 14.92/2.24  fof(f48877,plain,(
% 14.92/2.24    ~spl3_133 | spl3_126 | ~spl3_80),
% 14.92/2.24    inference(avatar_split_clause,[],[f43109,f13663,f43227,f43794])).
% 14.92/2.24  fof(f43794,plain,(
% 14.92/2.24    spl3_133 <=> k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_133])])).
% 14.92/2.24  fof(f13663,plain,(
% 14.92/2.24    spl3_80 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).
% 14.92/2.24  fof(f43109,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK1,sK0),k1_xboole_0) | k1_xboole_0 != k3_xboole_0(sK1,sK2) | ~spl3_80),
% 14.92/2.24    inference(superposition,[],[f22558,f13665])).
% 14.92/2.24  fof(f13665,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2)) | ~spl3_80),
% 14.92/2.24    inference(avatar_component_clause,[],[f13663])).
% 14.92/2.24  fof(f48876,plain,(
% 14.92/2.24    ~spl3_122 | spl3_173 | ~spl3_27),
% 14.92/2.24    inference(avatar_split_clause,[],[f43087,f967,f48874,f43209])).
% 14.92/2.24  fof(f43209,plain,(
% 14.92/2.24    spl3_122 <=> k1_xboole_0 = k2_xboole_0(sK0,sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_122])])).
% 14.92/2.24  fof(f48874,plain,(
% 14.92/2.24    spl3_173 <=> ! [X35] : r1_tarski(k3_xboole_0(X35,sK1),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_173])])).
% 14.92/2.24  fof(f43087,plain,(
% 14.92/2.24    ( ! [X35] : (r1_tarski(k3_xboole_0(X35,sK1),k1_xboole_0) | k1_xboole_0 != k2_xboole_0(sK0,sK2)) ) | ~spl3_27),
% 14.92/2.24    inference(superposition,[],[f22558,f1859])).
% 14.92/2.24  fof(f1859,plain,(
% 14.92/2.24    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,sK1),k2_xboole_0(sK0,sK2))) ) | ~spl3_27),
% 14.92/2.24    inference(resolution,[],[f1827,f50])).
% 14.92/2.24  fof(f1827,plain,(
% 14.92/2.24    ( ! [X1] : (r1_tarski(k3_xboole_0(X1,sK1),k2_xboole_0(sK0,sK2))) ) | ~spl3_27),
% 14.92/2.24    inference(forward_demodulation,[],[f1822,f1111])).
% 14.92/2.24  fof(f1822,plain,(
% 14.92/2.24    ( ! [X1] : (r1_tarski(k3_xboole_0(X1,sK1),k2_xboole_0(k2_xboole_0(sK0,sK2),k1_xboole_0))) ) | ~spl3_27),
% 14.92/2.24    inference(superposition,[],[f1697,f560])).
% 14.92/2.24  fof(f48872,plain,(
% 14.92/2.24    ~spl3_120 | spl3_172 | ~spl3_26),
% 14.92/2.24    inference(avatar_split_clause,[],[f43085,f962,f48870,f43200])).
% 14.92/2.24  fof(f43200,plain,(
% 14.92/2.24    spl3_120 <=> k1_xboole_0 = k2_xboole_0(sK1,sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_120])])).
% 14.92/2.24  fof(f48870,plain,(
% 14.92/2.24    spl3_172 <=> ! [X33] : r1_tarski(k3_xboole_0(X33,sK0),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_172])])).
% 14.92/2.24  fof(f43085,plain,(
% 14.92/2.24    ( ! [X33] : (r1_tarski(k3_xboole_0(X33,sK0),k1_xboole_0) | k1_xboole_0 != k2_xboole_0(sK1,sK2)) ) | ~spl3_26),
% 14.92/2.24    inference(superposition,[],[f22558,f1812])).
% 14.92/2.24  fof(f1812,plain,(
% 14.92/2.24    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,sK0),k2_xboole_0(sK1,sK2))) ) | ~spl3_26),
% 14.92/2.24    inference(resolution,[],[f1780,f50])).
% 14.92/2.24  fof(f1780,plain,(
% 14.92/2.24    ( ! [X1] : (r1_tarski(k3_xboole_0(X1,sK0),k2_xboole_0(sK1,sK2))) ) | ~spl3_26),
% 14.92/2.24    inference(forward_demodulation,[],[f1775,f1111])).
% 14.92/2.24  fof(f1775,plain,(
% 14.92/2.24    ( ! [X1] : (r1_tarski(k3_xboole_0(X1,sK0),k2_xboole_0(k2_xboole_0(sK1,sK2),k1_xboole_0))) ) | ~spl3_26),
% 14.92/2.24    inference(superposition,[],[f1674,f560])).
% 14.92/2.24  fof(f48868,plain,(
% 14.92/2.24    ~spl3_124 | spl3_171 | ~spl3_2),
% 14.92/2.24    inference(avatar_split_clause,[],[f43082,f61,f48866,f43218])).
% 14.92/2.24  fof(f48866,plain,(
% 14.92/2.24    spl3_171 <=> ! [X30] : r1_tarski(k3_xboole_0(X30,k4_xboole_0(sK1,sK0)),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_171])])).
% 14.92/2.24  fof(f43082,plain,(
% 14.92/2.24    ( ! [X30] : (r1_tarski(k3_xboole_0(X30,k4_xboole_0(sK1,sK0)),k1_xboole_0) | k1_xboole_0 != sK2) ) | ~spl3_2),
% 14.92/2.24    inference(superposition,[],[f22558,f1644])).
% 14.92/2.24  fof(f1644,plain,(
% 14.92/2.24    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,k4_xboole_0(sK1,sK0)),sK2)) ) | ~spl3_2),
% 14.92/2.24    inference(resolution,[],[f1492,f50])).
% 14.92/2.24  fof(f1492,plain,(
% 14.92/2.24    ( ! [X1] : (r1_tarski(k3_xboole_0(X1,k4_xboole_0(sK1,sK0)),sK2)) ) | ~spl3_2),
% 14.92/2.24    inference(forward_demodulation,[],[f1486,f1111])).
% 14.92/2.24  fof(f1486,plain,(
% 14.92/2.24    ( ! [X1] : (r1_tarski(k3_xboole_0(X1,k4_xboole_0(sK1,sK0)),k2_xboole_0(sK2,k1_xboole_0))) ) | ~spl3_2),
% 14.92/2.24    inference(superposition,[],[f919,f560])).
% 14.92/2.24  fof(f48864,plain,(
% 14.92/2.24    ~spl3_124 | spl3_170 | ~spl3_1),
% 14.92/2.24    inference(avatar_split_clause,[],[f43081,f56,f48862,f43218])).
% 14.92/2.24  fof(f48862,plain,(
% 14.92/2.24    spl3_170 <=> ! [X29] : r1_tarski(k3_xboole_0(X29,k4_xboole_0(sK0,sK1)),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_170])])).
% 14.92/2.24  fof(f43081,plain,(
% 14.92/2.24    ( ! [X29] : (r1_tarski(k3_xboole_0(X29,k4_xboole_0(sK0,sK1)),k1_xboole_0) | k1_xboole_0 != sK2) ) | ~spl3_1),
% 14.92/2.24    inference(superposition,[],[f22558,f1450])).
% 14.92/2.24  fof(f1450,plain,(
% 14.92/2.24    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,k4_xboole_0(sK0,sK1)),sK2)) ) | ~spl3_1),
% 14.92/2.24    inference(resolution,[],[f1435,f50])).
% 14.92/2.24  fof(f1435,plain,(
% 14.92/2.24    ( ! [X1] : (r1_tarski(k3_xboole_0(X1,k4_xboole_0(sK0,sK1)),sK2)) ) | ~spl3_1),
% 14.92/2.24    inference(forward_demodulation,[],[f1430,f1111])).
% 14.92/2.24  fof(f1430,plain,(
% 14.92/2.24    ( ! [X1] : (r1_tarski(k3_xboole_0(X1,k4_xboole_0(sK0,sK1)),k2_xboole_0(sK2,k1_xboole_0))) ) | ~spl3_1),
% 14.92/2.24    inference(superposition,[],[f918,f560])).
% 14.92/2.24  fof(f48634,plain,(
% 14.92/2.24    ~spl3_129 | spl3_128),
% 14.92/2.24    inference(avatar_split_clause,[],[f46350,f43236,f43241])).
% 14.92/2.24  fof(f46350,plain,(
% 14.92/2.24    k1_xboole_0 != sK1 | spl3_128),
% 14.92/2.24    inference(superposition,[],[f46276,f8902])).
% 14.92/2.24  fof(f8902,plain,(
% 14.92/2.24    ( ! [X6,X7] : (k2_xboole_0(k4_xboole_0(X6,X7),X6) = X6) )),
% 14.92/2.24    inference(forward_demodulation,[],[f8819,f7367])).
% 14.92/2.24  fof(f7367,plain,(
% 14.92/2.24    ( ! [X23,X22] : (k5_xboole_0(k4_xboole_0(X22,X23),k3_xboole_0(X22,X23)) = X22) )),
% 14.92/2.24    inference(superposition,[],[f3042,f1559])).
% 14.92/2.24  fof(f8819,plain,(
% 14.92/2.24    ( ! [X6,X7] : (k2_xboole_0(k4_xboole_0(X6,X7),X6) = k5_xboole_0(k4_xboole_0(X6,X7),k3_xboole_0(X6,X7))) )),
% 14.92/2.24    inference(superposition,[],[f3037,f44])).
% 14.92/2.24  fof(f46276,plain,(
% 14.92/2.24    ( ! [X1] : (k1_xboole_0 != k2_xboole_0(k4_xboole_0(sK1,sK2),X1)) ) | spl3_128),
% 14.92/2.24    inference(resolution,[],[f43237,f43073])).
% 14.92/2.24  fof(f43073,plain,(
% 14.92/2.24    ( ! [X12,X11] : (r1_tarski(X11,k1_xboole_0) | k1_xboole_0 != k2_xboole_0(X11,X12)) )),
% 14.92/2.24    inference(superposition,[],[f22558,f980])).
% 14.92/2.24  fof(f980,plain,(
% 14.92/2.24    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X3,X4))) )),
% 14.92/2.24    inference(resolution,[],[f947,f50])).
% 14.92/2.24  fof(f947,plain,(
% 14.92/2.24    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 14.92/2.24    inference(subsumption_resolution,[],[f928,f294])).
% 14.92/2.24  fof(f928,plain,(
% 14.92/2.24    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X1) | r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 14.92/2.24    inference(superposition,[],[f54,f148])).
% 14.92/2.24  fof(f148,plain,(
% 14.92/2.24    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(X6,X6)) )),
% 14.92/2.24    inference(resolution,[],[f50,f101])).
% 14.92/2.24  fof(f101,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 14.92/2.24    inference(forward_demodulation,[],[f95,f37])).
% 14.92/2.24  fof(f95,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(X0,k5_xboole_0(X0,k1_xboole_0))) )),
% 14.92/2.24    inference(superposition,[],[f43,f38])).
% 14.92/2.24  fof(f43237,plain,(
% 14.92/2.24    ~r1_tarski(k4_xboole_0(sK1,sK2),k1_xboole_0) | spl3_128),
% 14.92/2.24    inference(avatar_component_clause,[],[f43236])).
% 14.92/2.24  fof(f48626,plain,(
% 14.92/2.24    spl3_128 | ~spl3_148),
% 14.92/2.24    inference(avatar_contradiction_clause,[],[f48625])).
% 14.92/2.24  fof(f48625,plain,(
% 14.92/2.24    $false | (spl3_128 | ~spl3_148)),
% 14.92/2.24    inference(subsumption_resolution,[],[f48205,f46350])).
% 14.92/2.24  fof(f48205,plain,(
% 14.92/2.24    k1_xboole_0 = sK1 | ~spl3_148),
% 14.92/2.24    inference(superposition,[],[f46387,f38])).
% 14.92/2.24  fof(f46387,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0) | ~spl3_148),
% 14.92/2.24    inference(avatar_component_clause,[],[f46385])).
% 14.92/2.24  fof(f46385,plain,(
% 14.92/2.24    spl3_148 <=> k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_148])])).
% 14.92/2.24  fof(f48624,plain,(
% 14.92/2.24    spl3_128 | ~spl3_148),
% 14.92/2.24    inference(avatar_contradiction_clause,[],[f48623])).
% 14.92/2.24  fof(f48623,plain,(
% 14.92/2.24    $false | (spl3_128 | ~spl3_148)),
% 14.92/2.24    inference(subsumption_resolution,[],[f48228,f46350])).
% 14.92/2.24  fof(f48228,plain,(
% 14.92/2.24    k1_xboole_0 = sK1 | ~spl3_148),
% 14.92/2.24    inference(superposition,[],[f38,f46387])).
% 14.92/2.24  fof(f48622,plain,(
% 14.92/2.24    spl3_128 | ~spl3_148),
% 14.92/2.24    inference(avatar_contradiction_clause,[],[f48621])).
% 14.92/2.24  fof(f48621,plain,(
% 14.92/2.24    $false | (spl3_128 | ~spl3_148)),
% 14.92/2.24    inference(subsumption_resolution,[],[f48359,f46350])).
% 14.92/2.24  fof(f48359,plain,(
% 14.92/2.24    k1_xboole_0 = sK1 | ~spl3_148),
% 14.92/2.24    inference(forward_demodulation,[],[f48358,f78])).
% 14.92/2.24  fof(f48358,plain,(
% 14.92/2.24    sK1 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_148),
% 14.92/2.24    inference(forward_demodulation,[],[f48290,f1113])).
% 14.92/2.24  fof(f1113,plain,(
% 14.92/2.24    ( ! [X6] : (k2_xboole_0(k1_xboole_0,X6) = X6) )),
% 14.92/2.24    inference(forward_demodulation,[],[f1112,f37])).
% 14.92/2.24  fof(f1112,plain,(
% 14.92/2.24    ( ! [X6] : (k5_xboole_0(X6,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X6)) )),
% 14.92/2.24    inference(forward_demodulation,[],[f1087,f70])).
% 14.92/2.24  fof(f70,plain,(
% 14.92/2.24    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 14.92/2.24    inference(superposition,[],[f40,f35])).
% 14.92/2.24  fof(f1087,plain,(
% 14.92/2.24    ( ! [X6] : (k2_xboole_0(k1_xboole_0,X6) = k5_xboole_0(X6,k3_xboole_0(k1_xboole_0,X6))) )),
% 14.92/2.24    inference(superposition,[],[f46,f78])).
% 14.92/2.24  fof(f48290,plain,(
% 14.92/2.24    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,sK1) | ~spl3_148),
% 14.92/2.24    inference(superposition,[],[f3037,f46387])).
% 14.92/2.24  fof(f48620,plain,(
% 14.92/2.24    spl3_169 | spl3_123 | ~spl3_27),
% 14.92/2.24    inference(avatar_split_clause,[],[f43152,f967,f43213,f48618])).
% 14.92/2.24  fof(f43152,plain,(
% 14.92/2.24    ( ! [X87] : (r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 != k2_xboole_0(X87,k2_xboole_0(sK0,sK2))) ) | ~spl3_27),
% 14.92/2.24    inference(superposition,[],[f22558,f1855])).
% 14.92/2.24  fof(f48616,plain,(
% 14.92/2.24    spl3_168 | spl3_121 | ~spl3_26),
% 14.92/2.24    inference(avatar_split_clause,[],[f43136,f962,f43204,f48614])).
% 14.92/2.24  fof(f43136,plain,(
% 14.92/2.24    ( ! [X75] : (r1_tarski(sK0,k1_xboole_0) | k1_xboole_0 != k2_xboole_0(X75,k2_xboole_0(sK1,sK2))) ) | ~spl3_26),
% 14.92/2.24    inference(superposition,[],[f22558,f1808])).
% 14.92/2.24  fof(f48612,plain,(
% 14.92/2.24    ~spl3_122 | spl3_167 | ~spl3_27),
% 14.92/2.24    inference(avatar_split_clause,[],[f43097,f967,f48610,f43209])).
% 14.92/2.24  fof(f48610,plain,(
% 14.92/2.24    spl3_167 <=> ! [X45] : r1_tarski(k3_xboole_0(sK1,X45),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_167])])).
% 14.92/2.24  fof(f43097,plain,(
% 14.92/2.24    ( ! [X45] : (r1_tarski(k3_xboole_0(sK1,X45),k1_xboole_0) | k1_xboole_0 != k2_xboole_0(sK0,sK2)) ) | ~spl3_27),
% 14.92/2.24    inference(superposition,[],[f22558,f1844])).
% 14.92/2.24  fof(f1844,plain,(
% 14.92/2.24    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,X2),k2_xboole_0(sK0,sK2))) ) | ~spl3_27),
% 14.92/2.24    inference(resolution,[],[f1826,f50])).
% 14.92/2.24  fof(f1826,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k3_xboole_0(sK1,X0),k2_xboole_0(sK0,sK2))) ) | ~spl3_27),
% 14.92/2.24    inference(forward_demodulation,[],[f1821,f1111])).
% 14.92/2.24  fof(f1821,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k3_xboole_0(sK1,X0),k2_xboole_0(k2_xboole_0(sK0,sK2),k1_xboole_0))) ) | ~spl3_27),
% 14.92/2.24    inference(superposition,[],[f1697,f548])).
% 14.92/2.24  fof(f48608,plain,(
% 14.92/2.24    ~spl3_120 | spl3_166 | ~spl3_26),
% 14.92/2.24    inference(avatar_split_clause,[],[f43093,f962,f48606,f43200])).
% 14.92/2.24  fof(f48606,plain,(
% 14.92/2.24    spl3_166 <=> ! [X41] : r1_tarski(k3_xboole_0(sK0,X41),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_166])])).
% 14.92/2.24  fof(f43093,plain,(
% 14.92/2.24    ( ! [X41] : (r1_tarski(k3_xboole_0(sK0,X41),k1_xboole_0) | k1_xboole_0 != k2_xboole_0(sK1,sK2)) ) | ~spl3_26),
% 14.92/2.24    inference(superposition,[],[f22558,f1797])).
% 14.92/2.24  fof(f1797,plain,(
% 14.92/2.24    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,X2),k2_xboole_0(sK1,sK2))) ) | ~spl3_26),
% 14.92/2.24    inference(resolution,[],[f1779,f50])).
% 14.92/2.24  fof(f1779,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,X0),k2_xboole_0(sK1,sK2))) ) | ~spl3_26),
% 14.92/2.24    inference(forward_demodulation,[],[f1774,f1111])).
% 14.92/2.24  fof(f1774,plain,(
% 14.92/2.24    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,X0),k2_xboole_0(k2_xboole_0(sK1,sK2),k1_xboole_0))) ) | ~spl3_26),
% 14.92/2.24    inference(superposition,[],[f1674,f548])).
% 14.92/2.24  fof(f48604,plain,(
% 14.92/2.24    ~spl3_124 | spl3_165 | ~spl3_2),
% 14.92/2.24    inference(avatar_split_clause,[],[f43090,f61,f48602,f43218])).
% 14.92/2.24  fof(f48602,plain,(
% 14.92/2.24    spl3_165 <=> ! [X38] : r1_tarski(k3_xboole_0(k4_xboole_0(sK1,sK0),X38),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_165])])).
% 14.92/2.24  fof(f43090,plain,(
% 14.92/2.24    ( ! [X38] : (r1_tarski(k3_xboole_0(k4_xboole_0(sK1,sK0),X38),k1_xboole_0) | k1_xboole_0 != sK2) ) | ~spl3_2),
% 14.92/2.24    inference(superposition,[],[f22558,f1633])).
% 14.92/2.24  fof(f1633,plain,(
% 14.92/2.24    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(k4_xboole_0(sK1,sK0),X2),sK2)) ) | ~spl3_2),
% 14.92/2.24    inference(resolution,[],[f1491,f50])).
% 14.92/2.24  fof(f48600,plain,(
% 14.92/2.24    ~spl3_124 | spl3_164 | ~spl3_1),
% 14.92/2.24    inference(avatar_split_clause,[],[f43089,f56,f48598,f43218])).
% 14.92/2.24  fof(f48598,plain,(
% 14.92/2.24    spl3_164 <=> ! [X37] : r1_tarski(k3_xboole_0(k4_xboole_0(sK0,sK1),X37),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_164])])).
% 14.92/2.24  fof(f43089,plain,(
% 14.92/2.24    ( ! [X37] : (r1_tarski(k3_xboole_0(k4_xboole_0(sK0,sK1),X37),k1_xboole_0) | k1_xboole_0 != sK2) ) | ~spl3_1),
% 14.92/2.24    inference(superposition,[],[f22558,f1439])).
% 14.92/2.24  fof(f1439,plain,(
% 14.92/2.24    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK1),X2),sK2)) ) | ~spl3_1),
% 14.92/2.24    inference(resolution,[],[f1434,f50])).
% 14.92/2.24  fof(f48596,plain,(
% 14.92/2.24    ~spl3_120 | spl3_163 | ~spl3_26),
% 14.92/2.24    inference(avatar_split_clause,[],[f43119,f962,f48594,f43200])).
% 14.92/2.24  fof(f48594,plain,(
% 14.92/2.24    spl3_163 <=> ! [X62] : r1_tarski(k4_xboole_0(sK0,X62),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_163])])).
% 14.92/2.24  fof(f43119,plain,(
% 14.92/2.24    ( ! [X62] : (r1_tarski(k4_xboole_0(sK0,X62),k1_xboole_0) | k1_xboole_0 != k2_xboole_0(sK1,sK2)) ) | ~spl3_26),
% 14.92/2.24    inference(superposition,[],[f22558,f1786])).
% 14.92/2.24  fof(f1786,plain,(
% 14.92/2.24    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X3),k2_xboole_0(sK1,sK2))) ) | ~spl3_26),
% 14.92/2.24    inference(resolution,[],[f1783,f50])).
% 14.92/2.24  fof(f48592,plain,(
% 14.92/2.24    ~spl3_122 | spl3_162 | ~spl3_27),
% 14.92/2.24    inference(avatar_split_clause,[],[f43117,f967,f48590,f43209])).
% 14.92/2.24  fof(f48590,plain,(
% 14.92/2.24    spl3_162 <=> ! [X60] : r1_tarski(k4_xboole_0(sK1,X60),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_162])])).
% 14.92/2.24  fof(f43117,plain,(
% 14.92/2.24    ( ! [X60] : (r1_tarski(k4_xboole_0(sK1,X60),k1_xboole_0) | k1_xboole_0 != k2_xboole_0(sK0,sK2)) ) | ~spl3_27),
% 14.92/2.24    inference(superposition,[],[f22558,f1833])).
% 14.92/2.24  fof(f1833,plain,(
% 14.92/2.24    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,X3),k2_xboole_0(sK0,sK2))) ) | ~spl3_27),
% 14.92/2.24    inference(resolution,[],[f1830,f50])).
% 14.92/2.24  fof(f48588,plain,(
% 14.92/2.24    ~spl3_146 | spl3_123 | ~spl3_35),
% 14.92/2.24    inference(avatar_split_clause,[],[f43160,f3906,f43213,f46373])).
% 14.92/2.24  fof(f3906,plain,(
% 14.92/2.24    spl3_35 <=> k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 14.92/2.24  fof(f43160,plain,(
% 14.92/2.24    r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 != k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)) | ~spl3_35),
% 14.92/2.24    inference(superposition,[],[f22558,f3908])).
% 14.92/2.24  fof(f3908,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))) | ~spl3_35),
% 14.92/2.24    inference(avatar_component_clause,[],[f3906])).
% 14.92/2.24  fof(f48361,plain,(
% 14.92/2.24    spl3_129 | ~spl3_148),
% 14.92/2.24    inference(avatar_contradiction_clause,[],[f48360])).
% 14.92/2.24  fof(f48360,plain,(
% 14.92/2.24    $false | (spl3_129 | ~spl3_148)),
% 14.92/2.24    inference(subsumption_resolution,[],[f48359,f43243])).
% 14.92/2.24  fof(f43243,plain,(
% 14.92/2.24    k1_xboole_0 != sK1 | spl3_129),
% 14.92/2.24    inference(avatar_component_clause,[],[f43241])).
% 14.92/2.24  fof(f48314,plain,(
% 14.92/2.24    spl3_129 | ~spl3_148),
% 14.92/2.24    inference(avatar_contradiction_clause,[],[f48313])).
% 14.92/2.24  fof(f48313,plain,(
% 14.92/2.24    $false | (spl3_129 | ~spl3_148)),
% 14.92/2.24    inference(subsumption_resolution,[],[f48228,f43243])).
% 14.92/2.24  fof(f48309,plain,(
% 14.92/2.24    spl3_129 | ~spl3_148),
% 14.92/2.24    inference(avatar_contradiction_clause,[],[f48308])).
% 14.92/2.24  fof(f48308,plain,(
% 14.92/2.24    $false | (spl3_129 | ~spl3_148)),
% 14.92/2.24    inference(subsumption_resolution,[],[f48205,f43243])).
% 14.92/2.24  fof(f48201,plain,(
% 14.92/2.24    spl3_161 | spl3_123 | ~spl3_7),
% 14.92/2.24    inference(avatar_split_clause,[],[f43157,f170,f43213,f48199])).
% 14.92/2.24  fof(f43157,plain,(
% 14.92/2.24    ( ! [X91] : (r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 != k2_xboole_0(sK0,k2_xboole_0(sK2,X91))) ) | ~spl3_7),
% 14.92/2.24    inference(superposition,[],[f22558,f1051])).
% 14.92/2.24  fof(f47972,plain,(
% 14.92/2.24    spl3_160 | ~spl3_159),
% 14.92/2.24    inference(avatar_split_clause,[],[f47907,f47786,f47969])).
% 14.92/2.24  fof(f47969,plain,(
% 14.92/2.24    spl3_160 <=> sK0 = k3_xboole_0(sK0,k2_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_160])])).
% 14.92/2.24  fof(f47786,plain,(
% 14.92/2.24    spl3_159 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_159])])).
% 14.92/2.24  fof(f47907,plain,(
% 14.92/2.24    sK0 = k3_xboole_0(sK0,k2_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_159),
% 14.92/2.24    inference(forward_demodulation,[],[f47829,f38])).
% 14.92/2.24  fof(f47829,plain,(
% 14.92/2.24    k4_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_159),
% 14.92/2.24    inference(superposition,[],[f44,f47788])).
% 14.92/2.24  fof(f47788,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_159),
% 14.92/2.24    inference(avatar_component_clause,[],[f47786])).
% 14.92/2.24  fof(f47789,plain,(
% 14.92/2.24    spl3_159 | ~spl3_157),
% 14.92/2.24    inference(avatar_split_clause,[],[f47259,f47254,f47786])).
% 14.92/2.24  fof(f47254,plain,(
% 14.92/2.24    spl3_157 <=> r1_tarski(sK0,k2_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_157])])).
% 14.92/2.24  fof(f47259,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_157),
% 14.92/2.24    inference(resolution,[],[f47256,f50])).
% 14.92/2.24  fof(f47256,plain,(
% 14.92/2.24    r1_tarski(sK0,k2_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_157),
% 14.92/2.24    inference(avatar_component_clause,[],[f47254])).
% 14.92/2.24  fof(f47588,plain,(
% 14.92/2.24    spl3_158 | ~spl3_156),
% 14.92/2.24    inference(avatar_split_clause,[],[f47252,f47246,f47585])).
% 14.92/2.24  fof(f47585,plain,(
% 14.92/2.24    spl3_158 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k5_xboole_0(sK1,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_158])])).
% 14.92/2.24  fof(f47246,plain,(
% 14.92/2.24    spl3_156 <=> r1_tarski(k4_xboole_0(sK0,sK2),k5_xboole_0(sK1,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_156])])).
% 14.92/2.24  fof(f47252,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k5_xboole_0(sK1,sK2)) | ~spl3_156),
% 14.92/2.24    inference(resolution,[],[f47248,f50])).
% 14.92/2.24  fof(f47248,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK0,sK2),k5_xboole_0(sK1,sK2)) | ~spl3_156),
% 14.92/2.24    inference(avatar_component_clause,[],[f47246])).
% 14.92/2.24  fof(f47257,plain,(
% 14.92/2.24    spl3_157 | ~spl3_156),
% 14.92/2.24    inference(avatar_split_clause,[],[f47250,f47246,f47254])).
% 14.92/2.24  fof(f47250,plain,(
% 14.92/2.24    r1_tarski(sK0,k2_xboole_0(sK2,k5_xboole_0(sK1,sK2))) | ~spl3_156),
% 14.92/2.24    inference(resolution,[],[f47248,f54])).
% 14.92/2.24  fof(f47249,plain,(
% 14.92/2.24    spl3_156 | ~spl3_154),
% 14.92/2.24    inference(avatar_split_clause,[],[f47235,f47067,f47246])).
% 14.92/2.24  fof(f47067,plain,(
% 14.92/2.24    spl3_154 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_154])])).
% 14.92/2.24  fof(f47235,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK0,sK2),k5_xboole_0(sK1,sK2)) | ~spl3_154),
% 14.92/2.24    inference(superposition,[],[f47181,f47])).
% 14.92/2.24  fof(f47181,plain,(
% 14.92/2.24    ( ! [X7] : (r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(k4_xboole_0(sK1,sK2),X7))) ) | ~spl3_154),
% 14.92/2.24    inference(subsumption_resolution,[],[f47101,f294])).
% 14.92/2.24  fof(f47101,plain,(
% 14.92/2.24    ( ! [X7] : (~r1_tarski(k1_xboole_0,X7) | r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(k4_xboole_0(sK1,sK2),X7))) ) | ~spl3_154),
% 14.92/2.24    inference(superposition,[],[f54,f47069])).
% 14.92/2.24  fof(f47069,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) | ~spl3_154),
% 14.92/2.24    inference(avatar_component_clause,[],[f47067])).
% 14.92/2.24  fof(f47229,plain,(
% 14.92/2.24    spl3_155 | ~spl3_154),
% 14.92/2.24    inference(avatar_split_clause,[],[f47094,f47067,f47226])).
% 14.92/2.24  fof(f47226,plain,(
% 14.92/2.24    spl3_155 <=> r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK2),k5_xboole_0(sK1,sK2)),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_155])])).
% 14.92/2.24  fof(f47094,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK2),k5_xboole_0(sK1,sK2)),k1_xboole_0) | ~spl3_154),
% 14.92/2.24    inference(superposition,[],[f510,f47069])).
% 14.92/2.24  fof(f510,plain,(
% 14.92/2.24    ( ! [X4,X2,X3] : (r1_tarski(k4_xboole_0(X2,k5_xboole_0(X3,X4)),k4_xboole_0(X2,k4_xboole_0(X3,X4)))) )),
% 14.92/2.24    inference(resolution,[],[f53,f43])).
% 14.92/2.24  fof(f47070,plain,(
% 14.92/2.24    spl3_154 | ~spl3_149),
% 14.92/2.24    inference(avatar_split_clause,[],[f46819,f46813,f47067])).
% 14.92/2.24  fof(f46813,plain,(
% 14.92/2.24    spl3_149 <=> r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_149])])).
% 14.92/2.24  fof(f46819,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) | ~spl3_149),
% 14.92/2.24    inference(resolution,[],[f46815,f50])).
% 14.92/2.24  fof(f46815,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) | ~spl3_149),
% 14.92/2.24    inference(avatar_component_clause,[],[f46813])).
% 14.92/2.24  fof(f47061,plain,(
% 14.92/2.24    spl3_153 | ~spl3_151),
% 14.92/2.24    inference(avatar_split_clause,[],[f47049,f47042,f47058])).
% 14.92/2.24  fof(f47058,plain,(
% 14.92/2.24    spl3_153 <=> r1_tarski(sK1,k2_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(sK2,sK0))))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_153])])).
% 14.92/2.24  fof(f47042,plain,(
% 14.92/2.24    spl3_151 <=> r1_tarski(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,k4_xboole_0(sK2,sK0)))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_151])])).
% 14.92/2.24  fof(f47049,plain,(
% 14.92/2.24    r1_tarski(sK1,k2_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(sK2,sK0)))) | ~spl3_151),
% 14.92/2.24    inference(resolution,[],[f47044,f54])).
% 14.92/2.24  fof(f47044,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,k4_xboole_0(sK2,sK0))) | ~spl3_151),
% 14.92/2.24    inference(avatar_component_clause,[],[f47042])).
% 14.92/2.24  fof(f47056,plain,(
% 14.92/2.24    spl3_152 | ~spl3_150),
% 14.92/2.24    inference(avatar_split_clause,[],[f47046,f47037,f47053])).
% 14.92/2.24  fof(f47053,plain,(
% 14.92/2.24    spl3_152 <=> r1_tarski(sK0,k2_xboole_0(sK1,k3_xboole_0(sK0,k4_xboole_0(sK2,sK1))))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_152])])).
% 14.92/2.24  fof(f47037,plain,(
% 14.92/2.24    spl3_150 <=> r1_tarski(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK2,sK1)))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_150])])).
% 14.92/2.24  fof(f47046,plain,(
% 14.92/2.24    r1_tarski(sK0,k2_xboole_0(sK1,k3_xboole_0(sK0,k4_xboole_0(sK2,sK1)))) | ~spl3_150),
% 14.92/2.24    inference(resolution,[],[f47039,f54])).
% 14.92/2.24  fof(f47039,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK2,sK1))) | ~spl3_150),
% 14.92/2.24    inference(avatar_component_clause,[],[f47037])).
% 14.92/2.24  fof(f47045,plain,(
% 14.92/2.24    spl3_151 | ~spl3_15),
% 14.92/2.24    inference(avatar_split_clause,[],[f46600,f353,f47042])).
% 14.92/2.24  fof(f353,plain,(
% 14.92/2.24    spl3_15 <=> k4_xboole_0(sK1,sK0) = k3_xboole_0(k4_xboole_0(sK1,sK0),sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 14.92/2.24  fof(f46600,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,k4_xboole_0(sK2,sK0))) | ~spl3_15),
% 14.92/2.24    inference(forward_demodulation,[],[f46599,f15339])).
% 14.92/2.24  fof(f15339,plain,(
% 14.92/2.24    ( ! [X8,X7,X9] : (k3_xboole_0(X7,k4_xboole_0(X8,X9)) = k3_xboole_0(X8,k4_xboole_0(X7,X9))) )),
% 14.92/2.24    inference(superposition,[],[f1947,f51])).
% 14.92/2.24  fof(f1947,plain,(
% 14.92/2.24    ( ! [X4,X2,X3] : (k3_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(k3_xboole_0(X3,X2),X4)) )),
% 14.92/2.24    inference(superposition,[],[f51,f40])).
% 14.92/2.24  fof(f46599,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK1,sK0),k3_xboole_0(sK2,k4_xboole_0(sK1,sK0))) | ~spl3_15),
% 14.92/2.24    inference(forward_demodulation,[],[f46598,f40])).
% 14.92/2.24  fof(f46598,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK1,sK0),k3_xboole_0(k4_xboole_0(sK1,sK0),sK2)) | ~spl3_15),
% 14.92/2.24    inference(forward_demodulation,[],[f46431,f1559])).
% 14.92/2.24  fof(f46431,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK1,sK0),k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k4_xboole_0(sK1,sK0),sK2))) | ~spl3_15),
% 14.92/2.24    inference(superposition,[],[f274,f355])).
% 14.92/2.24  fof(f355,plain,(
% 14.92/2.24    k4_xboole_0(sK1,sK0) = k3_xboole_0(k4_xboole_0(sK1,sK0),sK2) | ~spl3_15),
% 14.92/2.24    inference(avatar_component_clause,[],[f353])).
% 14.92/2.24  fof(f274,plain,(
% 14.92/2.24    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 14.92/2.24    inference(forward_demodulation,[],[f256,f41])).
% 14.92/2.24  fof(f256,plain,(
% 14.92/2.24    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),X0))) )),
% 14.92/2.24    inference(superposition,[],[f98,f44])).
% 14.92/2.24  fof(f98,plain,(
% 14.92/2.24    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),k5_xboole_0(X3,X2))) )),
% 14.92/2.24    inference(superposition,[],[f43,f41])).
% 14.92/2.24  fof(f47040,plain,(
% 14.92/2.24    spl3_150 | ~spl3_14),
% 14.92/2.24    inference(avatar_split_clause,[],[f46597,f348,f47037])).
% 14.92/2.24  fof(f348,plain,(
% 14.92/2.24    spl3_14 <=> k4_xboole_0(sK0,sK1) = k3_xboole_0(k4_xboole_0(sK0,sK1),sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 14.92/2.24  fof(f46597,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK2,sK1))) | ~spl3_14),
% 14.92/2.24    inference(forward_demodulation,[],[f46596,f15339])).
% 14.92/2.24  fof(f46596,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK0,sK1),k3_xboole_0(sK2,k4_xboole_0(sK0,sK1))) | ~spl3_14),
% 14.92/2.24    inference(forward_demodulation,[],[f46595,f40])).
% 14.92/2.24  fof(f46595,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK0,sK1),k3_xboole_0(k4_xboole_0(sK0,sK1),sK2)) | ~spl3_14),
% 14.92/2.24    inference(forward_demodulation,[],[f46430,f1559])).
% 14.92/2.24  fof(f46430,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK2))) | ~spl3_14),
% 14.92/2.24    inference(superposition,[],[f274,f350])).
% 14.92/2.24  fof(f350,plain,(
% 14.92/2.24    k4_xboole_0(sK0,sK1) = k3_xboole_0(k4_xboole_0(sK0,sK1),sK2) | ~spl3_14),
% 14.92/2.24    inference(avatar_component_clause,[],[f348])).
% 14.92/2.24  fof(f46816,plain,(
% 14.92/2.24    spl3_149 | ~spl3_72 | ~spl3_79),
% 14.92/2.24    inference(avatar_split_clause,[],[f46594,f13486,f12545,f46813])).
% 14.92/2.24  fof(f12545,plain,(
% 14.92/2.24    spl3_72 <=> k4_xboole_0(sK1,sK2) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 14.92/2.24  fof(f13486,plain,(
% 14.92/2.24    spl3_79 <=> k4_xboole_0(sK0,sK2) = k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_79])])).
% 14.92/2.24  fof(f46594,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) | (~spl3_72 | ~spl3_79)),
% 14.92/2.24    inference(forward_demodulation,[],[f46593,f12547])).
% 14.92/2.24  fof(f12547,plain,(
% 14.92/2.24    k4_xboole_0(sK1,sK2) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_72),
% 14.92/2.24    inference(avatar_component_clause,[],[f12545])).
% 14.92/2.24  fof(f46593,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK0,sK2),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | ~spl3_79),
% 14.92/2.24    inference(forward_demodulation,[],[f46592,f15339])).
% 14.92/2.24  fof(f46592,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK0,sK2),k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))) | ~spl3_79),
% 14.92/2.24    inference(forward_demodulation,[],[f46591,f40])).
% 14.92/2.24  fof(f46591,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK0,sK2),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)) | ~spl3_79),
% 14.92/2.24    inference(forward_demodulation,[],[f46426,f1559])).
% 14.92/2.24  fof(f46426,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK0,sK2),k5_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1))) | ~spl3_79),
% 14.92/2.24    inference(superposition,[],[f274,f13488])).
% 14.92/2.24  fof(f13488,plain,(
% 14.92/2.24    k4_xboole_0(sK0,sK2) = k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) | ~spl3_79),
% 14.92/2.24    inference(avatar_component_clause,[],[f13486])).
% 14.92/2.24  fof(f46396,plain,(
% 14.92/2.24    ~spl3_148 | spl3_123),
% 14.92/2.24    inference(avatar_split_clause,[],[f46395,f43213,f46385])).
% 14.92/2.24  fof(f46395,plain,(
% 14.92/2.24    k1_xboole_0 != k4_xboole_0(sK1,k1_xboole_0) | spl3_123),
% 14.92/2.24    inference(resolution,[],[f43214,f49])).
% 14.92/2.24  fof(f43214,plain,(
% 14.92/2.24    ~r1_tarski(sK1,k1_xboole_0) | spl3_123),
% 14.92/2.24    inference(avatar_component_clause,[],[f43213])).
% 14.92/2.24  fof(f46388,plain,(
% 14.92/2.24    spl3_148 | ~spl3_123),
% 14.92/2.24    inference(avatar_split_clause,[],[f46382,f43213,f46385])).
% 14.92/2.24  fof(f46382,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0) | ~spl3_123),
% 14.92/2.24    inference(resolution,[],[f43215,f50])).
% 14.92/2.24  fof(f43215,plain,(
% 14.92/2.24    r1_tarski(sK1,k1_xboole_0) | ~spl3_123),
% 14.92/2.24    inference(avatar_component_clause,[],[f43213])).
% 14.92/2.24  fof(f46380,plain,(
% 14.92/2.24    spl3_147 | spl3_123 | ~spl3_29),
% 14.92/2.24    inference(avatar_split_clause,[],[f43154,f1001,f43213,f46378])).
% 14.92/2.24  fof(f43154,plain,(
% 14.92/2.24    ( ! [X89] : (r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 != k2_xboole_0(k2_xboole_0(sK0,sK2),X89)) ) | ~spl3_29),
% 14.92/2.24    inference(superposition,[],[f22558,f1067])).
% 14.92/2.24  fof(f46376,plain,(
% 14.92/2.24    ~spl3_146 | spl3_121 | ~spl3_34),
% 14.92/2.24    inference(avatar_split_clause,[],[f43144,f3798,f43204,f46373])).
% 14.92/2.24  fof(f3798,plain,(
% 14.92/2.24    spl3_34 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 14.92/2.24  fof(f43144,plain,(
% 14.92/2.24    r1_tarski(sK0,k1_xboole_0) | k1_xboole_0 != k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)) | ~spl3_34),
% 14.92/2.24    inference(superposition,[],[f22558,f3800])).
% 14.92/2.24  fof(f3800,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))) | ~spl3_34),
% 14.92/2.24    inference(avatar_component_clause,[],[f3798])).
% 14.92/2.24  fof(f46371,plain,(
% 14.92/2.24    ~spl3_145 | spl3_128),
% 14.92/2.24    inference(avatar_split_clause,[],[f46333,f43236,f46368])).
% 14.92/2.24  fof(f46368,plain,(
% 14.92/2.24    spl3_145 <=> k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_145])])).
% 14.92/2.24  fof(f46333,plain,(
% 14.92/2.24    k1_xboole_0 != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) | spl3_128),
% 14.92/2.24    inference(superposition,[],[f46275,f1592])).
% 14.92/2.24  fof(f1592,plain,(
% 14.92/2.24    ( ! [X2,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X1,X2))) )),
% 14.92/2.24    inference(forward_demodulation,[],[f1591,f41])).
% 14.92/2.24  fof(f1591,plain,(
% 14.92/2.24    ( ! [X2,X1] : (k5_xboole_0(k3_xboole_0(X1,X2),X1) = k2_xboole_0(k3_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X1,X2))) )),
% 14.92/2.24    inference(forward_demodulation,[],[f1518,f51])).
% 14.92/2.24  fof(f1518,plain,(
% 14.92/2.24    ( ! [X2,X1] : (k5_xboole_0(k3_xboole_0(X1,X2),X1) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X1,X2),X1),k4_xboole_0(X1,X2))) )),
% 14.92/2.24    inference(superposition,[],[f47,f45])).
% 14.92/2.24  fof(f46275,plain,(
% 14.92/2.24    ( ! [X0] : (k1_xboole_0 != k2_xboole_0(X0,k4_xboole_0(sK1,sK2))) ) | spl3_128),
% 14.92/2.24    inference(resolution,[],[f43237,f43074])).
% 14.92/2.24  fof(f43074,plain,(
% 14.92/2.24    ( ! [X14,X13] : (r1_tarski(X13,k1_xboole_0) | k1_xboole_0 != k2_xboole_0(X14,X13)) )),
% 14.92/2.24    inference(superposition,[],[f22558,f984])).
% 14.92/2.24  fof(f984,plain,(
% 14.92/2.24    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,X3))) )),
% 14.92/2.24    inference(resolution,[],[f913,f50])).
% 14.92/2.24  fof(f913,plain,(
% 14.92/2.24    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) )),
% 14.92/2.24    inference(resolution,[],[f54,f524])).
% 14.92/2.24  fof(f46365,plain,(
% 14.92/2.24    ~spl3_144 | spl3_128),
% 14.92/2.24    inference(avatar_split_clause,[],[f46281,f43236,f46362])).
% 14.92/2.24  fof(f46362,plain,(
% 14.92/2.24    spl3_144 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_144])])).
% 14.92/2.24  fof(f46281,plain,(
% 14.92/2.24    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) | spl3_128),
% 14.92/2.24    inference(resolution,[],[f43237,f49])).
% 14.92/2.24  fof(f46349,plain,(
% 14.92/2.24    ~spl3_143 | spl3_142),
% 14.92/2.24    inference(avatar_split_clause,[],[f46343,f46339,f46346])).
% 14.92/2.24  fof(f46346,plain,(
% 14.92/2.24    spl3_143 <=> k1_xboole_0 = k5_xboole_0(sK1,sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_143])])).
% 14.92/2.24  fof(f46339,plain,(
% 14.92/2.24    spl3_142 <=> k1_xboole_0 = k5_xboole_0(sK2,sK1)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_142])])).
% 14.92/2.24  fof(f46343,plain,(
% 14.92/2.24    k1_xboole_0 != k5_xboole_0(sK1,sK2) | spl3_142),
% 14.92/2.24    inference(superposition,[],[f46341,f41])).
% 14.92/2.24  fof(f46341,plain,(
% 14.92/2.24    k1_xboole_0 != k5_xboole_0(sK2,sK1) | spl3_142),
% 14.92/2.24    inference(avatar_component_clause,[],[f46339])).
% 14.92/2.24  fof(f46342,plain,(
% 14.92/2.24    ~spl3_142 | spl3_128),
% 14.92/2.24    inference(avatar_split_clause,[],[f46334,f43236,f46339])).
% 14.92/2.24  fof(f46334,plain,(
% 14.92/2.24    k1_xboole_0 != k5_xboole_0(sK2,sK1) | spl3_128),
% 14.92/2.24    inference(superposition,[],[f46275,f47])).
% 14.92/2.24  fof(f46272,plain,(
% 14.92/2.24    spl3_106 | ~spl3_107),
% 14.92/2.24    inference(avatar_contradiction_clause,[],[f46271])).
% 14.92/2.24  fof(f46271,plain,(
% 14.92/2.24    $false | (spl3_106 | ~spl3_107)),
% 14.92/2.24    inference(subsumption_resolution,[],[f46270,f25728])).
% 14.92/2.24  fof(f25728,plain,(
% 14.92/2.24    k1_xboole_0 != k4_xboole_0(sK1,sK2) | spl3_106),
% 14.92/2.24    inference(avatar_component_clause,[],[f25726])).
% 14.92/2.24  fof(f25726,plain,(
% 14.92/2.24    spl3_106 <=> k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_106])])).
% 14.92/2.24  fof(f46270,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(sK1,sK2) | ~spl3_107),
% 14.92/2.24    inference(resolution,[],[f25733,f50])).
% 14.92/2.24  fof(f25733,plain,(
% 14.92/2.24    r1_tarski(sK1,sK2) | ~spl3_107),
% 14.92/2.24    inference(avatar_component_clause,[],[f25731])).
% 14.92/2.24  fof(f25731,plain,(
% 14.92/2.24    spl3_107 <=> r1_tarski(sK1,sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_107])])).
% 14.92/2.24  fof(f46268,plain,(
% 14.92/2.24    spl3_107 | ~spl3_128),
% 14.92/2.24    inference(avatar_split_clause,[],[f45879,f43236,f25731])).
% 14.92/2.24  fof(f45879,plain,(
% 14.92/2.24    r1_tarski(sK1,sK2) | ~spl3_128),
% 14.92/2.24    inference(forward_demodulation,[],[f45876,f1111])).
% 14.92/2.24  fof(f45876,plain,(
% 14.92/2.24    r1_tarski(sK1,k2_xboole_0(sK2,k1_xboole_0)) | ~spl3_128),
% 14.92/2.24    inference(resolution,[],[f43238,f54])).
% 14.92/2.24  fof(f43238,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK1,sK2),k1_xboole_0) | ~spl3_128),
% 14.92/2.24    inference(avatar_component_clause,[],[f43236])).
% 14.92/2.24  fof(f45851,plain,(
% 14.92/2.24    ~spl3_127 | ~spl3_74 | spl3_106),
% 14.92/2.24    inference(avatar_split_clause,[],[f45843,f25726,f12832,f43232])).
% 14.92/2.24  fof(f12832,plain,(
% 14.92/2.24    spl3_74 <=> sK0 = k2_xboole_0(k4_xboole_0(sK1,sK2),sK0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).
% 14.92/2.24  fof(f45843,plain,(
% 14.92/2.24    k1_xboole_0 != sK0 | (~spl3_74 | spl3_106)),
% 14.92/2.24    inference(subsumption_resolution,[],[f43896,f25728])).
% 14.92/2.24  fof(f43896,plain,(
% 14.92/2.24    k1_xboole_0 != sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK2) | ~spl3_74),
% 14.92/2.24    inference(superposition,[],[f43661,f12834])).
% 14.92/2.24  fof(f12834,plain,(
% 14.92/2.24    sK0 = k2_xboole_0(k4_xboole_0(sK1,sK2),sK0) | ~spl3_74),
% 14.92/2.24    inference(avatar_component_clause,[],[f12832])).
% 14.92/2.24  fof(f43661,plain,(
% 14.92/2.24    ( ! [X4,X3] : (k1_xboole_0 != k2_xboole_0(X3,X4) | k1_xboole_0 = X3) )),
% 14.92/2.24    inference(forward_demodulation,[],[f43656,f38])).
% 14.92/2.24  fof(f43656,plain,(
% 14.92/2.24    ( ! [X4,X3] : (k1_xboole_0 != k2_xboole_0(X3,X4) | k1_xboole_0 = k4_xboole_0(X3,k1_xboole_0)) )),
% 14.92/2.24    inference(resolution,[],[f43073,f50])).
% 14.92/2.24  fof(f45842,plain,(
% 14.92/2.24    ~spl3_74 | spl3_106 | ~spl3_140),
% 14.92/2.24    inference(avatar_contradiction_clause,[],[f45841])).
% 14.92/2.24  fof(f45841,plain,(
% 14.92/2.24    $false | (~spl3_74 | spl3_106 | ~spl3_140)),
% 14.92/2.24    inference(subsumption_resolution,[],[f45840,f25728])).
% 14.92/2.24  fof(f45840,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(sK1,sK2) | (~spl3_74 | ~spl3_140)),
% 14.92/2.24    inference(subsumption_resolution,[],[f43896,f45804])).
% 14.92/2.24  fof(f45804,plain,(
% 14.92/2.24    k1_xboole_0 = sK0 | ~spl3_140),
% 14.92/2.24    inference(forward_demodulation,[],[f45803,f78])).
% 14.92/2.24  fof(f45803,plain,(
% 14.92/2.24    sK0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_140),
% 14.92/2.24    inference(forward_demodulation,[],[f45736,f1113])).
% 14.92/2.24  fof(f45736,plain,(
% 14.92/2.24    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,sK0) | ~spl3_140),
% 14.92/2.24    inference(superposition,[],[f3037,f45597])).
% 14.92/2.24  fof(f45597,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_140),
% 14.92/2.24    inference(avatar_component_clause,[],[f45595])).
% 14.92/2.24  fof(f45595,plain,(
% 14.92/2.24    spl3_140 <=> k1_xboole_0 = k4_xboole_0(sK0,k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_140])])).
% 14.92/2.24  fof(f45834,plain,(
% 14.92/2.24    ~spl3_54 | spl3_106 | ~spl3_140),
% 14.92/2.24    inference(avatar_contradiction_clause,[],[f45833])).
% 14.92/2.24  fof(f45833,plain,(
% 14.92/2.24    $false | (~spl3_54 | spl3_106 | ~spl3_140)),
% 14.92/2.24    inference(subsumption_resolution,[],[f45832,f25728])).
% 14.92/2.24  fof(f45832,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(sK1,sK2) | (~spl3_54 | ~spl3_140)),
% 14.92/2.24    inference(subsumption_resolution,[],[f44026,f45804])).
% 14.92/2.24  fof(f44026,plain,(
% 14.92/2.24    k1_xboole_0 != sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK2) | ~spl3_54),
% 14.92/2.24    inference(superposition,[],[f43810,f9264])).
% 14.92/2.24  fof(f43810,plain,(
% 14.92/2.24    ( ! [X4,X3] : (k1_xboole_0 != k2_xboole_0(X3,X4) | k1_xboole_0 = X4) )),
% 14.92/2.24    inference(forward_demodulation,[],[f43805,f38])).
% 14.92/2.24  fof(f43805,plain,(
% 14.92/2.24    ( ! [X4,X3] : (k1_xboole_0 != k2_xboole_0(X3,X4) | k1_xboole_0 = k4_xboole_0(X4,k1_xboole_0)) )),
% 14.92/2.24    inference(resolution,[],[f43074,f50])).
% 14.92/2.24  fof(f45830,plain,(
% 14.92/2.24    spl3_114 | ~spl3_140),
% 14.92/2.24    inference(avatar_contradiction_clause,[],[f45829])).
% 14.92/2.24  fof(f45829,plain,(
% 14.92/2.24    $false | (spl3_114 | ~spl3_140)),
% 14.92/2.24    inference(subsumption_resolution,[],[f44050,f45804])).
% 14.92/2.24  fof(f44050,plain,(
% 14.92/2.24    k1_xboole_0 != sK0 | spl3_114),
% 14.92/2.24    inference(resolution,[],[f43879,f25771])).
% 14.92/2.24  fof(f25771,plain,(
% 14.92/2.24    ~r1_tarski(k3_xboole_0(sK0,sK2),sK1) | spl3_114),
% 14.92/2.24    inference(avatar_component_clause,[],[f25769])).
% 14.92/2.24  fof(f25769,plain,(
% 14.92/2.24    spl3_114 <=> r1_tarski(k3_xboole_0(sK0,sK2),sK1)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_114])])).
% 14.92/2.24  fof(f45828,plain,(
% 14.92/2.24    spl3_100 | ~spl3_140),
% 14.92/2.24    inference(avatar_contradiction_clause,[],[f45827])).
% 14.92/2.24  fof(f45827,plain,(
% 14.92/2.24    $false | (spl3_100 | ~spl3_140)),
% 14.92/2.24    inference(subsumption_resolution,[],[f44051,f45804])).
% 14.92/2.24  fof(f44051,plain,(
% 14.92/2.24    k1_xboole_0 != sK0 | spl3_100),
% 14.92/2.24    inference(resolution,[],[f43879,f25694])).
% 14.92/2.24  fof(f25694,plain,(
% 14.92/2.24    ~r1_tarski(k3_xboole_0(sK0,sK1),sK2) | spl3_100),
% 14.92/2.24    inference(avatar_component_clause,[],[f25692])).
% 14.92/2.24  fof(f25692,plain,(
% 14.92/2.24    spl3_100 <=> r1_tarski(k3_xboole_0(sK0,sK1),sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_100])])).
% 14.92/2.24  fof(f45825,plain,(
% 14.92/2.24    spl3_114 | ~spl3_140),
% 14.92/2.24    inference(avatar_contradiction_clause,[],[f45824])).
% 14.92/2.24  fof(f45824,plain,(
% 14.92/2.24    $false | (spl3_114 | ~spl3_140)),
% 14.92/2.24    inference(subsumption_resolution,[],[f44932,f45804])).
% 14.92/2.24  fof(f44932,plain,(
% 14.92/2.24    k1_xboole_0 != sK0 | spl3_114),
% 14.92/2.24    inference(superposition,[],[f44918,f8900])).
% 14.92/2.24  fof(f44918,plain,(
% 14.92/2.24    ( ! [X13] : (k1_xboole_0 != k2_xboole_0(k3_xboole_0(sK0,sK2),X13)) ) | spl3_114),
% 14.92/2.24    inference(resolution,[],[f44134,f25771])).
% 14.92/2.24  fof(f44134,plain,(
% 14.92/2.24    ( ! [X28,X29,X27] : (r1_tarski(X27,X29) | k1_xboole_0 != k2_xboole_0(X27,X28)) )),
% 14.92/2.24    inference(superposition,[],[f44055,f1263])).
% 14.92/2.24  fof(f1263,plain,(
% 14.92/2.24    ( ! [X8,X7] : (k3_xboole_0(X7,k2_xboole_0(X7,X8)) = X7) )),
% 14.92/2.24    inference(forward_demodulation,[],[f1241,f38])).
% 14.92/2.24  fof(f1241,plain,(
% 14.92/2.24    ( ! [X8,X7] : (k3_xboole_0(X7,k2_xboole_0(X7,X8)) = k4_xboole_0(X7,k1_xboole_0)) )),
% 14.92/2.24    inference(superposition,[],[f44,f980])).
% 14.92/2.24  fof(f45823,plain,(
% 14.92/2.24    spl3_100 | ~spl3_140),
% 14.92/2.24    inference(avatar_contradiction_clause,[],[f45822])).
% 14.92/2.24  fof(f45822,plain,(
% 14.92/2.24    $false | (spl3_100 | ~spl3_140)),
% 14.92/2.24    inference(subsumption_resolution,[],[f44941,f45804])).
% 14.92/2.24  fof(f44941,plain,(
% 14.92/2.24    k1_xboole_0 != sK0 | spl3_100),
% 14.92/2.24    inference(superposition,[],[f44919,f8900])).
% 14.92/2.24  fof(f44919,plain,(
% 14.92/2.24    ( ! [X14] : (k1_xboole_0 != k2_xboole_0(k3_xboole_0(sK0,sK1),X14)) ) | spl3_100),
% 14.92/2.24    inference(resolution,[],[f44134,f25694])).
% 14.92/2.24  fof(f45821,plain,(
% 14.92/2.24    spl3_114 | ~spl3_140),
% 14.92/2.24    inference(avatar_contradiction_clause,[],[f45820])).
% 14.92/2.24  fof(f45820,plain,(
% 14.92/2.24    $false | (spl3_114 | ~spl3_140)),
% 14.92/2.24    inference(subsumption_resolution,[],[f44966,f45804])).
% 14.92/2.24  fof(f44966,plain,(
% 14.92/2.24    k1_xboole_0 != sK0 | spl3_114),
% 14.92/2.24    inference(superposition,[],[f44935,f4322])).
% 14.92/2.24  fof(f44935,plain,(
% 14.92/2.24    ( ! [X0] : (k1_xboole_0 != k2_xboole_0(X0,k3_xboole_0(sK0,sK2))) ) | spl3_114),
% 14.92/2.24    inference(superposition,[],[f44918,f11923])).
% 14.92/2.24  fof(f45819,plain,(
% 14.92/2.24    spl3_100 | ~spl3_140),
% 14.92/2.24    inference(avatar_contradiction_clause,[],[f45818])).
% 14.92/2.24  fof(f45818,plain,(
% 14.92/2.24    $false | (spl3_100 | ~spl3_140)),
% 14.92/2.24    inference(subsumption_resolution,[],[f44975,f45804])).
% 14.92/2.24  fof(f44975,plain,(
% 14.92/2.24    k1_xboole_0 != sK0 | spl3_100),
% 14.92/2.24    inference(superposition,[],[f44944,f4322])).
% 14.92/2.24  fof(f44944,plain,(
% 14.92/2.24    ( ! [X0] : (k1_xboole_0 != k2_xboole_0(X0,k3_xboole_0(sK0,sK1))) ) | spl3_100),
% 14.92/2.24    inference(superposition,[],[f44919,f11923])).
% 14.92/2.24  fof(f45817,plain,(
% 14.92/2.24    spl3_125 | ~spl3_140),
% 14.92/2.24    inference(avatar_contradiction_clause,[],[f45816])).
% 14.92/2.24  fof(f45816,plain,(
% 14.92/2.24    $false | (spl3_125 | ~spl3_140)),
% 14.92/2.24    inference(subsumption_resolution,[],[f45044,f45804])).
% 14.92/2.24  fof(f45044,plain,(
% 14.92/2.24    k1_xboole_0 != sK0 | spl3_125),
% 14.92/2.24    inference(resolution,[],[f43223,f43106])).
% 14.92/2.24  fof(f43106,plain,(
% 14.92/2.24    ( ! [X50,X51] : (r1_tarski(k4_xboole_0(X50,X51),k1_xboole_0) | k1_xboole_0 != X50) )),
% 14.92/2.24    inference(superposition,[],[f22558,f534])).
% 14.92/2.24  fof(f43223,plain,(
% 14.92/2.24    ~r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) | spl3_125),
% 14.92/2.24    inference(avatar_component_clause,[],[f43222])).
% 14.92/2.24  fof(f45815,plain,(
% 14.92/2.24    spl3_125 | ~spl3_140),
% 14.92/2.24    inference(avatar_contradiction_clause,[],[f45814])).
% 14.92/2.24  fof(f45814,plain,(
% 14.92/2.24    $false | (spl3_125 | ~spl3_140)),
% 14.92/2.24    inference(subsumption_resolution,[],[f45045,f45804])).
% 14.92/2.24  fof(f45045,plain,(
% 14.92/2.24    k1_xboole_0 != sK0 | spl3_125),
% 14.92/2.24    inference(resolution,[],[f43223,f44059])).
% 14.92/2.24  fof(f44059,plain,(
% 14.92/2.24    ( ! [X14,X15,X13] : (r1_tarski(k4_xboole_0(X13,X14),X15) | k1_xboole_0 != X13) )),
% 14.92/2.24    inference(superposition,[],[f43879,f268])).
% 14.92/2.24  fof(f45813,plain,(
% 14.92/2.24    spl3_125 | ~spl3_140),
% 14.92/2.24    inference(avatar_contradiction_clause,[],[f45812])).
% 14.92/2.24  fof(f45812,plain,(
% 14.92/2.24    $false | (spl3_125 | ~spl3_140)),
% 14.92/2.24    inference(subsumption_resolution,[],[f45053,f45804])).
% 14.92/2.24  fof(f45053,plain,(
% 14.92/2.24    k1_xboole_0 != sK0 | spl3_125),
% 14.92/2.24    inference(superposition,[],[f45046,f4330])).
% 14.92/2.24  fof(f45046,plain,(
% 14.92/2.24    ( ! [X0] : (k1_xboole_0 != k2_xboole_0(X0,k4_xboole_0(sK0,sK1))) ) | spl3_125),
% 14.92/2.24    inference(resolution,[],[f43223,f43074])).
% 14.92/2.24  fof(f45811,plain,(
% 14.92/2.24    spl3_125 | ~spl3_140),
% 14.92/2.24    inference(avatar_contradiction_clause,[],[f45810])).
% 14.92/2.24  fof(f45810,plain,(
% 14.92/2.24    $false | (spl3_125 | ~spl3_140)),
% 14.92/2.24    inference(subsumption_resolution,[],[f45071,f45804])).
% 14.92/2.24  fof(f45071,plain,(
% 14.92/2.24    k1_xboole_0 != sK0 | spl3_125),
% 14.92/2.24    inference(superposition,[],[f45047,f8902])).
% 14.92/2.24  fof(f45047,plain,(
% 14.92/2.24    ( ! [X1] : (k1_xboole_0 != k2_xboole_0(k4_xboole_0(sK0,sK1),X1)) ) | spl3_125),
% 14.92/2.24    inference(resolution,[],[f43223,f43073])).
% 14.92/2.24  fof(f45806,plain,(
% 14.92/2.24    spl3_127 | ~spl3_140),
% 14.92/2.24    inference(avatar_contradiction_clause,[],[f45805])).
% 14.92/2.24  fof(f45805,plain,(
% 14.92/2.24    $false | (spl3_127 | ~spl3_140)),
% 14.92/2.24    inference(subsumption_resolution,[],[f45804,f43234])).
% 14.92/2.24  fof(f43234,plain,(
% 14.92/2.24    k1_xboole_0 != sK0 | spl3_127),
% 14.92/2.24    inference(avatar_component_clause,[],[f43232])).
% 14.92/2.24  fof(f45760,plain,(
% 14.92/2.24    spl3_127 | ~spl3_140),
% 14.92/2.24    inference(avatar_contradiction_clause,[],[f45759])).
% 14.92/2.24  fof(f45759,plain,(
% 14.92/2.24    $false | (spl3_127 | ~spl3_140)),
% 14.92/2.24    inference(subsumption_resolution,[],[f45677,f43234])).
% 14.92/2.24  fof(f45677,plain,(
% 14.92/2.24    k1_xboole_0 = sK0 | ~spl3_140),
% 14.92/2.24    inference(superposition,[],[f38,f45597])).
% 14.92/2.24  fof(f45755,plain,(
% 14.92/2.24    spl3_127 | ~spl3_140),
% 14.92/2.24    inference(avatar_contradiction_clause,[],[f45754])).
% 14.92/2.24  fof(f45754,plain,(
% 14.92/2.24    $false | (spl3_127 | ~spl3_140)),
% 14.92/2.24    inference(subsumption_resolution,[],[f45654,f43234])).
% 14.92/2.24  fof(f45654,plain,(
% 14.92/2.24    k1_xboole_0 = sK0 | ~spl3_140),
% 14.92/2.24    inference(superposition,[],[f45597,f38])).
% 14.92/2.24  fof(f45650,plain,(
% 14.92/2.24    spl3_141 | spl3_121 | ~spl3_6),
% 14.92/2.24    inference(avatar_split_clause,[],[f43141,f165,f43204,f45648])).
% 14.92/2.24  fof(f43141,plain,(
% 14.92/2.24    ( ! [X79] : (r1_tarski(sK0,k1_xboole_0) | k1_xboole_0 != k2_xboole_0(sK1,k2_xboole_0(sK2,X79))) ) | ~spl3_6),
% 14.92/2.24    inference(superposition,[],[f22558,f1048])).
% 14.92/2.24  fof(f45606,plain,(
% 14.92/2.24    ~spl3_140 | spl3_121),
% 14.92/2.24    inference(avatar_split_clause,[],[f45605,f43204,f45595])).
% 14.92/2.24  fof(f45605,plain,(
% 14.92/2.24    k1_xboole_0 != k4_xboole_0(sK0,k1_xboole_0) | spl3_121),
% 14.92/2.24    inference(resolution,[],[f43205,f49])).
% 14.92/2.24  fof(f43205,plain,(
% 14.92/2.24    ~r1_tarski(sK0,k1_xboole_0) | spl3_121),
% 14.92/2.24    inference(avatar_component_clause,[],[f43204])).
% 14.92/2.24  fof(f45598,plain,(
% 14.92/2.24    spl3_140 | ~spl3_121),
% 14.92/2.24    inference(avatar_split_clause,[],[f45592,f43204,f45595])).
% 14.92/2.24  fof(f45592,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_121),
% 14.92/2.24    inference(resolution,[],[f43206,f50])).
% 14.92/2.24  fof(f43206,plain,(
% 14.92/2.24    r1_tarski(sK0,k1_xboole_0) | ~spl3_121),
% 14.92/2.24    inference(avatar_component_clause,[],[f43204])).
% 14.92/2.24  fof(f45590,plain,(
% 14.92/2.24    spl3_139 | spl3_121 | ~spl3_28),
% 14.92/2.24    inference(avatar_split_clause,[],[f43138,f996,f43204,f45588])).
% 14.92/2.24  fof(f43138,plain,(
% 14.92/2.24    ( ! [X77] : (r1_tarski(sK0,k1_xboole_0) | k1_xboole_0 != k2_xboole_0(k2_xboole_0(sK1,sK2),X77)) ) | ~spl3_28),
% 14.92/2.24    inference(superposition,[],[f22558,f1059])).
% 14.92/2.24  fof(f45586,plain,(
% 14.92/2.24    spl3_135 | spl3_126 | ~spl3_7),
% 14.92/2.24    inference(avatar_split_clause,[],[f43122,f170,f43227,f45003])).
% 14.92/2.24  fof(f45003,plain,(
% 14.92/2.24    spl3_135 <=> ! [X64] : k1_xboole_0 != k2_xboole_0(sK2,X64)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_135])])).
% 14.92/2.24  fof(f43122,plain,(
% 14.92/2.24    ( ! [X65] : (r1_tarski(k4_xboole_0(sK1,sK0),k1_xboole_0) | k1_xboole_0 != k2_xboole_0(sK2,X65)) ) | ~spl3_7),
% 14.92/2.24    inference(superposition,[],[f22558,f993])).
% 14.92/2.24  fof(f993,plain,(
% 14.92/2.24    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK2,X3))) ) | ~spl3_7),
% 14.92/2.24    inference(resolution,[],[f960,f50])).
% 14.92/2.24  fof(f45585,plain,(
% 14.92/2.24    ~spl3_138 | spl3_125),
% 14.92/2.24    inference(avatar_split_clause,[],[f45059,f43222,f45582])).
% 14.92/2.24  fof(f45582,plain,(
% 14.92/2.24    spl3_138 <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_138])])).
% 14.92/2.24  fof(f45059,plain,(
% 14.92/2.24    k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | spl3_125),
% 14.92/2.24    inference(superposition,[],[f45046,f1592])).
% 14.92/2.24  fof(f45086,plain,(
% 14.92/2.24    ~spl3_137 | spl3_125),
% 14.92/2.24    inference(avatar_split_clause,[],[f45052,f43222,f45083])).
% 14.92/2.24  fof(f45083,plain,(
% 14.92/2.24    spl3_137 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_137])])).
% 14.92/2.24  fof(f45052,plain,(
% 14.92/2.24    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | spl3_125),
% 14.92/2.24    inference(resolution,[],[f43223,f49])).
% 14.92/2.24  fof(f45068,plain,(
% 14.92/2.24    ~spl3_136 | spl3_125),
% 14.92/2.24    inference(avatar_split_clause,[],[f45060,f43222,f45065])).
% 14.92/2.24  fof(f45065,plain,(
% 14.92/2.24    spl3_136 <=> k1_xboole_0 = k5_xboole_0(sK1,sK0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_136])])).
% 14.92/2.24  fof(f45060,plain,(
% 14.92/2.24    k1_xboole_0 != k5_xboole_0(sK1,sK0) | spl3_125),
% 14.92/2.24    inference(superposition,[],[f45046,f47])).
% 14.92/2.24  fof(f45015,plain,(
% 14.92/2.24    ~spl3_115 | spl3_119),
% 14.92/2.24    inference(avatar_contradiction_clause,[],[f45014])).
% 14.92/2.24  fof(f45014,plain,(
% 14.92/2.24    $false | (~spl3_115 | spl3_119)),
% 14.92/2.24    inference(subsumption_resolution,[],[f45013,f26382])).
% 14.92/2.24  fof(f26382,plain,(
% 14.92/2.24    k1_xboole_0 != k4_xboole_0(sK0,sK1) | spl3_119),
% 14.92/2.24    inference(avatar_component_clause,[],[f26380])).
% 14.92/2.24  fof(f26380,plain,(
% 14.92/2.24    spl3_119 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_119])])).
% 14.92/2.24  fof(f45013,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_115),
% 14.92/2.24    inference(resolution,[],[f25775,f50])).
% 14.92/2.24  fof(f25775,plain,(
% 14.92/2.24    r1_tarski(sK0,sK1) | ~spl3_115),
% 14.92/2.24    inference(avatar_component_clause,[],[f25773])).
% 14.92/2.24  fof(f25773,plain,(
% 14.92/2.24    spl3_115 <=> r1_tarski(sK0,sK1)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_115])])).
% 14.92/2.24  fof(f45011,plain,(
% 14.92/2.24    spl3_115 | ~spl3_125),
% 14.92/2.24    inference(avatar_split_clause,[],[f45009,f43222,f25773])).
% 14.92/2.24  fof(f45009,plain,(
% 14.92/2.24    r1_tarski(sK0,sK1) | ~spl3_125),
% 14.92/2.24    inference(forward_demodulation,[],[f45006,f1111])).
% 14.92/2.24  fof(f45006,plain,(
% 14.92/2.24    r1_tarski(sK0,k2_xboole_0(sK1,k1_xboole_0)) | ~spl3_125),
% 14.92/2.24    inference(resolution,[],[f43224,f54])).
% 14.92/2.24  fof(f43224,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) | ~spl3_125),
% 14.92/2.24    inference(avatar_component_clause,[],[f43222])).
% 14.92/2.24  fof(f45005,plain,(
% 14.92/2.24    spl3_135 | spl3_125 | ~spl3_6),
% 14.92/2.24    inference(avatar_split_clause,[],[f43121,f165,f43222,f45003])).
% 14.92/2.24  fof(f43121,plain,(
% 14.92/2.24    ( ! [X64] : (r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) | k1_xboole_0 != k2_xboole_0(sK2,X64)) ) | ~spl3_6),
% 14.92/2.24    inference(superposition,[],[f22558,f989])).
% 14.92/2.24  fof(f989,plain,(
% 14.92/2.24    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK2,X3))) ) | ~spl3_6),
% 14.92/2.24    inference(resolution,[],[f959,f50])).
% 14.92/2.24  fof(f45001,plain,(
% 14.92/2.24    ~spl3_131 | spl3_128 | ~spl3_25),
% 14.92/2.24    inference(avatar_split_clause,[],[f43108,f711,f43236,f43784])).
% 14.92/2.24  fof(f43784,plain,(
% 14.92/2.24    spl3_131 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_131])])).
% 14.92/2.24  fof(f711,plain,(
% 14.92/2.24    spl3_25 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k3_xboole_0(sK0,sK1))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 14.92/2.24  fof(f43108,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK1,sK2),k1_xboole_0) | k1_xboole_0 != k3_xboole_0(sK0,sK1) | ~spl3_25),
% 14.92/2.24    inference(superposition,[],[f22558,f713])).
% 14.92/2.24  fof(f713,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k3_xboole_0(sK0,sK1)) | ~spl3_25),
% 14.92/2.24    inference(avatar_component_clause,[],[f711])).
% 14.92/2.24  fof(f45000,plain,(
% 14.92/2.24    ~spl3_131 | spl3_130 | ~spl3_24),
% 14.92/2.24    inference(avatar_split_clause,[],[f43107,f706,f43245,f43784])).
% 14.92/2.24  fof(f706,plain,(
% 14.92/2.24    spl3_24 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK1))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 14.92/2.24  fof(f43107,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK0,sK2),k1_xboole_0) | k1_xboole_0 != k3_xboole_0(sK0,sK1) | ~spl3_24),
% 14.92/2.24    inference(superposition,[],[f22558,f708])).
% 14.92/2.24  fof(f708,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK1)) | ~spl3_24),
% 14.92/2.24    inference(avatar_component_clause,[],[f706])).
% 14.92/2.24  fof(f43802,plain,(
% 14.92/2.24    ~spl3_134 | spl3_114),
% 14.92/2.24    inference(avatar_split_clause,[],[f43778,f25769,f43799])).
% 14.92/2.24  fof(f43778,plain,(
% 14.92/2.24    k1_xboole_0 != k3_xboole_0(sK0,sK2) | spl3_114),
% 14.92/2.24    inference(resolution,[],[f43772,f25771])).
% 14.92/2.24  fof(f43772,plain,(
% 14.92/2.24    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != X0) )),
% 14.92/2.24    inference(forward_demodulation,[],[f43664,f1111])).
% 14.92/2.24  fof(f43664,plain,(
% 14.92/2.24    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k2_xboole_0(X1,k1_xboole_0))) )),
% 14.92/2.24    inference(resolution,[],[f43106,f54])).
% 14.92/2.24  fof(f43797,plain,(
% 14.92/2.24    ~spl3_133 | spl3_108),
% 14.92/2.24    inference(avatar_split_clause,[],[f43777,f25736,f43794])).
% 14.92/2.24  fof(f25736,plain,(
% 14.92/2.24    spl3_108 <=> r1_tarski(k3_xboole_0(sK1,sK2),sK0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_108])])).
% 14.92/2.24  fof(f43777,plain,(
% 14.92/2.24    k1_xboole_0 != k3_xboole_0(sK1,sK2) | spl3_108),
% 14.92/2.24    inference(resolution,[],[f43772,f25738])).
% 14.92/2.24  fof(f25738,plain,(
% 14.92/2.24    ~r1_tarski(k3_xboole_0(sK1,sK2),sK0) | spl3_108),
% 14.92/2.24    inference(avatar_component_clause,[],[f25736])).
% 14.92/2.24  fof(f43792,plain,(
% 14.92/2.24    ~spl3_132 | spl3_3),
% 14.92/2.24    inference(avatar_split_clause,[],[f43780,f66,f43789])).
% 14.92/2.24  fof(f43789,plain,(
% 14.92/2.24    spl3_132 <=> k1_xboole_0 = k5_xboole_0(sK0,sK1)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_132])])).
% 14.92/2.24  fof(f43780,plain,(
% 14.92/2.24    k1_xboole_0 != k5_xboole_0(sK0,sK1) | spl3_3),
% 14.92/2.24    inference(resolution,[],[f43772,f68])).
% 14.92/2.24  fof(f43787,plain,(
% 14.92/2.24    ~spl3_131 | spl3_100),
% 14.92/2.24    inference(avatar_split_clause,[],[f43779,f25692,f43784])).
% 14.92/2.24  fof(f43779,plain,(
% 14.92/2.24    k1_xboole_0 != k3_xboole_0(sK0,sK1) | spl3_100),
% 14.92/2.24    inference(resolution,[],[f43772,f25694])).
% 14.92/2.24  fof(f43248,plain,(
% 14.92/2.24    ~spl3_129 | spl3_130 | ~spl3_85),
% 14.92/2.24    inference(avatar_split_clause,[],[f43183,f15056,f43245,f43241])).
% 14.92/2.24  fof(f43183,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK0,sK2),k1_xboole_0) | k1_xboole_0 != sK1 | ~spl3_85),
% 14.92/2.24    inference(forward_demodulation,[],[f43182,f78])).
% 14.92/2.24  fof(f43182,plain,(
% 14.92/2.24    r1_tarski(k5_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)),k1_xboole_0) | k1_xboole_0 != sK1 | ~spl3_85),
% 14.92/2.24    inference(inner_rewriting,[],[f43104])).
% 14.92/2.24  fof(f43104,plain,(
% 14.92/2.24    r1_tarski(k5_xboole_0(sK1,k4_xboole_0(sK0,sK2)),k1_xboole_0) | k1_xboole_0 != sK1 | ~spl3_85),
% 14.92/2.24    inference(superposition,[],[f22558,f15058])).
% 14.92/2.24  fof(f43239,plain,(
% 14.92/2.24    ~spl3_127 | spl3_128 | ~spl3_83),
% 14.92/2.24    inference(avatar_split_clause,[],[f43181,f14842,f43236,f43232])).
% 14.92/2.24  fof(f43181,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK1,sK2),k1_xboole_0) | k1_xboole_0 != sK0 | ~spl3_83),
% 14.92/2.24    inference(forward_demodulation,[],[f43180,f78])).
% 14.92/2.24  fof(f43180,plain,(
% 14.92/2.24    r1_tarski(k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)),k1_xboole_0) | k1_xboole_0 != sK0 | ~spl3_83),
% 14.92/2.24    inference(inner_rewriting,[],[f43103])).
% 14.92/2.24  fof(f43103,plain,(
% 14.92/2.24    r1_tarski(k5_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k1_xboole_0) | k1_xboole_0 != sK0 | ~spl3_83),
% 14.92/2.24    inference(superposition,[],[f22558,f14844])).
% 14.92/2.24  fof(f43230,plain,(
% 14.92/2.24    ~spl3_124 | spl3_126 | ~spl3_47),
% 14.92/2.24    inference(avatar_split_clause,[],[f43179,f5140,f43227,f43218])).
% 14.92/2.24  fof(f5140,plain,(
% 14.92/2.24    spl3_47 <=> k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(sK1,sK0)),sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 14.92/2.24  fof(f43179,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK1,sK0),k1_xboole_0) | k1_xboole_0 != sK2 | ~spl3_47),
% 14.92/2.24    inference(forward_demodulation,[],[f43178,f78])).
% 14.92/2.24  fof(f43178,plain,(
% 14.92/2.24    r1_tarski(k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)),k1_xboole_0) | k1_xboole_0 != sK2 | ~spl3_47),
% 14.92/2.24    inference(inner_rewriting,[],[f43102])).
% 14.92/2.24  fof(f43102,plain,(
% 14.92/2.24    r1_tarski(k5_xboole_0(sK2,k4_xboole_0(sK1,sK0)),k1_xboole_0) | k1_xboole_0 != sK2 | ~spl3_47),
% 14.92/2.24    inference(superposition,[],[f22558,f5142])).
% 14.92/2.24  fof(f5142,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(sK1,sK0)),sK2) | ~spl3_47),
% 14.92/2.24    inference(avatar_component_clause,[],[f5140])).
% 14.92/2.24  fof(f43225,plain,(
% 14.92/2.24    ~spl3_124 | spl3_125 | ~spl3_46),
% 14.92/2.24    inference(avatar_split_clause,[],[f43177,f5135,f43222,f43218])).
% 14.92/2.24  fof(f5135,plain,(
% 14.92/2.24    spl3_46 <=> k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(sK0,sK1)),sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 14.92/2.24  fof(f43177,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) | k1_xboole_0 != sK2 | ~spl3_46),
% 14.92/2.24    inference(forward_demodulation,[],[f43176,f78])).
% 14.92/2.24  fof(f43176,plain,(
% 14.92/2.24    r1_tarski(k5_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)),k1_xboole_0) | k1_xboole_0 != sK2 | ~spl3_46),
% 14.92/2.24    inference(inner_rewriting,[],[f43101])).
% 14.92/2.24  fof(f43101,plain,(
% 14.92/2.24    r1_tarski(k5_xboole_0(sK2,k4_xboole_0(sK0,sK1)),k1_xboole_0) | k1_xboole_0 != sK2 | ~spl3_46),
% 14.92/2.24    inference(superposition,[],[f22558,f5137])).
% 14.92/2.24  fof(f5137,plain,(
% 14.92/2.24    k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(sK0,sK1)),sK2) | ~spl3_46),
% 14.92/2.24    inference(avatar_component_clause,[],[f5135])).
% 14.92/2.24  fof(f43216,plain,(
% 14.92/2.24    ~spl3_122 | spl3_123 | ~spl3_29),
% 14.92/2.24    inference(avatar_split_clause,[],[f43156,f1001,f43213,f43209])).
% 14.92/2.24  fof(f43156,plain,(
% 14.92/2.24    r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 != k2_xboole_0(sK0,sK2) | ~spl3_29),
% 14.92/2.24    inference(superposition,[],[f22558,f1003])).
% 14.92/2.24  fof(f43207,plain,(
% 14.92/2.24    ~spl3_120 | spl3_121 | ~spl3_28),
% 14.92/2.24    inference(avatar_split_clause,[],[f43140,f996,f43204,f43200])).
% 14.92/2.24  fof(f43140,plain,(
% 14.92/2.24    r1_tarski(sK0,k1_xboole_0) | k1_xboole_0 != k2_xboole_0(sK1,sK2) | ~spl3_28),
% 14.92/2.24    inference(superposition,[],[f22558,f998])).
% 14.92/2.24  fof(f26383,plain,(
% 14.92/2.24    ~spl3_119 | ~spl3_20 | spl3_117),
% 14.92/2.24    inference(avatar_split_clause,[],[f26378,f26369,f386,f26380])).
% 14.92/2.24  fof(f386,plain,(
% 14.92/2.24    spl3_20 <=> k4_xboole_0(sK0,sK1) = k3_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 14.92/2.24  fof(f26369,plain,(
% 14.92/2.24    spl3_117 <=> k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_117])])).
% 14.92/2.24  fof(f26378,plain,(
% 14.92/2.24    k1_xboole_0 != k4_xboole_0(sK0,sK1) | (~spl3_20 | spl3_117)),
% 14.92/2.24    inference(superposition,[],[f26371,f388])).
% 14.92/2.24  fof(f388,plain,(
% 14.92/2.24    k4_xboole_0(sK0,sK1) = k3_xboole_0(sK2,k4_xboole_0(sK0,sK1)) | ~spl3_20),
% 14.92/2.24    inference(avatar_component_clause,[],[f386])).
% 14.92/2.24  fof(f26371,plain,(
% 14.92/2.24    k1_xboole_0 != k3_xboole_0(sK2,k4_xboole_0(sK0,sK1)) | spl3_117),
% 14.92/2.24    inference(avatar_component_clause,[],[f26369])).
% 14.92/2.24  fof(f26377,plain,(
% 14.92/2.24    ~spl3_118 | spl3_116),
% 14.92/2.24    inference(avatar_split_clause,[],[f26367,f26362,f26374])).
% 14.92/2.24  fof(f26374,plain,(
% 14.92/2.24    spl3_118 <=> k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK2,sK1))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_118])])).
% 14.92/2.24  fof(f26362,plain,(
% 14.92/2.24    spl3_116 <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK2),sK1)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_116])])).
% 14.92/2.24  fof(f26367,plain,(
% 14.92/2.24    k1_xboole_0 != k3_xboole_0(sK0,k4_xboole_0(sK2,sK1)) | spl3_116),
% 14.92/2.24    inference(superposition,[],[f26364,f51])).
% 14.92/2.24  fof(f26364,plain,(
% 14.92/2.24    k1_xboole_0 != k4_xboole_0(k3_xboole_0(sK0,sK2),sK1) | spl3_116),
% 14.92/2.24    inference(avatar_component_clause,[],[f26362])).
% 14.92/2.24  fof(f26372,plain,(
% 14.92/2.24    ~spl3_117 | spl3_116),
% 14.92/2.24    inference(avatar_split_clause,[],[f26366,f26362,f26369])).
% 14.92/2.24  fof(f26366,plain,(
% 14.92/2.24    k1_xboole_0 != k3_xboole_0(sK2,k4_xboole_0(sK0,sK1)) | spl3_116),
% 14.92/2.24    inference(superposition,[],[f26364,f1947])).
% 14.92/2.24  fof(f26365,plain,(
% 14.92/2.24    ~spl3_116 | spl3_114),
% 14.92/2.24    inference(avatar_split_clause,[],[f26226,f25769,f26362])).
% 14.92/2.24  fof(f26226,plain,(
% 14.92/2.24    k1_xboole_0 != k4_xboole_0(k3_xboole_0(sK0,sK2),sK1) | spl3_114),
% 14.92/2.24    inference(resolution,[],[f25771,f49])).
% 14.92/2.24  fof(f25776,plain,(
% 14.92/2.24    ~spl3_114 | spl3_115 | ~spl3_75),
% 14.92/2.24    inference(avatar_split_clause,[],[f25486,f12916,f25773,f25769])).
% 14.92/2.24  fof(f12916,plain,(
% 14.92/2.24    spl3_75 <=> sK1 = k2_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).
% 14.92/2.24  fof(f25486,plain,(
% 14.92/2.24    r1_tarski(sK0,sK1) | ~r1_tarski(k3_xboole_0(sK0,sK2),sK1) | ~spl3_75),
% 14.92/2.24    inference(superposition,[],[f931,f12918])).
% 14.92/2.24  fof(f12918,plain,(
% 14.92/2.24    sK1 = k2_xboole_0(k4_xboole_0(sK0,sK2),sK1) | ~spl3_75),
% 14.92/2.24    inference(avatar_component_clause,[],[f12916])).
% 14.92/2.24  fof(f931,plain,(
% 14.92/2.24    ( ! [X8,X7,X9] : (r1_tarski(X7,k2_xboole_0(k4_xboole_0(X7,X8),X9)) | ~r1_tarski(k3_xboole_0(X7,X8),X9)) )),
% 14.92/2.24    inference(superposition,[],[f54,f44])).
% 14.92/2.24  fof(f25767,plain,(
% 14.92/2.24    ~spl3_113 | ~spl3_21 | spl3_111),
% 14.92/2.24    inference(avatar_split_clause,[],[f25762,f25753,f391,f25764])).
% 14.92/2.24  fof(f25764,plain,(
% 14.92/2.24    spl3_113 <=> k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_113])])).
% 14.92/2.24  fof(f391,plain,(
% 14.92/2.24    spl3_21 <=> k4_xboole_0(sK1,sK0) = k3_xboole_0(sK2,k4_xboole_0(sK1,sK0))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 14.92/2.24  fof(f25753,plain,(
% 14.92/2.24    spl3_111 <=> k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(sK1,sK0))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_111])])).
% 14.92/2.24  fof(f25762,plain,(
% 14.92/2.24    k1_xboole_0 != k4_xboole_0(sK1,sK0) | (~spl3_21 | spl3_111)),
% 14.92/2.24    inference(superposition,[],[f25755,f393])).
% 14.92/2.24  fof(f393,plain,(
% 14.92/2.24    k4_xboole_0(sK1,sK0) = k3_xboole_0(sK2,k4_xboole_0(sK1,sK0)) | ~spl3_21),
% 14.92/2.24    inference(avatar_component_clause,[],[f391])).
% 14.92/2.24  fof(f25755,plain,(
% 14.92/2.24    k1_xboole_0 != k3_xboole_0(sK2,k4_xboole_0(sK1,sK0)) | spl3_111),
% 14.92/2.24    inference(avatar_component_clause,[],[f25753])).
% 14.92/2.24  fof(f25761,plain,(
% 14.92/2.24    ~spl3_112 | spl3_110),
% 14.92/2.24    inference(avatar_split_clause,[],[f25751,f25746,f25758])).
% 14.92/2.24  fof(f25758,plain,(
% 14.92/2.24    spl3_112 <=> k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK2,sK0))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_112])])).
% 14.92/2.24  fof(f25746,plain,(
% 14.92/2.24    spl3_110 <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK1,sK2),sK0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_110])])).
% 14.92/2.24  fof(f25751,plain,(
% 14.92/2.24    k1_xboole_0 != k3_xboole_0(sK1,k4_xboole_0(sK2,sK0)) | spl3_110),
% 14.92/2.24    inference(superposition,[],[f25748,f51])).
% 14.92/2.24  fof(f25748,plain,(
% 14.92/2.24    k1_xboole_0 != k4_xboole_0(k3_xboole_0(sK1,sK2),sK0) | spl3_110),
% 14.92/2.24    inference(avatar_component_clause,[],[f25746])).
% 14.92/2.24  fof(f25756,plain,(
% 14.92/2.24    ~spl3_111 | spl3_110),
% 14.92/2.24    inference(avatar_split_clause,[],[f25750,f25746,f25753])).
% 14.92/2.24  fof(f25750,plain,(
% 14.92/2.24    k1_xboole_0 != k3_xboole_0(sK2,k4_xboole_0(sK1,sK0)) | spl3_110),
% 14.92/2.24    inference(superposition,[],[f25748,f1947])).
% 14.92/2.24  fof(f25749,plain,(
% 14.92/2.24    ~spl3_110 | spl3_108),
% 14.92/2.24    inference(avatar_split_clause,[],[f25744,f25736,f25746])).
% 14.92/2.24  fof(f25744,plain,(
% 14.92/2.24    k1_xboole_0 != k4_xboole_0(k3_xboole_0(sK1,sK2),sK0) | spl3_108),
% 14.92/2.24    inference(resolution,[],[f25738,f49])).
% 14.92/2.24  fof(f25743,plain,(
% 14.92/2.24    ~spl3_108 | spl3_109 | ~spl3_74),
% 14.92/2.24    inference(avatar_split_clause,[],[f25485,f12832,f25740,f25736])).
% 14.92/2.24  fof(f25740,plain,(
% 14.92/2.24    spl3_109 <=> r1_tarski(sK1,sK0)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_109])])).
% 14.92/2.24  fof(f25485,plain,(
% 14.92/2.24    r1_tarski(sK1,sK0) | ~r1_tarski(k3_xboole_0(sK1,sK2),sK0) | ~spl3_74),
% 14.92/2.24    inference(superposition,[],[f931,f12834])).
% 14.92/2.24  fof(f25734,plain,(
% 14.92/2.24    spl3_107 | ~spl3_100 | ~spl3_51),
% 14.92/2.24    inference(avatar_split_clause,[],[f25690,f9092,f25692,f25731])).
% 14.92/2.24  fof(f25690,plain,(
% 14.92/2.24    ~r1_tarski(k3_xboole_0(sK0,sK1),sK2) | r1_tarski(sK1,sK2) | ~spl3_51),
% 14.92/2.24    inference(forward_demodulation,[],[f25488,f40])).
% 14.92/2.24  fof(f25488,plain,(
% 14.92/2.24    r1_tarski(sK1,sK2) | ~r1_tarski(k3_xboole_0(sK1,sK0),sK2) | ~spl3_51),
% 14.92/2.24    inference(superposition,[],[f931,f9094])).
% 14.92/2.24  fof(f25729,plain,(
% 14.92/2.24    ~spl3_106 | ~spl3_72 | spl3_104),
% 14.92/2.24    inference(avatar_split_clause,[],[f25724,f25714,f12545,f25726])).
% 14.92/2.24  fof(f25714,plain,(
% 14.92/2.24    spl3_104 <=> k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_104])])).
% 14.92/2.24  fof(f25724,plain,(
% 14.92/2.24    k1_xboole_0 != k4_xboole_0(sK1,sK2) | (~spl3_72 | spl3_104)),
% 14.92/2.24    inference(superposition,[],[f25716,f12547])).
% 14.92/2.24  fof(f25716,plain,(
% 14.92/2.24    k1_xboole_0 != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | spl3_104),
% 14.92/2.24    inference(avatar_component_clause,[],[f25714])).
% 14.92/2.24  fof(f25723,plain,(
% 14.92/2.24    ~spl3_105 | ~spl3_73 | spl3_103),
% 14.92/2.24    inference(avatar_split_clause,[],[f25718,f25709,f12589,f25720])).
% 14.92/2.24  fof(f25720,plain,(
% 14.92/2.24    spl3_105 <=> k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_105])])).
% 14.92/2.24  fof(f12589,plain,(
% 14.92/2.24    spl3_73 <=> k4_xboole_0(sK0,sK2) = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).
% 14.92/2.24  fof(f25709,plain,(
% 14.92/2.24    spl3_103 <=> k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_103])])).
% 14.92/2.24  fof(f25718,plain,(
% 14.92/2.24    k1_xboole_0 != k4_xboole_0(sK0,sK2) | (~spl3_73 | spl3_103)),
% 14.92/2.24    inference(superposition,[],[f25711,f12591])).
% 14.92/2.24  fof(f12591,plain,(
% 14.92/2.24    k4_xboole_0(sK0,sK2) = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl3_73),
% 14.92/2.24    inference(avatar_component_clause,[],[f12589])).
% 14.92/2.24  fof(f25711,plain,(
% 14.92/2.24    k1_xboole_0 != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl3_103),
% 14.92/2.24    inference(avatar_component_clause,[],[f25709])).
% 14.92/2.24  fof(f25717,plain,(
% 14.92/2.24    ~spl3_104 | spl3_102),
% 14.92/2.24    inference(avatar_split_clause,[],[f25707,f25702,f25714])).
% 14.92/2.24  fof(f25702,plain,(
% 14.92/2.24    spl3_102 <=> k1_xboole_0 = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_102])])).
% 14.92/2.24  fof(f25707,plain,(
% 14.92/2.24    k1_xboole_0 != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | spl3_102),
% 14.92/2.24    inference(superposition,[],[f25704,f51])).
% 14.92/2.24  fof(f25704,plain,(
% 14.92/2.24    k1_xboole_0 != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) | spl3_102),
% 14.92/2.24    inference(avatar_component_clause,[],[f25702])).
% 14.92/2.24  fof(f25712,plain,(
% 14.92/2.24    ~spl3_103 | spl3_102),
% 14.92/2.24    inference(avatar_split_clause,[],[f25706,f25702,f25709])).
% 14.92/2.24  fof(f25706,plain,(
% 14.92/2.24    k1_xboole_0 != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl3_102),
% 14.92/2.24    inference(superposition,[],[f25704,f1947])).
% 14.92/2.24  fof(f25705,plain,(
% 14.92/2.24    ~spl3_102 | spl3_100),
% 14.92/2.24    inference(avatar_split_clause,[],[f25700,f25692,f25702])).
% 14.92/2.24  fof(f25700,plain,(
% 14.92/2.24    k1_xboole_0 != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) | spl3_100),
% 14.92/2.24    inference(resolution,[],[f25694,f49])).
% 14.92/2.24  fof(f25699,plain,(
% 14.92/2.24    ~spl3_100 | spl3_101 | ~spl3_50),
% 14.92/2.24    inference(avatar_split_clause,[],[f25487,f9087,f25696,f25692])).
% 14.92/2.24  fof(f25696,plain,(
% 14.92/2.24    spl3_101 <=> r1_tarski(sK0,sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_101])])).
% 14.92/2.24  fof(f9087,plain,(
% 14.92/2.24    spl3_50 <=> sK2 = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 14.92/2.24  fof(f25487,plain,(
% 14.92/2.24    r1_tarski(sK0,sK2) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK2) | ~spl3_50),
% 14.92/2.24    inference(superposition,[],[f931,f9089])).
% 14.92/2.24  fof(f9089,plain,(
% 14.92/2.24    sK2 = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) | ~spl3_50),
% 14.92/2.24    inference(avatar_component_clause,[],[f9087])).
% 14.92/2.24  fof(f19544,plain,(
% 14.92/2.24    spl3_99 | ~spl3_87),
% 14.92/2.24    inference(avatar_split_clause,[],[f16740,f15791,f19541])).
% 14.92/2.24  fof(f19541,plain,(
% 14.92/2.24    spl3_99 <=> sK0 = k3_xboole_0(sK0,k2_xboole_0(sK1,k3_xboole_0(sK0,sK2)))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_99])])).
% 14.92/2.24  fof(f16740,plain,(
% 14.92/2.24    sK0 = k3_xboole_0(sK0,k2_xboole_0(sK1,k3_xboole_0(sK0,sK2))) | ~spl3_87),
% 14.92/2.24    inference(forward_demodulation,[],[f16686,f38])).
% 14.92/2.24  fof(f16686,plain,(
% 14.92/2.24    k4_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(sK1,k3_xboole_0(sK0,sK2))) | ~spl3_87),
% 14.92/2.24    inference(superposition,[],[f44,f15793])).
% 14.92/2.24  fof(f19530,plain,(
% 14.92/2.24    spl3_98 | ~spl3_86),
% 14.92/2.24    inference(avatar_split_clause,[],[f16652,f15786,f19527])).
% 14.92/2.24  fof(f19527,plain,(
% 14.92/2.24    spl3_98 <=> sK1 = k3_xboole_0(sK1,k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_98])])).
% 14.92/2.24  fof(f16652,plain,(
% 14.92/2.24    sK1 = k3_xboole_0(sK1,k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))) | ~spl3_86),
% 14.92/2.24    inference(forward_demodulation,[],[f16598,f38])).
% 14.92/2.24  fof(f16598,plain,(
% 14.92/2.24    k4_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))) | ~spl3_86),
% 14.92/2.24    inference(superposition,[],[f44,f15788])).
% 14.92/2.24  fof(f19525,plain,(
% 14.92/2.24    spl3_97 | ~spl3_85),
% 14.92/2.24    inference(avatar_split_clause,[],[f16579,f15056,f19522])).
% 14.92/2.24  fof(f19522,plain,(
% 14.92/2.24    spl3_97 <=> sK1 = k2_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK0,sK2)))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_97])])).
% 14.92/2.24  fof(f16579,plain,(
% 14.92/2.24    sK1 = k2_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK0,sK2))) | ~spl3_85),
% 14.92/2.24    inference(forward_demodulation,[],[f16546,f37])).
% 14.92/2.24  fof(f16546,plain,(
% 14.92/2.24    k5_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK0,sK2))) | ~spl3_85),
% 14.92/2.24    inference(superposition,[],[f3037,f15058])).
% 14.92/2.24  fof(f19390,plain,(
% 14.92/2.24    spl3_96 | ~spl3_83),
% 14.92/2.24    inference(avatar_split_clause,[],[f16487,f14842,f19387])).
% 14.92/2.24  fof(f19387,plain,(
% 14.92/2.24    spl3_96 <=> sK0 = k2_xboole_0(sK0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).
% 14.92/2.24  fof(f16487,plain,(
% 14.92/2.24    sK0 = k2_xboole_0(sK0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | ~spl3_83),
% 14.92/2.24    inference(forward_demodulation,[],[f16454,f37])).
% 14.92/2.24  fof(f16454,plain,(
% 14.92/2.24    k5_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | ~spl3_83),
% 14.92/2.24    inference(superposition,[],[f3037,f14844])).
% 14.92/2.24  fof(f19289,plain,(
% 14.92/2.24    spl3_95 | ~spl3_93),
% 14.92/2.24    inference(avatar_split_clause,[],[f19277,f19270,f19286])).
% 14.92/2.24  fof(f19286,plain,(
% 14.92/2.24    spl3_95 <=> r1_tarski(sK0,k2_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK0,sK1))))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_95])])).
% 14.92/2.24  fof(f19270,plain,(
% 14.92/2.24    spl3_93 <=> r1_tarski(k4_xboole_0(sK0,sK2),k5_xboole_0(sK2,k3_xboole_0(sK0,sK1)))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).
% 14.92/2.24  fof(f19277,plain,(
% 14.92/2.24    r1_tarski(sK0,k2_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK0,sK1)))) | ~spl3_93),
% 14.92/2.24    inference(resolution,[],[f19272,f54])).
% 14.92/2.24  fof(f19272,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK0,sK2),k5_xboole_0(sK2,k3_xboole_0(sK0,sK1))) | ~spl3_93),
% 14.92/2.24    inference(avatar_component_clause,[],[f19270])).
% 14.92/2.24  fof(f19284,plain,(
% 14.92/2.24    spl3_94 | ~spl3_92),
% 14.92/2.24    inference(avatar_split_clause,[],[f19274,f19265,f19281])).
% 14.92/2.24  fof(f19281,plain,(
% 14.92/2.24    spl3_94 <=> r1_tarski(sK1,k2_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK0,sK1))))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_94])])).
% 14.92/2.24  fof(f19265,plain,(
% 14.92/2.24    spl3_92 <=> r1_tarski(k4_xboole_0(sK1,sK2),k5_xboole_0(sK2,k3_xboole_0(sK0,sK1)))),
% 14.92/2.24    introduced(avatar_definition,[new_symbols(naming,[spl3_92])])).
% 14.92/2.24  fof(f19274,plain,(
% 14.92/2.24    r1_tarski(sK1,k2_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK0,sK1)))) | ~spl3_92),
% 14.92/2.24    inference(resolution,[],[f19267,f54])).
% 14.92/2.24  fof(f19267,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK1,sK2),k5_xboole_0(sK2,k3_xboole_0(sK0,sK1))) | ~spl3_92),
% 14.92/2.24    inference(avatar_component_clause,[],[f19265])).
% 14.92/2.24  fof(f19273,plain,(
% 14.92/2.24    spl3_93 | ~spl3_73),
% 14.92/2.24    inference(avatar_split_clause,[],[f19175,f12589,f19270])).
% 14.92/2.24  fof(f19175,plain,(
% 14.92/2.24    r1_tarski(k4_xboole_0(sK0,sK2),k5_xboole_0(sK2,k3_xboole_0(sK0,sK1))) | ~spl3_73),
% 14.92/2.24    inference(forward_demodulation,[],[f19174,f40])).
% 14.92/2.26  fof(f19174,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK0,sK2),k5_xboole_0(sK2,k3_xboole_0(sK1,sK0))) | ~spl3_73),
% 14.92/2.26    inference(forward_demodulation,[],[f18985,f41])).
% 14.92/2.26  fof(f18985,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK0,sK2),k5_xboole_0(k3_xboole_0(sK1,sK0),sK2)) | ~spl3_73),
% 14.92/2.26    inference(superposition,[],[f1978,f12591])).
% 14.92/2.26  fof(f1978,plain,(
% 14.92/2.26    ( ! [X17,X18,X16] : (r1_tarski(k3_xboole_0(X16,k4_xboole_0(X17,X18)),k5_xboole_0(k3_xboole_0(X16,X17),X18))) )),
% 14.92/2.26    inference(superposition,[],[f43,f51])).
% 14.92/2.26  fof(f19268,plain,(
% 14.92/2.26    spl3_92 | ~spl3_72),
% 14.92/2.26    inference(avatar_split_clause,[],[f19173,f12545,f19265])).
% 14.92/2.26  fof(f19173,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK1,sK2),k5_xboole_0(sK2,k3_xboole_0(sK0,sK1))) | ~spl3_72),
% 14.92/2.26    inference(forward_demodulation,[],[f18983,f41])).
% 14.92/2.26  fof(f18983,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK1,sK2),k5_xboole_0(k3_xboole_0(sK0,sK1),sK2)) | ~spl3_72),
% 14.92/2.26    inference(superposition,[],[f1978,f12547])).
% 14.92/2.26  fof(f19259,plain,(
% 14.92/2.26    spl3_91 | ~spl3_89),
% 14.92/2.26    inference(avatar_split_clause,[],[f19247,f19240,f19256])).
% 14.92/2.26  fof(f19256,plain,(
% 14.92/2.26    spl3_91 <=> r1_tarski(sK1,k2_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK1,sK2))))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_91])])).
% 14.92/2.26  fof(f19240,plain,(
% 14.92/2.26    spl3_89 <=> r1_tarski(k4_xboole_0(sK1,sK0),k5_xboole_0(sK0,k3_xboole_0(sK1,sK2)))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_89])])).
% 14.92/2.26  fof(f19247,plain,(
% 14.92/2.26    r1_tarski(sK1,k2_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | ~spl3_89),
% 14.92/2.26    inference(resolution,[],[f19242,f54])).
% 14.92/2.26  fof(f19242,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK1,sK0),k5_xboole_0(sK0,k3_xboole_0(sK1,sK2))) | ~spl3_89),
% 14.92/2.26    inference(avatar_component_clause,[],[f19240])).
% 14.92/2.26  fof(f19254,plain,(
% 14.92/2.26    spl3_90 | ~spl3_88),
% 14.92/2.26    inference(avatar_split_clause,[],[f19244,f19235,f19251])).
% 14.92/2.26  fof(f19251,plain,(
% 14.92/2.26    spl3_90 <=> r1_tarski(sK0,k2_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK0,sK2))))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_90])])).
% 14.92/2.26  fof(f19235,plain,(
% 14.92/2.26    spl3_88 <=> r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK0,sK2)))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_88])])).
% 14.92/2.26  fof(f19244,plain,(
% 14.92/2.26    r1_tarski(sK0,k2_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK0,sK2)))) | ~spl3_88),
% 14.92/2.26    inference(resolution,[],[f19237,f54])).
% 14.92/2.26  fof(f19237,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK0,sK2))) | ~spl3_88),
% 14.92/2.26    inference(avatar_component_clause,[],[f19235])).
% 14.92/2.26  fof(f19243,plain,(
% 14.92/2.26    spl3_89 | ~spl3_21),
% 14.92/2.26    inference(avatar_split_clause,[],[f19179,f391,f19240])).
% 14.92/2.26  fof(f19179,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK1,sK0),k5_xboole_0(sK0,k3_xboole_0(sK1,sK2))) | ~spl3_21),
% 14.92/2.26    inference(forward_demodulation,[],[f19178,f40])).
% 14.92/2.26  fof(f19178,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK1,sK0),k5_xboole_0(sK0,k3_xboole_0(sK2,sK1))) | ~spl3_21),
% 14.92/2.26    inference(forward_demodulation,[],[f18987,f41])).
% 14.92/2.26  fof(f18987,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK1,sK0),k5_xboole_0(k3_xboole_0(sK2,sK1),sK0)) | ~spl3_21),
% 14.92/2.26    inference(superposition,[],[f1978,f393])).
% 14.92/2.26  fof(f19238,plain,(
% 14.92/2.26    spl3_88 | ~spl3_20),
% 14.92/2.26    inference(avatar_split_clause,[],[f19177,f386,f19235])).
% 14.92/2.26  fof(f19177,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK0,sK2))) | ~spl3_20),
% 14.92/2.26    inference(forward_demodulation,[],[f19176,f40])).
% 14.92/2.26  fof(f19176,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK2,sK0))) | ~spl3_20),
% 14.92/2.26    inference(forward_demodulation,[],[f18986,f41])).
% 14.92/2.26  fof(f18986,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK2,sK0),sK1)) | ~spl3_20),
% 14.92/2.26    inference(superposition,[],[f1978,f388])).
% 14.92/2.26  fof(f15794,plain,(
% 14.92/2.26    spl3_87 | ~spl3_69),
% 14.92/2.26    inference(avatar_split_clause,[],[f11860,f11855,f15791])).
% 14.92/2.26  fof(f11855,plain,(
% 14.92/2.26    spl3_69 <=> r1_tarski(sK0,k2_xboole_0(sK1,k3_xboole_0(sK0,sK2)))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 14.92/2.26  fof(f11860,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,k3_xboole_0(sK0,sK2))) | ~spl3_69),
% 14.92/2.26    inference(resolution,[],[f11857,f50])).
% 14.92/2.26  fof(f11857,plain,(
% 14.92/2.26    r1_tarski(sK0,k2_xboole_0(sK1,k3_xboole_0(sK0,sK2))) | ~spl3_69),
% 14.92/2.26    inference(avatar_component_clause,[],[f11855])).
% 14.92/2.26  fof(f15789,plain,(
% 14.92/2.26    spl3_86 | ~spl3_67),
% 14.92/2.26    inference(avatar_split_clause,[],[f11817,f11812,f15786])).
% 14.92/2.26  fof(f11812,plain,(
% 14.92/2.26    spl3_67 <=> r1_tarski(sK1,k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).
% 14.92/2.26  fof(f11817,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))) | ~spl3_67),
% 14.92/2.26    inference(resolution,[],[f11814,f50])).
% 14.92/2.26  fof(f11814,plain,(
% 14.92/2.26    r1_tarski(sK1,k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))) | ~spl3_67),
% 14.92/2.26    inference(avatar_component_clause,[],[f11812])).
% 14.92/2.26  fof(f15059,plain,(
% 14.92/2.26    spl3_85 | ~spl3_63),
% 14.92/2.26    inference(avatar_split_clause,[],[f10223,f10187,f15056])).
% 14.92/2.26  fof(f10187,plain,(
% 14.92/2.26    spl3_63 <=> r1_tarski(k5_xboole_0(sK1,k4_xboole_0(sK0,sK2)),sK1)),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 14.92/2.26  fof(f10223,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK1,k4_xboole_0(sK0,sK2)),sK1) | ~spl3_63),
% 14.92/2.26    inference(resolution,[],[f10189,f50])).
% 14.92/2.26  fof(f10189,plain,(
% 14.92/2.26    r1_tarski(k5_xboole_0(sK1,k4_xboole_0(sK0,sK2)),sK1) | ~spl3_63),
% 14.92/2.26    inference(avatar_component_clause,[],[f10187])).
% 14.92/2.26  fof(f15053,plain,(
% 14.92/2.26    spl3_84 | ~spl3_62),
% 14.92/2.26    inference(avatar_split_clause,[],[f10219,f10175,f15050])).
% 14.92/2.26  fof(f15050,plain,(
% 14.92/2.26    spl3_84 <=> k2_xboole_0(sK2,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK2,sK1))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).
% 14.92/2.26  fof(f10175,plain,(
% 14.92/2.26    spl3_62 <=> sK0 = k3_xboole_0(sK0,k2_xboole_0(sK2,sK1))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 14.92/2.26  fof(f10219,plain,(
% 14.92/2.26    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK2,sK1)) | ~spl3_62),
% 14.92/2.26    inference(forward_demodulation,[],[f10195,f3066])).
% 14.92/2.26  fof(f10195,plain,(
% 14.92/2.26    k2_xboole_0(sK0,k2_xboole_0(sK2,sK1)) = k5_xboole_0(k5_xboole_0(sK0,k2_xboole_0(sK2,sK1)),sK0) | ~spl3_62),
% 14.92/2.26    inference(superposition,[],[f46,f10177])).
% 14.92/2.26  fof(f10177,plain,(
% 14.92/2.26    sK0 = k3_xboole_0(sK0,k2_xboole_0(sK2,sK1)) | ~spl3_62),
% 14.92/2.26    inference(avatar_component_clause,[],[f10175])).
% 14.92/2.26  fof(f14845,plain,(
% 14.92/2.26    spl3_83 | ~spl3_56),
% 14.92/2.26    inference(avatar_split_clause,[],[f9411,f9376,f14842])).
% 14.92/2.26  fof(f9376,plain,(
% 14.92/2.26    spl3_56 <=> r1_tarski(k5_xboole_0(sK0,k4_xboole_0(sK1,sK2)),sK0)),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 14.92/2.26  fof(f9411,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK2)),sK0) | ~spl3_56),
% 14.92/2.26    inference(resolution,[],[f9378,f50])).
% 14.92/2.26  fof(f9378,plain,(
% 14.92/2.26    r1_tarski(k5_xboole_0(sK0,k4_xboole_0(sK1,sK2)),sK0) | ~spl3_56),
% 14.92/2.26    inference(avatar_component_clause,[],[f9376])).
% 14.92/2.26  fof(f14839,plain,(
% 14.92/2.26    spl3_82 | ~spl3_55),
% 14.92/2.26    inference(avatar_split_clause,[],[f9407,f9364,f14836])).
% 14.92/2.26  fof(f14836,plain,(
% 14.92/2.26    spl3_82 <=> k2_xboole_0(sK2,sK0) = k2_xboole_0(sK1,k2_xboole_0(sK2,sK0))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).
% 14.92/2.26  fof(f9364,plain,(
% 14.92/2.26    spl3_55 <=> sK1 = k3_xboole_0(sK1,k2_xboole_0(sK2,sK0))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 14.92/2.26  fof(f9407,plain,(
% 14.92/2.26    k2_xboole_0(sK2,sK0) = k2_xboole_0(sK1,k2_xboole_0(sK2,sK0)) | ~spl3_55),
% 14.92/2.26    inference(forward_demodulation,[],[f9384,f3066])).
% 14.92/2.26  fof(f9384,plain,(
% 14.92/2.26    k2_xboole_0(sK1,k2_xboole_0(sK2,sK0)) = k5_xboole_0(k5_xboole_0(sK1,k2_xboole_0(sK2,sK0)),sK1) | ~spl3_55),
% 14.92/2.26    inference(superposition,[],[f46,f9366])).
% 14.92/2.26  fof(f9366,plain,(
% 14.92/2.26    sK1 = k3_xboole_0(sK1,k2_xboole_0(sK2,sK0)) | ~spl3_55),
% 14.92/2.26    inference(avatar_component_clause,[],[f9364])).
% 14.92/2.26  fof(f13671,plain,(
% 14.92/2.26    spl3_81 | ~spl3_68),
% 14.92/2.26    inference(avatar_split_clause,[],[f11853,f11847,f13668])).
% 14.92/2.26  fof(f11847,plain,(
% 14.92/2.26    spl3_68 <=> r1_tarski(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 14.92/2.26  fof(f11853,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) | ~spl3_68),
% 14.92/2.26    inference(resolution,[],[f11849,f50])).
% 14.92/2.26  fof(f11849,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) | ~spl3_68),
% 14.92/2.26    inference(avatar_component_clause,[],[f11847])).
% 14.92/2.26  fof(f13666,plain,(
% 14.92/2.26    spl3_80 | ~spl3_66),
% 14.92/2.26    inference(avatar_split_clause,[],[f11810,f11804,f13663])).
% 14.92/2.26  fof(f11804,plain,(
% 14.92/2.26    spl3_66 <=> r1_tarski(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 14.92/2.26  fof(f11810,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2)) | ~spl3_66),
% 14.92/2.26    inference(resolution,[],[f11806,f50])).
% 14.92/2.26  fof(f11806,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2)) | ~spl3_66),
% 14.92/2.26    inference(avatar_component_clause,[],[f11804])).
% 14.92/2.26  fof(f13489,plain,(
% 14.92/2.26    spl3_79 | ~spl3_61),
% 14.92/2.26    inference(avatar_split_clause,[],[f10155,f10067,f13486])).
% 14.92/2.26  fof(f10155,plain,(
% 14.92/2.26    k4_xboole_0(sK0,sK2) = k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) | ~spl3_61),
% 14.92/2.26    inference(superposition,[],[f1325,f10069])).
% 14.92/2.26  fof(f1325,plain,(
% 14.92/2.26    ( ! [X8,X7] : (k3_xboole_0(X7,k2_xboole_0(X8,X7)) = X7) )),
% 14.92/2.26    inference(forward_demodulation,[],[f1302,f38])).
% 14.92/2.26  fof(f1302,plain,(
% 14.92/2.26    ( ! [X8,X7] : (k4_xboole_0(X7,k1_xboole_0) = k3_xboole_0(X7,k2_xboole_0(X8,X7))) )),
% 14.92/2.26    inference(superposition,[],[f44,f984])).
% 14.92/2.26  fof(f13483,plain,(
% 14.92/2.26    spl3_78 | ~spl3_60),
% 14.92/2.26    inference(avatar_split_clause,[],[f10143,f10054,f13480])).
% 14.92/2.26  fof(f13480,plain,(
% 14.92/2.26    spl3_78 <=> k2_xboole_0(sK2,sK1) = k2_xboole_0(k2_xboole_0(sK2,sK1),sK0)),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).
% 14.92/2.26  fof(f10054,plain,(
% 14.92/2.26    spl3_60 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 14.92/2.26  fof(f10143,plain,(
% 14.92/2.26    k2_xboole_0(sK2,sK1) = k2_xboole_0(k2_xboole_0(sK2,sK1),sK0) | ~spl3_60),
% 14.92/2.26    inference(forward_demodulation,[],[f10122,f37])).
% 14.92/2.26  fof(f10122,plain,(
% 14.92/2.26    k5_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0) = k2_xboole_0(k2_xboole_0(sK2,sK1),sK0) | ~spl3_60),
% 14.92/2.26    inference(superposition,[],[f3037,f10056])).
% 14.92/2.26  fof(f10056,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) | ~spl3_60),
% 14.92/2.26    inference(avatar_component_clause,[],[f10054])).
% 14.92/2.26  fof(f13366,plain,(
% 14.92/2.26    spl3_77 | ~spl3_54),
% 14.92/2.26    inference(avatar_split_clause,[],[f9346,f9262,f13363])).
% 14.92/2.26  fof(f13363,plain,(
% 14.92/2.26    spl3_77 <=> k4_xboole_0(sK1,sK2) = k3_xboole_0(k4_xboole_0(sK1,sK2),sK0)),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).
% 14.92/2.26  fof(f9346,plain,(
% 14.92/2.26    k4_xboole_0(sK1,sK2) = k3_xboole_0(k4_xboole_0(sK1,sK2),sK0) | ~spl3_54),
% 14.92/2.26    inference(superposition,[],[f1325,f9264])).
% 14.92/2.26  fof(f13360,plain,(
% 14.92/2.26    spl3_76 | ~spl3_53),
% 14.92/2.26    inference(avatar_split_clause,[],[f9334,f9249,f13357])).
% 14.92/2.26  fof(f13357,plain,(
% 14.92/2.26    spl3_76 <=> k2_xboole_0(sK2,sK0) = k2_xboole_0(k2_xboole_0(sK2,sK0),sK1)),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 14.92/2.26  fof(f9249,plain,(
% 14.92/2.26    spl3_53 <=> k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 14.92/2.26  fof(f9334,plain,(
% 14.92/2.26    k2_xboole_0(sK2,sK0) = k2_xboole_0(k2_xboole_0(sK2,sK0),sK1) | ~spl3_53),
% 14.92/2.26    inference(forward_demodulation,[],[f9315,f37])).
% 14.92/2.26  fof(f9315,plain,(
% 14.92/2.26    k5_xboole_0(k2_xboole_0(sK2,sK0),k1_xboole_0) = k2_xboole_0(k2_xboole_0(sK2,sK0),sK1) | ~spl3_53),
% 14.92/2.26    inference(superposition,[],[f3037,f9251])).
% 14.92/2.26  fof(f9251,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)) | ~spl3_53),
% 14.92/2.26    inference(avatar_component_clause,[],[f9249])).
% 14.92/2.26  fof(f12919,plain,(
% 14.92/2.26    spl3_75 | ~spl3_73),
% 14.92/2.26    inference(avatar_split_clause,[],[f12914,f12589,f12916])).
% 14.92/2.26  fof(f12914,plain,(
% 14.92/2.26    sK1 = k2_xboole_0(k4_xboole_0(sK0,sK2),sK1) | ~spl3_73),
% 14.92/2.26    inference(forward_demodulation,[],[f12892,f3066])).
% 14.92/2.26  fof(f12892,plain,(
% 14.92/2.26    k2_xboole_0(k4_xboole_0(sK0,sK2),sK1) = k5_xboole_0(k5_xboole_0(k4_xboole_0(sK0,sK2),sK1),k4_xboole_0(sK0,sK2)) | ~spl3_73),
% 14.92/2.26    inference(superposition,[],[f1090,f12591])).
% 14.92/2.26  fof(f12835,plain,(
% 14.92/2.26    spl3_74 | ~spl3_72),
% 14.92/2.26    inference(avatar_split_clause,[],[f12830,f12545,f12832])).
% 14.92/2.26  fof(f12830,plain,(
% 14.92/2.26    sK0 = k2_xboole_0(k4_xboole_0(sK1,sK2),sK0) | ~spl3_72),
% 14.92/2.26    inference(forward_demodulation,[],[f12808,f3066])).
% 14.92/2.26  fof(f12808,plain,(
% 14.92/2.26    k2_xboole_0(k4_xboole_0(sK1,sK2),sK0) = k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,sK2),sK0),k4_xboole_0(sK1,sK2)) | ~spl3_72),
% 14.92/2.26    inference(superposition,[],[f1090,f12547])).
% 14.92/2.26  fof(f12592,plain,(
% 14.92/2.26    spl3_73 | ~spl3_59),
% 14.92/2.26    inference(avatar_split_clause,[],[f10038,f9976,f12589])).
% 14.92/2.26  fof(f10038,plain,(
% 14.92/2.26    k4_xboole_0(sK0,sK2) = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl3_59),
% 14.92/2.26    inference(forward_demodulation,[],[f10037,f38])).
% 14.92/2.26  fof(f10037,plain,(
% 14.92/2.26    k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl3_59),
% 14.92/2.26    inference(forward_demodulation,[],[f9987,f40])).
% 14.92/2.26  fof(f9987,plain,(
% 14.92/2.26    k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) = k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) | ~spl3_59),
% 14.92/2.26    inference(superposition,[],[f44,f9978])).
% 14.92/2.26  fof(f12548,plain,(
% 14.92/2.26    spl3_72 | ~spl3_52),
% 14.92/2.26    inference(avatar_split_clause,[],[f9233,f9175,f12545])).
% 14.92/2.26  fof(f9233,plain,(
% 14.92/2.26    k4_xboole_0(sK1,sK2) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_52),
% 14.92/2.26    inference(forward_demodulation,[],[f9232,f38])).
% 14.92/2.26  fof(f9232,plain,(
% 14.92/2.26    k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_52),
% 14.92/2.26    inference(forward_demodulation,[],[f9186,f40])).
% 14.92/2.26  fof(f9186,plain,(
% 14.92/2.26    k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) = k3_xboole_0(k4_xboole_0(sK1,sK2),sK0) | ~spl3_52),
% 14.92/2.26    inference(superposition,[],[f44,f9177])).
% 14.92/2.26  fof(f11870,plain,(
% 14.92/2.26    spl3_71 | ~spl3_47),
% 14.92/2.26    inference(avatar_split_clause,[],[f8919,f5140,f11867])).
% 14.92/2.26  fof(f11867,plain,(
% 14.92/2.26    spl3_71 <=> sK2 = k2_xboole_0(sK2,k5_xboole_0(sK2,k4_xboole_0(sK1,sK0)))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).
% 14.92/2.26  fof(f8919,plain,(
% 14.92/2.26    sK2 = k2_xboole_0(sK2,k5_xboole_0(sK2,k4_xboole_0(sK1,sK0))) | ~spl3_47),
% 14.92/2.26    inference(forward_demodulation,[],[f8837,f37])).
% 14.92/2.26  fof(f8837,plain,(
% 14.92/2.26    k5_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,k5_xboole_0(sK2,k4_xboole_0(sK1,sK0))) | ~spl3_47),
% 14.92/2.26    inference(superposition,[],[f3037,f5142])).
% 14.92/2.26  fof(f11865,plain,(
% 14.92/2.26    spl3_70 | ~spl3_46),
% 14.92/2.26    inference(avatar_split_clause,[],[f8918,f5135,f11862])).
% 14.92/2.26  fof(f11862,plain,(
% 14.92/2.26    spl3_70 <=> sK2 = k2_xboole_0(sK2,k5_xboole_0(sK2,k4_xboole_0(sK0,sK1)))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 14.92/2.26  fof(f8918,plain,(
% 14.92/2.26    sK2 = k2_xboole_0(sK2,k5_xboole_0(sK2,k4_xboole_0(sK0,sK1))) | ~spl3_46),
% 14.92/2.26    inference(forward_demodulation,[],[f8836,f37])).
% 14.92/2.26  fof(f8836,plain,(
% 14.92/2.26    k5_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,k5_xboole_0(sK2,k4_xboole_0(sK0,sK1))) | ~spl3_46),
% 14.92/2.26    inference(superposition,[],[f3037,f5137])).
% 14.92/2.26  fof(f11858,plain,(
% 14.92/2.26    spl3_69 | ~spl3_68),
% 14.92/2.26    inference(avatar_split_clause,[],[f11851,f11847,f11855])).
% 14.92/2.26  fof(f11851,plain,(
% 14.92/2.26    r1_tarski(sK0,k2_xboole_0(sK1,k3_xboole_0(sK0,sK2))) | ~spl3_68),
% 14.92/2.26    inference(resolution,[],[f11849,f54])).
% 14.92/2.26  fof(f11850,plain,(
% 14.92/2.26    spl3_68 | ~spl3_57),
% 14.92/2.26    inference(avatar_split_clause,[],[f11829,f9961,f11847])).
% 14.92/2.26  fof(f11829,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) | ~spl3_57),
% 14.92/2.26    inference(superposition,[],[f9966,f44])).
% 14.92/2.26  fof(f11815,plain,(
% 14.92/2.26    spl3_67 | ~spl3_66),
% 14.92/2.26    inference(avatar_split_clause,[],[f11808,f11804,f11812])).
% 14.92/2.26  fof(f11808,plain,(
% 14.92/2.26    r1_tarski(sK1,k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))) | ~spl3_66),
% 14.92/2.26    inference(resolution,[],[f11806,f54])).
% 14.92/2.26  fof(f11807,plain,(
% 14.92/2.26    spl3_66 | ~spl3_48),
% 14.92/2.26    inference(avatar_split_clause,[],[f11786,f9072,f11804])).
% 14.92/2.26  fof(f11786,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2)) | ~spl3_48),
% 14.92/2.26    inference(superposition,[],[f9077,f44])).
% 14.92/2.26  fof(f11692,plain,(
% 14.92/2.26    spl3_65 | ~spl3_33),
% 14.92/2.26    inference(avatar_split_clause,[],[f9882,f1062,f11689])).
% 14.92/2.26  fof(f11689,plain,(
% 14.92/2.26    spl3_65 <=> k2_xboole_0(sK0,sK2) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 14.92/2.26  fof(f1062,plain,(
% 14.92/2.26    spl3_33 <=> sK1 = k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 14.92/2.26  fof(f9882,plain,(
% 14.92/2.26    k2_xboole_0(sK0,sK2) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | ~spl3_33),
% 14.92/2.26    inference(superposition,[],[f8969,f1064])).
% 14.92/2.26  fof(f1064,plain,(
% 14.92/2.26    sK1 = k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | ~spl3_33),
% 14.92/2.26    inference(avatar_component_clause,[],[f1062])).
% 14.92/2.26  fof(f8969,plain,(
% 14.92/2.26    ( ! [X2,X1] : (k2_xboole_0(k3_xboole_0(X2,X1),X1) = X1) )),
% 14.92/2.26    inference(superposition,[],[f8900,f40])).
% 14.92/2.26  fof(f11687,plain,(
% 14.92/2.26    spl3_64 | ~spl3_32),
% 14.92/2.26    inference(avatar_split_clause,[],[f9875,f1054,f11684])).
% 14.92/2.26  fof(f11684,plain,(
% 14.92/2.26    spl3_64 <=> k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 14.92/2.26  fof(f1054,plain,(
% 14.92/2.26    spl3_32 <=> sK0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 14.92/2.26  fof(f9875,plain,(
% 14.92/2.26    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_32),
% 14.92/2.26    inference(superposition,[],[f8969,f1056])).
% 14.92/2.26  fof(f1056,plain,(
% 14.92/2.26    sK0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_32),
% 14.92/2.26    inference(avatar_component_clause,[],[f1054])).
% 14.92/2.26  fof(f10190,plain,(
% 14.92/2.26    spl3_63 | ~spl3_61),
% 14.92/2.26    inference(avatar_split_clause,[],[f10161,f10067,f10187])).
% 14.92/2.26  fof(f10161,plain,(
% 14.92/2.26    r1_tarski(k5_xboole_0(sK1,k4_xboole_0(sK0,sK2)),sK1) | ~spl3_61),
% 14.92/2.26    inference(superposition,[],[f3056,f10069])).
% 14.92/2.26  fof(f3056,plain,(
% 14.92/2.26    ( ! [X17,X18] : (r1_tarski(k5_xboole_0(X17,X18),k2_xboole_0(X17,X18))) )),
% 14.92/2.26    inference(superposition,[],[f917,f3034])).
% 14.92/2.26  fof(f917,plain,(
% 14.92/2.26    ( ! [X6,X5] : (r1_tarski(X5,k2_xboole_0(X6,k5_xboole_0(X6,X5)))) )),
% 14.92/2.26    inference(resolution,[],[f54,f98])).
% 14.92/2.26  fof(f10178,plain,(
% 14.92/2.26    spl3_62 | ~spl3_60),
% 14.92/2.26    inference(avatar_split_clause,[],[f10130,f10054,f10175])).
% 14.92/2.26  fof(f10130,plain,(
% 14.92/2.26    sK0 = k3_xboole_0(sK0,k2_xboole_0(sK2,sK1)) | ~spl3_60),
% 14.92/2.26    inference(forward_demodulation,[],[f10082,f38])).
% 14.92/2.26  fof(f10082,plain,(
% 14.92/2.26    k4_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(sK2,sK1)) | ~spl3_60),
% 14.92/2.26    inference(superposition,[],[f44,f10056])).
% 14.92/2.26  fof(f10070,plain,(
% 14.92/2.26    spl3_61 | ~spl3_59),
% 14.92/2.26    inference(avatar_split_clause,[],[f10052,f9976,f10067])).
% 14.92/2.26  fof(f10052,plain,(
% 14.92/2.26    sK1 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl3_59),
% 14.92/2.26    inference(forward_demodulation,[],[f10027,f37])).
% 14.92/2.26  fof(f10027,plain,(
% 14.92/2.26    k5_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl3_59),
% 14.92/2.26    inference(superposition,[],[f3037,f9978])).
% 14.92/2.26  fof(f10057,plain,(
% 14.92/2.26    spl3_60 | ~spl3_58),
% 14.92/2.26    inference(avatar_split_clause,[],[f9974,f9969,f10054])).
% 14.92/2.26  fof(f9969,plain,(
% 14.92/2.26    spl3_58 <=> r1_tarski(sK0,k2_xboole_0(sK2,sK1))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 14.92/2.26  fof(f9974,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) | ~spl3_58),
% 14.92/2.26    inference(resolution,[],[f9971,f50])).
% 14.92/2.26  fof(f9971,plain,(
% 14.92/2.26    r1_tarski(sK0,k2_xboole_0(sK2,sK1)) | ~spl3_58),
% 14.92/2.26    inference(avatar_component_clause,[],[f9969])).
% 14.92/2.26  fof(f9979,plain,(
% 14.92/2.26    spl3_59 | ~spl3_57),
% 14.92/2.26    inference(avatar_split_clause,[],[f9967,f9961,f9976])).
% 14.92/2.26  fof(f9967,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) | ~spl3_57),
% 14.92/2.26    inference(resolution,[],[f9963,f50])).
% 14.92/2.26  fof(f9972,plain,(
% 14.92/2.26    spl3_58 | ~spl3_24),
% 14.92/2.26    inference(avatar_split_clause,[],[f9892,f706,f9969])).
% 14.92/2.26  fof(f9892,plain,(
% 14.92/2.26    r1_tarski(sK0,k2_xboole_0(sK2,sK1)) | ~spl3_24),
% 14.92/2.26    inference(superposition,[],[f1864,f8969])).
% 14.92/2.26  fof(f1864,plain,(
% 14.92/2.26    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(sK2,k2_xboole_0(k3_xboole_0(sK0,sK1),X0)))) ) | ~spl3_24),
% 14.92/2.26    inference(resolution,[],[f954,f54])).
% 14.92/2.26  fof(f954,plain,(
% 14.92/2.26    ( ! [X23] : (r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),X23))) ) | ~spl3_24),
% 14.92/2.26    inference(subsumption_resolution,[],[f937,f294])).
% 14.92/2.26  fof(f937,plain,(
% 14.92/2.26    ( ! [X23] : (~r1_tarski(k1_xboole_0,X23) | r1_tarski(k4_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),X23))) ) | ~spl3_24),
% 14.92/2.26    inference(superposition,[],[f54,f708])).
% 14.92/2.26  fof(f9964,plain,(
% 14.92/2.26    spl3_57 | ~spl3_24),
% 14.92/2.26    inference(avatar_split_clause,[],[f9894,f706,f9961])).
% 14.92/2.26  fof(f9894,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK0,sK2),sK1) | ~spl3_24),
% 14.92/2.26    inference(superposition,[],[f954,f8969])).
% 14.92/2.26  fof(f9379,plain,(
% 14.92/2.26    spl3_56 | ~spl3_54),
% 14.92/2.26    inference(avatar_split_clause,[],[f9352,f9262,f9376])).
% 14.92/2.26  fof(f9352,plain,(
% 14.92/2.26    r1_tarski(k5_xboole_0(sK0,k4_xboole_0(sK1,sK2)),sK0) | ~spl3_54),
% 14.92/2.26    inference(superposition,[],[f3056,f9264])).
% 14.92/2.26  fof(f9367,plain,(
% 14.92/2.26    spl3_55 | ~spl3_53),
% 14.92/2.26    inference(avatar_split_clause,[],[f9321,f9249,f9364])).
% 14.92/2.26  fof(f9321,plain,(
% 14.92/2.26    sK1 = k3_xboole_0(sK1,k2_xboole_0(sK2,sK0)) | ~spl3_53),
% 14.92/2.26    inference(forward_demodulation,[],[f9277,f38])).
% 14.92/2.26  fof(f9277,plain,(
% 14.92/2.26    k4_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,k2_xboole_0(sK2,sK0)) | ~spl3_53),
% 14.92/2.26    inference(superposition,[],[f44,f9251])).
% 14.92/2.26  fof(f9265,plain,(
% 14.92/2.26    spl3_54 | ~spl3_52),
% 14.92/2.26    inference(avatar_split_clause,[],[f9247,f9175,f9262])).
% 14.92/2.26  fof(f9247,plain,(
% 14.92/2.26    sK0 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_52),
% 14.92/2.26    inference(forward_demodulation,[],[f9224,f37])).
% 14.92/2.26  fof(f9224,plain,(
% 14.92/2.26    k5_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_52),
% 14.92/2.26    inference(superposition,[],[f3037,f9177])).
% 14.92/2.26  fof(f9252,plain,(
% 14.92/2.26    spl3_53 | ~spl3_49),
% 14.92/2.26    inference(avatar_split_clause,[],[f9085,f9080,f9249])).
% 14.92/2.26  fof(f9080,plain,(
% 14.92/2.26    spl3_49 <=> r1_tarski(sK1,k2_xboole_0(sK2,sK0))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 14.92/2.26  fof(f9085,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)) | ~spl3_49),
% 14.92/2.26    inference(resolution,[],[f9082,f50])).
% 14.92/2.26  fof(f9082,plain,(
% 14.92/2.26    r1_tarski(sK1,k2_xboole_0(sK2,sK0)) | ~spl3_49),
% 14.92/2.26    inference(avatar_component_clause,[],[f9080])).
% 14.92/2.26  fof(f9178,plain,(
% 14.92/2.26    spl3_52 | ~spl3_48),
% 14.92/2.26    inference(avatar_split_clause,[],[f9078,f9072,f9175])).
% 14.92/2.26  fof(f9078,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0) | ~spl3_48),
% 14.92/2.26    inference(resolution,[],[f9074,f50])).
% 14.92/2.26  fof(f9095,plain,(
% 14.92/2.26    spl3_51 | ~spl3_21),
% 14.92/2.26    inference(avatar_split_clause,[],[f9001,f391,f9092])).
% 14.92/2.26  fof(f9001,plain,(
% 14.92/2.26    sK2 = k2_xboole_0(k4_xboole_0(sK1,sK0),sK2) | ~spl3_21),
% 14.92/2.26    inference(superposition,[],[f8900,f393])).
% 14.92/2.26  fof(f9090,plain,(
% 14.92/2.26    spl3_50 | ~spl3_20),
% 14.92/2.26    inference(avatar_split_clause,[],[f9000,f386,f9087])).
% 14.92/2.26  fof(f9000,plain,(
% 14.92/2.26    sK2 = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) | ~spl3_20),
% 14.92/2.26    inference(superposition,[],[f8900,f388])).
% 14.92/2.26  fof(f9083,plain,(
% 14.92/2.26    spl3_49 | ~spl3_25),
% 14.92/2.26    inference(avatar_split_clause,[],[f9003,f711,f9080])).
% 14.92/2.26  fof(f9003,plain,(
% 14.92/2.26    r1_tarski(sK1,k2_xboole_0(sK2,sK0)) | ~spl3_25),
% 14.92/2.26    inference(superposition,[],[f1869,f8900])).
% 14.92/2.26  fof(f1869,plain,(
% 14.92/2.26    ( ! [X0] : (r1_tarski(sK1,k2_xboole_0(sK2,k2_xboole_0(k3_xboole_0(sK0,sK1),X0)))) ) | ~spl3_25),
% 14.92/2.26    inference(resolution,[],[f955,f54])).
% 14.92/2.26  fof(f955,plain,(
% 14.92/2.26    ( ! [X24] : (r1_tarski(k4_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),X24))) ) | ~spl3_25),
% 14.92/2.26    inference(subsumption_resolution,[],[f938,f294])).
% 14.92/2.26  fof(f938,plain,(
% 14.92/2.26    ( ! [X24] : (~r1_tarski(k1_xboole_0,X24) | r1_tarski(k4_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),X24))) ) | ~spl3_25),
% 14.92/2.26    inference(superposition,[],[f54,f713])).
% 14.92/2.26  fof(f9075,plain,(
% 14.92/2.26    spl3_48 | ~spl3_25),
% 14.92/2.26    inference(avatar_split_clause,[],[f9005,f711,f9072])).
% 14.92/2.26  fof(f9005,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK1,sK2),sK0) | ~spl3_25),
% 14.92/2.26    inference(superposition,[],[f955,f8900])).
% 14.92/2.26  fof(f5143,plain,(
% 14.92/2.26    spl3_47 | ~spl3_41),
% 14.92/2.26    inference(avatar_split_clause,[],[f4504,f4497,f5140])).
% 14.92/2.26  fof(f4497,plain,(
% 14.92/2.26    spl3_41 <=> r1_tarski(k5_xboole_0(sK2,k4_xboole_0(sK1,sK0)),sK2)),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 14.92/2.26  fof(f4504,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(sK1,sK0)),sK2) | ~spl3_41),
% 14.92/2.26    inference(resolution,[],[f4499,f50])).
% 14.92/2.26  fof(f4499,plain,(
% 14.92/2.26    r1_tarski(k5_xboole_0(sK2,k4_xboole_0(sK1,sK0)),sK2) | ~spl3_41),
% 14.92/2.26    inference(avatar_component_clause,[],[f4497])).
% 14.92/2.26  fof(f5138,plain,(
% 14.92/2.26    spl3_46 | ~spl3_40),
% 14.92/2.26    inference(avatar_split_clause,[],[f4502,f4492,f5135])).
% 14.92/2.26  fof(f4492,plain,(
% 14.92/2.26    spl3_40 <=> r1_tarski(k5_xboole_0(sK2,k4_xboole_0(sK0,sK1)),sK2)),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 14.92/2.26  fof(f4502,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(sK0,sK1)),sK2) | ~spl3_40),
% 14.92/2.26    inference(resolution,[],[f4494,f50])).
% 14.92/2.26  fof(f4494,plain,(
% 14.92/2.26    r1_tarski(k5_xboole_0(sK2,k4_xboole_0(sK0,sK1)),sK2) | ~spl3_40),
% 14.92/2.26    inference(avatar_component_clause,[],[f4492])).
% 14.92/2.26  fof(f4788,plain,(
% 14.92/2.26    spl3_45 | ~spl3_43),
% 14.92/2.26    inference(avatar_split_clause,[],[f4751,f4698,f4785])).
% 14.92/2.26  fof(f4785,plain,(
% 14.92/2.26    spl3_45 <=> r1_tarski(k5_xboole_0(sK1,k2_xboole_0(sK0,sK2)),k2_xboole_0(sK0,sK2))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 14.92/2.26  fof(f4698,plain,(
% 14.92/2.26    spl3_43 <=> k2_xboole_0(sK0,sK2) = k2_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 14.92/2.26  fof(f4751,plain,(
% 14.92/2.26    r1_tarski(k5_xboole_0(sK1,k2_xboole_0(sK0,sK2)),k2_xboole_0(sK0,sK2)) | ~spl3_43),
% 14.92/2.26    inference(forward_demodulation,[],[f4749,f41])).
% 14.92/2.26  fof(f4749,plain,(
% 14.92/2.26    r1_tarski(k5_xboole_0(k2_xboole_0(sK0,sK2),sK1),k2_xboole_0(sK0,sK2)) | ~spl3_43),
% 14.92/2.26    inference(superposition,[],[f3056,f4700])).
% 14.92/2.26  fof(f4700,plain,(
% 14.92/2.26    k2_xboole_0(sK0,sK2) = k2_xboole_0(k2_xboole_0(sK0,sK2),sK1) | ~spl3_43),
% 14.92/2.26    inference(avatar_component_clause,[],[f4698])).
% 14.92/2.26  fof(f4783,plain,(
% 14.92/2.26    spl3_44 | ~spl3_42),
% 14.92/2.26    inference(avatar_split_clause,[],[f4726,f4693,f4780])).
% 14.92/2.26  fof(f4780,plain,(
% 14.92/2.26    spl3_44 <=> r1_tarski(k5_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 14.92/2.26  fof(f4693,plain,(
% 14.92/2.26    spl3_42 <=> k2_xboole_0(sK1,sK2) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK0)),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 14.92/2.26  fof(f4726,plain,(
% 14.92/2.26    r1_tarski(k5_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) | ~spl3_42),
% 14.92/2.26    inference(forward_demodulation,[],[f4724,f41])).
% 14.92/2.26  fof(f4724,plain,(
% 14.92/2.26    r1_tarski(k5_xboole_0(k2_xboole_0(sK1,sK2),sK0),k2_xboole_0(sK1,sK2)) | ~spl3_42),
% 14.92/2.26    inference(superposition,[],[f3056,f4695])).
% 14.92/2.26  fof(f4695,plain,(
% 14.92/2.26    k2_xboole_0(sK1,sK2) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK0) | ~spl3_42),
% 14.92/2.26    inference(avatar_component_clause,[],[f4693])).
% 14.92/2.26  fof(f4701,plain,(
% 14.92/2.26    spl3_43 | ~spl3_33),
% 14.92/2.26    inference(avatar_split_clause,[],[f4523,f1062,f4698])).
% 14.92/2.26  fof(f4523,plain,(
% 14.92/2.26    k2_xboole_0(sK0,sK2) = k2_xboole_0(k2_xboole_0(sK0,sK2),sK1) | ~spl3_33),
% 14.92/2.26    inference(superposition,[],[f4326,f1064])).
% 14.92/2.26  fof(f4326,plain,(
% 14.92/2.26    ( ! [X2,X1] : (k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1) )),
% 14.92/2.26    inference(superposition,[],[f4322,f40])).
% 14.92/2.26  fof(f4696,plain,(
% 14.92/2.26    spl3_42 | ~spl3_32),
% 14.92/2.26    inference(avatar_split_clause,[],[f4519,f1054,f4693])).
% 14.92/2.26  fof(f4519,plain,(
% 14.92/2.26    k2_xboole_0(sK1,sK2) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK0) | ~spl3_32),
% 14.92/2.26    inference(superposition,[],[f4326,f1056])).
% 14.92/2.26  fof(f4500,plain,(
% 14.92/2.26    spl3_41 | ~spl3_39),
% 14.92/2.26    inference(avatar_split_clause,[],[f4488,f4417,f4497])).
% 14.92/2.26  fof(f4417,plain,(
% 14.92/2.26    spl3_39 <=> sK2 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK0))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 14.92/2.26  fof(f4488,plain,(
% 14.92/2.26    r1_tarski(k5_xboole_0(sK2,k4_xboole_0(sK1,sK0)),sK2) | ~spl3_39),
% 14.92/2.26    inference(superposition,[],[f3056,f4419])).
% 14.92/2.26  fof(f4419,plain,(
% 14.92/2.26    sK2 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK0)) | ~spl3_39),
% 14.92/2.26    inference(avatar_component_clause,[],[f4417])).
% 14.92/2.26  fof(f4495,plain,(
% 14.92/2.26    spl3_40 | ~spl3_38),
% 14.92/2.26    inference(avatar_split_clause,[],[f4453,f4412,f4492])).
% 14.92/2.26  fof(f4412,plain,(
% 14.92/2.26    spl3_38 <=> sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 14.92/2.26  fof(f4453,plain,(
% 14.92/2.26    r1_tarski(k5_xboole_0(sK2,k4_xboole_0(sK0,sK1)),sK2) | ~spl3_38),
% 14.92/2.26    inference(superposition,[],[f3056,f4414])).
% 14.92/2.26  fof(f4414,plain,(
% 14.92/2.26    sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) | ~spl3_38),
% 14.92/2.26    inference(avatar_component_clause,[],[f4412])).
% 14.92/2.26  fof(f4420,plain,(
% 14.92/2.26    spl3_39 | ~spl3_21),
% 14.92/2.26    inference(avatar_split_clause,[],[f4347,f391,f4417])).
% 14.92/2.26  fof(f4347,plain,(
% 14.92/2.26    sK2 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK0)) | ~spl3_21),
% 14.92/2.26    inference(superposition,[],[f4322,f393])).
% 14.92/2.26  fof(f4415,plain,(
% 14.92/2.26    spl3_38 | ~spl3_20),
% 14.92/2.26    inference(avatar_split_clause,[],[f4346,f386,f4412])).
% 14.92/2.26  fof(f4346,plain,(
% 14.92/2.26    sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) | ~spl3_20),
% 14.92/2.26    inference(superposition,[],[f4322,f388])).
% 14.92/2.26  fof(f4243,plain,(
% 14.92/2.26    spl3_37 | ~spl3_35),
% 14.92/2.26    inference(avatar_split_clause,[],[f4024,f3906,f4240])).
% 14.92/2.26  fof(f4024,plain,(
% 14.92/2.26    sK1 = k3_xboole_0(sK1,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))) | ~spl3_35),
% 14.92/2.26    inference(forward_demodulation,[],[f3987,f38])).
% 14.92/2.26  fof(f3987,plain,(
% 14.92/2.26    k4_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))) | ~spl3_35),
% 14.92/2.26    inference(superposition,[],[f44,f3908])).
% 14.92/2.26  fof(f4234,plain,(
% 14.92/2.26    spl3_36 | ~spl3_34),
% 14.92/2.26    inference(avatar_split_clause,[],[f3969,f3798,f4231])).
% 14.92/2.26  fof(f3969,plain,(
% 14.92/2.26    sK0 = k3_xboole_0(sK0,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))) | ~spl3_34),
% 14.92/2.26    inference(forward_demodulation,[],[f3932,f38])).
% 14.92/2.26  fof(f3932,plain,(
% 14.92/2.26    k4_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))) | ~spl3_34),
% 14.92/2.26    inference(superposition,[],[f44,f3800])).
% 14.92/2.26  fof(f3909,plain,(
% 14.92/2.26    spl3_35 | ~spl3_31),
% 14.92/2.26    inference(avatar_split_clause,[],[f1072,f1043,f3906])).
% 14.92/2.26  fof(f1043,plain,(
% 14.92/2.26    spl3_31 <=> r1_tarski(sK1,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 14.92/2.26  fof(f1072,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))) | ~spl3_31),
% 14.92/2.26    inference(resolution,[],[f1045,f50])).
% 14.92/2.26  fof(f1045,plain,(
% 14.92/2.26    r1_tarski(sK1,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))) | ~spl3_31),
% 14.92/2.26    inference(avatar_component_clause,[],[f1043])).
% 14.92/2.26  fof(f3801,plain,(
% 14.92/2.26    spl3_34 | ~spl3_30),
% 14.92/2.26    inference(avatar_split_clause,[],[f1070,f1038,f3798])).
% 14.92/2.26  fof(f1038,plain,(
% 14.92/2.26    spl3_30 <=> r1_tarski(sK0,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1)))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 14.92/2.26  fof(f1070,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))) | ~spl3_30),
% 14.92/2.26    inference(resolution,[],[f1040,f50])).
% 14.92/2.26  fof(f1040,plain,(
% 14.92/2.26    r1_tarski(sK0,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))) | ~spl3_30),
% 14.92/2.26    inference(avatar_component_clause,[],[f1038])).
% 14.92/2.26  fof(f1065,plain,(
% 14.92/2.26    spl3_33 | ~spl3_29),
% 14.92/2.26    inference(avatar_split_clause,[],[f1033,f1001,f1062])).
% 14.92/2.26  fof(f1033,plain,(
% 14.92/2.26    sK1 = k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | ~spl3_29),
% 14.92/2.26    inference(forward_demodulation,[],[f1024,f38])).
% 14.92/2.26  fof(f1024,plain,(
% 14.92/2.26    k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k1_xboole_0) | ~spl3_29),
% 14.92/2.26    inference(superposition,[],[f44,f1003])).
% 14.92/2.26  fof(f1057,plain,(
% 14.92/2.26    spl3_32 | ~spl3_28),
% 14.92/2.26    inference(avatar_split_clause,[],[f1017,f996,f1054])).
% 14.92/2.26  fof(f1017,plain,(
% 14.92/2.26    sK0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_28),
% 14.92/2.26    inference(forward_demodulation,[],[f1008,f38])).
% 14.92/2.26  fof(f1008,plain,(
% 14.92/2.26    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_28),
% 14.92/2.26    inference(superposition,[],[f44,f998])).
% 14.92/2.26  fof(f1046,plain,(
% 14.92/2.26    spl3_31 | ~spl3_23),
% 14.92/2.26    inference(avatar_split_clause,[],[f915,f699,f1043])).
% 14.92/2.26  fof(f699,plain,(
% 14.92/2.26    spl3_23 <=> r1_tarski(k4_xboole_0(sK1,sK2),k3_xboole_0(sK0,sK1))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 14.92/2.26  fof(f915,plain,(
% 14.92/2.26    r1_tarski(sK1,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))) | ~spl3_23),
% 14.92/2.26    inference(resolution,[],[f54,f701])).
% 14.92/2.26  fof(f701,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK1,sK2),k3_xboole_0(sK0,sK1)) | ~spl3_23),
% 14.92/2.26    inference(avatar_component_clause,[],[f699])).
% 14.92/2.26  fof(f1041,plain,(
% 14.92/2.26    spl3_30 | ~spl3_22),
% 14.92/2.26    inference(avatar_split_clause,[],[f914,f669,f1038])).
% 14.92/2.26  fof(f669,plain,(
% 14.92/2.26    spl3_22 <=> r1_tarski(k4_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK1))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 14.92/2.26  fof(f914,plain,(
% 14.92/2.26    r1_tarski(sK0,k2_xboole_0(sK2,k3_xboole_0(sK0,sK1))) | ~spl3_22),
% 14.92/2.26    inference(resolution,[],[f54,f671])).
% 14.92/2.26  fof(f671,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK1)) | ~spl3_22),
% 14.92/2.26    inference(avatar_component_clause,[],[f669])).
% 14.92/2.26  fof(f1004,plain,(
% 14.92/2.26    spl3_29 | ~spl3_27),
% 14.92/2.26    inference(avatar_split_clause,[],[f974,f967,f1001])).
% 14.92/2.26  fof(f974,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | ~spl3_27),
% 14.92/2.26    inference(resolution,[],[f969,f50])).
% 14.92/2.26  fof(f999,plain,(
% 14.92/2.26    spl3_28 | ~spl3_26),
% 14.92/2.26    inference(avatar_split_clause,[],[f972,f962,f996])).
% 14.92/2.26  fof(f972,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_26),
% 14.92/2.26    inference(resolution,[],[f964,f50])).
% 14.92/2.26  fof(f970,plain,(
% 14.92/2.26    spl3_27 | ~spl3_2),
% 14.92/2.26    inference(avatar_split_clause,[],[f924,f61,f967])).
% 14.92/2.26  fof(f924,plain,(
% 14.92/2.26    r1_tarski(sK1,k2_xboole_0(sK0,sK2)) | ~spl3_2),
% 14.92/2.26    inference(resolution,[],[f54,f63])).
% 14.92/2.26  fof(f965,plain,(
% 14.92/2.26    spl3_26 | ~spl3_1),
% 14.92/2.26    inference(avatar_split_clause,[],[f923,f56,f962])).
% 14.92/2.26  fof(f923,plain,(
% 14.92/2.26    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_1),
% 14.92/2.26    inference(resolution,[],[f54,f58])).
% 14.92/2.26  fof(f714,plain,(
% 14.92/2.26    spl3_25 | ~spl3_23),
% 14.92/2.26    inference(avatar_split_clause,[],[f704,f699,f711])).
% 14.92/2.26  fof(f704,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k3_xboole_0(sK0,sK1)) | ~spl3_23),
% 14.92/2.26    inference(resolution,[],[f701,f50])).
% 14.92/2.26  fof(f709,plain,(
% 14.92/2.26    spl3_24 | ~spl3_22),
% 14.92/2.26    inference(avatar_split_clause,[],[f674,f669,f706])).
% 14.92/2.26  fof(f674,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK1)) | ~spl3_22),
% 14.92/2.26    inference(resolution,[],[f671,f50])).
% 14.92/2.26  fof(f702,plain,(
% 14.92/2.26    spl3_23 | ~spl3_2),
% 14.92/2.26    inference(avatar_split_clause,[],[f692,f61,f699])).
% 14.92/2.26  fof(f692,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK1,sK2),k3_xboole_0(sK0,sK1)) | ~spl3_2),
% 14.92/2.26    inference(forward_demodulation,[],[f685,f40])).
% 14.92/2.26  fof(f685,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK0)) | ~spl3_2),
% 14.92/2.26    inference(superposition,[],[f514,f44])).
% 14.92/2.26  fof(f672,plain,(
% 14.92/2.26    spl3_22 | ~spl3_1),
% 14.92/2.26    inference(avatar_split_clause,[],[f656,f56,f669])).
% 14.92/2.26  fof(f656,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK1)) | ~spl3_1),
% 14.92/2.26    inference(superposition,[],[f513,f44])).
% 14.92/2.26  fof(f394,plain,(
% 14.92/2.26    spl3_21 | ~spl3_15),
% 14.92/2.26    inference(avatar_split_clause,[],[f361,f353,f391])).
% 14.92/2.26  fof(f361,plain,(
% 14.92/2.26    k4_xboole_0(sK1,sK0) = k3_xboole_0(sK2,k4_xboole_0(sK1,sK0)) | ~spl3_15),
% 14.92/2.26    inference(superposition,[],[f355,f40])).
% 14.92/2.26  fof(f389,plain,(
% 14.92/2.26    spl3_20 | ~spl3_14),
% 14.92/2.26    inference(avatar_split_clause,[],[f357,f348,f386])).
% 14.92/2.26  fof(f357,plain,(
% 14.92/2.26    k4_xboole_0(sK0,sK1) = k3_xboole_0(sK2,k4_xboole_0(sK0,sK1)) | ~spl3_14),
% 14.92/2.26    inference(superposition,[],[f350,f40])).
% 14.92/2.26  fof(f384,plain,(
% 14.92/2.26    spl3_19 | ~spl3_13),
% 14.92/2.26    inference(avatar_split_clause,[],[f219,f210,f381])).
% 14.92/2.26  fof(f381,plain,(
% 14.92/2.26    spl3_19 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK1,sK0)))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 14.92/2.26  fof(f210,plain,(
% 14.92/2.26    spl3_13 <=> r1_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK1,sK0)))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 14.92/2.26  fof(f219,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK1,sK0))) | ~spl3_13),
% 14.92/2.26    inference(resolution,[],[f212,f48])).
% 14.92/2.26  fof(f212,plain,(
% 14.92/2.26    r1_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK1,sK0))) | ~spl3_13),
% 14.92/2.26    inference(avatar_component_clause,[],[f210])).
% 14.92/2.26  fof(f379,plain,(
% 14.92/2.26    spl3_18 | ~spl3_11),
% 14.92/2.26    inference(avatar_split_clause,[],[f217,f200,f376])).
% 14.92/2.26  fof(f376,plain,(
% 14.92/2.26    spl3_18 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k4_xboole_0(sK1,sK0)))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 14.92/2.26  fof(f200,plain,(
% 14.92/2.26    spl3_11 <=> r1_tarski(k1_xboole_0,k5_xboole_0(sK2,k4_xboole_0(sK1,sK0)))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 14.92/2.26  fof(f217,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k4_xboole_0(sK1,sK0))) | ~spl3_11),
% 14.92/2.26    inference(resolution,[],[f202,f50])).
% 14.92/2.26  fof(f202,plain,(
% 14.92/2.26    r1_tarski(k1_xboole_0,k5_xboole_0(sK2,k4_xboole_0(sK1,sK0))) | ~spl3_11),
% 14.92/2.26    inference(avatar_component_clause,[],[f200])).
% 14.92/2.26  fof(f374,plain,(
% 14.92/2.26    spl3_17 | ~spl3_10),
% 14.92/2.26    inference(avatar_split_clause,[],[f216,f195,f371])).
% 14.92/2.26  fof(f371,plain,(
% 14.92/2.26    spl3_17 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 14.92/2.26  fof(f195,plain,(
% 14.92/2.26    spl3_10 <=> r1_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 14.92/2.26  fof(f216,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))) | ~spl3_10),
% 14.92/2.26    inference(resolution,[],[f197,f48])).
% 14.92/2.26  fof(f197,plain,(
% 14.92/2.26    r1_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))) | ~spl3_10),
% 14.92/2.26    inference(avatar_component_clause,[],[f195])).
% 14.92/2.26  fof(f369,plain,(
% 14.92/2.26    spl3_16 | ~spl3_8),
% 14.92/2.26    inference(avatar_split_clause,[],[f214,f185,f366])).
% 14.92/2.26  fof(f366,plain,(
% 14.92/2.26    spl3_16 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k4_xboole_0(sK0,sK1)))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 14.92/2.26  fof(f185,plain,(
% 14.92/2.26    spl3_8 <=> r1_tarski(k1_xboole_0,k5_xboole_0(sK2,k4_xboole_0(sK0,sK1)))),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 14.92/2.26  fof(f214,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k4_xboole_0(sK0,sK1))) | ~spl3_8),
% 14.92/2.26    inference(resolution,[],[f187,f50])).
% 14.92/2.26  fof(f187,plain,(
% 14.92/2.26    r1_tarski(k1_xboole_0,k5_xboole_0(sK2,k4_xboole_0(sK0,sK1))) | ~spl3_8),
% 14.92/2.26    inference(avatar_component_clause,[],[f185])).
% 14.92/2.26  fof(f356,plain,(
% 14.92/2.26    spl3_15 | ~spl3_7),
% 14.92/2.26    inference(avatar_split_clause,[],[f271,f170,f353])).
% 14.92/2.26  fof(f271,plain,(
% 14.92/2.26    k4_xboole_0(sK1,sK0) = k3_xboole_0(k4_xboole_0(sK1,sK0),sK2) | ~spl3_7),
% 14.92/2.26    inference(forward_demodulation,[],[f251,f38])).
% 14.92/2.26  fof(f251,plain,(
% 14.92/2.26    k3_xboole_0(k4_xboole_0(sK1,sK0),sK2) = k4_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0) | ~spl3_7),
% 14.92/2.26    inference(superposition,[],[f44,f172])).
% 14.92/2.26  fof(f351,plain,(
% 14.92/2.26    spl3_14 | ~spl3_6),
% 14.92/2.26    inference(avatar_split_clause,[],[f270,f165,f348])).
% 14.92/2.26  fof(f270,plain,(
% 14.92/2.26    k4_xboole_0(sK0,sK1) = k3_xboole_0(k4_xboole_0(sK0,sK1),sK2) | ~spl3_6),
% 14.92/2.26    inference(forward_demodulation,[],[f250,f38])).
% 14.92/2.26  fof(f250,plain,(
% 14.92/2.26    k3_xboole_0(k4_xboole_0(sK0,sK1),sK2) = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | ~spl3_6),
% 14.92/2.26    inference(superposition,[],[f44,f167])).
% 14.92/2.26  fof(f213,plain,(
% 14.92/2.26    spl3_13 | ~spl3_7),
% 14.92/2.26    inference(avatar_split_clause,[],[f182,f170,f210])).
% 14.92/2.26  fof(f182,plain,(
% 14.92/2.26    r1_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK1,sK0))) | ~spl3_7),
% 14.92/2.26    inference(superposition,[],[f42,f172])).
% 14.92/2.26  fof(f208,plain,(
% 14.92/2.26    spl3_12 | ~spl3_7),
% 14.92/2.26    inference(avatar_split_clause,[],[f181,f170,f205])).
% 14.92/2.26  fof(f205,plain,(
% 14.92/2.26    spl3_12 <=> r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,sK0)),k1_xboole_0)),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 14.92/2.26  fof(f181,plain,(
% 14.92/2.26    r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,sK0)),k1_xboole_0) | ~spl3_7),
% 14.92/2.26    inference(superposition,[],[f42,f172])).
% 14.92/2.26  fof(f203,plain,(
% 14.92/2.26    spl3_11 | ~spl3_7),
% 14.92/2.26    inference(avatar_split_clause,[],[f179,f170,f200])).
% 14.92/2.26  fof(f179,plain,(
% 14.92/2.26    r1_tarski(k1_xboole_0,k5_xboole_0(sK2,k4_xboole_0(sK1,sK0))) | ~spl3_7),
% 14.92/2.26    inference(superposition,[],[f98,f172])).
% 14.92/2.26  fof(f198,plain,(
% 14.92/2.26    spl3_10 | ~spl3_6),
% 14.92/2.26    inference(avatar_split_clause,[],[f177,f165,f195])).
% 14.92/2.26  fof(f177,plain,(
% 14.92/2.26    r1_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK0,sK1))) | ~spl3_6),
% 14.92/2.26    inference(superposition,[],[f42,f167])).
% 14.92/2.26  fof(f193,plain,(
% 14.92/2.26    spl3_9 | ~spl3_6),
% 14.92/2.26    inference(avatar_split_clause,[],[f176,f165,f190])).
% 14.92/2.26  fof(f190,plain,(
% 14.92/2.26    spl3_9 <=> r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)),k1_xboole_0)),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 14.92/2.26  fof(f176,plain,(
% 14.92/2.26    r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK0,sK1)),k1_xboole_0) | ~spl3_6),
% 14.92/2.26    inference(superposition,[],[f42,f167])).
% 14.92/2.26  fof(f188,plain,(
% 14.92/2.26    spl3_8 | ~spl3_6),
% 14.92/2.26    inference(avatar_split_clause,[],[f174,f165,f185])).
% 14.92/2.26  fof(f174,plain,(
% 14.92/2.26    r1_tarski(k1_xboole_0,k5_xboole_0(sK2,k4_xboole_0(sK0,sK1))) | ~spl3_6),
% 14.92/2.26    inference(superposition,[],[f98,f167])).
% 14.92/2.26  fof(f173,plain,(
% 14.92/2.26    spl3_7 | ~spl3_2),
% 14.92/2.26    inference(avatar_split_clause,[],[f147,f61,f170])).
% 14.92/2.26  fof(f147,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK2) | ~spl3_2),
% 14.92/2.26    inference(resolution,[],[f50,f63])).
% 14.92/2.26  fof(f168,plain,(
% 14.92/2.26    spl3_6 | ~spl3_1),
% 14.92/2.26    inference(avatar_split_clause,[],[f146,f56,f165])).
% 14.92/2.26  fof(f146,plain,(
% 14.92/2.26    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) | ~spl3_1),
% 14.92/2.26    inference(resolution,[],[f50,f58])).
% 14.92/2.26  fof(f122,plain,(
% 14.92/2.26    ~spl3_5 | spl3_3),
% 14.92/2.26    inference(avatar_split_clause,[],[f117,f66,f119])).
% 14.92/2.26  fof(f119,plain,(
% 14.92/2.26    spl3_5 <=> k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,sK1),sK2)),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 14.92/2.26  fof(f117,plain,(
% 14.92/2.26    k1_xboole_0 != k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) | spl3_3),
% 14.92/2.26    inference(resolution,[],[f49,f68])).
% 14.92/2.26  fof(f93,plain,(
% 14.92/2.26    spl3_4),
% 14.92/2.26    inference(avatar_split_clause,[],[f88,f90])).
% 14.92/2.26  fof(f90,plain,(
% 14.92/2.26    spl3_4 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 14.92/2.26    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 14.92/2.26  fof(f88,plain,(
% 14.92/2.26    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 14.92/2.26    inference(superposition,[],[f86,f38])).
% 14.92/2.26  fof(f69,plain,(
% 14.92/2.26    ~spl3_3),
% 14.92/2.26    inference(avatar_split_clause,[],[f34,f66])).
% 14.92/2.26  fof(f34,plain,(
% 14.92/2.26    ~r1_tarski(k5_xboole_0(sK0,sK1),sK2)),
% 14.92/2.26    inference(cnf_transformation,[],[f30])).
% 14.92/2.26  fof(f30,plain,(
% 14.92/2.26    ~r1_tarski(k5_xboole_0(sK0,sK1),sK2) & r1_tarski(k4_xboole_0(sK1,sK0),sK2) & r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 14.92/2.26    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f29])).
% 14.92/2.26  fof(f29,plain,(
% 14.92/2.26    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X1),X2) & r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)) => (~r1_tarski(k5_xboole_0(sK0,sK1),sK2) & r1_tarski(k4_xboole_0(sK1,sK0),sK2) & r1_tarski(k4_xboole_0(sK0,sK1),sK2))),
% 14.92/2.26    introduced(choice_axiom,[])).
% 14.92/2.26  fof(f25,plain,(
% 14.92/2.26    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X1),X2) & r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2))),
% 14.92/2.26    inference(flattening,[],[f24])).
% 14.92/2.26  fof(f24,plain,(
% 14.92/2.26    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X1),X2) & (r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)))),
% 14.92/2.26    inference(ennf_transformation,[],[f21])).
% 14.92/2.26  fof(f21,negated_conjecture,(
% 14.92/2.26    ~! [X0,X1,X2] : ((r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)) => r1_tarski(k5_xboole_0(X0,X1),X2))),
% 14.92/2.26    inference(negated_conjecture,[],[f20])).
% 14.92/2.26  fof(f20,conjecture,(
% 14.92/2.26    ! [X0,X1,X2] : ((r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)) => r1_tarski(k5_xboole_0(X0,X1),X2))),
% 14.92/2.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_xboole_1)).
% 14.92/2.26  fof(f64,plain,(
% 14.92/2.26    spl3_2),
% 14.92/2.26    inference(avatar_split_clause,[],[f33,f61])).
% 14.92/2.26  fof(f33,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK1,sK0),sK2)),
% 14.92/2.26    inference(cnf_transformation,[],[f30])).
% 14.92/2.26  fof(f59,plain,(
% 14.92/2.26    spl3_1),
% 14.92/2.26    inference(avatar_split_clause,[],[f32,f56])).
% 14.92/2.26  fof(f32,plain,(
% 14.92/2.26    r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 14.92/2.26    inference(cnf_transformation,[],[f30])).
% 14.92/2.26  % SZS output end Proof for theBenchmark
% 14.92/2.26  % (21676)------------------------------
% 14.92/2.26  % (21676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.92/2.26  % (21676)Termination reason: Refutation
% 14.92/2.26  
% 14.92/2.26  % (21676)Memory used [KB]: 30191
% 14.92/2.26  % (21676)Time elapsed: 1.819 s
% 14.92/2.26  % (21676)------------------------------
% 14.92/2.26  % (21676)------------------------------
% 14.92/2.26  % (21672)Success in time 1.905 s
%------------------------------------------------------------------------------
