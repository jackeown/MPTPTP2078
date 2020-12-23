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
% DateTime   : Thu Dec  3 12:59:03 EST 2020

% Result     : Theorem 3.72s
% Output     : Refutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  105 (2496 expanded)
%              Number of leaves         :   25 ( 885 expanded)
%              Depth                    :   22
%              Number of atoms          :  126 (2528 expanded)
%              Number of equality atoms :   99 (2491 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4060,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f70,f224,f3315,f4056,f4059])).

fof(f4059,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f4058])).

fof(f4058,plain,
    ( $false
    | spl5_5 ),
    inference(trivial_inequality_removal,[],[f4057])).

fof(f4057,plain,
    ( k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4))
    | spl5_5 ),
    inference(superposition,[],[f4055,f365])).

fof(f365,plain,(
    ! [X37,X35,X38,X36] : k3_tarski(k2_tarski(k2_tarski(k4_tarski(X35,X36),k4_tarski(X35,X37)),k2_tarski(k4_tarski(X38,X36),k4_tarski(X38,X37)))) = k2_zfmisc_1(k2_tarski(X35,X38),k2_tarski(X36,X37)) ),
    inference(superposition,[],[f56,f157])).

fof(f157,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) ),
    inference(superposition,[],[f50,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f27,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f32,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f35,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f37,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) ),
    inference(definition_unfolding,[],[f40,f26,f44])).

fof(f26,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(definition_unfolding,[],[f36,f46])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f4055,plain,
    ( k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) != k3_tarski(k2_tarski(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4))))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f4053])).

fof(f4053,plain,
    ( spl5_5
  <=> k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) = k3_tarski(k2_tarski(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f4056,plain,
    ( ~ spl5_5
    | spl5_4 ),
    inference(avatar_split_clause,[],[f4051,f3312,f4053])).

fof(f3312,plain,
    ( spl5_4
  <=> k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) = k3_tarski(k2_tarski(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f4051,plain,
    ( k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) != k3_tarski(k2_tarski(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4))))
    | spl5_4 ),
    inference(backward_demodulation,[],[f3314,f4049])).

fof(f4049,plain,(
    ! [X8,X7,X9] : k2_tarski(k4_tarski(X7,X8),k4_tarski(X7,X9)) = k2_tarski(k4_tarski(X7,X9),k4_tarski(X7,X8)) ),
    inference(superposition,[],[f4025,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f33,f25])).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f4025,plain,(
    ! [X39,X37,X38] : k2_zfmisc_1(k2_tarski(X37,X37),k2_tarski(X38,X39)) = k2_tarski(k4_tarski(X37,X39),k4_tarski(X37,X38)) ),
    inference(superposition,[],[f3881,f365])).

fof(f3881,plain,(
    ! [X59,X60] : k2_tarski(X60,X59) = k3_tarski(k2_tarski(k2_tarski(X59,X60),k2_tarski(X59,X60))) ),
    inference(superposition,[],[f3222,f3221])).

fof(f3221,plain,(
    ! [X37,X38] : k2_tarski(X38,X37) = k3_tarski(k2_tarski(k2_tarski(X37,X38),k2_tarski(X38,X37))) ),
    inference(superposition,[],[f3138,f83])).

fof(f83,plain,(
    ! [X14,X15] : k2_tarski(X14,X15) = k6_enumset1(X15,X15,X15,X15,X15,X15,X14,X14) ),
    inference(superposition,[],[f53,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X0) ),
    inference(superposition,[],[f52,f49])).

fof(f52,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1) ),
    inference(definition_unfolding,[],[f28,f47,f47])).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

fof(f53,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0) ),
    inference(definition_unfolding,[],[f29,f47,f47])).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

fof(f3138,plain,(
    ! [X2,X0,X3,X1] : k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) = k6_enumset1(X0,X0,X0,X0,X0,X3,X1,X2) ),
    inference(superposition,[],[f2444,f49])).

fof(f2444,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) = k6_enumset1(X1,X2,X0,X3,X4,X7,X5,X6) ),
    inference(forward_demodulation,[],[f2380,f2426])).

fof(f2426,plain,(
    ! [X14,X21,X19,X17,X15,X20,X18,X16] : k3_tarski(k2_tarski(k6_enumset1(X17,X17,X18,X19,X20,X21,X14,X14),k2_tarski(X15,X16))) = k6_enumset1(X18,X19,X17,X20,X21,X16,X14,X15) ),
    inference(forward_demodulation,[],[f2425,f1830])).

fof(f1830,plain,(
    ! [X146,X144,X142,X149,X147,X145,X143,X148] : k3_tarski(k2_tarski(k6_enumset1(X144,X144,X144,X144,X142,X143,X145,X146),k3_tarski(k2_tarski(k2_tarski(X147,X147),k2_tarski(X148,X149))))) = k6_enumset1(X142,X143,X144,X145,X146,X147,X148,X149) ),
    inference(forward_demodulation,[],[f1766,f50])).

fof(f1766,plain,(
    ! [X146,X144,X142,X149,X147,X145,X143,X148] : k3_tarski(k2_tarski(k6_enumset1(X142,X142,X142,X143,X144,X145,X146,X147),k2_tarski(X148,X149))) = k3_tarski(k2_tarski(k6_enumset1(X144,X144,X144,X144,X142,X143,X145,X146),k3_tarski(k2_tarski(k2_tarski(X147,X147),k2_tarski(X148,X149))))) ),
    inference(superposition,[],[f169,f788])).

fof(f788,plain,(
    ! [X6,X8,X7,X5,X9] : k6_enumset1(X6,X6,X6,X6,X5,X7,X8,X9) = k6_enumset1(X7,X7,X7,X7,X6,X5,X8,X9) ),
    inference(superposition,[],[f174,f173])).

fof(f173,plain,(
    ! [X14,X17,X15,X18,X16] : k6_enumset1(X14,X14,X14,X14,X15,X16,X17,X18) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(k2_tarski(X15,X15),k2_tarski(X14,X16))),k2_tarski(X17,X18))) ),
    inference(forward_demodulation,[],[f160,f168])).

fof(f168,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X2))) ),
    inference(backward_demodulation,[],[f52,f157])).

fof(f160,plain,(
    ! [X14,X17,X15,X18,X16] : k6_enumset1(X14,X14,X14,X14,X15,X16,X17,X18) = k3_tarski(k2_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X16,X14),k2_tarski(X17,X18))) ),
    inference(superposition,[],[f50,f53])).

fof(f174,plain,(
    ! [X23,X21,X19,X22,X20] : k6_enumset1(X19,X19,X19,X19,X20,X21,X22,X23) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(k2_tarski(X21,X21),k2_tarski(X20,X19))),k2_tarski(X22,X23))) ),
    inference(forward_demodulation,[],[f161,f168])).

fof(f161,plain,(
    ! [X23,X21,X19,X22,X20] : k6_enumset1(X19,X19,X19,X19,X20,X21,X22,X23) = k3_tarski(k2_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X19,X20),k2_tarski(X22,X23))) ),
    inference(superposition,[],[f50,f53])).

fof(f169,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k3_tarski(k2_tarski(k2_tarski(X6,X6),k2_tarski(X7,X8))))) ),
    inference(backward_demodulation,[],[f64,f157])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) ),
    inference(backward_demodulation,[],[f57,f58])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) ),
    inference(definition_unfolding,[],[f43,f48,f26,f39])).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) ),
    inference(definition_unfolding,[],[f41,f26,f45,f46])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_enumset1)).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))) ),
    inference(definition_unfolding,[],[f42,f48,f26,f44,f47])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).

fof(f2425,plain,(
    ! [X14,X21,X19,X17,X15,X20,X18,X16] : k3_tarski(k2_tarski(k6_enumset1(X17,X17,X18,X19,X20,X21,X14,X14),k2_tarski(X15,X16))) = k3_tarski(k2_tarski(k6_enumset1(X17,X17,X17,X17,X18,X19,X20,X21),k3_tarski(k2_tarski(k2_tarski(X16,X16),k2_tarski(X14,X15))))) ),
    inference(forward_demodulation,[],[f2364,f168])).

fof(f2364,plain,(
    ! [X14,X21,X19,X17,X15,X20,X18,X16] : k3_tarski(k2_tarski(k6_enumset1(X17,X17,X18,X19,X20,X21,X14,X14),k2_tarski(X15,X16))) = k3_tarski(k2_tarski(k6_enumset1(X17,X17,X17,X17,X18,X19,X20,X21),k6_enumset1(X16,X16,X16,X16,X16,X16,X15,X14))) ),
    inference(superposition,[],[f170,f180])).

fof(f180,plain,(
    ! [X4,X2,X3] : k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2) = k3_tarski(k2_tarski(k2_tarski(X2,X2),k2_tarski(X4,X3))) ),
    inference(superposition,[],[f168,f53])).

fof(f170,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k3_tarski(k2_tarski(k2_tarski(X5,X6),k2_tarski(X7,X8))))) ),
    inference(backward_demodulation,[],[f58,f157])).

fof(f2380,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X5),k2_tarski(X6,X7))) ),
    inference(superposition,[],[f170,f169])).

fof(f3222,plain,(
    ! [X45,X43,X46,X44] : k3_tarski(k2_tarski(k2_tarski(X43,X44),k2_tarski(X45,X46))) = k3_tarski(k2_tarski(k2_tarski(X43,X45),k2_tarski(X46,X44))) ),
    inference(superposition,[],[f3138,f157])).

fof(f3314,plain,
    ( k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) != k3_tarski(k2_tarski(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3))))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f3312])).

fof(f3315,plain,
    ( ~ spl5_4
    | spl5_2 ),
    inference(avatar_split_clause,[],[f3284,f67,f3312])).

fof(f67,plain,
    ( spl5_2
  <=> k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) = k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f3284,plain,
    ( k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) != k3_tarski(k2_tarski(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3))))
    | spl5_2 ),
    inference(superposition,[],[f69,f3138])).

fof(f69,plain,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f224,plain,
    ( ~ spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f219,f67,f221])).

fof(f221,plain,
    ( spl5_3
  <=> k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) = k3_tarski(k2_tarski(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f219,plain,
    ( k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) != k3_tarski(k2_tarski(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4))))
    | spl5_2 ),
    inference(superposition,[],[f69,f157])).

fof(f70,plain,
    ( ~ spl5_2
    | spl5_1 ),
    inference(avatar_split_clause,[],[f65,f60,f67])).

fof(f60,plain,
    ( spl5_1
  <=> k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) = k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f65,plain,
    ( k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4))
    | spl5_1 ),
    inference(forward_demodulation,[],[f62,f55])).

fof(f62,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) != k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f63,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f51,f60])).

fof(f51,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) != k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) ),
    inference(definition_unfolding,[],[f24,f30,f25,f46,f31,f31,f31,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f24,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))
   => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:05:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (10403)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.46  % (10397)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (10405)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (10402)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (10406)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (10408)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (10410)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (10400)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (10398)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (10394)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (10399)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (10393)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (10395)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (10396)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (10407)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (10404)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.51  % (10404)Refutation not found, incomplete strategy% (10404)------------------------------
% 0.21/0.51  % (10404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (10404)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (10404)Memory used [KB]: 10618
% 0.21/0.51  % (10404)Time elapsed: 0.101 s
% 0.21/0.51  % (10404)------------------------------
% 0.21/0.51  % (10404)------------------------------
% 0.21/0.51  % (10401)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (10409)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 3.72/0.83  % (10403)Refutation found. Thanks to Tanya!
% 3.72/0.83  % SZS status Theorem for theBenchmark
% 3.72/0.83  % SZS output start Proof for theBenchmark
% 3.72/0.83  fof(f4060,plain,(
% 3.72/0.83    $false),
% 3.72/0.83    inference(avatar_sat_refutation,[],[f63,f70,f224,f3315,f4056,f4059])).
% 3.72/0.83  fof(f4059,plain,(
% 3.72/0.83    spl5_5),
% 3.72/0.83    inference(avatar_contradiction_clause,[],[f4058])).
% 3.72/0.83  fof(f4058,plain,(
% 3.72/0.83    $false | spl5_5),
% 3.72/0.83    inference(trivial_inequality_removal,[],[f4057])).
% 3.72/0.83  fof(f4057,plain,(
% 3.72/0.83    k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) | spl5_5),
% 3.72/0.83    inference(superposition,[],[f4055,f365])).
% 3.72/0.83  fof(f365,plain,(
% 3.72/0.83    ( ! [X37,X35,X38,X36] : (k3_tarski(k2_tarski(k2_tarski(k4_tarski(X35,X36),k4_tarski(X35,X37)),k2_tarski(k4_tarski(X38,X36),k4_tarski(X38,X37)))) = k2_zfmisc_1(k2_tarski(X35,X38),k2_tarski(X36,X37))) )),
% 3.72/0.83    inference(superposition,[],[f56,f157])).
% 3.72/0.83  fof(f157,plain,(
% 3.72/0.83    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))) )),
% 3.72/0.83    inference(superposition,[],[f50,f49])).
% 3.72/0.83  fof(f49,plain,(
% 3.72/0.83    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.72/0.83    inference(definition_unfolding,[],[f27,f47])).
% 3.72/0.83  fof(f47,plain,(
% 3.72/0.83    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.72/0.83    inference(definition_unfolding,[],[f32,f46])).
% 3.72/0.83  fof(f46,plain,(
% 3.72/0.83    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.72/0.83    inference(definition_unfolding,[],[f35,f45])).
% 3.72/0.83  fof(f45,plain,(
% 3.72/0.83    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.72/0.83    inference(definition_unfolding,[],[f37,f44])).
% 3.72/0.83  fof(f44,plain,(
% 3.72/0.83    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.72/0.83    inference(definition_unfolding,[],[f38,f39])).
% 3.72/0.83  fof(f39,plain,(
% 3.72/0.83    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.72/0.83    inference(cnf_transformation,[],[f12])).
% 3.72/0.83  fof(f12,axiom,(
% 3.72/0.83    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.72/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 3.72/0.83  fof(f38,plain,(
% 3.72/0.83    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.72/0.83    inference(cnf_transformation,[],[f11])).
% 3.72/0.83  fof(f11,axiom,(
% 3.72/0.83    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.72/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 3.72/0.83  fof(f37,plain,(
% 3.72/0.83    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.72/0.83    inference(cnf_transformation,[],[f10])).
% 3.72/0.83  fof(f10,axiom,(
% 3.72/0.83    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.72/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 3.72/0.83  fof(f35,plain,(
% 3.72/0.83    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.72/0.83    inference(cnf_transformation,[],[f9])).
% 3.72/0.83  fof(f9,axiom,(
% 3.72/0.83    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.72/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 3.72/0.83  fof(f32,plain,(
% 3.72/0.83    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.72/0.83    inference(cnf_transformation,[],[f8])).
% 3.72/0.83  fof(f8,axiom,(
% 3.72/0.83    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.72/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 3.72/0.83  fof(f27,plain,(
% 3.72/0.83    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.72/0.83    inference(cnf_transformation,[],[f7])).
% 3.72/0.83  fof(f7,axiom,(
% 3.72/0.83    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.72/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.72/0.83  fof(f50,plain,(
% 3.72/0.83    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)))) )),
% 3.72/0.83    inference(definition_unfolding,[],[f40,f26,f44])).
% 3.72/0.83  fof(f26,plain,(
% 3.72/0.83    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 3.72/0.83    inference(cnf_transformation,[],[f14])).
% 3.72/0.83  fof(f14,axiom,(
% 3.72/0.83    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 3.72/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.72/0.83  fof(f40,plain,(
% 3.72/0.83    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 3.72/0.83    inference(cnf_transformation,[],[f5])).
% 3.72/0.83  fof(f5,axiom,(
% 3.72/0.83    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 3.72/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).
% 3.72/0.83  fof(f56,plain,(
% 3.72/0.83    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 3.72/0.83    inference(definition_unfolding,[],[f36,f46])).
% 3.72/0.83  fof(f36,plain,(
% 3.72/0.83    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 3.72/0.83    inference(cnf_transformation,[],[f15])).
% 3.72/0.83  fof(f15,axiom,(
% 3.72/0.83    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 3.72/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 3.72/0.83  fof(f4055,plain,(
% 3.72/0.83    k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) != k3_tarski(k2_tarski(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)))) | spl5_5),
% 3.72/0.83    inference(avatar_component_clause,[],[f4053])).
% 3.72/0.83  fof(f4053,plain,(
% 3.72/0.83    spl5_5 <=> k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) = k3_tarski(k2_tarski(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4))))),
% 3.72/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 3.72/0.83  fof(f4056,plain,(
% 3.72/0.83    ~spl5_5 | spl5_4),
% 3.72/0.83    inference(avatar_split_clause,[],[f4051,f3312,f4053])).
% 3.72/0.83  fof(f3312,plain,(
% 3.72/0.83    spl5_4 <=> k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) = k3_tarski(k2_tarski(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3))))),
% 3.72/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 3.72/0.83  fof(f4051,plain,(
% 3.72/0.83    k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) != k3_tarski(k2_tarski(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)))) | spl5_4),
% 3.72/0.83    inference(backward_demodulation,[],[f3314,f4049])).
% 3.72/0.83  fof(f4049,plain,(
% 3.72/0.83    ( ! [X8,X7,X9] : (k2_tarski(k4_tarski(X7,X8),k4_tarski(X7,X9)) = k2_tarski(k4_tarski(X7,X9),k4_tarski(X7,X8))) )),
% 3.72/0.83    inference(superposition,[],[f4025,f55])).
% 3.72/0.83  fof(f55,plain,(
% 3.72/0.83    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2))) )),
% 3.72/0.83    inference(definition_unfolding,[],[f33,f25])).
% 3.72/0.83  fof(f25,plain,(
% 3.72/0.83    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.72/0.83    inference(cnf_transformation,[],[f6])).
% 3.72/0.83  fof(f6,axiom,(
% 3.72/0.83    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.72/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 3.72/0.83  fof(f33,plain,(
% 3.72/0.83    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 3.72/0.83    inference(cnf_transformation,[],[f16])).
% 3.72/0.83  fof(f16,axiom,(
% 3.72/0.83    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 3.72/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 3.72/0.83  fof(f4025,plain,(
% 3.72/0.83    ( ! [X39,X37,X38] : (k2_zfmisc_1(k2_tarski(X37,X37),k2_tarski(X38,X39)) = k2_tarski(k4_tarski(X37,X39),k4_tarski(X37,X38))) )),
% 3.72/0.83    inference(superposition,[],[f3881,f365])).
% 3.72/0.83  fof(f3881,plain,(
% 3.72/0.83    ( ! [X59,X60] : (k2_tarski(X60,X59) = k3_tarski(k2_tarski(k2_tarski(X59,X60),k2_tarski(X59,X60)))) )),
% 3.72/0.83    inference(superposition,[],[f3222,f3221])).
% 3.72/0.83  fof(f3221,plain,(
% 3.72/0.83    ( ! [X37,X38] : (k2_tarski(X38,X37) = k3_tarski(k2_tarski(k2_tarski(X37,X38),k2_tarski(X38,X37)))) )),
% 3.72/0.83    inference(superposition,[],[f3138,f83])).
% 3.72/0.83  fof(f83,plain,(
% 3.72/0.83    ( ! [X14,X15] : (k2_tarski(X14,X15) = k6_enumset1(X15,X15,X15,X15,X15,X15,X14,X14)) )),
% 3.72/0.83    inference(superposition,[],[f53,f71])).
% 3.72/0.83  fof(f71,plain,(
% 3.72/0.83    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X0)) )),
% 3.72/0.83    inference(superposition,[],[f52,f49])).
% 3.72/0.83  fof(f52,plain,(
% 3.72/0.83    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1)) )),
% 3.72/0.83    inference(definition_unfolding,[],[f28,f47,f47])).
% 3.72/0.83  fof(f28,plain,(
% 3.72/0.83    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 3.72/0.83    inference(cnf_transformation,[],[f13])).
% 3.72/0.83  fof(f13,axiom,(
% 3.72/0.83    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 3.72/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).
% 3.72/0.83  fof(f53,plain,(
% 3.72/0.83    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) )),
% 3.72/0.83    inference(definition_unfolding,[],[f29,f47,f47])).
% 3.72/0.83  fof(f29,plain,(
% 3.72/0.83    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 3.72/0.83    inference(cnf_transformation,[],[f1])).
% 3.72/0.83  fof(f1,axiom,(
% 3.72/0.83    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 3.72/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).
% 3.72/0.83  fof(f3138,plain,(
% 3.72/0.83    ( ! [X2,X0,X3,X1] : (k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) = k6_enumset1(X0,X0,X0,X0,X0,X3,X1,X2)) )),
% 3.72/0.83    inference(superposition,[],[f2444,f49])).
% 3.72/0.83  fof(f2444,plain,(
% 3.72/0.83    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) = k6_enumset1(X1,X2,X0,X3,X4,X7,X5,X6)) )),
% 3.72/0.83    inference(forward_demodulation,[],[f2380,f2426])).
% 3.72/0.83  fof(f2426,plain,(
% 3.72/0.83    ( ! [X14,X21,X19,X17,X15,X20,X18,X16] : (k3_tarski(k2_tarski(k6_enumset1(X17,X17,X18,X19,X20,X21,X14,X14),k2_tarski(X15,X16))) = k6_enumset1(X18,X19,X17,X20,X21,X16,X14,X15)) )),
% 3.72/0.83    inference(forward_demodulation,[],[f2425,f1830])).
% 3.72/0.83  fof(f1830,plain,(
% 3.72/0.83    ( ! [X146,X144,X142,X149,X147,X145,X143,X148] : (k3_tarski(k2_tarski(k6_enumset1(X144,X144,X144,X144,X142,X143,X145,X146),k3_tarski(k2_tarski(k2_tarski(X147,X147),k2_tarski(X148,X149))))) = k6_enumset1(X142,X143,X144,X145,X146,X147,X148,X149)) )),
% 3.72/0.83    inference(forward_demodulation,[],[f1766,f50])).
% 3.72/0.83  fof(f1766,plain,(
% 3.72/0.83    ( ! [X146,X144,X142,X149,X147,X145,X143,X148] : (k3_tarski(k2_tarski(k6_enumset1(X142,X142,X142,X143,X144,X145,X146,X147),k2_tarski(X148,X149))) = k3_tarski(k2_tarski(k6_enumset1(X144,X144,X144,X144,X142,X143,X145,X146),k3_tarski(k2_tarski(k2_tarski(X147,X147),k2_tarski(X148,X149)))))) )),
% 3.72/0.83    inference(superposition,[],[f169,f788])).
% 3.72/0.83  fof(f788,plain,(
% 3.72/0.83    ( ! [X6,X8,X7,X5,X9] : (k6_enumset1(X6,X6,X6,X6,X5,X7,X8,X9) = k6_enumset1(X7,X7,X7,X7,X6,X5,X8,X9)) )),
% 3.72/0.83    inference(superposition,[],[f174,f173])).
% 3.72/0.83  fof(f173,plain,(
% 3.72/0.83    ( ! [X14,X17,X15,X18,X16] : (k6_enumset1(X14,X14,X14,X14,X15,X16,X17,X18) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(k2_tarski(X15,X15),k2_tarski(X14,X16))),k2_tarski(X17,X18)))) )),
% 3.72/0.83    inference(forward_demodulation,[],[f160,f168])).
% 3.72/0.83  fof(f168,plain,(
% 3.72/0.83    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X2)))) )),
% 3.72/0.83    inference(backward_demodulation,[],[f52,f157])).
% 3.72/0.83  fof(f160,plain,(
% 3.72/0.83    ( ! [X14,X17,X15,X18,X16] : (k6_enumset1(X14,X14,X14,X14,X15,X16,X17,X18) = k3_tarski(k2_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X16,X14),k2_tarski(X17,X18)))) )),
% 3.72/0.83    inference(superposition,[],[f50,f53])).
% 3.72/0.83  fof(f174,plain,(
% 3.72/0.83    ( ! [X23,X21,X19,X22,X20] : (k6_enumset1(X19,X19,X19,X19,X20,X21,X22,X23) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(k2_tarski(X21,X21),k2_tarski(X20,X19))),k2_tarski(X22,X23)))) )),
% 3.72/0.83    inference(forward_demodulation,[],[f161,f168])).
% 3.72/0.83  fof(f161,plain,(
% 3.72/0.83    ( ! [X23,X21,X19,X22,X20] : (k6_enumset1(X19,X19,X19,X19,X20,X21,X22,X23) = k3_tarski(k2_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X19,X20),k2_tarski(X22,X23)))) )),
% 3.72/0.83    inference(superposition,[],[f50,f53])).
% 3.72/0.83  fof(f169,plain,(
% 3.72/0.83    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k3_tarski(k2_tarski(k2_tarski(X6,X6),k2_tarski(X7,X8)))))) )),
% 3.72/0.83    inference(backward_demodulation,[],[f64,f157])).
% 3.72/0.83  fof(f64,plain,(
% 3.72/0.83    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)))) )),
% 3.72/0.83    inference(backward_demodulation,[],[f57,f58])).
% 3.72/0.83  fof(f58,plain,(
% 3.72/0.83    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)))) )),
% 3.72/0.83    inference(definition_unfolding,[],[f43,f48,f26,f39])).
% 3.72/0.83  fof(f48,plain,(
% 3.72/0.83    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8)))) )),
% 3.72/0.83    inference(definition_unfolding,[],[f41,f26,f45,f46])).
% 3.72/0.83  fof(f41,plain,(
% 3.72/0.83    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) )),
% 3.72/0.83    inference(cnf_transformation,[],[f2])).
% 3.72/0.83  fof(f2,axiom,(
% 3.72/0.83    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 3.72/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).
% 3.72/0.83  fof(f43,plain,(
% 3.72/0.83    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) )),
% 3.72/0.83    inference(cnf_transformation,[],[f4])).
% 3.72/0.83  fof(f4,axiom,(
% 3.72/0.83    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))),
% 3.72/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_enumset1)).
% 3.72/0.83  fof(f57,plain,(
% 3.72/0.83    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8)))) )),
% 3.72/0.83    inference(definition_unfolding,[],[f42,f48,f26,f44,f47])).
% 3.72/0.83  fof(f42,plain,(
% 3.72/0.83    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))) )),
% 3.72/0.83    inference(cnf_transformation,[],[f3])).
% 3.72/0.83  fof(f3,axiom,(
% 3.72/0.83    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 3.72/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).
% 3.72/0.83  fof(f2425,plain,(
% 3.72/0.83    ( ! [X14,X21,X19,X17,X15,X20,X18,X16] : (k3_tarski(k2_tarski(k6_enumset1(X17,X17,X18,X19,X20,X21,X14,X14),k2_tarski(X15,X16))) = k3_tarski(k2_tarski(k6_enumset1(X17,X17,X17,X17,X18,X19,X20,X21),k3_tarski(k2_tarski(k2_tarski(X16,X16),k2_tarski(X14,X15)))))) )),
% 3.72/0.83    inference(forward_demodulation,[],[f2364,f168])).
% 3.72/0.83  fof(f2364,plain,(
% 3.72/0.83    ( ! [X14,X21,X19,X17,X15,X20,X18,X16] : (k3_tarski(k2_tarski(k6_enumset1(X17,X17,X18,X19,X20,X21,X14,X14),k2_tarski(X15,X16))) = k3_tarski(k2_tarski(k6_enumset1(X17,X17,X17,X17,X18,X19,X20,X21),k6_enumset1(X16,X16,X16,X16,X16,X16,X15,X14)))) )),
% 3.72/0.83    inference(superposition,[],[f170,f180])).
% 3.72/0.83  fof(f180,plain,(
% 3.72/0.83    ( ! [X4,X2,X3] : (k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2) = k3_tarski(k2_tarski(k2_tarski(X2,X2),k2_tarski(X4,X3)))) )),
% 3.72/0.83    inference(superposition,[],[f168,f53])).
% 3.72/0.83  fof(f170,plain,(
% 3.72/0.83    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k3_tarski(k2_tarski(k2_tarski(X5,X6),k2_tarski(X7,X8)))))) )),
% 3.72/0.83    inference(backward_demodulation,[],[f58,f157])).
% 3.72/0.83  fof(f2380,plain,(
% 3.72/0.83    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k3_tarski(k2_tarski(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) = k3_tarski(k2_tarski(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X5),k2_tarski(X6,X7)))) )),
% 3.72/0.83    inference(superposition,[],[f170,f169])).
% 3.72/0.83  fof(f3222,plain,(
% 3.72/0.83    ( ! [X45,X43,X46,X44] : (k3_tarski(k2_tarski(k2_tarski(X43,X44),k2_tarski(X45,X46))) = k3_tarski(k2_tarski(k2_tarski(X43,X45),k2_tarski(X46,X44)))) )),
% 3.72/0.83    inference(superposition,[],[f3138,f157])).
% 3.72/0.83  fof(f3314,plain,(
% 3.72/0.83    k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) != k3_tarski(k2_tarski(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3)))) | spl5_4),
% 3.72/0.83    inference(avatar_component_clause,[],[f3312])).
% 3.72/0.83  fof(f3315,plain,(
% 3.72/0.83    ~spl5_4 | spl5_2),
% 3.72/0.83    inference(avatar_split_clause,[],[f3284,f67,f3312])).
% 3.72/0.83  fof(f67,plain,(
% 3.72/0.83    spl5_2 <=> k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) = k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4))),
% 3.72/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 3.72/0.83  fof(f3284,plain,(
% 3.72/0.83    k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) != k3_tarski(k2_tarski(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3)))) | spl5_2),
% 3.72/0.83    inference(superposition,[],[f69,f3138])).
% 3.72/0.83  fof(f69,plain,(
% 3.72/0.83    k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) | spl5_2),
% 3.72/0.83    inference(avatar_component_clause,[],[f67])).
% 3.72/0.83  fof(f224,plain,(
% 3.72/0.83    ~spl5_3 | spl5_2),
% 3.72/0.83    inference(avatar_split_clause,[],[f219,f67,f221])).
% 3.72/0.83  fof(f221,plain,(
% 3.72/0.83    spl5_3 <=> k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) = k3_tarski(k2_tarski(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4))))),
% 3.72/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 3.72/0.83  fof(f219,plain,(
% 3.72/0.83    k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) != k3_tarski(k2_tarski(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)))) | spl5_2),
% 3.72/0.83    inference(superposition,[],[f69,f157])).
% 3.72/0.83  fof(f70,plain,(
% 3.72/0.83    ~spl5_2 | spl5_1),
% 3.72/0.83    inference(avatar_split_clause,[],[f65,f60,f67])).
% 3.72/0.83  fof(f60,plain,(
% 3.72/0.83    spl5_1 <=> k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) = k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4))),
% 3.72/0.83    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 3.72/0.83  fof(f65,plain,(
% 3.72/0.83    k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) | spl5_1),
% 3.72/0.83    inference(forward_demodulation,[],[f62,f55])).
% 3.72/0.83  fof(f62,plain,(
% 3.72/0.83    k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) != k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) | spl5_1),
% 3.72/0.83    inference(avatar_component_clause,[],[f60])).
% 3.72/0.83  fof(f63,plain,(
% 3.72/0.83    ~spl5_1),
% 3.72/0.83    inference(avatar_split_clause,[],[f51,f60])).
% 3.72/0.83  fof(f51,plain,(
% 3.72/0.83    k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) != k6_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4))),
% 3.72/0.83    inference(definition_unfolding,[],[f24,f30,f25,f46,f31,f31,f31,f31])).
% 3.72/0.83  fof(f31,plain,(
% 3.72/0.83    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 3.72/0.83    inference(cnf_transformation,[],[f17])).
% 3.72/0.83  fof(f17,axiom,(
% 3.72/0.83    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 3.72/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 3.72/0.83  fof(f30,plain,(
% 3.72/0.83    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 3.72/0.83    inference(cnf_transformation,[],[f18])).
% 3.72/0.83  fof(f18,axiom,(
% 3.72/0.83    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 3.72/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 3.72/0.83  fof(f24,plain,(
% 3.72/0.83    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 3.72/0.83    inference(cnf_transformation,[],[f23])).
% 3.72/0.83  fof(f23,plain,(
% 3.72/0.83    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 3.72/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f22])).
% 3.72/0.83  fof(f22,plain,(
% 3.72/0.83    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 3.72/0.83    introduced(choice_axiom,[])).
% 3.72/0.83  fof(f21,plain,(
% 3.72/0.83    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 3.72/0.83    inference(ennf_transformation,[],[f20])).
% 3.72/0.83  fof(f20,negated_conjecture,(
% 3.72/0.83    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 3.72/0.83    inference(negated_conjecture,[],[f19])).
% 3.72/0.83  fof(f19,conjecture,(
% 3.72/0.83    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 3.72/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_mcart_1)).
% 3.72/0.83  % SZS output end Proof for theBenchmark
% 3.72/0.83  % (10403)------------------------------
% 3.72/0.83  % (10403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.72/0.83  % (10403)Termination reason: Refutation
% 3.72/0.83  
% 3.72/0.83  % (10403)Memory used [KB]: 12153
% 3.72/0.83  % (10403)Time elapsed: 0.426 s
% 3.72/0.83  % (10403)------------------------------
% 3.72/0.83  % (10403)------------------------------
% 3.72/0.84  % (10392)Success in time 0.48 s
%------------------------------------------------------------------------------
