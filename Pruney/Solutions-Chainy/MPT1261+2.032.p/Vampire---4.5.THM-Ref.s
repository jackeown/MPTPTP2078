%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:52 EST 2020

% Result     : Theorem 12.95s
% Output     : Refutation 12.95s
% Verified   : 
% Statistics : Number of formulae       : 1572 (10650 expanded)
%              Number of leaves         :  356 (4175 expanded)
%              Depth                    :   20
%              Number of atoms          : 3858 (18072 expanded)
%              Number of equality atoms :  851 (7279 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18869,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f118,f123,f128,f133,f148,f526,f868,f879,f888,f893,f898,f910,f916,f942,f959,f968,f997,f1661,f1776,f1788,f1790,f1826,f1862,f1871,f1876,f2101,f2108,f2113,f2450,f2497,f2499,f2541,f2588,f2598,f2603,f2608,f2759,f2762,f2763,f2792,f2797,f2802,f2807,f2812,f2817,f2826,f2831,f2836,f3092,f3114,f3119,f3123,f3157,f3168,f3223,f3255,f3257,f3274,f3370,f3375,f3385,f3391,f3396,f3402,f3408,f3477,f3605,f3607,f3631,f3667,f3673,f3678,f3683,f3688,f3718,f3727,f3784,f3786,f3802,f3811,f3848,f4064,f4066,f4083,f4331,f4333,f4350,f4435,f4441,f4443,f4449,f4455,f4456,f4468,f4472,f4477,f4482,f4485,f4490,f4504,f4509,f4514,f4519,f4534,f4552,f4620,f4629,f4634,f4639,f4661,f4666,f4672,f4678,f4683,f4688,f4693,f4797,f4802,f4877,f4915,f4922,f4929,f4935,f4955,f4961,f4980,f4985,f4990,f4995,f5000,f5005,f5010,f5015,f5020,f5072,f5081,f5179,f5181,f5225,f5269,f5271,f5388,f5390,f5425,f5431,f5437,f5443,f5449,f5455,f5460,f5465,f5627,f5628,f5639,f5645,f5650,f5656,f5662,f5945,f5951,f5957,f5962,f5968,f5974,f5979,f5985,f5991,f6003,f6009,f6221,f6228,f6229,f6235,f6243,f6248,f6253,f6283,f6288,f6293,f6298,f6303,f6305,f6310,f6315,f6320,f6321,f6327,f6329,f6334,f6340,f6354,f6373,f6377,f6426,f6428,f6433,f6438,f6443,f6448,f6450,f6455,f6460,f6489,f6496,f6553,f6693,f6699,f6714,f6719,f6724,f6729,f6734,f6739,f6744,f6760,f6761,f6766,f6825,f6832,f6846,f7071,f7076,f7081,f7086,f7091,f7096,f7101,f7106,f7111,f7116,f7121,f7126,f7131,f7136,f7141,f7146,f7151,f7156,f7312,f7314,f7347,f7485,f7486,f7689,f7704,f7709,f7979,f7981,f8012,f8210,f8225,f8230,f10402,f10521,f10533,f10538,f10562,f10569,f10577,f10582,f10587,f10907,f10910,f11520,f12120,f12137,f12142,f12147,f12802,f13465,f13470,f13475,f13481,f14108,f14111,f14174,f15046,f15353,f15357,f15358,f15362,f15451,f15454,f15461,f15475,f16791,f16793,f16796,f16829,f16832,f16840,f17146,f17157,f17162,f17169,f17175,f17184,f17189,f17194,f17199,f17401,f17410,f17465,f17476,f17481,f17488,f17494,f17503,f17508,f17513,f17518,f17538,f17767,f17773,f17805,f17810,f17815,f17846,f17851,f17856,f17861,f17873,f17878,f17883,f18077,f18085,f18086,f18090,f18237,f18239,f18245,f18338,f18340,f18343,f18385,f18388,f18396,f18433,f18438,f18635,f18662,f18667,f18672,f18677,f18734,f18739,f18744,f18749,f18754,f18759,f18847,f18865,f18868])).

fof(f18868,plain,
    ( spl2_302
    | ~ spl2_314 ),
    inference(avatar_split_clause,[],[f18846,f18632,f18070])).

fof(f18070,plain,
    ( spl2_302
  <=> k1_xboole_0 = k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_302])])).

fof(f18632,plain,
    ( spl2_314
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_314])])).

fof(f18846,plain,
    ( k1_xboole_0 = k6_subset_1(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_314 ),
    inference(resolution,[],[f18821,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_subset_1(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f88,f78])).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f18821,plain,
    ( ! [X37] : r1_tarski(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),X37)
    | ~ spl2_314 ),
    inference(resolution,[],[f18776,f1041])).

fof(f1041,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k3_tarski(k2_tarski(X1,X0)))
      | r1_tarski(k6_subset_1(X2,X0),X1) ) ),
    inference(superposition,[],[f106,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f93,f78,f80])).

fof(f80,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f18776,plain,
    ( ! [X0] : r1_tarski(sK1,k3_tarski(k2_tarski(X0,k2_pre_topc(sK0,sK1))))
    | ~ spl2_314 ),
    inference(resolution,[],[f18775,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),X2)
      | r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f94,f80,f78])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f18775,plain,
    ( ! [X2] : r1_tarski(k6_subset_1(sK1,X2),k2_pre_topc(sK0,sK1))
    | ~ spl2_314 ),
    inference(superposition,[],[f18655,f863])).

fof(f863,plain,(
    ! [X2,X1] : k6_subset_1(X1,X2) = k1_setfam_1(k2_tarski(X1,k6_subset_1(X1,X2))) ),
    inference(backward_demodulation,[],[f160,f862])).

fof(f862,plain,(
    ! [X8,X9] : k6_subset_1(X8,X9) = k6_subset_1(X8,k1_setfam_1(k2_tarski(X8,X9))) ),
    inference(forward_demodulation,[],[f852,f860])).

fof(f860,plain,(
    ! [X6,X7] : k6_subset_1(X6,X7) = k3_subset_1(X6,k1_setfam_1(k2_tarski(X6,X7))) ),
    inference(backward_demodulation,[],[f518,f859])).

fof(f859,plain,(
    ! [X6,X7] : k3_subset_1(X6,k6_subset_1(X6,X7)) = k1_setfam_1(k2_tarski(X6,X7)) ),
    inference(forward_demodulation,[],[f851,f100])).

fof(f100,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f81,f79,f78,f78])).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f81,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f851,plain,(
    ! [X6,X7] : k3_subset_1(X6,k6_subset_1(X6,X7)) = k6_subset_1(X6,k6_subset_1(X6,X7)) ),
    inference(resolution,[],[f103,f76])).

fof(f76,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f85,f78])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f518,plain,(
    ! [X6,X7] : k6_subset_1(X6,X7) = k3_subset_1(X6,k3_subset_1(X6,k6_subset_1(X6,X7))) ),
    inference(resolution,[],[f86,f76])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f852,plain,(
    ! [X8,X9] : k3_subset_1(X8,k1_setfam_1(k2_tarski(X8,X9))) = k6_subset_1(X8,k1_setfam_1(k2_tarski(X8,X9))) ),
    inference(resolution,[],[f103,f163])).

fof(f163,plain,(
    ! [X6,X5] : m1_subset_1(k1_setfam_1(k2_tarski(X5,X6)),k1_zfmisc_1(X5)) ),
    inference(superposition,[],[f76,f100])).

fof(f160,plain,(
    ! [X2,X1] : k1_setfam_1(k2_tarski(X1,k6_subset_1(X1,X2))) = k6_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(superposition,[],[f100,f100])).

fof(f18655,plain,
    ( ! [X21] : r1_tarski(k1_setfam_1(k2_tarski(sK1,X21)),k2_pre_topc(sK0,sK1))
    | ~ spl2_314 ),
    inference(resolution,[],[f18634,f161])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2) ) ),
    inference(superposition,[],[f151,f100])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f95,f99])).

fof(f99,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f75,f78])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f18634,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_314 ),
    inference(avatar_component_clause,[],[f18632])).

fof(f18865,plain,
    ( spl2_302
    | ~ spl2_314 ),
    inference(avatar_split_clause,[],[f18843,f18632,f18070])).

fof(f18843,plain,
    ( k1_xboole_0 = k6_subset_1(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_314 ),
    inference(resolution,[],[f18821,f168])).

fof(f168,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | k1_xboole_0 = X3 ) ),
    inference(superposition,[],[f104,f165])).

fof(f165,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f159,f97])).

fof(f97,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f67,f79])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f159,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k6_subset_1(X0,X0) ),
    inference(superposition,[],[f100,f98])).

fof(f98,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f68,f78])).

fof(f68,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f18847,plain,
    ( spl2_302
    | ~ spl2_314 ),
    inference(avatar_split_clause,[],[f18835,f18632,f18070])).

fof(f18835,plain,
    ( k1_xboole_0 = k6_subset_1(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_314 ),
    inference(resolution,[],[f18821,f162])).

fof(f162,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k6_subset_1(X3,X4),k1_setfam_1(k2_tarski(X3,X4)))
      | k1_xboole_0 = k6_subset_1(X3,X4) ) ),
    inference(superposition,[],[f104,f100])).

fof(f18759,plain,
    ( spl2_324
    | ~ spl2_265
    | ~ spl2_317 ),
    inference(avatar_split_clause,[],[f18723,f18669,f16826,f18756])).

fof(f18756,plain,
    ( spl2_324
  <=> k3_subset_1(k2_pre_topc(sK0,sK1),sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_324])])).

fof(f16826,plain,
    ( spl2_265
  <=> k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_265])])).

fof(f18669,plain,
    ( spl2_317
  <=> k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_317])])).

fof(f18723,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)))
    | ~ spl2_265
    | ~ spl2_317 ),
    inference(backward_demodulation,[],[f16828,f18671])).

fof(f18671,plain,
    ( k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_317 ),
    inference(avatar_component_clause,[],[f18669])).

fof(f16828,plain,
    ( k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1)))
    | ~ spl2_265 ),
    inference(avatar_component_clause,[],[f16826])).

fof(f18754,plain,
    ( spl2_323
    | ~ spl2_264
    | ~ spl2_317 ),
    inference(avatar_split_clause,[],[f18722,f18669,f16788,f18751])).

fof(f18751,plain,
    ( spl2_323
  <=> k1_xboole_0 = k6_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_323])])).

fof(f16788,plain,
    ( spl2_264
  <=> k1_xboole_0 = k6_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_264])])).

fof(f18722,plain,
    ( k1_xboole_0 = k6_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_264
    | ~ spl2_317 ),
    inference(backward_demodulation,[],[f16790,f18671])).

fof(f16790,plain,
    ( k1_xboole_0 = k6_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_264 ),
    inference(avatar_component_clause,[],[f16788])).

fof(f18749,plain,
    ( spl2_322
    | ~ spl2_246
    | ~ spl2_317 ),
    inference(avatar_split_clause,[],[f18684,f18669,f12144,f18746])).

fof(f18746,plain,
    ( spl2_322
  <=> k2_tops_1(sK0,sK1) = k4_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k3_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_322])])).

fof(f12144,plain,
    ( spl2_246
  <=> k2_tops_1(sK0,sK1) = k4_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k3_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_246])])).

fof(f18684,plain,
    ( k2_tops_1(sK0,sK1) = k4_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k3_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)))
    | ~ spl2_246
    | ~ spl2_317 ),
    inference(backward_demodulation,[],[f12146,f18671])).

fof(f12146,plain,
    ( k2_tops_1(sK0,sK1) = k4_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k3_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1)))
    | ~ spl2_246 ),
    inference(avatar_component_clause,[],[f12144])).

fof(f18744,plain,
    ( spl2_321
    | ~ spl2_235
    | ~ spl2_317 ),
    inference(avatar_split_clause,[],[f18682,f18669,f10535,f18741])).

fof(f18741,plain,
    ( spl2_321
  <=> k3_subset_1(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_321])])).

fof(f10535,plain,
    ( spl2_235
  <=> k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_235])])).

fof(f18682,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)))
    | ~ spl2_235
    | ~ spl2_317 ),
    inference(backward_demodulation,[],[f10537,f18671])).

fof(f10537,plain,
    ( k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1)))
    | ~ spl2_235 ),
    inference(avatar_component_clause,[],[f10535])).

fof(f18739,plain,
    ( spl2_320
    | ~ spl2_234
    | ~ spl2_317 ),
    inference(avatar_split_clause,[],[f18681,f18669,f10530,f18736])).

fof(f18736,plain,
    ( spl2_320
  <=> k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) = k3_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_320])])).

fof(f10530,plain,
    ( spl2_234
  <=> k6_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1)) = k3_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_234])])).

fof(f18681,plain,
    ( k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) = k3_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl2_234
    | ~ spl2_317 ),
    inference(backward_demodulation,[],[f10532,f18671])).

fof(f10532,plain,
    ( k6_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1)) = k3_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl2_234 ),
    inference(avatar_component_clause,[],[f10530])).

fof(f18734,plain,
    ( spl2_319
    | ~ spl2_233
    | ~ spl2_317 ),
    inference(avatar_split_clause,[],[f18678,f18669,f10518,f18731])).

fof(f18731,plain,
    ( spl2_319
  <=> r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_319])])).

fof(f10518,plain,
    ( spl2_233
  <=> r1_tarski(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_233])])).

fof(f18678,plain,
    ( r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_233
    | ~ spl2_317 ),
    inference(backward_demodulation,[],[f10520,f18671])).

fof(f10520,plain,
    ( r1_tarski(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_233 ),
    inference(avatar_component_clause,[],[f10518])).

fof(f18677,plain,
    ( spl2_318
    | ~ spl2_314 ),
    inference(avatar_split_clause,[],[f18654,f18632,f18674])).

fof(f18674,plain,
    ( spl2_318
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_318])])).

fof(f18654,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl2_314 ),
    inference(resolution,[],[f18634,f515])).

fof(f515,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    inference(resolution,[],[f86,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f18672,plain,
    ( spl2_317
    | ~ spl2_314 ),
    inference(avatar_split_clause,[],[f18653,f18632,f18669])).

fof(f18653,plain,
    ( k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_314 ),
    inference(resolution,[],[f18634,f848])).

fof(f848,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | k6_subset_1(X1,X2) = k3_subset_1(X1,X2) ) ),
    inference(resolution,[],[f103,f91])).

fof(f18667,plain,
    ( spl2_316
    | ~ spl2_314 ),
    inference(avatar_split_clause,[],[f18651,f18632,f18664])).

fof(f18664,plain,
    ( spl2_316
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_316])])).

fof(f18651,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl2_314 ),
    inference(resolution,[],[f18634,f2085])).

fof(f2085,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = X1 ) ),
    inference(resolution,[],[f134,f91])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 ) ),
    inference(forward_demodulation,[],[f87,f66])).

fof(f66,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f87,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f18662,plain,
    ( spl2_315
    | ~ spl2_15
    | ~ spl2_202
    | ~ spl2_314 ),
    inference(avatar_split_clause,[],[f18657,f18632,f6843,f913,f18659])).

fof(f18659,plain,
    ( spl2_315
  <=> r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_315])])).

fof(f913,plain,
    ( spl2_15
  <=> sK1 = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f6843,plain,
    ( spl2_202
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_202])])).

fof(f18657,plain,
    ( r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),sK1))))
    | ~ spl2_15
    | ~ spl2_202
    | ~ spl2_314 ),
    inference(forward_demodulation,[],[f18648,f77])).

fof(f18648,plain,
    ( r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),k2_pre_topc(sK0,sK1))))
    | ~ spl2_15
    | ~ spl2_202
    | ~ spl2_314 ),
    inference(resolution,[],[f18634,f6902])).

fof(f6902,plain,
    ( ! [X10] :
        ( ~ r1_tarski(sK1,X10)
        | r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),X10))) )
    | ~ spl2_15
    | ~ spl2_202 ),
    inference(backward_demodulation,[],[f1317,f6845])).

fof(f6845,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl2_202 ),
    inference(avatar_component_clause,[],[f6843])).

fof(f1317,plain,
    ( ! [X10] :
        ( ~ r1_tarski(sK1,X10)
        | r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(k3_subset_1(u1_struct_0(sK0),sK1),X10))) )
    | ~ spl2_15 ),
    inference(superposition,[],[f107,f915])).

fof(f915,plain,
    ( sK1 = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f913])).

fof(f18635,plain,
    ( spl2_314
    | ~ spl2_160
    | ~ spl2_223
    | ~ spl2_251 ),
    inference(avatar_split_clause,[],[f18630,f13478,f7482,f6225,f18632])).

fof(f6225,plain,
    ( spl2_160
  <=> k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_160])])).

fof(f7482,plain,
    ( spl2_223
  <=> r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_223])])).

fof(f13478,plain,
    ( spl2_251
  <=> k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_251])])).

fof(f18630,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_160
    | ~ spl2_223
    | ~ spl2_251 ),
    inference(forward_demodulation,[],[f18629,f13480])).

fof(f13480,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl2_251 ),
    inference(avatar_component_clause,[],[f13478])).

fof(f18629,plain,
    ( r1_tarski(sK1,k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))))
    | ~ spl2_160
    | ~ spl2_223 ),
    inference(forward_demodulation,[],[f18627,f77])).

fof(f18627,plain,
    ( r1_tarski(sK1,k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))))
    | ~ spl2_160
    | ~ spl2_223 ),
    inference(resolution,[],[f6273,f7484])).

fof(f7484,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl2_223 ),
    inference(avatar_component_clause,[],[f7482])).

fof(f6273,plain,
    ( ! [X18] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK1),X18)
        | r1_tarski(sK1,k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),X18))) )
    | ~ spl2_160 ),
    inference(superposition,[],[f107,f6227])).

fof(f6227,plain,
    ( k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_160 ),
    inference(avatar_component_clause,[],[f6225])).

fof(f18438,plain,
    ( spl2_313
    | ~ spl2_15
    | ~ spl2_202
    | ~ spl2_290 ),
    inference(avatar_split_clause,[],[f18421,f17764,f6843,f913,f18435])).

fof(f18435,plain,
    ( spl2_313
  <=> r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_313])])).

fof(f17764,plain,
    ( spl2_290
  <=> r1_tarski(sK1,k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_290])])).

fof(f18421,plain,
    ( r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))))))
    | ~ spl2_15
    | ~ spl2_202
    | ~ spl2_290 ),
    inference(resolution,[],[f6902,f17766])).

fof(f17766,plain,
    ( r1_tarski(sK1,k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))))
    | ~ spl2_290 ),
    inference(avatar_component_clause,[],[f17764])).

fof(f18433,plain,
    ( spl2_312
    | ~ spl2_15
    | ~ spl2_202
    | ~ spl2_291 ),
    inference(avatar_split_clause,[],[f18420,f17770,f6843,f913,f18430])).

fof(f18430,plain,
    ( spl2_312
  <=> r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_312])])).

fof(f17770,plain,
    ( spl2_291
  <=> r1_tarski(sK1,k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_291])])).

fof(f18420,plain,
    ( r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))))))
    | ~ spl2_15
    | ~ spl2_202
    | ~ spl2_291 ),
    inference(resolution,[],[f6902,f17772])).

fof(f17772,plain,
    ( r1_tarski(sK1,k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))))
    | ~ spl2_291 ),
    inference(avatar_component_clause,[],[f17770])).

fof(f18396,plain,
    ( spl2_311
    | ~ spl2_309 ),
    inference(avatar_split_clause,[],[f18391,f18335,f18393])).

fof(f18393,plain,
    ( spl2_311
  <=> k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) = k4_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_xboole_0,k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_311])])).

fof(f18335,plain,
    ( spl2_309
  <=> k1_xboole_0 = k6_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_309])])).

fof(f18391,plain,
    ( k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) = k4_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_xboole_0,k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1)))))
    | ~ spl2_309 ),
    inference(forward_demodulation,[],[f18375,f77])).

fof(f18375,plain,
    ( k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) = k4_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_xboole_0,k1_setfam_1(k2_tarski(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))))
    | ~ spl2_309 ),
    inference(superposition,[],[f2102,f18337])).

fof(f18337,plain,
    ( k1_xboole_0 = k6_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl2_309 ),
    inference(avatar_component_clause,[],[f18335])).

fof(f2102,plain,(
    ! [X6,X7] : k4_subset_1(X6,k6_subset_1(X6,X7),k1_setfam_1(k2_tarski(X6,X7))) = X6 ),
    inference(forward_demodulation,[],[f2089,f859])).

fof(f2089,plain,(
    ! [X6,X7] : k4_subset_1(X6,k6_subset_1(X6,X7),k3_subset_1(X6,k6_subset_1(X6,X7))) = X6 ),
    inference(resolution,[],[f134,f76])).

fof(f18388,plain,
    ( spl2_310
    | ~ spl2_309 ),
    inference(avatar_split_clause,[],[f18387,f18335,f18382])).

fof(f18382,plain,
    ( spl2_310
  <=> k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) = k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_310])])).

fof(f18387,plain,
    ( k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) = k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1))))
    | ~ spl2_309 ),
    inference(forward_demodulation,[],[f18386,f77])).

fof(f18386,plain,
    ( k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) = k1_setfam_1(k2_tarski(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)))
    | ~ spl2_309 ),
    inference(forward_demodulation,[],[f18371,f856])).

fof(f856,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f514,f855])).

fof(f855,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f847,f165])).

fof(f847,plain,(
    ! [X0] : k6_subset_1(X0,X0) = k3_subset_1(X0,X0) ),
    inference(resolution,[],[f103,f136])).

fof(f136,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(superposition,[],[f76,f98])).

fof(f514,plain,(
    ! [X0] : k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    inference(resolution,[],[f86,f136])).

fof(f18371,plain,
    ( k1_setfam_1(k2_tarski(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))) = k3_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_xboole_0)
    | ~ spl2_309 ),
    inference(superposition,[],[f859,f18337])).

fof(f18385,plain,
    ( spl2_310
    | ~ spl2_309 ),
    inference(avatar_split_clause,[],[f18380,f18335,f18382])).

fof(f18380,plain,
    ( k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) = k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1))))
    | ~ spl2_309 ),
    inference(forward_demodulation,[],[f18379,f98])).

fof(f18379,plain,
    ( k6_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_xboole_0) = k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1))))
    | ~ spl2_309 ),
    inference(forward_demodulation,[],[f18366,f77])).

fof(f18366,plain,
    ( k6_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_xboole_0) = k1_setfam_1(k2_tarski(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)))
    | ~ spl2_309 ),
    inference(superposition,[],[f100,f18337])).

fof(f18343,plain,
    ( spl2_309
    | ~ spl2_295 ),
    inference(avatar_split_clause,[],[f18333,f17843,f18335])).

fof(f17843,plain,
    ( spl2_295
  <=> r1_tarski(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_295])])).

fof(f18333,plain,
    ( k1_xboole_0 = k6_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl2_295 ),
    inference(resolution,[],[f18311,f104])).

fof(f18311,plain,
    ( ! [X1] : r1_tarski(k6_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)),X1)
    | ~ spl2_295 ),
    inference(resolution,[],[f17997,f1041])).

fof(f17997,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k3_tarski(k2_tarski(X0,k1_tops_1(sK0,sK1))))
    | ~ spl2_295 ),
    inference(resolution,[],[f17996,f107])).

fof(f17996,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),X0),k1_tops_1(sK0,sK1))
    | ~ spl2_295 ),
    inference(superposition,[],[f17867,f863])).

fof(f17867,plain,
    ( ! [X1] : r1_tarski(k1_setfam_1(k2_tarski(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),X1)),k1_tops_1(sK0,sK1))
    | ~ spl2_295 ),
    inference(resolution,[],[f17845,f161])).

fof(f17845,plain,
    ( r1_tarski(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl2_295 ),
    inference(avatar_component_clause,[],[f17843])).

fof(f18340,plain,
    ( spl2_309
    | ~ spl2_295 ),
    inference(avatar_split_clause,[],[f18330,f17843,f18335])).

fof(f18330,plain,
    ( k1_xboole_0 = k6_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl2_295 ),
    inference(resolution,[],[f18311,f168])).

fof(f18338,plain,
    ( spl2_309
    | ~ spl2_295 ),
    inference(avatar_split_clause,[],[f18322,f17843,f18335])).

fof(f18322,plain,
    ( k1_xboole_0 = k6_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl2_295 ),
    inference(resolution,[],[f18311,f162])).

fof(f18245,plain,
    ( spl2_308
    | ~ spl2_302 ),
    inference(avatar_split_clause,[],[f18201,f18070,f18242])).

fof(f18242,plain,
    ( spl2_308
  <=> sK1 = k4_subset_1(sK1,k1_xboole_0,k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_308])])).

fof(f18201,plain,
    ( sK1 = k4_subset_1(sK1,k1_xboole_0,k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1))))
    | ~ spl2_302 ),
    inference(superposition,[],[f2102,f18072])).

fof(f18072,plain,
    ( k1_xboole_0 = k6_subset_1(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_302 ),
    inference(avatar_component_clause,[],[f18070])).

fof(f18239,plain,
    ( spl2_307
    | ~ spl2_302 ),
    inference(avatar_split_clause,[],[f18238,f18070,f18234])).

fof(f18234,plain,
    ( spl2_307
  <=> sK1 = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_307])])).

fof(f18238,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))
    | ~ spl2_302 ),
    inference(forward_demodulation,[],[f18197,f856])).

fof(f18197,plain,
    ( k3_subset_1(sK1,k1_xboole_0) = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))
    | ~ spl2_302 ),
    inference(superposition,[],[f859,f18072])).

fof(f18237,plain,
    ( spl2_307
    | ~ spl2_302 ),
    inference(avatar_split_clause,[],[f18232,f18070,f18234])).

fof(f18232,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))
    | ~ spl2_302 ),
    inference(forward_demodulation,[],[f18192,f98])).

fof(f18192,plain,
    ( k6_subset_1(sK1,k1_xboole_0) = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))
    | ~ spl2_302 ),
    inference(superposition,[],[f100,f18072])).

fof(f18090,plain,
    ( spl2_302
    | spl2_306
    | ~ spl2_295 ),
    inference(avatar_split_clause,[],[f18068,f17843,f18088,f18070])).

fof(f18088,plain,
    ( spl2_306
  <=> ! [X15] : ~ r1_tarski(k1_tops_1(sK0,sK1),k6_subset_1(X15,k6_subset_1(sK1,k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_306])])).

fof(f18068,plain,
    ( ! [X15] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK1),k6_subset_1(X15,k6_subset_1(sK1,k2_pre_topc(sK0,sK1))))
        | k1_xboole_0 = k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) )
    | ~ spl2_295 ),
    inference(resolution,[],[f17868,f104])).

fof(f17868,plain,
    ( ! [X2] :
        ( r1_tarski(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),X2)
        | ~ r1_tarski(k1_tops_1(sK0,sK1),X2) )
    | ~ spl2_295 ),
    inference(resolution,[],[f17845,f95])).

fof(f18086,plain,
    ( spl2_302
    | ~ spl2_305
    | ~ spl2_295 ),
    inference(avatar_split_clause,[],[f18065,f17843,f18082,f18070])).

fof(f18082,plain,
    ( spl2_305
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_305])])).

fof(f18065,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 = k6_subset_1(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_295 ),
    inference(resolution,[],[f17868,f168])).

fof(f18085,plain,
    ( spl2_304
    | ~ spl2_305
    | ~ spl2_295 ),
    inference(avatar_split_clause,[],[f18064,f17843,f18082,f18079])).

fof(f18079,plain,
    ( spl2_304
  <=> ! [X10] : k1_xboole_0 = k6_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),X10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_304])])).

fof(f18064,plain,
    ( ! [X10] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0)
        | k1_xboole_0 = k6_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),X10) )
    | ~ spl2_295 ),
    inference(resolution,[],[f17868,f184])).

fof(f184,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | k1_xboole_0 = k6_subset_1(X2,X3) ) ),
    inference(resolution,[],[f168,f151])).

fof(f18077,plain,
    ( spl2_302
    | ~ spl2_303
    | ~ spl2_295 ),
    inference(avatar_split_clause,[],[f18057,f17843,f18074,f18070])).

fof(f18074,plain,
    ( spl2_303
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_303])])).

fof(f18057,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1))))
    | k1_xboole_0 = k6_subset_1(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_295 ),
    inference(resolution,[],[f17868,f162])).

fof(f17883,plain,
    ( spl2_301
    | ~ spl2_295 ),
    inference(avatar_split_clause,[],[f17866,f17843,f17880])).

fof(f17880,plain,
    ( spl2_301
  <=> k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) = k3_subset_1(k1_tops_1(sK0,sK1),k3_subset_1(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_301])])).

fof(f17866,plain,
    ( k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) = k3_subset_1(k1_tops_1(sK0,sK1),k3_subset_1(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1))))
    | ~ spl2_295 ),
    inference(resolution,[],[f17845,f515])).

fof(f17878,plain,
    ( spl2_300
    | ~ spl2_295 ),
    inference(avatar_split_clause,[],[f17865,f17843,f17875])).

fof(f17875,plain,
    ( spl2_300
  <=> k3_subset_1(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1))) = k6_subset_1(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_300])])).

fof(f17865,plain,
    ( k3_subset_1(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1))) = k6_subset_1(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1)))
    | ~ spl2_295 ),
    inference(resolution,[],[f17845,f848])).

fof(f17873,plain,
    ( spl2_299
    | ~ spl2_295 ),
    inference(avatar_split_clause,[],[f17863,f17843,f17870])).

fof(f17870,plain,
    ( spl2_299
  <=> k1_tops_1(sK0,sK1) = k4_subset_1(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k3_subset_1(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_299])])).

fof(f17863,plain,
    ( k1_tops_1(sK0,sK1) = k4_subset_1(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k3_subset_1(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1))))
    | ~ spl2_295 ),
    inference(resolution,[],[f17845,f2085])).

fof(f17861,plain,
    ( spl2_298
    | ~ spl2_291 ),
    inference(avatar_split_clause,[],[f17837,f17770,f17858])).

fof(f17858,plain,
    ( spl2_298
  <=> sK1 = k3_subset_1(k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),k3_subset_1(k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_298])])).

fof(f17837,plain,
    ( sK1 = k3_subset_1(k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),k3_subset_1(k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),sK1))
    | ~ spl2_291 ),
    inference(resolution,[],[f17772,f515])).

fof(f17856,plain,
    ( spl2_297
    | ~ spl2_291 ),
    inference(avatar_split_clause,[],[f17836,f17770,f17853])).

fof(f17853,plain,
    ( spl2_297
  <=> k3_subset_1(k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),sK1) = k6_subset_1(k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_297])])).

fof(f17836,plain,
    ( k3_subset_1(k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),sK1) = k6_subset_1(k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),sK1)
    | ~ spl2_291 ),
    inference(resolution,[],[f17772,f848])).

fof(f17851,plain,
    ( spl2_296
    | ~ spl2_291 ),
    inference(avatar_split_clause,[],[f17834,f17770,f17848])).

fof(f17848,plain,
    ( spl2_296
  <=> k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) = k4_subset_1(k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),sK1,k3_subset_1(k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_296])])).

fof(f17834,plain,
    ( k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) = k4_subset_1(k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),sK1,k3_subset_1(k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),sK1))
    | ~ spl2_291 ),
    inference(resolution,[],[f17772,f2085])).

fof(f17846,plain,
    ( spl2_295
    | ~ spl2_291 ),
    inference(avatar_split_clause,[],[f17833,f17770,f17843])).

fof(f17833,plain,
    ( r1_tarski(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl2_291 ),
    inference(resolution,[],[f17772,f106])).

fof(f17815,plain,
    ( spl2_294
    | ~ spl2_290 ),
    inference(avatar_split_clause,[],[f17795,f17764,f17812])).

fof(f17812,plain,
    ( spl2_294
  <=> sK1 = k3_subset_1(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),k3_subset_1(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_294])])).

fof(f17795,plain,
    ( sK1 = k3_subset_1(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),k3_subset_1(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),sK1))
    | ~ spl2_290 ),
    inference(resolution,[],[f17766,f515])).

fof(f17810,plain,
    ( spl2_293
    | ~ spl2_290 ),
    inference(avatar_split_clause,[],[f17794,f17764,f17807])).

fof(f17807,plain,
    ( spl2_293
  <=> k3_subset_1(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),sK1) = k6_subset_1(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_293])])).

fof(f17794,plain,
    ( k3_subset_1(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),sK1) = k6_subset_1(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),sK1)
    | ~ spl2_290 ),
    inference(resolution,[],[f17766,f848])).

fof(f17805,plain,
    ( spl2_292
    | ~ spl2_290 ),
    inference(avatar_split_clause,[],[f17792,f17764,f17802])).

fof(f17802,plain,
    ( spl2_292
  <=> k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) = k4_subset_1(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),sK1,k3_subset_1(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_292])])).

fof(f17792,plain,
    ( k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) = k4_subset_1(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),sK1,k3_subset_1(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),sK1))
    | ~ spl2_290 ),
    inference(resolution,[],[f17766,f2085])).

fof(f17773,plain,
    ( spl2_291
    | ~ spl2_22
    | ~ spl2_198 ),
    inference(avatar_split_clause,[],[f17768,f6757,f1773,f17770])).

fof(f1773,plain,
    ( spl2_22
  <=> k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f6757,plain,
    ( spl2_198
  <=> r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_198])])).

fof(f17768,plain,
    ( r1_tarski(sK1,k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))))
    | ~ spl2_22
    | ~ spl2_198 ),
    inference(forward_demodulation,[],[f17760,f77])).

fof(f17760,plain,
    ( r1_tarski(sK1,k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))))
    | ~ spl2_22
    | ~ spl2_198 ),
    inference(resolution,[],[f6573,f6759])).

fof(f6759,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl2_198 ),
    inference(avatar_component_clause,[],[f6757])).

fof(f6573,plain,
    ( ! [X18] :
        ( ~ r1_tarski(k2_tops_1(sK0,sK1),X18)
        | r1_tarski(sK1,k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),X18))) )
    | ~ spl2_22 ),
    inference(superposition,[],[f107,f1774])).

fof(f1774,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f1773])).

fof(f17767,plain,
    ( spl2_290
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f17762,f1773,f17764])).

fof(f17762,plain,
    ( r1_tarski(sK1,k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))))
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f17741,f77])).

fof(f17741,plain,
    ( r1_tarski(sK1,k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))))
    | ~ spl2_22 ),
    inference(resolution,[],[f6573,f135])).

fof(f135,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f99,f98])).

fof(f17538,plain,
    ( spl2_289
    | ~ spl2_282
    | ~ spl2_284
    | ~ spl2_288 ),
    inference(avatar_split_clause,[],[f17533,f17515,f17491,f17478,f17535])).

fof(f17535,plain,
    ( spl2_289
  <=> k1_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_289])])).

fof(f17478,plain,
    ( spl2_282
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_282])])).

fof(f17491,plain,
    ( spl2_284
  <=> k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_284])])).

fof(f17515,plain,
    ( spl2_288
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_288])])).

fof(f17533,plain,
    ( k1_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))
    | ~ spl2_282
    | ~ spl2_284
    | ~ spl2_288 ),
    inference(forward_demodulation,[],[f17532,f17517])).

fof(f17517,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))
    | ~ spl2_288 ),
    inference(avatar_component_clause,[],[f17515])).

fof(f17532,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) = k6_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))
    | ~ spl2_282
    | ~ spl2_284 ),
    inference(forward_demodulation,[],[f17526,f17493])).

fof(f17493,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_284 ),
    inference(avatar_component_clause,[],[f17491])).

fof(f17526,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) = k6_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))
    | ~ spl2_282 ),
    inference(resolution,[],[f17480,f850])).

fof(f850,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(X4))
      | k3_subset_1(X4,k3_subset_1(X4,X5)) = k6_subset_1(X4,k3_subset_1(X4,X5)) ) ),
    inference(resolution,[],[f103,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f17480,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_282 ),
    inference(avatar_component_clause,[],[f17478])).

fof(f17518,plain,
    ( spl2_288
    | ~ spl2_226
    | ~ spl2_284 ),
    inference(avatar_split_clause,[],[f17498,f17491,f7706,f17515])).

fof(f7706,plain,
    ( spl2_226
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_226])])).

fof(f17498,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))
    | ~ spl2_226
    | ~ spl2_284 ),
    inference(backward_demodulation,[],[f7708,f17493])).

fof(f7708,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))
    | ~ spl2_226 ),
    inference(avatar_component_clause,[],[f7706])).

fof(f17513,plain,
    ( spl2_287
    | ~ spl2_245
    | ~ spl2_284 ),
    inference(avatar_split_clause,[],[f17497,f17491,f12139,f17510])).

fof(f17510,plain,
    ( spl2_287
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_287])])).

fof(f12139,plain,
    ( spl2_245
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_245])])).

fof(f17497,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))
    | ~ spl2_245
    | ~ spl2_284 ),
    inference(backward_demodulation,[],[f12141,f17493])).

fof(f12141,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))
    | ~ spl2_245 ),
    inference(avatar_component_clause,[],[f12139])).

fof(f17508,plain,
    ( spl2_286
    | ~ spl2_283
    | ~ spl2_284 ),
    inference(avatar_split_clause,[],[f17496,f17491,f17485,f17505])).

fof(f17505,plain,
    ( spl2_286
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_286])])).

fof(f17485,plain,
    ( spl2_283
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_283])])).

fof(f17496,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl2_283
    | ~ spl2_284 ),
    inference(backward_demodulation,[],[f17487,f17493])).

fof(f17487,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl2_283 ),
    inference(avatar_component_clause,[],[f17485])).

fof(f17503,plain,
    ( ~ spl2_285
    | spl2_280
    | ~ spl2_284 ),
    inference(avatar_split_clause,[],[f17495,f17491,f17469,f17500])).

fof(f17500,plain,
    ( spl2_285
  <=> r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_285])])).

fof(f17469,plain,
    ( spl2_280
  <=> r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_280])])).

fof(f17495,plain,
    ( ~ r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | spl2_280
    | ~ spl2_284 ),
    inference(backward_demodulation,[],[f17471,f17493])).

fof(f17471,plain,
    ( ~ r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | spl2_280 ),
    inference(avatar_component_clause,[],[f17469])).

fof(f17494,plain,
    ( spl2_284
    | ~ spl2_231
    | ~ spl2_279 ),
    inference(avatar_split_clause,[],[f17489,f17462,f8227,f17491])).

fof(f8227,plain,
    ( spl2_231
  <=> k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k6_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_231])])).

fof(f17462,plain,
    ( spl2_279
  <=> k6_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_279])])).

fof(f17489,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_231
    | ~ spl2_279 ),
    inference(backward_demodulation,[],[f8229,f17464])).

fof(f17464,plain,
    ( k6_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_279 ),
    inference(avatar_component_clause,[],[f17462])).

fof(f8229,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k6_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_231 ),
    inference(avatar_component_clause,[],[f8227])).

fof(f17488,plain,
    ( spl2_283
    | ~ spl2_228
    | ~ spl2_231 ),
    inference(avatar_split_clause,[],[f17483,f8227,f8009,f17485])).

fof(f8009,plain,
    ( spl2_228
  <=> k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_228])])).

fof(f17483,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl2_228
    | ~ spl2_231 ),
    inference(forward_demodulation,[],[f17459,f8229])).

fof(f17459,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl2_228 ),
    inference(superposition,[],[f2102,f8011])).

fof(f8011,plain,
    ( k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))
    | ~ spl2_228 ),
    inference(avatar_component_clause,[],[f8009])).

fof(f17481,plain,
    ( spl2_282
    | ~ spl2_228 ),
    inference(avatar_split_clause,[],[f17453,f8009,f17478])).

fof(f17453,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_228 ),
    inference(superposition,[],[f163,f8011])).

fof(f17476,plain,
    ( ~ spl2_280
    | spl2_281
    | ~ spl2_228
    | ~ spl2_231 ),
    inference(avatar_split_clause,[],[f17467,f8227,f8009,f17473,f17469])).

fof(f17473,plain,
    ( spl2_281
  <=> k1_xboole_0 = k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_281])])).

fof(f17467,plain,
    ( k1_xboole_0 = k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl2_228
    | ~ spl2_231 ),
    inference(forward_demodulation,[],[f17466,f8229])).

fof(f17466,plain,
    ( ~ r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | k1_xboole_0 = k6_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_228
    | ~ spl2_231 ),
    inference(forward_demodulation,[],[f17452,f8229])).

fof(f17452,plain,
    ( ~ r1_tarski(k6_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | k1_xboole_0 = k6_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_228 ),
    inference(superposition,[],[f162,f8011])).

fof(f17465,plain,
    ( spl2_279
    | ~ spl2_228 ),
    inference(avatar_split_clause,[],[f17451,f8009,f17462])).

fof(f17451,plain,
    ( k6_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_228 ),
    inference(superposition,[],[f102,f8011])).

fof(f102,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f83,f78,f79])).

fof(f83,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f17410,plain,
    ( spl2_278
    | ~ spl2_189
    | ~ spl2_237
    | ~ spl2_240 ),
    inference(avatar_split_clause,[],[f17405,f10584,f10566,f6690,f17407])).

fof(f17407,plain,
    ( spl2_278
  <=> k1_tops_1(sK0,sK1) = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_278])])).

fof(f6690,plain,
    ( spl2_189
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_189])])).

fof(f10566,plain,
    ( spl2_237
  <=> k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_237])])).

fof(f10584,plain,
    ( spl2_240
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_240])])).

fof(f17405,plain,
    ( k1_tops_1(sK0,sK1) = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_189
    | ~ spl2_237
    | ~ spl2_240 ),
    inference(forward_demodulation,[],[f17404,f10586])).

fof(f10586,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_240 ),
    inference(avatar_component_clause,[],[f10584])).

fof(f17404,plain,
    ( k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_189
    | ~ spl2_237 ),
    inference(forward_demodulation,[],[f17363,f10568])).

fof(f10568,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl2_237 ),
    inference(avatar_component_clause,[],[f10566])).

fof(f17363,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_189 ),
    inference(resolution,[],[f850,f6692])).

fof(f6692,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_189 ),
    inference(avatar_component_clause,[],[f6690])).

fof(f17401,plain,
    ( spl2_277
    | ~ spl2_270
    | ~ spl2_272
    | ~ spl2_276 ),
    inference(avatar_split_clause,[],[f17396,f17196,f17172,f17159,f17398])).

fof(f17398,plain,
    ( spl2_277
  <=> k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_277])])).

fof(f17159,plain,
    ( spl2_270
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_270])])).

fof(f17172,plain,
    ( spl2_272
  <=> k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_272])])).

fof(f17196,plain,
    ( spl2_276
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_276])])).

fof(f17396,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl2_270
    | ~ spl2_272
    | ~ spl2_276 ),
    inference(forward_demodulation,[],[f17395,f17198])).

fof(f17198,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl2_276 ),
    inference(avatar_component_clause,[],[f17196])).

fof(f17395,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) = k6_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl2_270
    | ~ spl2_272 ),
    inference(forward_demodulation,[],[f17361,f17174])).

fof(f17174,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_272 ),
    inference(avatar_component_clause,[],[f17172])).

fof(f17361,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) = k6_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl2_270 ),
    inference(resolution,[],[f850,f17161])).

fof(f17161,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_270 ),
    inference(avatar_component_clause,[],[f17159])).

fof(f17199,plain,
    ( spl2_276
    | ~ spl2_225
    | ~ spl2_272 ),
    inference(avatar_split_clause,[],[f17179,f17172,f7701,f17196])).

fof(f7701,plain,
    ( spl2_225
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_225])])).

fof(f17179,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl2_225
    | ~ spl2_272 ),
    inference(backward_demodulation,[],[f7703,f17174])).

fof(f7703,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl2_225 ),
    inference(avatar_component_clause,[],[f7701])).

fof(f17194,plain,
    ( spl2_275
    | ~ spl2_244
    | ~ spl2_272 ),
    inference(avatar_split_clause,[],[f17178,f17172,f12134,f17191])).

fof(f17191,plain,
    ( spl2_275
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_275])])).

fof(f12134,plain,
    ( spl2_244
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_244])])).

fof(f17178,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl2_244
    | ~ spl2_272 ),
    inference(backward_demodulation,[],[f12136,f17174])).

fof(f12136,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl2_244 ),
    inference(avatar_component_clause,[],[f12134])).

fof(f17189,plain,
    ( spl2_274
    | ~ spl2_271
    | ~ spl2_272 ),
    inference(avatar_split_clause,[],[f17177,f17172,f17166,f17186])).

fof(f17186,plain,
    ( spl2_274
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_274])])).

fof(f17166,plain,
    ( spl2_271
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_271])])).

fof(f17177,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ spl2_271
    | ~ spl2_272 ),
    inference(backward_demodulation,[],[f17168,f17174])).

fof(f17168,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ spl2_271 ),
    inference(avatar_component_clause,[],[f17166])).

fof(f17184,plain,
    ( ~ spl2_273
    | spl2_268
    | ~ spl2_272 ),
    inference(avatar_split_clause,[],[f17176,f17172,f17150,f17181])).

fof(f17181,plain,
    ( spl2_273
  <=> r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_273])])).

fof(f17150,plain,
    ( spl2_268
  <=> r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_268])])).

fof(f17176,plain,
    ( ~ r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | spl2_268
    | ~ spl2_272 ),
    inference(backward_demodulation,[],[f17152,f17174])).

fof(f17152,plain,
    ( ~ r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | spl2_268 ),
    inference(avatar_component_clause,[],[f17150])).

fof(f17175,plain,
    ( spl2_272
    | ~ spl2_230
    | ~ spl2_267 ),
    inference(avatar_split_clause,[],[f17170,f17143,f8222,f17172])).

fof(f8222,plain,
    ( spl2_230
  <=> k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k6_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_230])])).

fof(f17143,plain,
    ( spl2_267
  <=> k6_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_267])])).

fof(f17170,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_230
    | ~ spl2_267 ),
    inference(backward_demodulation,[],[f8224,f17145])).

fof(f17145,plain,
    ( k6_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_267 ),
    inference(avatar_component_clause,[],[f17143])).

fof(f8224,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k6_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_230 ),
    inference(avatar_component_clause,[],[f8222])).

fof(f17169,plain,
    ( spl2_271
    | ~ spl2_222
    | ~ spl2_230 ),
    inference(avatar_split_clause,[],[f17164,f8222,f7344,f17166])).

fof(f7344,plain,
    ( spl2_222
  <=> k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_222])])).

fof(f17164,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ spl2_222
    | ~ spl2_230 ),
    inference(forward_demodulation,[],[f17141,f8224])).

fof(f17141,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ spl2_222 ),
    inference(superposition,[],[f2102,f7346])).

fof(f7346,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl2_222 ),
    inference(avatar_component_clause,[],[f7344])).

fof(f17162,plain,
    ( spl2_270
    | ~ spl2_222 ),
    inference(avatar_split_clause,[],[f17135,f7344,f17159])).

fof(f17135,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_222 ),
    inference(superposition,[],[f163,f7346])).

fof(f17157,plain,
    ( ~ spl2_268
    | spl2_269
    | ~ spl2_222
    | ~ spl2_230 ),
    inference(avatar_split_clause,[],[f17148,f8222,f7344,f17154,f17150])).

fof(f17154,plain,
    ( spl2_269
  <=> k1_xboole_0 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_269])])).

fof(f17148,plain,
    ( k1_xboole_0 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ spl2_222
    | ~ spl2_230 ),
    inference(forward_demodulation,[],[f17147,f8224])).

fof(f17147,plain,
    ( ~ r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | k1_xboole_0 = k6_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_222
    | ~ spl2_230 ),
    inference(forward_demodulation,[],[f17134,f8224])).

fof(f17134,plain,
    ( ~ r1_tarski(k6_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | k1_xboole_0 = k6_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_222 ),
    inference(superposition,[],[f162,f7346])).

fof(f17146,plain,
    ( spl2_267
    | ~ spl2_222 ),
    inference(avatar_split_clause,[],[f17133,f7344,f17143])).

fof(f17133,plain,
    ( k6_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_222 ),
    inference(superposition,[],[f102,f7346])).

fof(f16840,plain,
    ( spl2_266
    | ~ spl2_264 ),
    inference(avatar_split_clause,[],[f16835,f16788,f16837])).

fof(f16837,plain,
    ( spl2_266
  <=> k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k4_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_xboole_0,k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_266])])).

fof(f16835,plain,
    ( k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k4_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_xboole_0,k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1))))
    | ~ spl2_264 ),
    inference(forward_demodulation,[],[f16822,f77])).

fof(f16822,plain,
    ( k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k4_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_xboole_0,k1_setfam_1(k2_tarski(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1))))
    | ~ spl2_264 ),
    inference(superposition,[],[f2102,f16790])).

fof(f16832,plain,
    ( spl2_265
    | ~ spl2_264 ),
    inference(avatar_split_clause,[],[f16831,f16788,f16826])).

fof(f16831,plain,
    ( k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1)))
    | ~ spl2_264 ),
    inference(forward_demodulation,[],[f16830,f77])).

fof(f16830,plain,
    ( k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k1_setfam_1(k2_tarski(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1)))
    | ~ spl2_264 ),
    inference(forward_demodulation,[],[f16818,f856])).

fof(f16818,plain,
    ( k1_setfam_1(k2_tarski(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1))) = k3_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_xboole_0)
    | ~ spl2_264 ),
    inference(superposition,[],[f859,f16790])).

fof(f16829,plain,
    ( spl2_265
    | ~ spl2_264 ),
    inference(avatar_split_clause,[],[f16824,f16788,f16826])).

fof(f16824,plain,
    ( k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1)))
    | ~ spl2_264 ),
    inference(forward_demodulation,[],[f16823,f98])).

fof(f16823,plain,
    ( k6_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_xboole_0) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1)))
    | ~ spl2_264 ),
    inference(forward_demodulation,[],[f16813,f77])).

fof(f16813,plain,
    ( k6_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_xboole_0) = k1_setfam_1(k2_tarski(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1)))
    | ~ spl2_264 ),
    inference(superposition,[],[f100,f16790])).

fof(f16796,plain,
    ( spl2_264
    | ~ spl2_233 ),
    inference(avatar_split_clause,[],[f16786,f10518,f16788])).

fof(f16786,plain,
    ( k1_xboole_0 = k6_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_233 ),
    inference(resolution,[],[f16762,f104])).

fof(f16762,plain,
    ( ! [X1] : r1_tarski(k6_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1)),X1)
    | ~ spl2_233 ),
    inference(resolution,[],[f15321,f1041])).

fof(f15321,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k3_tarski(k2_tarski(X0,k2_tops_1(sK0,sK1))))
    | ~ spl2_233 ),
    inference(resolution,[],[f15320,f107])).

fof(f15320,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),X0),k2_tops_1(sK0,sK1))
    | ~ spl2_233 ),
    inference(superposition,[],[f10526,f863])).

fof(f10526,plain,
    ( ! [X0] : r1_tarski(k1_setfam_1(k2_tarski(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),X0)),k2_tops_1(sK0,sK1))
    | ~ spl2_233 ),
    inference(resolution,[],[f10520,f161])).

fof(f16793,plain,
    ( spl2_264
    | ~ spl2_233 ),
    inference(avatar_split_clause,[],[f16783,f10518,f16788])).

fof(f16783,plain,
    ( k1_xboole_0 = k6_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_233 ),
    inference(resolution,[],[f16762,f168])).

fof(f16791,plain,
    ( spl2_264
    | ~ spl2_233 ),
    inference(avatar_split_clause,[],[f16775,f10518,f16788])).

fof(f16775,plain,
    ( k1_xboole_0 = k6_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_233 ),
    inference(resolution,[],[f16762,f162])).

fof(f15475,plain,
    ( ~ spl2_263
    | ~ spl2_48
    | spl2_258 ),
    inference(avatar_split_clause,[],[f15470,f15350,f2833,f15472])).

fof(f15472,plain,
    ( spl2_263
  <=> r1_tarski(sK1,k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_263])])).

fof(f2833,plain,
    ( spl2_48
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f15350,plain,
    ( spl2_258
  <=> r1_tarski(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_258])])).

fof(f15470,plain,
    ( ~ r1_tarski(sK1,k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1))))
    | ~ spl2_48
    | spl2_258 ),
    inference(resolution,[],[f15352,f3094])).

fof(f3094,plain,
    ( ! [X1] :
        ( r1_tarski(k2_tops_1(sK0,sK1),X1)
        | ~ r1_tarski(sK1,X1) )
    | ~ spl2_48 ),
    inference(resolution,[],[f2835,f95])).

fof(f2835,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f2833])).

fof(f15352,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1))))
    | spl2_258 ),
    inference(avatar_component_clause,[],[f15350])).

fof(f15461,plain,
    ( spl2_262
    | ~ spl2_257 ),
    inference(avatar_split_clause,[],[f15456,f15346,f15458])).

fof(f15458,plain,
    ( spl2_262
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k1_xboole_0,k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_262])])).

fof(f15346,plain,
    ( spl2_257
  <=> k1_xboole_0 = k6_subset_1(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_257])])).

fof(f15456,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k1_xboole_0,k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1))))
    | ~ spl2_257 ),
    inference(forward_demodulation,[],[f15442,f77])).

fof(f15442,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k1_xboole_0,k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),sK1)))
    | ~ spl2_257 ),
    inference(superposition,[],[f2102,f15348])).

fof(f15348,plain,
    ( k1_xboole_0 = k6_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_257 ),
    inference(avatar_component_clause,[],[f15346])).

fof(f15454,plain,
    ( spl2_261
    | ~ spl2_257 ),
    inference(avatar_split_clause,[],[f15453,f15346,f15448])).

fof(f15448,plain,
    ( spl2_261
  <=> k2_pre_topc(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_261])])).

fof(f15453,plain,
    ( k2_pre_topc(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))
    | ~ spl2_257 ),
    inference(forward_demodulation,[],[f15452,f77])).

fof(f15452,plain,
    ( k2_pre_topc(sK0,sK1) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl2_257 ),
    inference(forward_demodulation,[],[f15439,f856])).

fof(f15439,plain,
    ( k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),sK1)) = k3_subset_1(k2_pre_topc(sK0,sK1),k1_xboole_0)
    | ~ spl2_257 ),
    inference(superposition,[],[f859,f15348])).

fof(f15451,plain,
    ( spl2_261
    | ~ spl2_257 ),
    inference(avatar_split_clause,[],[f15446,f15346,f15448])).

fof(f15446,plain,
    ( k2_pre_topc(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))
    | ~ spl2_257 ),
    inference(forward_demodulation,[],[f15445,f98])).

fof(f15445,plain,
    ( k6_subset_1(k2_pre_topc(sK0,sK1),k1_xboole_0) = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))
    | ~ spl2_257 ),
    inference(forward_demodulation,[],[f15434,f77])).

fof(f15434,plain,
    ( k6_subset_1(k2_pre_topc(sK0,sK1),k1_xboole_0) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl2_257 ),
    inference(superposition,[],[f100,f15348])).

fof(f15362,plain,
    ( spl2_257
    | spl2_260
    | ~ spl2_233 ),
    inference(avatar_split_clause,[],[f15343,f10518,f15360,f15346])).

fof(f15360,plain,
    ( spl2_260
  <=> ! [X15] : ~ r1_tarski(k2_tops_1(sK0,sK1),k6_subset_1(X15,k6_subset_1(k2_pre_topc(sK0,sK1),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_260])])).

fof(f15343,plain,
    ( ! [X15] :
        ( ~ r1_tarski(k2_tops_1(sK0,sK1),k6_subset_1(X15,k6_subset_1(k2_pre_topc(sK0,sK1),sK1)))
        | k1_xboole_0 = k6_subset_1(k2_pre_topc(sK0,sK1),sK1) )
    | ~ spl2_233 ),
    inference(resolution,[],[f10527,f104])).

fof(f10527,plain,
    ( ! [X1] :
        ( r1_tarski(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),X1)
        | ~ r1_tarski(k2_tops_1(sK0,sK1),X1) )
    | ~ spl2_233 ),
    inference(resolution,[],[f10520,f95])).

fof(f15358,plain,
    ( spl2_257
    | ~ spl2_186
    | ~ spl2_233 ),
    inference(avatar_split_clause,[],[f15340,f10518,f6486,f15346])).

fof(f6486,plain,
    ( spl2_186
  <=> r1_tarski(k2_tops_1(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_186])])).

fof(f15340,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 = k6_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_233 ),
    inference(resolution,[],[f10527,f168])).

fof(f15357,plain,
    ( spl2_259
    | ~ spl2_186
    | ~ spl2_233 ),
    inference(avatar_split_clause,[],[f15339,f10518,f6486,f15355])).

fof(f15355,plain,
    ( spl2_259
  <=> ! [X10] : k1_xboole_0 = k6_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),X10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_259])])).

fof(f15339,plain,
    ( ! [X10] :
        ( ~ r1_tarski(k2_tops_1(sK0,sK1),k1_xboole_0)
        | k1_xboole_0 = k6_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),X10) )
    | ~ spl2_233 ),
    inference(resolution,[],[f10527,f184])).

fof(f15353,plain,
    ( spl2_257
    | ~ spl2_258
    | ~ spl2_233 ),
    inference(avatar_split_clause,[],[f15344,f10518,f15350,f15346])).

fof(f15344,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1))))
    | k1_xboole_0 = k6_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_233 ),
    inference(forward_demodulation,[],[f15332,f77])).

fof(f15332,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),sK1)))
    | k1_xboole_0 = k6_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_233 ),
    inference(resolution,[],[f10527,f162])).

fof(f15046,plain,
    ( ~ spl2_255
    | spl2_256
    | ~ spl2_188
    | ~ spl2_236 ),
    inference(avatar_split_clause,[],[f15037,f10559,f6550,f15043,f15039])).

fof(f15039,plain,
    ( spl2_255
  <=> r1_tarski(k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_255])])).

fof(f15043,plain,
    ( spl2_256
  <=> k1_xboole_0 = k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_256])])).

fof(f6550,plain,
    ( spl2_188
  <=> k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_188])])).

fof(f10559,plain,
    ( spl2_236
  <=> k6_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_236])])).

fof(f15037,plain,
    ( k1_xboole_0 = k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl2_188
    | ~ spl2_236 ),
    inference(forward_demodulation,[],[f15036,f10561])).

fof(f10561,plain,
    ( k6_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl2_236 ),
    inference(avatar_component_clause,[],[f10559])).

fof(f15036,plain,
    ( ~ r1_tarski(k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | k1_xboole_0 = k6_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl2_188
    | ~ spl2_236 ),
    inference(forward_demodulation,[],[f15010,f10561])).

fof(f15010,plain,
    ( ~ r1_tarski(k6_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | k1_xboole_0 = k6_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl2_188 ),
    inference(superposition,[],[f162,f6552])).

fof(f6552,plain,
    ( k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_188 ),
    inference(avatar_component_clause,[],[f6550])).

fof(f14174,plain,
    ( ~ spl2_253
    | spl2_254
    | ~ spl2_175
    | ~ spl2_200 ),
    inference(avatar_split_clause,[],[f14162,f6822,f6337,f14171,f14167])).

fof(f14167,plain,
    ( spl2_253
  <=> r1_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_253])])).

fof(f14171,plain,
    ( spl2_254
  <=> r1_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_254])])).

fof(f6337,plain,
    ( spl2_175
  <=> k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_175])])).

fof(f6822,plain,
    ( spl2_200
  <=> k6_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_200])])).

fof(f14162,plain,
    ( r1_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ r1_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | ~ spl2_175
    | ~ spl2_200 ),
    inference(superposition,[],[f6755,f6824])).

fof(f6824,plain,
    ( k6_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl2_200 ),
    inference(avatar_component_clause,[],[f6822])).

fof(f6755,plain,
    ( ! [X1] :
        ( r1_tarski(k6_subset_1(X1,sK1),k2_tops_1(sK0,sK1))
        | ~ r1_tarski(X1,k2_pre_topc(sK0,sK1)) )
    | ~ spl2_175 ),
    inference(superposition,[],[f106,f6339])).

fof(f6339,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_175 ),
    inference(avatar_component_clause,[],[f6337])).

fof(f14111,plain,
    ( spl2_252
    | ~ spl2_55 ),
    inference(avatar_split_clause,[],[f14102,f3367,f14105])).

fof(f14105,plain,
    ( spl2_252
  <=> k1_xboole_0 = k6_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_252])])).

fof(f3367,plain,
    ( spl2_55
  <=> k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).

fof(f14102,plain,
    ( k1_xboole_0 = k6_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl2_55 ),
    inference(resolution,[],[f14079,f104])).

fof(f14079,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),u1_struct_0(sK0)),X0)
    | ~ spl2_55 ),
    inference(resolution,[],[f5141,f1041])).

fof(f5141,plain,
    ( ! [X144] : r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_tarski(k2_tarski(X144,u1_struct_0(sK0))))
    | ~ spl2_55 ),
    inference(resolution,[],[f1309,f3659])).

fof(f3659,plain,
    ( ! [X1] :
        ( ~ r1_tarski(u1_struct_0(sK0),X1)
        | r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),X1) )
    | ~ spl2_55 ),
    inference(superposition,[],[f151,f3369])).

fof(f3369,plain,
    ( k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))
    | ~ spl2_55 ),
    inference(avatar_component_clause,[],[f3367])).

fof(f1309,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) ),
    inference(resolution,[],[f107,f99])).

fof(f14108,plain,
    ( spl2_252
    | ~ spl2_55 ),
    inference(avatar_split_clause,[],[f14099,f3367,f14105])).

fof(f14099,plain,
    ( k1_xboole_0 = k6_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl2_55 ),
    inference(resolution,[],[f14079,f168])).

fof(f13481,plain,
    ( spl2_251
    | ~ spl2_175 ),
    inference(avatar_split_clause,[],[f13476,f6337,f13478])).

fof(f13476,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl2_175 ),
    inference(forward_demodulation,[],[f13361,f77])).

fof(f13361,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)))
    | ~ spl2_175 ),
    inference(superposition,[],[f1504,f6339])).

fof(f1504,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X1,X0)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) ),
    inference(superposition,[],[f101,f77])).

fof(f101,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f82,f80,f80,f80])).

fof(f82,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f13475,plain,
    ( spl2_250
    | ~ spl2_199 ),
    inference(avatar_split_clause,[],[f13360,f6763,f13472])).

fof(f13472,plain,
    ( spl2_250
  <=> k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_250])])).

fof(f6763,plain,
    ( spl2_199
  <=> k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_199])])).

fof(f13360,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)))
    | ~ spl2_199 ),
    inference(superposition,[],[f1504,f6765])).

fof(f6765,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))
    | ~ spl2_199 ),
    inference(avatar_component_clause,[],[f6763])).

fof(f13470,plain,
    ( spl2_249
    | ~ spl2_109 ),
    inference(avatar_split_clause,[],[f13359,f4799,f13467])).

fof(f13467,plain,
    ( spl2_249
  <=> u1_struct_0(sK0) = k3_tarski(k2_tarski(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_249])])).

fof(f4799,plain,
    ( spl2_109
  <=> u1_struct_0(sK0) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_109])])).

fof(f13359,plain,
    ( u1_struct_0(sK0) = k3_tarski(k2_tarski(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl2_109 ),
    inference(superposition,[],[f1504,f4801])).

fof(f4801,plain,
    ( u1_struct_0(sK0) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))
    | ~ spl2_109 ),
    inference(avatar_component_clause,[],[f4799])).

fof(f13465,plain,
    ( spl2_248
    | ~ spl2_217 ),
    inference(avatar_split_clause,[],[f13460,f7138,f13462])).

fof(f13462,plain,
    ( spl2_248
  <=> u1_struct_0(sK0) = k3_tarski(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_248])])).

fof(f7138,plain,
    ( spl2_217
  <=> u1_struct_0(sK0) = k3_tarski(k2_tarski(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_217])])).

fof(f13460,plain,
    ( u1_struct_0(sK0) = k3_tarski(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))
    | ~ spl2_217 ),
    inference(forward_demodulation,[],[f13358,f77])).

fof(f13358,plain,
    ( u1_struct_0(sK0) = k3_tarski(k2_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)))
    | ~ spl2_217 ),
    inference(superposition,[],[f1504,f7140])).

fof(f7140,plain,
    ( u1_struct_0(sK0) = k3_tarski(k2_tarski(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)))
    | ~ spl2_217 ),
    inference(avatar_component_clause,[],[f7138])).

fof(f12802,plain,
    ( spl2_247
    | ~ spl2_188
    | ~ spl2_236 ),
    inference(avatar_split_clause,[],[f12797,f10559,f6550,f12799])).

fof(f12799,plain,
    ( spl2_247
  <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_247])])).

fof(f12797,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl2_188
    | ~ spl2_236 ),
    inference(forward_demodulation,[],[f12679,f10561])).

fof(f12679,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl2_188 ),
    inference(superposition,[],[f2102,f6552])).

fof(f12147,plain,
    ( spl2_246
    | ~ spl2_233 ),
    inference(avatar_split_clause,[],[f12071,f10518,f12144])).

fof(f12071,plain,
    ( k2_tops_1(sK0,sK1) = k4_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k3_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1)))
    | ~ spl2_233 ),
    inference(resolution,[],[f2085,f10520])).

fof(f12142,plain,
    ( spl2_245
    | ~ spl2_223 ),
    inference(avatar_split_clause,[],[f12069,f7482,f12139])).

fof(f12069,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))
    | ~ spl2_223 ),
    inference(resolution,[],[f2085,f7484])).

fof(f12137,plain,
    ( spl2_244
    | ~ spl2_198 ),
    inference(avatar_split_clause,[],[f12068,f6757,f12134])).

fof(f12068,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl2_198 ),
    inference(resolution,[],[f2085,f6759])).

fof(f12120,plain,
    ( spl2_243
    | ~ spl2_216 ),
    inference(avatar_split_clause,[],[f11854,f7133,f12117])).

fof(f12117,plain,
    ( spl2_243
  <=> k5_xboole_0(u1_struct_0(sK0),sK1) = k4_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1),k3_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_243])])).

fof(f7133,plain,
    ( spl2_216
  <=> r1_tarski(k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1),k5_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_216])])).

fof(f11854,plain,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) = k4_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1),k3_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1)))
    | ~ spl2_216 ),
    inference(resolution,[],[f2085,f7135])).

fof(f7135,plain,
    ( r1_tarski(k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1),k5_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_216 ),
    inference(avatar_component_clause,[],[f7133])).

fof(f11520,plain,
    ( spl2_242
    | ~ spl2_55
    | ~ spl2_109 ),
    inference(avatar_split_clause,[],[f11501,f4799,f3367,f11517])).

fof(f11517,plain,
    ( spl2_242
  <=> k1_xboole_0 = k6_subset_1(k6_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_242])])).

fof(f11501,plain,
    ( k1_xboole_0 = k6_subset_1(k6_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1),u1_struct_0(sK0))
    | ~ spl2_55
    | ~ spl2_109 ),
    inference(superposition,[],[f11465,f3369])).

fof(f11465,plain,
    ( ! [X17] : k1_xboole_0 = k6_subset_1(k6_subset_1(k6_subset_1(u1_struct_0(sK0),X17),sK1),u1_struct_0(sK0))
    | ~ spl2_109 ),
    inference(resolution,[],[f11438,f168])).

fof(f11438,plain,
    ( ! [X2,X3] : r1_tarski(k6_subset_1(k6_subset_1(k6_subset_1(u1_struct_0(sK0),X2),sK1),u1_struct_0(sK0)),X3)
    | ~ spl2_109 ),
    inference(resolution,[],[f10973,f1041])).

fof(f10973,plain,
    ( ! [X0,X1] : r1_tarski(k6_subset_1(k6_subset_1(u1_struct_0(sK0),X0),sK1),k3_tarski(k2_tarski(X1,u1_struct_0(sK0))))
    | ~ spl2_109 ),
    inference(resolution,[],[f10970,f107])).

fof(f10970,plain,
    ( ! [X2,X3] : r1_tarski(k6_subset_1(k6_subset_1(k6_subset_1(u1_struct_0(sK0),X2),sK1),X3),u1_struct_0(sK0))
    | ~ spl2_109 ),
    inference(superposition,[],[f10339,f863])).

fof(f10339,plain,
    ( ! [X4,X3] : r1_tarski(k1_setfam_1(k2_tarski(k6_subset_1(k6_subset_1(u1_struct_0(sK0),X3),sK1),X4)),u1_struct_0(sK0))
    | ~ spl2_109 ),
    inference(resolution,[],[f10325,f161])).

fof(f10325,plain,
    ( ! [X4] : r1_tarski(k6_subset_1(k6_subset_1(u1_struct_0(sK0),X4),sK1),u1_struct_0(sK0))
    | ~ spl2_109 ),
    inference(superposition,[],[f1037,f4801])).

fof(f1037,plain,(
    ! [X8,X7,X9] : r1_tarski(k6_subset_1(k6_subset_1(k3_tarski(k2_tarski(X7,X8)),X9),X7),X8) ),
    inference(resolution,[],[f106,f99])).

fof(f10910,plain,
    ( spl2_241
    | ~ spl2_92
    | ~ spl2_116 ),
    inference(avatar_split_clause,[],[f10902,f4958,f4511,f10904])).

fof(f10904,plain,
    ( spl2_241
  <=> k1_xboole_0 = k6_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_241])])).

fof(f4511,plain,
    ( spl2_92
  <=> k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) = k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_92])])).

fof(f4958,plain,
    ( spl2_116
  <=> k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_116])])).

fof(f10902,plain,
    ( k1_xboole_0 = k6_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | ~ spl2_92
    | ~ spl2_116 ),
    inference(resolution,[],[f10884,f104])).

fof(f10884,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),u1_struct_0(sK0)),X0)
    | ~ spl2_92
    | ~ spl2_116 ),
    inference(resolution,[],[f5145,f1041])).

fof(f5145,plain,
    ( ! [X150] : r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k3_tarski(k2_tarski(X150,u1_struct_0(sK0))))
    | ~ spl2_92
    | ~ spl2_116 ),
    inference(resolution,[],[f1309,f4966])).

fof(f4966,plain,
    ( ! [X1] :
        ( ~ r1_tarski(u1_struct_0(sK0),X1)
        | r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),X1) )
    | ~ spl2_92
    | ~ spl2_116 ),
    inference(backward_demodulation,[],[f4612,f4960])).

fof(f4960,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))
    | ~ spl2_116 ),
    inference(avatar_component_clause,[],[f4958])).

fof(f4612,plain,
    ( ! [X1] :
        ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),X1)
        | ~ r1_tarski(u1_struct_0(sK0),X1) )
    | ~ spl2_92 ),
    inference(superposition,[],[f151,f4513])).

fof(f4513,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) = k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))
    | ~ spl2_92 ),
    inference(avatar_component_clause,[],[f4511])).

fof(f10907,plain,
    ( spl2_241
    | ~ spl2_92
    | ~ spl2_116 ),
    inference(avatar_split_clause,[],[f10899,f4958,f4511,f10904])).

fof(f10899,plain,
    ( k1_xboole_0 = k6_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | ~ spl2_92
    | ~ spl2_116 ),
    inference(resolution,[],[f10884,f168])).

fof(f10587,plain,
    ( spl2_240
    | ~ spl2_197
    | ~ spl2_237 ),
    inference(avatar_split_clause,[],[f10572,f10566,f6741,f10584])).

fof(f6741,plain,
    ( spl2_197
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_197])])).

fof(f10572,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_197
    | ~ spl2_237 ),
    inference(backward_demodulation,[],[f6743,f10568])).

fof(f6743,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_197 ),
    inference(avatar_component_clause,[],[f6741])).

fof(f10582,plain,
    ( spl2_239
    | ~ spl2_195
    | ~ spl2_237 ),
    inference(avatar_split_clause,[],[f10571,f10566,f6731,f10579])).

fof(f10579,plain,
    ( spl2_239
  <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_239])])).

fof(f6731,plain,
    ( spl2_195
  <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_195])])).

fof(f10571,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_195
    | ~ spl2_237 ),
    inference(backward_demodulation,[],[f6733,f10568])).

fof(f6733,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_195 ),
    inference(avatar_component_clause,[],[f6731])).

fof(f10577,plain,
    ( spl2_238
    | ~ spl2_194
    | ~ spl2_237 ),
    inference(avatar_split_clause,[],[f10570,f10566,f6726,f10574])).

fof(f10574,plain,
    ( spl2_238
  <=> k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_238])])).

fof(f6726,plain,
    ( spl2_194
  <=> k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_194])])).

fof(f10570,plain,
    ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_194
    | ~ spl2_237 ),
    inference(backward_demodulation,[],[f6728,f10568])).

fof(f6728,plain,
    ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_194 ),
    inference(avatar_component_clause,[],[f6726])).

fof(f10569,plain,
    ( spl2_237
    | ~ spl2_196
    | ~ spl2_236 ),
    inference(avatar_split_clause,[],[f10564,f10559,f6736,f10566])).

fof(f6736,plain,
    ( spl2_196
  <=> k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k6_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_196])])).

fof(f10564,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl2_196
    | ~ spl2_236 ),
    inference(backward_demodulation,[],[f6738,f10561])).

fof(f6738,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k6_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl2_196 ),
    inference(avatar_component_clause,[],[f6736])).

fof(f10562,plain,
    ( spl2_236
    | ~ spl2_188 ),
    inference(avatar_split_clause,[],[f10551,f6550,f10559])).

fof(f10551,plain,
    ( k6_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl2_188 ),
    inference(superposition,[],[f102,f6552])).

fof(f10538,plain,
    ( spl2_235
    | ~ spl2_233 ),
    inference(avatar_split_clause,[],[f10525,f10518,f10535])).

fof(f10525,plain,
    ( k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1)))
    | ~ spl2_233 ),
    inference(resolution,[],[f10520,f515])).

fof(f10533,plain,
    ( spl2_234
    | ~ spl2_233 ),
    inference(avatar_split_clause,[],[f10524,f10518,f10530])).

fof(f10524,plain,
    ( k6_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1)) = k3_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl2_233 ),
    inference(resolution,[],[f10520,f848])).

fof(f10521,plain,
    ( spl2_233
    | ~ spl2_175 ),
    inference(avatar_split_clause,[],[f10513,f6337,f10518])).

fof(f10513,plain,
    ( r1_tarski(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_175 ),
    inference(superposition,[],[f10327,f98])).

fof(f10327,plain,
    ( ! [X6] : r1_tarski(k6_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),X6),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_175 ),
    inference(superposition,[],[f1037,f6339])).

fof(f10402,plain,
    ( spl2_232
    | ~ spl2_55
    | ~ spl2_217 ),
    inference(avatar_split_clause,[],[f10390,f7138,f3367,f10399])).

fof(f10399,plain,
    ( spl2_232
  <=> r1_tarski(k6_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1),k5_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_232])])).

fof(f10390,plain,
    ( r1_tarski(k6_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1),k5_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_55
    | ~ spl2_217 ),
    inference(superposition,[],[f10324,f3369])).

fof(f10324,plain,
    ( ! [X3] : r1_tarski(k6_subset_1(k6_subset_1(u1_struct_0(sK0),X3),sK1),k5_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_217 ),
    inference(superposition,[],[f1037,f7140])).

fof(f8230,plain,
    ( spl2_231
    | ~ spl2_223 ),
    inference(avatar_split_clause,[],[f8171,f7482,f8227])).

fof(f8171,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k6_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_223 ),
    inference(resolution,[],[f848,f7484])).

fof(f8225,plain,
    ( spl2_230
    | ~ spl2_198 ),
    inference(avatar_split_clause,[],[f8170,f6757,f8222])).

fof(f8170,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k6_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_198 ),
    inference(resolution,[],[f848,f6759])).

fof(f8210,plain,
    ( spl2_229
    | ~ spl2_216 ),
    inference(avatar_split_clause,[],[f8022,f7133,f8207])).

fof(f8207,plain,
    ( spl2_229
  <=> k3_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1)) = k6_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_229])])).

fof(f8022,plain,
    ( k3_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1)) = k6_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1))
    | ~ spl2_216 ),
    inference(resolution,[],[f848,f7135])).

fof(f8012,plain,
    ( spl2_228
    | ~ spl2_227 ),
    inference(avatar_split_clause,[],[f8007,f7976,f8009])).

fof(f7976,plain,
    ( spl2_227
  <=> k1_xboole_0 = k6_subset_1(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_227])])).

fof(f8007,plain,
    ( k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))
    | ~ spl2_227 ),
    inference(forward_demodulation,[],[f8006,f98])).

fof(f8006,plain,
    ( k6_subset_1(k1_tops_1(sK0,sK1),k1_xboole_0) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))
    | ~ spl2_227 ),
    inference(forward_demodulation,[],[f7998,f77])).

fof(f7998,plain,
    ( k6_subset_1(k1_tops_1(sK0,sK1),k1_xboole_0) = k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)))
    | ~ spl2_227 ),
    inference(superposition,[],[f100,f7978])).

fof(f7978,plain,
    ( k1_xboole_0 = k6_subset_1(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl2_227 ),
    inference(avatar_component_clause,[],[f7976])).

fof(f7981,plain,
    ( spl2_227
    | ~ spl2_199
    | ~ spl2_201 ),
    inference(avatar_split_clause,[],[f7974,f6829,f6763,f7976])).

fof(f6829,plain,
    ( spl2_201
  <=> k1_xboole_0 = k6_subset_1(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_201])])).

fof(f7974,plain,
    ( k1_xboole_0 = k6_subset_1(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl2_199
    | ~ spl2_201 ),
    inference(resolution,[],[f7960,f104])).

fof(f7960,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)),X0)
    | ~ spl2_199
    | ~ spl2_201 ),
    inference(resolution,[],[f7949,f106])).

fof(f7949,plain,
    ( ! [X0] : r1_tarski(k1_tops_1(sK0,sK1),k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),X0)))
    | ~ spl2_199
    | ~ spl2_201 ),
    inference(superposition,[],[f7837,f77])).

fof(f7837,plain,
    ( ! [X0] : r1_tarski(k1_tops_1(sK0,sK1),k3_tarski(k2_tarski(X0,k2_pre_topc(sK0,sK1))))
    | ~ spl2_199
    | ~ spl2_201 ),
    inference(resolution,[],[f7793,f107])).

fof(f7793,plain,
    ( ! [X2] : r1_tarski(k6_subset_1(k1_tops_1(sK0,sK1),X2),k2_pre_topc(sK0,sK1))
    | ~ spl2_199
    | ~ spl2_201 ),
    inference(superposition,[],[f7761,f6765])).

fof(f7761,plain,
    ( ! [X0,X1] : r1_tarski(k6_subset_1(k1_tops_1(sK0,sK1),X1),k3_tarski(k2_tarski(sK1,X0)))
    | ~ spl2_201 ),
    inference(superposition,[],[f7734,f77])).

fof(f7734,plain,
    ( ! [X17,X18] : r1_tarski(k6_subset_1(k1_tops_1(sK0,sK1),X17),k3_tarski(k2_tarski(X18,sK1)))
    | ~ spl2_201 ),
    inference(resolution,[],[f7497,f1309])).

fof(f7497,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(sK1,X3)
        | r1_tarski(k6_subset_1(k1_tops_1(sK0,sK1),X4),X3) )
    | ~ spl2_201 ),
    inference(resolution,[],[f7489,f95])).

fof(f7489,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(k1_tops_1(sK0,sK1),X0),sK1)
    | ~ spl2_201 ),
    inference(resolution,[],[f7472,f106])).

fof(f7472,plain,
    ( ! [X0] : r1_tarski(k1_tops_1(sK0,sK1),k3_tarski(k2_tarski(X0,sK1)))
    | ~ spl2_201 ),
    inference(superposition,[],[f7466,f77])).

fof(f7466,plain,
    ( ! [X0] : r1_tarski(k1_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,X0)))
    | ~ spl2_201 ),
    inference(resolution,[],[f7160,f170])).

fof(f170,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(superposition,[],[f99,f165])).

fof(f7160,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | r1_tarski(k1_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,X0))) )
    | ~ spl2_201 ),
    inference(superposition,[],[f107,f6831])).

fof(f6831,plain,
    ( k1_xboole_0 = k6_subset_1(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_201 ),
    inference(avatar_component_clause,[],[f6829])).

fof(f7979,plain,
    ( spl2_227
    | ~ spl2_199
    | ~ spl2_201 ),
    inference(avatar_split_clause,[],[f7972,f6829,f6763,f7976])).

fof(f7972,plain,
    ( k1_xboole_0 = k6_subset_1(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl2_199
    | ~ spl2_201 ),
    inference(resolution,[],[f7960,f168])).

fof(f7709,plain,
    ( spl2_226
    | ~ spl2_223 ),
    inference(avatar_split_clause,[],[f7655,f7482,f7706])).

fof(f7655,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))
    | ~ spl2_223 ),
    inference(resolution,[],[f515,f7484])).

fof(f7704,plain,
    ( spl2_225
    | ~ spl2_198 ),
    inference(avatar_split_clause,[],[f7654,f6757,f7701])).

fof(f7654,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl2_198 ),
    inference(resolution,[],[f515,f6759])).

fof(f7689,plain,
    ( spl2_224
    | ~ spl2_216 ),
    inference(avatar_split_clause,[],[f7512,f7133,f7686])).

fof(f7686,plain,
    ( spl2_224
  <=> k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1) = k3_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k3_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_224])])).

fof(f7512,plain,
    ( k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1) = k3_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k3_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1)))
    | ~ spl2_216 ),
    inference(resolution,[],[f515,f7135])).

fof(f7486,plain,
    ( spl2_223
    | ~ spl2_175
    | ~ spl2_201 ),
    inference(avatar_split_clause,[],[f7477,f6829,f6337,f7482])).

fof(f7477,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl2_175
    | ~ spl2_201 ),
    inference(superposition,[],[f7466,f6339])).

fof(f7485,plain,
    ( spl2_223
    | ~ spl2_199
    | ~ spl2_201 ),
    inference(avatar_split_clause,[],[f7476,f6829,f6763,f7482])).

fof(f7476,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl2_199
    | ~ spl2_201 ),
    inference(superposition,[],[f7466,f6765])).

fof(f7347,plain,
    ( spl2_222
    | ~ spl2_221 ),
    inference(avatar_split_clause,[],[f7342,f7309,f7344])).

fof(f7309,plain,
    ( spl2_221
  <=> k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_221])])).

fof(f7342,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl2_221 ),
    inference(forward_demodulation,[],[f7341,f98])).

fof(f7341,plain,
    ( k6_subset_1(k2_tops_1(sK0,sK1),k1_xboole_0) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl2_221 ),
    inference(forward_demodulation,[],[f7331,f77])).

fof(f7331,plain,
    ( k6_subset_1(k2_tops_1(sK0,sK1),k1_xboole_0) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)))
    | ~ spl2_221 ),
    inference(superposition,[],[f100,f7311])).

fof(f7311,plain,
    ( k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl2_221 ),
    inference(avatar_component_clause,[],[f7309])).

fof(f7314,plain,
    ( spl2_221
    | ~ spl2_48
    | ~ spl2_175 ),
    inference(avatar_split_clause,[],[f7307,f6337,f2833,f7309])).

fof(f7307,plain,
    ( k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl2_48
    | ~ spl2_175 ),
    inference(resolution,[],[f7295,f104])).

fof(f7295,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)),X0)
    | ~ spl2_48
    | ~ spl2_175 ),
    inference(resolution,[],[f7284,f106])).

fof(f7284,plain,
    ( ! [X0] : r1_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),X0)))
    | ~ spl2_48
    | ~ spl2_175 ),
    inference(superposition,[],[f6769,f77])).

fof(f6769,plain,
    ( ! [X0] : r1_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(X0,k2_pre_topc(sK0,sK1))))
    | ~ spl2_48
    | ~ spl2_175 ),
    inference(resolution,[],[f6749,f107])).

fof(f6749,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),X0),k2_pre_topc(sK0,sK1))
    | ~ spl2_48
    | ~ spl2_175 ),
    inference(superposition,[],[f5528,f6339])).

fof(f5528,plain,
    ( ! [X0,X1] : r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),X1),k3_tarski(k2_tarski(sK1,X0)))
    | ~ spl2_48 ),
    inference(superposition,[],[f5483,f77])).

fof(f5483,plain,
    ( ! [X6,X5] : r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),X5),k3_tarski(k2_tarski(X6,sK1)))
    | ~ spl2_48 ),
    inference(resolution,[],[f5163,f1309])).

fof(f5163,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(sK1,X3)
        | r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),X4),X3) )
    | ~ spl2_48 ),
    inference(resolution,[],[f5147,f95])).

fof(f5147,plain,
    ( ! [X152] : r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),X152),sK1)
    | ~ spl2_48 ),
    inference(resolution,[],[f1309,f3105])).

fof(f3105,plain,
    ( ! [X6,X5] :
        ( ~ r1_tarski(sK1,k3_tarski(k2_tarski(X5,X6)))
        | r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),X5),X6) )
    | ~ spl2_48 ),
    inference(resolution,[],[f3094,f106])).

fof(f7312,plain,
    ( spl2_221
    | ~ spl2_48
    | ~ spl2_175 ),
    inference(avatar_split_clause,[],[f7305,f6337,f2833,f7309])).

fof(f7305,plain,
    ( k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl2_48
    | ~ spl2_175 ),
    inference(resolution,[],[f7295,f168])).

fof(f7156,plain,
    ( spl2_220
    | ~ spl2_151
    | ~ spl2_202 ),
    inference(avatar_split_clause,[],[f7064,f6843,f5965,f7153])).

fof(f7153,plain,
    ( spl2_220
  <=> k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_220])])).

fof(f5965,plain,
    ( spl2_151
  <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_151])])).

fof(f7064,plain,
    ( k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_151
    | ~ spl2_202 ),
    inference(backward_demodulation,[],[f5967,f6845])).

fof(f5967,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_151 ),
    inference(avatar_component_clause,[],[f5965])).

fof(f7151,plain,
    ( spl2_219
    | ~ spl2_137
    | ~ spl2_202 ),
    inference(avatar_split_clause,[],[f7059,f6843,f5446,f7148])).

fof(f7148,plain,
    ( spl2_219
  <=> k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_219])])).

fof(f5446,plain,
    ( spl2_137
  <=> k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_137])])).

fof(f7059,plain,
    ( k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_137
    | ~ spl2_202 ),
    inference(backward_demodulation,[],[f5448,f6845])).

fof(f5448,plain,
    ( k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_137 ),
    inference(avatar_component_clause,[],[f5446])).

fof(f7146,plain,
    ( spl2_218
    | ~ spl2_132
    | ~ spl2_202 ),
    inference(avatar_split_clause,[],[f7058,f6843,f5385,f7143])).

fof(f7143,plain,
    ( spl2_218
  <=> k1_xboole_0 = k6_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_218])])).

fof(f5385,plain,
    ( spl2_132
  <=> k1_xboole_0 = k6_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_132])])).

fof(f7058,plain,
    ( k1_xboole_0 = k6_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl2_132
    | ~ spl2_202 ),
    inference(backward_demodulation,[],[f5387,f6845])).

fof(f5387,plain,
    ( k1_xboole_0 = k6_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl2_132 ),
    inference(avatar_component_clause,[],[f5385])).

fof(f7141,plain,
    ( spl2_217
    | ~ spl2_104
    | ~ spl2_202 ),
    inference(avatar_split_clause,[],[f7029,f6843,f4675,f7138])).

fof(f4675,plain,
    ( spl2_104
  <=> u1_struct_0(sK0) = k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_104])])).

fof(f7029,plain,
    ( u1_struct_0(sK0) = k3_tarski(k2_tarski(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)))
    | ~ spl2_104
    | ~ spl2_202 ),
    inference(backward_demodulation,[],[f4677,f6845])).

fof(f4677,plain,
    ( u1_struct_0(sK0) = k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_104 ),
    inference(avatar_component_clause,[],[f4675])).

fof(f7136,plain,
    ( spl2_216
    | ~ spl2_95
    | ~ spl2_202 ),
    inference(avatar_split_clause,[],[f7022,f6843,f4549,f7133])).

fof(f4549,plain,
    ( spl2_95
  <=> r1_tarski(k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_95])])).

fof(f7022,plain,
    ( r1_tarski(k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1),k5_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_95
    | ~ spl2_202 ),
    inference(backward_demodulation,[],[f4551,f6845])).

fof(f4551,plain,
    ( r1_tarski(k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_95 ),
    inference(avatar_component_clause,[],[f4549])).

fof(f7131,plain,
    ( spl2_215
    | ~ spl2_83
    | ~ spl2_202 ),
    inference(avatar_split_clause,[],[f7019,f6843,f4446,f7128])).

fof(f7128,plain,
    ( spl2_215
  <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_215])])).

fof(f4446,plain,
    ( spl2_83
  <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_83])])).

fof(f7019,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_83
    | ~ spl2_202 ),
    inference(backward_demodulation,[],[f4448,f6845])).

fof(f4448,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_83 ),
    inference(avatar_component_clause,[],[f4446])).

fof(f7126,plain,
    ( spl2_214
    | ~ spl2_80
    | ~ spl2_202 ),
    inference(avatar_split_clause,[],[f7012,f6843,f4347,f7123])).

fof(f7123,plain,
    ( spl2_214
  <=> k6_subset_1(k2_tops_1(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k6_subset_1(k2_tops_1(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_214])])).

fof(f4347,plain,
    ( spl2_80
  <=> k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).

fof(f7012,plain,
    ( k6_subset_1(k2_tops_1(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k6_subset_1(k2_tops_1(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),sK1))))
    | ~ spl2_80
    | ~ spl2_202 ),
    inference(backward_demodulation,[],[f4349,f6845])).

fof(f4349,plain,
    ( k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_80 ),
    inference(avatar_component_clause,[],[f4347])).

fof(f7121,plain,
    ( spl2_213
    | ~ spl2_79
    | ~ spl2_202 ),
    inference(avatar_split_clause,[],[f7011,f6843,f4328,f7118])).

fof(f7118,plain,
    ( spl2_213
  <=> k1_xboole_0 = k6_subset_1(k6_subset_1(k2_tops_1(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_213])])).

fof(f4328,plain,
    ( spl2_79
  <=> k1_xboole_0 = k6_subset_1(k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_79])])).

fof(f7011,plain,
    ( k1_xboole_0 = k6_subset_1(k6_subset_1(k2_tops_1(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl2_79
    | ~ spl2_202 ),
    inference(backward_demodulation,[],[f4330,f6845])).

fof(f4330,plain,
    ( k1_xboole_0 = k6_subset_1(k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl2_79 ),
    inference(avatar_component_clause,[],[f4328])).

fof(f7116,plain,
    ( spl2_212
    | ~ spl2_29
    | ~ spl2_202 ),
    inference(avatar_split_clause,[],[f6922,f6843,f2105,f7113])).

fof(f7113,plain,
    ( spl2_212
  <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_212])])).

fof(f2105,plain,
    ( spl2_29
  <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f6922,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_29
    | ~ spl2_202 ),
    inference(backward_demodulation,[],[f2107,f6845])).

fof(f2107,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f2105])).

fof(f7111,plain,
    ( spl2_211
    | ~ spl2_28
    | ~ spl2_202 ),
    inference(avatar_split_clause,[],[f6921,f6843,f2098,f7108])).

fof(f7108,plain,
    ( spl2_211
  <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_211])])).

fof(f2098,plain,
    ( spl2_28
  <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f6921,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1),sK1)
    | ~ spl2_28
    | ~ spl2_202 ),
    inference(backward_demodulation,[],[f2100,f6845])).

fof(f2100,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1)
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f2098])).

fof(f7106,plain,
    ( spl2_210
    | ~ spl2_20
    | ~ spl2_202 ),
    inference(avatar_split_clause,[],[f6861,f6843,f994,f7103])).

fof(f7103,plain,
    ( spl2_210
  <=> sK1 = k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_210])])).

fof(f994,plain,
    ( spl2_20
  <=> sK1 = k5_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f6861,plain,
    ( sK1 = k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_20
    | ~ spl2_202 ),
    inference(backward_demodulation,[],[f996,f6845])).

fof(f996,plain,
    ( sK1 = k5_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f994])).

fof(f7101,plain,
    ( ~ spl2_209
    | spl2_19
    | ~ spl2_202 ),
    inference(avatar_split_clause,[],[f6855,f6843,f965,f7098])).

fof(f7098,plain,
    ( spl2_209
  <=> r1_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_209])])).

fof(f965,plain,
    ( spl2_19
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f6855,plain,
    ( ~ r1_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),sK1)
    | spl2_19
    | ~ spl2_202 ),
    inference(backward_demodulation,[],[f967,f6845])).

fof(f967,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),sK1)
    | spl2_19 ),
    inference(avatar_component_clause,[],[f965])).

fof(f7096,plain,
    ( spl2_208
    | ~ spl2_17
    | ~ spl2_202 ),
    inference(avatar_split_clause,[],[f6854,f6843,f956,f7093])).

fof(f7093,plain,
    ( spl2_208
  <=> k5_xboole_0(u1_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_208])])).

fof(f956,plain,
    ( spl2_17
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f6854,plain,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))
    | ~ spl2_17
    | ~ spl2_202 ),
    inference(backward_demodulation,[],[f958,f6845])).

fof(f958,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f956])).

fof(f7091,plain,
    ( spl2_207
    | ~ spl2_15
    | ~ spl2_202 ),
    inference(avatar_split_clause,[],[f6853,f6843,f913,f7088])).

fof(f7088,plain,
    ( spl2_207
  <=> sK1 = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_207])])).

fof(f6853,plain,
    ( sK1 = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_15
    | ~ spl2_202 ),
    inference(backward_demodulation,[],[f915,f6845])).

fof(f7086,plain,
    ( spl2_206
    | ~ spl2_13
    | ~ spl2_202 ),
    inference(avatar_split_clause,[],[f6851,f6843,f895,f7083])).

fof(f7083,plain,
    ( spl2_206
  <=> r1_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_206])])).

fof(f895,plain,
    ( spl2_13
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f6851,plain,
    ( r1_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl2_13
    | ~ spl2_202 ),
    inference(backward_demodulation,[],[f897,f6845])).

fof(f897,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f895])).

fof(f7081,plain,
    ( spl2_205
    | ~ spl2_12
    | ~ spl2_202 ),
    inference(avatar_split_clause,[],[f6850,f6843,f890,f7078])).

fof(f7078,plain,
    ( spl2_205
  <=> m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_205])])).

fof(f890,plain,
    ( spl2_12
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f6850,plain,
    ( m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_12
    | ~ spl2_202 ),
    inference(backward_demodulation,[],[f892,f6845])).

fof(f892,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f890])).

fof(f7076,plain,
    ( ~ spl2_204
    | spl2_11
    | ~ spl2_202 ),
    inference(avatar_split_clause,[],[f6849,f6843,f885,f7073])).

fof(f7073,plain,
    ( spl2_204
  <=> r1_tarski(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_204])])).

fof(f885,plain,
    ( spl2_11
  <=> r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f6849,plain,
    ( ~ r1_tarski(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))
    | spl2_11
    | ~ spl2_202 ),
    inference(backward_demodulation,[],[f887,f6845])).

fof(f887,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f885])).

fof(f7071,plain,
    ( spl2_203
    | ~ spl2_7
    | ~ spl2_202 ),
    inference(avatar_split_clause,[],[f6847,f6843,f523,f7068])).

fof(f7068,plain,
    ( spl2_203
  <=> sK1 = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_203])])).

fof(f523,plain,
    ( spl2_7
  <=> sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f6847,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_7
    | ~ spl2_202 ),
    inference(backward_demodulation,[],[f525,f6845])).

fof(f525,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f523])).

fof(f6846,plain,
    ( spl2_202
    | ~ spl2_8
    | ~ spl2_200 ),
    inference(avatar_split_clause,[],[f6841,f6822,f865,f6843])).

fof(f865,plain,
    ( spl2_8
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k6_subset_1(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f6841,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl2_8
    | ~ spl2_200 ),
    inference(backward_demodulation,[],[f867,f6824])).

fof(f867,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k6_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f865])).

fof(f6832,plain,
    ( spl2_201
    | ~ spl2_173 ),
    inference(avatar_split_clause,[],[f6827,f6324,f6829])).

fof(f6324,plain,
    ( spl2_173
  <=> k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_173])])).

fof(f6827,plain,
    ( k1_xboole_0 = k6_subset_1(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_173 ),
    inference(forward_demodulation,[],[f6806,f287])).

fof(f287,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f284,f165])).

fof(f284,plain,(
    ! [X1] : k6_subset_1(X1,X1) = k5_xboole_0(X1,X1) ),
    inference(superposition,[],[f102,f171])).

fof(f171,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f166,f98])).

fof(f166,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = k1_setfam_1(k2_tarski(X0,X0)) ),
    inference(superposition,[],[f100,f165])).

fof(f6806,plain,
    ( k6_subset_1(k1_tops_1(sK0,sK1),sK1) = k5_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_173 ),
    inference(superposition,[],[f281,f6326])).

fof(f6326,plain,
    ( k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl2_173 ),
    inference(avatar_component_clause,[],[f6324])).

fof(f281,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) ),
    inference(superposition,[],[f102,f77])).

fof(f6825,plain,
    ( spl2_200
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f6804,f907,f6822])).

fof(f907,plain,
    ( spl2_14
  <=> sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f6804,plain,
    ( k6_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl2_14 ),
    inference(superposition,[],[f281,f909])).

fof(f909,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f907])).

fof(f6766,plain,
    ( spl2_199
    | ~ spl2_175 ),
    inference(avatar_split_clause,[],[f6754,f6337,f6763])).

fof(f6754,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))
    | ~ spl2_175 ),
    inference(superposition,[],[f101,f6339])).

fof(f6761,plain,
    ( spl2_198
    | ~ spl2_175 ),
    inference(avatar_split_clause,[],[f6751,f6337,f6757])).

fof(f6751,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl2_175 ),
    inference(superposition,[],[f1309,f6339])).

fof(f6760,plain,
    ( spl2_198
    | ~ spl2_48
    | ~ spl2_175 ),
    inference(avatar_split_clause,[],[f6750,f6337,f2833,f6757])).

fof(f6750,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl2_48
    | ~ spl2_175 ),
    inference(superposition,[],[f5168,f6339])).

fof(f5168,plain,
    ( ! [X0] : r1_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,X0)))
    | ~ spl2_48 ),
    inference(resolution,[],[f5146,f107])).

fof(f5146,plain,
    ( ! [X151] : r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),sK1),X151)
    | ~ spl2_48 ),
    inference(resolution,[],[f1309,f3573])).

fof(f3573,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK1,k3_tarski(k2_tarski(X1,X0)))
        | r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),X0),X1) )
    | ~ spl2_48 ),
    inference(superposition,[],[f3105,f77])).

fof(f6744,plain,
    ( spl2_197
    | ~ spl2_189 ),
    inference(avatar_split_clause,[],[f6708,f6690,f6741])).

fof(f6708,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_189 ),
    inference(resolution,[],[f6692,f86])).

fof(f6739,plain,
    ( spl2_196
    | ~ spl2_189 ),
    inference(avatar_split_clause,[],[f6707,f6690,f6736])).

fof(f6707,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k6_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl2_189 ),
    inference(resolution,[],[f6692,f103])).

fof(f6734,plain,
    ( spl2_195
    | ~ spl2_189 ),
    inference(avatar_split_clause,[],[f6705,f6690,f6731])).

fof(f6705,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_189 ),
    inference(resolution,[],[f6692,f134])).

fof(f6729,plain,
    ( spl2_194
    | ~ spl2_4
    | ~ spl2_189 ),
    inference(avatar_split_clause,[],[f6703,f6690,f125,f6726])).

fof(f125,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f6703,plain,
    ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_4
    | ~ spl2_189 ),
    inference(resolution,[],[f6692,f3224])).

fof(f3224,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) )
    | ~ spl2_4 ),
    inference(resolution,[],[f69,f127])).

fof(f127,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f125])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(f6724,plain,
    ( spl2_193
    | ~ spl2_3
    | ~ spl2_189 ),
    inference(avatar_split_clause,[],[f6702,f6690,f120,f6721])).

fof(f6721,plain,
    ( spl2_193
  <=> k4_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_193])])).

fof(f120,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f6702,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl2_3
    | ~ spl2_189 ),
    inference(resolution,[],[f6692,f3703])).

fof(f3703,plain,
    ( ! [X27] :
        ( ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X27) = k3_tarski(k2_tarski(sK1,X27)) )
    | ~ spl2_3 ),
    inference(resolution,[],[f108,f122])).

fof(f122,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f96,f80])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f6719,plain,
    ( spl2_192
    | ~ spl2_4
    | ~ spl2_189 ),
    inference(avatar_split_clause,[],[f6701,f6690,f125,f6716])).

fof(f6716,plain,
    ( spl2_192
  <=> k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_192])])).

fof(f6701,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl2_4
    | ~ spl2_189 ),
    inference(resolution,[],[f6692,f3862])).

fof(f3862,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl2_4 ),
    inference(resolution,[],[f70,f127])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f6714,plain,
    ( spl2_191
    | ~ spl2_4
    | ~ spl2_189 ),
    inference(avatar_split_clause,[],[f6700,f6690,f125,f6711])).

fof(f6711,plain,
    ( spl2_191
  <=> k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_191])])).

fof(f6700,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))
    | ~ spl2_4
    | ~ spl2_189 ),
    inference(resolution,[],[f6692,f4111])).

fof(f4111,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl2_4 ),
    inference(resolution,[],[f71,f127])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f6699,plain,
    ( spl2_190
    | ~ spl2_22
    | ~ spl2_173 ),
    inference(avatar_split_clause,[],[f6694,f6324,f1773,f6696])).

fof(f6696,plain,
    ( spl2_190
  <=> k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_190])])).

fof(f6694,plain,
    ( k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_22
    | ~ spl2_173 ),
    inference(forward_demodulation,[],[f6684,f1774])).

fof(f6684,plain,
    ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_173 ),
    inference(superposition,[],[f102,f6326])).

fof(f6693,plain,
    ( spl2_189
    | ~ spl2_16
    | ~ spl2_173 ),
    inference(avatar_split_clause,[],[f6679,f6324,f939,f6690])).

fof(f939,plain,
    ( spl2_16
  <=> k1_xboole_0 = k6_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f6679,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_16
    | ~ spl2_173 ),
    inference(superposition,[],[f2292,f6326])).

fof(f2292,plain,
    ( ! [X60] : m1_subset_1(k1_setfam_1(k2_tarski(sK1,X60)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_16 ),
    inference(superposition,[],[f163,f1409])).

fof(f1409,plain,
    ( ! [X2] : k1_setfam_1(k2_tarski(sK1,X2)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,X2))))
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f1408,f77])).

fof(f1408,plain,
    ( ! [X2] : k1_setfam_1(k2_tarski(sK1,X2)) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(sK1,X2)),u1_struct_0(sK0)))
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f1402,f98])).

fof(f1402,plain,
    ( ! [X2] : k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(sK1,X2)),u1_struct_0(sK0))) = k6_subset_1(k1_setfam_1(k2_tarski(sK1,X2)),k1_xboole_0)
    | ~ spl2_16 ),
    inference(superposition,[],[f100,f1379])).

fof(f1379,plain,
    ( ! [X10] : k1_xboole_0 = k6_subset_1(k1_setfam_1(k2_tarski(sK1,X10)),u1_struct_0(sK0))
    | ~ spl2_16 ),
    inference(resolution,[],[f1365,f168])).

fof(f1365,plain,
    ( ! [X0,X1] : r1_tarski(k6_subset_1(k1_setfam_1(k2_tarski(sK1,X0)),u1_struct_0(sK0)),X1)
    | ~ spl2_16 ),
    inference(resolution,[],[f1323,f106])).

fof(f1323,plain,
    ( ! [X2,X1] : r1_tarski(k1_setfam_1(k2_tarski(sK1,X1)),k3_tarski(k2_tarski(u1_struct_0(sK0),X2)))
    | ~ spl2_16 ),
    inference(resolution,[],[f1320,f161])).

fof(f1320,plain,
    ( ! [X0] : r1_tarski(sK1,k3_tarski(k2_tarski(u1_struct_0(sK0),X0)))
    | ~ spl2_16 ),
    inference(resolution,[],[f1318,f170])).

fof(f1318,plain,
    ( ! [X11] :
        ( ~ r1_tarski(k1_xboole_0,X11)
        | r1_tarski(sK1,k3_tarski(k2_tarski(u1_struct_0(sK0),X11))) )
    | ~ spl2_16 ),
    inference(superposition,[],[f107,f941])).

fof(f941,plain,
    ( k1_xboole_0 = k6_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f939])).

fof(f6553,plain,
    ( spl2_188
    | ~ spl2_168 ),
    inference(avatar_split_clause,[],[f6548,f6295,f6550])).

fof(f6295,plain,
    ( spl2_168
  <=> k1_xboole_0 = k6_subset_1(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_168])])).

fof(f6548,plain,
    ( k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_168 ),
    inference(forward_demodulation,[],[f6547,f98])).

fof(f6547,plain,
    ( k6_subset_1(k1_tops_1(sK0,sK1),k1_xboole_0) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_168 ),
    inference(forward_demodulation,[],[f6542,f77])).

fof(f6542,plain,
    ( k6_subset_1(k1_tops_1(sK0,sK1),k1_xboole_0) = k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)))
    | ~ spl2_168 ),
    inference(superposition,[],[f100,f6297])).

fof(f6297,plain,
    ( k1_xboole_0 = k6_subset_1(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_168 ),
    inference(avatar_component_clause,[],[f6295])).

fof(f6496,plain,
    ( spl2_187
    | ~ spl2_45
    | ~ spl2_176 ),
    inference(avatar_split_clause,[],[f6415,f6351,f2819,f6493])).

fof(f6493,plain,
    ( spl2_187
  <=> sK1 = k4_subset_1(sK1,k1_xboole_0,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_187])])).

fof(f2819,plain,
    ( spl2_45
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f6351,plain,
    ( spl2_176
  <=> sK1 = k4_subset_1(sK1,k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_176])])).

fof(f6415,plain,
    ( sK1 = k4_subset_1(sK1,k1_xboole_0,k2_tops_1(sK0,sK1))
    | ~ spl2_45
    | ~ spl2_176 ),
    inference(backward_demodulation,[],[f6353,f2821])).

fof(f2821,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f2819])).

fof(f6353,plain,
    ( sK1 = k4_subset_1(sK1,k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_176 ),
    inference(avatar_component_clause,[],[f6351])).

fof(f6489,plain,
    ( ~ spl2_186
    | ~ spl2_45
    | spl2_170 ),
    inference(avatar_split_clause,[],[f6408,f6307,f2819,f6486])).

fof(f6307,plain,
    ( spl2_170
  <=> r1_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_170])])).

fof(f6408,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k1_xboole_0)
    | ~ spl2_45
    | spl2_170 ),
    inference(backward_demodulation,[],[f6309,f2821])).

fof(f6309,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | spl2_170 ),
    inference(avatar_component_clause,[],[f6307])).

fof(f6460,plain,
    ( spl2_185
    | ~ spl2_45
    | ~ spl2_164 ),
    inference(avatar_split_clause,[],[f6386,f6250,f2819,f6457])).

fof(f6457,plain,
    ( spl2_185
  <=> k1_xboole_0 = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_185])])).

fof(f6250,plain,
    ( spl2_164
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_164])])).

fof(f6386,plain,
    ( k1_xboole_0 = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_45
    | ~ spl2_164 ),
    inference(backward_demodulation,[],[f6252,f2821])).

fof(f6252,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_164 ),
    inference(avatar_component_clause,[],[f6250])).

fof(f6455,plain,
    ( spl2_184
    | ~ spl2_45
    | ~ spl2_163 ),
    inference(avatar_split_clause,[],[f6385,f6245,f2819,f6452])).

fof(f6452,plain,
    ( spl2_184
  <=> sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_184])])).

fof(f6245,plain,
    ( spl2_163
  <=> sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_163])])).

fof(f6385,plain,
    ( sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k1_xboole_0)
    | ~ spl2_45
    | ~ spl2_163 ),
    inference(backward_demodulation,[],[f6247,f2821])).

fof(f6247,plain,
    ( sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_163 ),
    inference(avatar_component_clause,[],[f6245])).

fof(f6450,plain,
    ( spl2_179
    | ~ spl2_45
    | ~ spl2_162 ),
    inference(avatar_split_clause,[],[f6449,f6240,f2819,f6423])).

fof(f6423,plain,
    ( spl2_179
  <=> sK1 = k2_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_179])])).

fof(f6240,plain,
    ( spl2_162
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_162])])).

fof(f6449,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | ~ spl2_45
    | ~ spl2_162 ),
    inference(forward_demodulation,[],[f6384,f856])).

fof(f6384,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_xboole_0)
    | ~ spl2_45
    | ~ spl2_162 ),
    inference(backward_demodulation,[],[f6242,f2821])).

fof(f6242,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_162 ),
    inference(avatar_component_clause,[],[f6240])).

fof(f6448,plain,
    ( spl2_183
    | ~ spl2_45
    | ~ spl2_161 ),
    inference(avatar_split_clause,[],[f6383,f6232,f2819,f6445])).

fof(f6445,plain,
    ( spl2_183
  <=> k1_xboole_0 = k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_183])])).

fof(f6232,plain,
    ( spl2_161
  <=> k1_tops_1(sK0,sK1) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_161])])).

fof(f6383,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_45
    | ~ spl2_161 ),
    inference(backward_demodulation,[],[f6234,f2821])).

fof(f6234,plain,
    ( k1_tops_1(sK0,sK1) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_161 ),
    inference(avatar_component_clause,[],[f6232])).

fof(f6443,plain,
    ( spl2_182
    | ~ spl2_45
    | ~ spl2_160 ),
    inference(avatar_split_clause,[],[f6382,f6225,f2819,f6440])).

fof(f6440,plain,
    ( spl2_182
  <=> k1_xboole_0 = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_182])])).

fof(f6382,plain,
    ( k1_xboole_0 = k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_45
    | ~ spl2_160 ),
    inference(backward_demodulation,[],[f6227,f2821])).

fof(f6438,plain,
    ( spl2_181
    | ~ spl2_45
    | ~ spl2_140 ),
    inference(avatar_split_clause,[],[f6381,f5462,f2819,f6435])).

fof(f6435,plain,
    ( spl2_181
  <=> k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_181])])).

fof(f5462,plain,
    ( spl2_140
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_140])])).

fof(f6381,plain,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_45
    | ~ spl2_140 ),
    inference(backward_demodulation,[],[f5464,f2821])).

fof(f5464,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_140 ),
    inference(avatar_component_clause,[],[f5462])).

fof(f6433,plain,
    ( ~ spl2_180
    | ~ spl2_45
    | spl2_46 ),
    inference(avatar_split_clause,[],[f6380,f2823,f2819,f6430])).

fof(f6430,plain,
    ( spl2_180
  <=> r1_tarski(k1_xboole_0,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_180])])).

fof(f2823,plain,
    ( spl2_46
  <=> r1_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f6380,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_tops_1(sK0,sK1))
    | ~ spl2_45
    | spl2_46 ),
    inference(backward_demodulation,[],[f2825,f2821])).

fof(f2825,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | spl2_46 ),
    inference(avatar_component_clause,[],[f2823])).

fof(f6428,plain,
    ( spl2_179
    | ~ spl2_22
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f6427,f2819,f1773,f6423])).

fof(f6427,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | ~ spl2_22
    | ~ spl2_45 ),
    inference(forward_demodulation,[],[f6379,f98])).

fof(f6379,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_xboole_0)
    | ~ spl2_22
    | ~ spl2_45 ),
    inference(backward_demodulation,[],[f1774,f2821])).

fof(f6426,plain,
    ( spl2_179
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f6421,f2819,f120,f114,f6423])).

fof(f114,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f6421,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_45 ),
    inference(forward_demodulation,[],[f6420,f98])).

fof(f6420,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_xboole_0)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_45 ),
    inference(forward_demodulation,[],[f6378,f1769])).

fof(f1769,plain,
    ( ! [X20] : k7_subset_1(u1_struct_0(sK0),sK1,X20) = k6_subset_1(sK1,X20)
    | ~ spl2_3 ),
    inference(resolution,[],[f105,f122])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2) ) ),
    inference(definition_unfolding,[],[f92,f78])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f6378,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | ~ spl2_2
    | ~ spl2_45 ),
    inference(backward_demodulation,[],[f115,f2821])).

fof(f115,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f6377,plain,
    ( spl2_45
    | spl2_178
    | ~ spl2_160 ),
    inference(avatar_split_clause,[],[f6368,f6225,f6375,f2819])).

fof(f6375,plain,
    ( spl2_178
  <=> ! [X7] : ~ r1_tarski(sK1,k6_subset_1(X7,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_178])])).

fof(f6368,plain,
    ( ! [X7] :
        ( ~ r1_tarski(sK1,k6_subset_1(X7,k1_tops_1(sK0,sK1)))
        | k1_xboole_0 = k1_tops_1(sK0,sK1) )
    | ~ spl2_160 ),
    inference(resolution,[],[f6275,f104])).

fof(f6275,plain,
    ( ! [X19] :
        ( r1_tarski(k1_tops_1(sK0,sK1),X19)
        | ~ r1_tarski(sK1,X19) )
    | ~ spl2_160 ),
    inference(superposition,[],[f151,f6227])).

fof(f6373,plain,
    ( ~ spl2_177
    | spl2_46
    | ~ spl2_160 ),
    inference(avatar_split_clause,[],[f6362,f6225,f2823,f6370])).

fof(f6370,plain,
    ( spl2_177
  <=> r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_177])])).

fof(f6362,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | spl2_46
    | ~ spl2_160 ),
    inference(resolution,[],[f6275,f2825])).

fof(f6354,plain,
    ( spl2_176
    | ~ spl2_162
    | ~ spl2_171 ),
    inference(avatar_split_clause,[],[f6349,f6312,f6240,f6351])).

fof(f6312,plain,
    ( spl2_171
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_171])])).

fof(f6349,plain,
    ( sK1 = k4_subset_1(sK1,k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_162
    | ~ spl2_171 ),
    inference(forward_demodulation,[],[f6344,f6242])).

fof(f6344,plain,
    ( sK1 = k4_subset_1(sK1,k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl2_171 ),
    inference(resolution,[],[f6314,f134])).

fof(f6314,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_171 ),
    inference(avatar_component_clause,[],[f6312])).

fof(f6340,plain,
    ( spl2_175
    | ~ spl2_105
    | ~ spl2_174 ),
    inference(avatar_split_clause,[],[f6335,f6331,f4680,f6337])).

fof(f4680,plain,
    ( spl2_105
  <=> k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_105])])).

fof(f6331,plain,
    ( spl2_174
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_174])])).

fof(f6335,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_105
    | ~ spl2_174 ),
    inference(backward_demodulation,[],[f4682,f6333])).

fof(f6333,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_174 ),
    inference(avatar_component_clause,[],[f6331])).

fof(f4682,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_105 ),
    inference(avatar_component_clause,[],[f4680])).

fof(f6334,plain,
    ( spl2_174
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f5939,f125,f120,f6331])).

fof(f5939,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f4111,f122])).

fof(f6329,plain,
    ( spl2_38
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_154 ),
    inference(avatar_split_clause,[],[f6328,f5982,f125,f120,f2756])).

fof(f2756,plain,
    ( spl2_38
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f5982,plain,
    ( spl2_154
  <=> sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_154])])).

fof(f6328,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_154 ),
    inference(forward_demodulation,[],[f5939,f5984])).

fof(f5984,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_154 ),
    inference(avatar_component_clause,[],[f5982])).

fof(f6327,plain,
    ( spl2_173
    | ~ spl2_44
    | ~ spl2_160 ),
    inference(avatar_split_clause,[],[f6322,f6225,f2814,f6324])).

fof(f2814,plain,
    ( spl2_44
  <=> k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f6322,plain,
    ( k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl2_44
    | ~ spl2_160 ),
    inference(forward_demodulation,[],[f2816,f6227])).

fof(f2816,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f2814])).

fof(f6321,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_38
    | ~ spl2_62 ),
    inference(avatar_split_clause,[],[f3566,f3475,f2756,f120,f110])).

fof(f110,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f3475,plain,
    ( spl2_62
  <=> ! [X0] :
        ( k2_pre_topc(sK0,X0) != X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_62])])).

fof(f3566,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK1,sK0)
    | ~ spl2_38
    | ~ spl2_62 ),
    inference(trivial_inequality_removal,[],[f3565])).

fof(f3565,plain,
    ( sK1 != sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK1,sK0)
    | ~ spl2_38
    | ~ spl2_62 ),
    inference(superposition,[],[f3476,f2758])).

fof(f2758,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f2756])).

fof(f3476,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) != X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl2_62 ),
    inference(avatar_component_clause,[],[f3475])).

fof(f6320,plain,
    ( spl2_172
    | ~ spl2_160 ),
    inference(avatar_split_clause,[],[f6278,f6225,f6317])).

fof(f6317,plain,
    ( spl2_172
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_172])])).

fof(f6278,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_160 ),
    inference(superposition,[],[f99,f6227])).

fof(f6315,plain,
    ( spl2_171
    | ~ spl2_160 ),
    inference(avatar_split_clause,[],[f6277,f6225,f6312])).

fof(f6277,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_160 ),
    inference(superposition,[],[f76,f6227])).

fof(f6310,plain,
    ( spl2_51
    | ~ spl2_170
    | ~ spl2_160 ),
    inference(avatar_split_clause,[],[f6276,f6225,f6307,f3116])).

fof(f3116,plain,
    ( spl2_51
  <=> k1_xboole_0 = k2_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f6276,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | k1_xboole_0 = k2_tops_1(sK0,sK1)
    | ~ spl2_160 ),
    inference(superposition,[],[f104,f6227])).

fof(f6305,plain,
    ( spl2_22
    | ~ spl2_130
    | ~ spl2_160 ),
    inference(avatar_split_clause,[],[f6304,f6225,f5222,f1773])).

fof(f5222,plain,
    ( spl2_130
  <=> k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_130])])).

fof(f6304,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_130
    | ~ spl2_160 ),
    inference(forward_demodulation,[],[f6274,f5224])).

fof(f5224,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_130 ),
    inference(avatar_component_clause,[],[f5222])).

fof(f6274,plain,
    ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_160 ),
    inference(superposition,[],[f100,f6227])).

fof(f6303,plain,
    ( ~ spl2_169
    | ~ spl2_52
    | ~ spl2_160 ),
    inference(avatar_split_clause,[],[f6272,f6225,f3121,f6300])).

fof(f6300,plain,
    ( spl2_169
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_169])])).

fof(f3121,plain,
    ( spl2_52
  <=> ! [X7] : ~ r1_tarski(sK1,k6_subset_1(X7,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f6272,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_52
    | ~ spl2_160 ),
    inference(superposition,[],[f3122,f6227])).

fof(f3122,plain,
    ( ! [X7] : ~ r1_tarski(sK1,k6_subset_1(X7,k2_tops_1(sK0,sK1)))
    | ~ spl2_52 ),
    inference(avatar_component_clause,[],[f3121])).

fof(f6298,plain,
    ( spl2_168
    | ~ spl2_16
    | ~ spl2_160 ),
    inference(avatar_split_clause,[],[f6271,f6225,f939,f6295])).

fof(f6271,plain,
    ( k1_xboole_0 = k6_subset_1(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_16
    | ~ spl2_160 ),
    inference(superposition,[],[f5324,f6227])).

fof(f5324,plain,
    ( ! [X10] : k1_xboole_0 = k6_subset_1(k6_subset_1(sK1,X10),u1_struct_0(sK0))
    | ~ spl2_16 ),
    inference(resolution,[],[f5310,f168])).

fof(f5310,plain,
    ( ! [X2,X3] : r1_tarski(k6_subset_1(k6_subset_1(sK1,X2),u1_struct_0(sK0)),X3)
    | ~ spl2_16 ),
    inference(resolution,[],[f5293,f106])).

fof(f5293,plain,
    ( ! [X0,X1] : r1_tarski(k6_subset_1(sK1,X1),k3_tarski(k2_tarski(u1_struct_0(sK0),X0)))
    | ~ spl2_16 ),
    inference(superposition,[],[f5128,f77])).

fof(f5128,plain,
    ( ! [X114,X115] : r1_tarski(k6_subset_1(sK1,X114),k3_tarski(k2_tarski(X115,u1_struct_0(sK0))))
    | ~ spl2_16 ),
    inference(resolution,[],[f1309,f1335])).

fof(f1335,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(u1_struct_0(sK0),X3)
        | r1_tarski(k6_subset_1(sK1,X4),X3) )
    | ~ spl2_16 ),
    inference(resolution,[],[f1328,f95])).

fof(f1328,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(sK1,X0),u1_struct_0(sK0))
    | ~ spl2_16 ),
    inference(resolution,[],[f1325,f106])).

fof(f1325,plain,
    ( ! [X0] : r1_tarski(sK1,k3_tarski(k2_tarski(X0,u1_struct_0(sK0))))
    | ~ spl2_16 ),
    inference(superposition,[],[f1320,f77])).

fof(f6293,plain,
    ( spl2_167
    | ~ spl2_13
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_160 ),
    inference(avatar_split_clause,[],[f6267,f6225,f1658,f939,f895,f6290])).

fof(f6290,plain,
    ( spl2_167
  <=> r1_tarski(k6_subset_1(k6_subset_1(k1_tops_1(sK0,sK1),sK1),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_167])])).

fof(f1658,plain,
    ( spl2_21
  <=> r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f6267,plain,
    ( r1_tarski(k6_subset_1(k6_subset_1(k1_tops_1(sK0,sK1),sK1),sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_13
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_160 ),
    inference(superposition,[],[f2862,f6227])).

fof(f2862,plain,
    ( ! [X1] : r1_tarski(k6_subset_1(k6_subset_1(k6_subset_1(sK1,X1),sK1),sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_13
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(resolution,[],[f2630,f106])).

fof(f2630,plain,
    ( ! [X1] : r1_tarski(k6_subset_1(k6_subset_1(sK1,X1),sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_13
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(resolution,[],[f2454,f1660])).

fof(f1660,plain,
    ( r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f1658])).

fof(f2454,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(u1_struct_0(sK0),X3)
        | r1_tarski(k6_subset_1(k6_subset_1(sK1,X4),sK1),X3) )
    | ~ spl2_13
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(resolution,[],[f2446,f95])).

fof(f2446,plain,
    ( ! [X2] : r1_tarski(k6_subset_1(k6_subset_1(sK1,X2),sK1),u1_struct_0(sK0))
    | ~ spl2_13
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(resolution,[],[f1706,f897])).

fof(f1706,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),X3)
        | r1_tarski(k6_subset_1(k6_subset_1(sK1,X4),sK1),X3) )
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(resolution,[],[f1697,f95])).

fof(f1697,plain,
    ( ! [X1] : r1_tarski(k6_subset_1(k6_subset_1(sK1,X1),sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(resolution,[],[f1687,f106])).

fof(f1687,plain,
    ( ! [X54] : r1_tarski(k6_subset_1(sK1,X54),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(resolution,[],[f1660,f1335])).

fof(f6288,plain,
    ( spl2_166
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_160 ),
    inference(avatar_split_clause,[],[f6261,f6225,f1658,f939,f6285])).

fof(f6285,plain,
    ( spl2_166
  <=> r1_tarski(k6_subset_1(k1_tops_1(sK0,sK1),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_166])])).

fof(f6261,plain,
    ( r1_tarski(k6_subset_1(k1_tops_1(sK0,sK1),sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_160 ),
    inference(superposition,[],[f1697,f6227])).

fof(f6283,plain,
    ( spl2_165
    | ~ spl2_16
    | ~ spl2_160 ),
    inference(avatar_split_clause,[],[f6254,f6225,f939,f6280])).

fof(f6280,plain,
    ( spl2_165
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_165])])).

fof(f6254,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_16
    | ~ spl2_160 ),
    inference(superposition,[],[f1328,f6227])).

fof(f6253,plain,
    ( spl2_164
    | ~ spl2_143
    | ~ spl2_161 ),
    inference(avatar_split_clause,[],[f6238,f6232,f5642,f6250])).

fof(f5642,plain,
    ( spl2_143
  <=> k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_143])])).

fof(f6238,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_143
    | ~ spl2_161 ),
    inference(backward_demodulation,[],[f5644,f6234])).

fof(f5644,plain,
    ( k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_143 ),
    inference(avatar_component_clause,[],[f5642])).

fof(f6248,plain,
    ( spl2_163
    | ~ spl2_146
    | ~ spl2_161 ),
    inference(avatar_split_clause,[],[f6237,f6232,f5659,f6245])).

fof(f5659,plain,
    ( spl2_146
  <=> sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k5_xboole_0(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_146])])).

fof(f6237,plain,
    ( sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_146
    | ~ spl2_161 ),
    inference(backward_demodulation,[],[f5661,f6234])).

fof(f5661,plain,
    ( sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k5_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_146 ),
    inference(avatar_component_clause,[],[f5659])).

fof(f6243,plain,
    ( spl2_162
    | ~ spl2_145
    | ~ spl2_161 ),
    inference(avatar_split_clause,[],[f6236,f6232,f5653,f6240])).

fof(f5653,plain,
    ( spl2_145
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_145])])).

fof(f6236,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_145
    | ~ spl2_161 ),
    inference(backward_demodulation,[],[f5655,f6234])).

fof(f5655,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_145 ),
    inference(avatar_component_clause,[],[f5653])).

fof(f6235,plain,
    ( spl2_161
    | ~ spl2_141
    | ~ spl2_160 ),
    inference(avatar_split_clause,[],[f6230,f6225,f5624,f6232])).

fof(f5624,plain,
    ( spl2_141
  <=> k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_141])])).

fof(f6230,plain,
    ( k1_tops_1(sK0,sK1) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_141
    | ~ spl2_160 ),
    inference(backward_demodulation,[],[f5626,f6227])).

fof(f5626,plain,
    ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_141 ),
    inference(avatar_component_clause,[],[f5624])).

fof(f6229,plain,
    ( spl2_160
    | ~ spl2_3
    | ~ spl2_140 ),
    inference(avatar_split_clause,[],[f6223,f5462,f120,f6225])).

fof(f6223,plain,
    ( k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_140 ),
    inference(superposition,[],[f1769,f5464])).

fof(f6228,plain,
    ( spl2_160
    | ~ spl2_3
    | ~ spl2_140 ),
    inference(avatar_split_clause,[],[f6222,f5462,f120,f6225])).

fof(f6222,plain,
    ( k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_140 ),
    inference(superposition,[],[f5464,f1769])).

fof(f6221,plain,
    ( ~ spl2_158
    | spl2_159
    | ~ spl2_8
    | ~ spl2_155 ),
    inference(avatar_split_clause,[],[f6210,f5988,f865,f6218,f6214])).

fof(f6214,plain,
    ( spl2_158
  <=> r1_tarski(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_158])])).

fof(f6218,plain,
    ( spl2_159
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_159])])).

fof(f5988,plain,
    ( spl2_155
  <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_155])])).

fof(f6210,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ r1_tarski(u1_struct_0(sK0),sK1)
    | ~ spl2_8
    | ~ spl2_155 ),
    inference(superposition,[],[f5998,f867])).

fof(f5998,plain,
    ( ! [X1] :
        ( r1_tarski(k6_subset_1(X1,sK1),k2_tops_1(sK0,sK1))
        | ~ r1_tarski(X1,sK1) )
    | ~ spl2_155 ),
    inference(superposition,[],[f106,f5990])).

fof(f5990,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_155 ),
    inference(avatar_component_clause,[],[f5988])).

fof(f6009,plain,
    ( spl2_157
    | ~ spl2_107
    | ~ spl2_156 ),
    inference(avatar_split_clause,[],[f6004,f6000,f4690,f6006])).

fof(f6006,plain,
    ( spl2_157
  <=> sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_157])])).

fof(f4690,plain,
    ( spl2_107
  <=> k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_107])])).

fof(f6000,plain,
    ( spl2_156
  <=> sK1 = k3_tarski(k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_156])])).

fof(f6004,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1)
    | ~ spl2_107
    | ~ spl2_156 ),
    inference(backward_demodulation,[],[f4692,f6002])).

fof(f6002,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,sK1))
    | ~ spl2_156 ),
    inference(avatar_component_clause,[],[f6000])).

fof(f4692,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1))
    | ~ spl2_107 ),
    inference(avatar_component_clause,[],[f4690])).

fof(f6003,plain,
    ( spl2_156
    | ~ spl2_155 ),
    inference(avatar_split_clause,[],[f5997,f5988,f6000])).

fof(f5997,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,sK1))
    | ~ spl2_155 ),
    inference(superposition,[],[f101,f5990])).

fof(f5991,plain,
    ( spl2_155
    | ~ spl2_105
    | ~ spl2_154 ),
    inference(avatar_split_clause,[],[f5986,f5982,f4680,f5988])).

fof(f5986,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_105
    | ~ spl2_154 ),
    inference(backward_demodulation,[],[f4682,f5984])).

fof(f5985,plain,
    ( spl2_154
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_38 ),
    inference(avatar_split_clause,[],[f5980,f2756,f125,f120,f5982])).

fof(f5980,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_38 ),
    inference(forward_demodulation,[],[f5939,f2758])).

fof(f5979,plain,
    ( spl2_153
    | ~ spl2_4
    | ~ spl2_88 ),
    inference(avatar_split_clause,[],[f5938,f4479,f125,f5976])).

fof(f5976,plain,
    ( spl2_153
  <=> k2_pre_topc(sK0,k2_tops_1(sK0,k1_xboole_0)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0),k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_153])])).

fof(f4479,plain,
    ( spl2_88
  <=> m1_subset_1(k2_tops_1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).

fof(f5938,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,k1_xboole_0)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0),k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_4
    | ~ spl2_88 ),
    inference(resolution,[],[f4111,f4481])).

fof(f4481,plain,
    ( m1_subset_1(k2_tops_1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_88 ),
    inference(avatar_component_clause,[],[f4479])).

fof(f5974,plain,
    ( spl2_152
    | ~ spl2_4
    | ~ spl2_56 ),
    inference(avatar_split_clause,[],[f5937,f3372,f125,f5971])).

fof(f5971,plain,
    ( spl2_152
  <=> k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_152])])).

fof(f3372,plain,
    ( spl2_56
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f5937,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl2_4
    | ~ spl2_56 ),
    inference(resolution,[],[f4111,f3374])).

fof(f3374,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_56 ),
    inference(avatar_component_clause,[],[f3372])).

fof(f5968,plain,
    ( spl2_151
    | ~ spl2_4
    | ~ spl2_12
    | ~ spl2_83 ),
    inference(avatar_split_clause,[],[f5963,f4446,f890,f125,f5965])).

fof(f5963,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_12
    | ~ spl2_83 ),
    inference(forward_demodulation,[],[f5929,f4448])).

fof(f5929,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(resolution,[],[f4111,f892])).

fof(f5962,plain,
    ( spl2_150
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f5928,f125,f5959])).

fof(f5959,plain,
    ( spl2_150
  <=> k2_pre_topc(sK0,k1_xboole_0) = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,k2_tops_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_150])])).

fof(f5928,plain,
    ( k2_pre_topc(sK0,k1_xboole_0) = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,k2_tops_1(sK0,k1_xboole_0))
    | ~ spl2_4 ),
    inference(resolution,[],[f4111,f169])).

fof(f169,plain,(
    ! [X4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X4)) ),
    inference(superposition,[],[f76,f165])).

fof(f5957,plain,
    ( spl2_149
    | ~ spl2_4
    | ~ spl2_117
    | ~ spl2_121 ),
    inference(avatar_split_clause,[],[f5952,f4997,f4977,f125,f5954])).

fof(f5954,plain,
    ( spl2_149
  <=> k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_149])])).

fof(f4977,plain,
    ( spl2_117
  <=> k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0)) = k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_117])])).

fof(f4997,plain,
    ( spl2_121
  <=> m1_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_121])])).

fof(f5952,plain,
    ( k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_4
    | ~ spl2_117
    | ~ spl2_121 ),
    inference(forward_demodulation,[],[f5927,f4979])).

fof(f4979,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0)) = k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_117 ),
    inference(avatar_component_clause,[],[f4977])).

fof(f5927,plain,
    ( k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))))
    | ~ spl2_4
    | ~ spl2_121 ),
    inference(resolution,[],[f4111,f4999])).

fof(f4999,plain,
    ( m1_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_121 ),
    inference(avatar_component_clause,[],[f4997])).

fof(f5951,plain,
    ( spl2_148
    | ~ spl2_4
    | ~ spl2_68
    | ~ spl2_82 ),
    inference(avatar_split_clause,[],[f5946,f4438,f3680,f125,f5948])).

fof(f5948,plain,
    ( spl2_148
  <=> k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_148])])).

fof(f3680,plain,
    ( spl2_68
  <=> m1_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).

fof(f4438,plain,
    ( spl2_82
  <=> k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_82])])).

fof(f5946,plain,
    ( k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl2_4
    | ~ spl2_68
    | ~ spl2_82 ),
    inference(forward_demodulation,[],[f5926,f4440])).

fof(f4440,plain,
    ( k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1))
    | ~ spl2_82 ),
    inference(avatar_component_clause,[],[f4438])).

fof(f5926,plain,
    ( k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))
    | ~ spl2_4
    | ~ spl2_68 ),
    inference(resolution,[],[f4111,f3682])).

fof(f3682,plain,
    ( m1_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_68 ),
    inference(avatar_component_clause,[],[f3680])).

fof(f5945,plain,
    ( spl2_147
    | ~ spl2_4
    | ~ spl2_81 ),
    inference(avatar_split_clause,[],[f5940,f4432,f125,f5942])).

fof(f5942,plain,
    ( spl2_147
  <=> k2_pre_topc(sK0,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_147])])).

fof(f4432,plain,
    ( spl2_81
  <=> k2_tops_1(sK0,u1_struct_0(sK0)) = k2_tops_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_81])])).

fof(f5940,plain,
    ( k2_pre_topc(sK0,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))
    | ~ spl2_4
    | ~ spl2_81 ),
    inference(forward_demodulation,[],[f5924,f4434])).

fof(f4434,plain,
    ( k2_tops_1(sK0,u1_struct_0(sK0)) = k2_tops_1(sK0,k1_xboole_0)
    | ~ spl2_81 ),
    inference(avatar_component_clause,[],[f4432])).

fof(f5924,plain,
    ( k2_pre_topc(sK0,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k2_tops_1(sK0,u1_struct_0(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f4111,f136])).

fof(f5662,plain,
    ( spl2_146
    | ~ spl2_142
    | ~ spl2_143 ),
    inference(avatar_split_clause,[],[f5657,f5642,f5636,f5659])).

fof(f5636,plain,
    ( spl2_142
  <=> sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_142])])).

fof(f5657,plain,
    ( sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k5_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_142
    | ~ spl2_143 ),
    inference(forward_demodulation,[],[f5638,f5644])).

fof(f5638,plain,
    ( sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_142 ),
    inference(avatar_component_clause,[],[f5636])).

fof(f5656,plain,
    ( spl2_145
    | ~ spl2_143
    | ~ spl2_144 ),
    inference(avatar_split_clause,[],[f5651,f5647,f5642,f5653])).

fof(f5647,plain,
    ( spl2_144
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_144])])).

fof(f5651,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_143
    | ~ spl2_144 ),
    inference(backward_demodulation,[],[f5649,f5644])).

fof(f5649,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_144 ),
    inference(avatar_component_clause,[],[f5647])).

fof(f5650,plain,
    ( spl2_144
    | ~ spl2_47 ),
    inference(avatar_split_clause,[],[f5633,f2828,f5647])).

fof(f2828,plain,
    ( spl2_47
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f5633,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_47 ),
    inference(resolution,[],[f2830,f86])).

fof(f2830,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f2828])).

fof(f5645,plain,
    ( spl2_143
    | ~ spl2_47
    | ~ spl2_141 ),
    inference(avatar_split_clause,[],[f5640,f5624,f2828,f5642])).

fof(f5640,plain,
    ( k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_47
    | ~ spl2_141 ),
    inference(forward_demodulation,[],[f5632,f5626])).

fof(f5632,plain,
    ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_47 ),
    inference(resolution,[],[f2830,f103])).

fof(f5639,plain,
    ( spl2_142
    | ~ spl2_47 ),
    inference(avatar_split_clause,[],[f5630,f2828,f5636])).

fof(f5630,plain,
    ( sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_47 ),
    inference(resolution,[],[f2830,f134])).

fof(f5628,plain,
    ( spl2_47
    | ~ spl2_130 ),
    inference(avatar_split_clause,[],[f5618,f5222,f2828])).

fof(f5618,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_130 ),
    inference(superposition,[],[f163,f5224])).

fof(f5627,plain,
    ( spl2_141
    | ~ spl2_130 ),
    inference(avatar_split_clause,[],[f5616,f5222,f5624])).

fof(f5616,plain,
    ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_130 ),
    inference(superposition,[],[f102,f5224])).

fof(f5465,plain,
    ( spl2_140
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f5419,f125,f120,f5462])).

fof(f5419,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f3862,f122])).

fof(f5460,plain,
    ( spl2_139
    | ~ spl2_4
    | ~ spl2_88 ),
    inference(avatar_split_clause,[],[f5418,f4479,f125,f5457])).

fof(f5457,plain,
    ( spl2_139
  <=> k1_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0),k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_139])])).

fof(f5418,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0),k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_4
    | ~ spl2_88 ),
    inference(resolution,[],[f3862,f4481])).

fof(f5455,plain,
    ( spl2_138
    | ~ spl2_4
    | ~ spl2_56 ),
    inference(avatar_split_clause,[],[f5417,f3372,f125,f5452])).

fof(f5452,plain,
    ( spl2_138
  <=> k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_138])])).

fof(f5417,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl2_4
    | ~ spl2_56 ),
    inference(resolution,[],[f3862,f3374])).

fof(f5449,plain,
    ( spl2_137
    | ~ spl2_4
    | ~ spl2_12
    | ~ spl2_83 ),
    inference(avatar_split_clause,[],[f5444,f4446,f890,f125,f5446])).

fof(f5444,plain,
    ( k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_12
    | ~ spl2_83 ),
    inference(forward_demodulation,[],[f5409,f4448])).

fof(f5409,plain,
    ( k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(resolution,[],[f3862,f892])).

fof(f5443,plain,
    ( spl2_136
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f5438,f125,f5440])).

fof(f5440,plain,
    ( spl2_136
  <=> k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_136])])).

fof(f5438,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f5408,f1770])).

fof(f1770,plain,(
    ! [X6,X5] : k1_xboole_0 = k7_subset_1(X5,k1_xboole_0,X6) ),
    inference(forward_demodulation,[],[f1763,f182])).

fof(f182,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f168,f99])).

fof(f1763,plain,(
    ! [X6,X5] : k6_subset_1(k1_xboole_0,X6) = k7_subset_1(X5,k1_xboole_0,X6) ),
    inference(resolution,[],[f105,f169])).

fof(f5408,plain,
    ( k1_tops_1(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k1_xboole_0,k2_tops_1(sK0,k1_xboole_0))
    | ~ spl2_4 ),
    inference(resolution,[],[f3862,f169])).

fof(f5437,plain,
    ( spl2_135
    | ~ spl2_4
    | ~ spl2_117
    | ~ spl2_121 ),
    inference(avatar_split_clause,[],[f5432,f4997,f4977,f125,f5434])).

fof(f5434,plain,
    ( spl2_135
  <=> k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_135])])).

fof(f5432,plain,
    ( k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_4
    | ~ spl2_117
    | ~ spl2_121 ),
    inference(forward_demodulation,[],[f5407,f4979])).

fof(f5407,plain,
    ( k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))))
    | ~ spl2_4
    | ~ spl2_121 ),
    inference(resolution,[],[f3862,f4999])).

fof(f5431,plain,
    ( spl2_134
    | ~ spl2_4
    | ~ spl2_68
    | ~ spl2_82 ),
    inference(avatar_split_clause,[],[f5426,f4438,f3680,f125,f5428])).

fof(f5428,plain,
    ( spl2_134
  <=> k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_134])])).

fof(f5426,plain,
    ( k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl2_4
    | ~ spl2_68
    | ~ spl2_82 ),
    inference(forward_demodulation,[],[f5406,f4440])).

fof(f5406,plain,
    ( k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))
    | ~ spl2_4
    | ~ spl2_68 ),
    inference(resolution,[],[f3862,f3682])).

fof(f5425,plain,
    ( spl2_133
    | ~ spl2_4
    | ~ spl2_81 ),
    inference(avatar_split_clause,[],[f5420,f4432,f125,f5422])).

fof(f5422,plain,
    ( spl2_133
  <=> k1_tops_1(sK0,u1_struct_0(sK0)) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_133])])).

fof(f5420,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))
    | ~ spl2_4
    | ~ spl2_81 ),
    inference(forward_demodulation,[],[f5404,f4434])).

fof(f5404,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k2_tops_1(sK0,u1_struct_0(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f3862,f136])).

fof(f5390,plain,
    ( spl2_132
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f5383,f865,f5385])).

fof(f5383,plain,
    ( k1_xboole_0 = k6_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl2_8 ),
    inference(resolution,[],[f5371,f104])).

fof(f5371,plain,
    ( ! [X3] : r1_tarski(k6_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)),X3)
    | ~ spl2_8 ),
    inference(resolution,[],[f5360,f106])).

fof(f5360,plain,
    ( ! [X0] : r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_tarski(k2_tarski(u1_struct_0(sK0),X0)))
    | ~ spl2_8 ),
    inference(superposition,[],[f5119,f77])).

fof(f5119,plain,
    ( ! [X89] : r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_tarski(k2_tarski(X89,u1_struct_0(sK0))))
    | ~ spl2_8 ),
    inference(resolution,[],[f1309,f870])).

fof(f870,plain,
    ( ! [X0] :
        ( ~ r1_tarski(u1_struct_0(sK0),X0)
        | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),X0) )
    | ~ spl2_8 ),
    inference(superposition,[],[f151,f867])).

fof(f5388,plain,
    ( spl2_132
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f5381,f865,f5385])).

fof(f5381,plain,
    ( k1_xboole_0 = k6_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl2_8 ),
    inference(resolution,[],[f5371,f168])).

fof(f5271,plain,
    ( spl2_131
    | ~ spl2_87 ),
    inference(avatar_split_clause,[],[f5264,f4474,f5266])).

fof(f5266,plain,
    ( spl2_131
  <=> k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_131])])).

fof(f4474,plain,
    ( spl2_87
  <=> r1_tarski(k2_tops_1(sK0,k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).

fof(f5264,plain,
    ( k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl2_87 ),
    inference(resolution,[],[f5252,f104])).

fof(f5252,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(k2_tops_1(sK0,k1_xboole_0),u1_struct_0(sK0)),X0)
    | ~ spl2_87 ),
    inference(resolution,[],[f5243,f106])).

fof(f5243,plain,
    ( ! [X0] : r1_tarski(k2_tops_1(sK0,k1_xboole_0),k3_tarski(k2_tarski(u1_struct_0(sK0),X0)))
    | ~ spl2_87 ),
    inference(superposition,[],[f5142,f77])).

fof(f5142,plain,
    ( ! [X145] : r1_tarski(k2_tops_1(sK0,k1_xboole_0),k3_tarski(k2_tarski(X145,u1_struct_0(sK0))))
    | ~ spl2_87 ),
    inference(resolution,[],[f1309,f4492])).

fof(f4492,plain,
    ( ! [X1] :
        ( ~ r1_tarski(u1_struct_0(sK0),X1)
        | r1_tarski(k2_tops_1(sK0,k1_xboole_0),X1) )
    | ~ spl2_87 ),
    inference(resolution,[],[f4476,f95])).

fof(f4476,plain,
    ( r1_tarski(k2_tops_1(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl2_87 ),
    inference(avatar_component_clause,[],[f4474])).

fof(f5269,plain,
    ( spl2_131
    | ~ spl2_87 ),
    inference(avatar_split_clause,[],[f5262,f4474,f5266])).

fof(f5262,plain,
    ( k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl2_87 ),
    inference(resolution,[],[f5252,f168])).

fof(f5225,plain,
    ( spl2_130
    | ~ spl2_129 ),
    inference(avatar_split_clause,[],[f5220,f5176,f5222])).

fof(f5176,plain,
    ( spl2_129
  <=> k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_129])])).

fof(f5220,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_129 ),
    inference(forward_demodulation,[],[f5219,f77])).

fof(f5219,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_129 ),
    inference(forward_demodulation,[],[f5206,f98])).

fof(f5206,plain,
    ( k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k6_subset_1(k2_tops_1(sK0,sK1),k1_xboole_0)
    | ~ spl2_129 ),
    inference(superposition,[],[f100,f5178])).

fof(f5178,plain,
    ( k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_129 ),
    inference(avatar_component_clause,[],[f5176])).

fof(f5181,plain,
    ( spl2_129
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f5174,f2833,f5176])).

fof(f5174,plain,
    ( k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_48 ),
    inference(resolution,[],[f5146,f104])).

fof(f5179,plain,
    ( spl2_129
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f5172,f2833,f5176])).

fof(f5172,plain,
    ( k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_48 ),
    inference(resolution,[],[f5146,f168])).

fof(f5081,plain,
    ( spl2_127
    | ~ spl2_128
    | ~ spl2_125 ),
    inference(avatar_split_clause,[],[f5064,f5017,f5078,f5074])).

fof(f5074,plain,
    ( spl2_127
  <=> k1_xboole_0 = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_127])])).

fof(f5078,plain,
    ( spl2_128
  <=> r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_128])])).

fof(f5017,plain,
    ( spl2_125
  <=> k2_tops_1(sK0,k1_xboole_0) = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_125])])).

fof(f5064,plain,
    ( ~ r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k1_xboole_0))
    | k1_xboole_0 = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))
    | ~ spl2_125 ),
    inference(superposition,[],[f104,f5019])).

fof(f5019,plain,
    ( k2_tops_1(sK0,k1_xboole_0) = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_125 ),
    inference(avatar_component_clause,[],[f5017])).

fof(f5072,plain,
    ( spl2_126
    | ~ spl2_115
    | ~ spl2_125 ),
    inference(avatar_split_clause,[],[f5067,f5017,f4952,f5069])).

fof(f5069,plain,
    ( spl2_126
  <=> k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_126])])).

fof(f4952,plain,
    ( spl2_115
  <=> k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_115])])).

fof(f5067,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))))
    | ~ spl2_115
    | ~ spl2_125 ),
    inference(forward_demodulation,[],[f5062,f4954])).

fof(f4954,plain,
    ( k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))
    | ~ spl2_115 ),
    inference(avatar_component_clause,[],[f4952])).

fof(f5062,plain,
    ( k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))))
    | ~ spl2_125 ),
    inference(superposition,[],[f100,f5019])).

fof(f5020,plain,
    ( spl2_125
    | ~ spl2_114
    | ~ spl2_116 ),
    inference(avatar_split_clause,[],[f4975,f4958,f4932,f5017])).

fof(f4932,plain,
    ( spl2_114
  <=> k2_tops_1(sK0,k1_xboole_0) = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_114])])).

fof(f4975,plain,
    ( k2_tops_1(sK0,k1_xboole_0) = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_114
    | ~ spl2_116 ),
    inference(backward_demodulation,[],[f4934,f4960])).

fof(f4934,plain,
    ( k2_tops_1(sK0,k1_xboole_0) = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_114 ),
    inference(avatar_component_clause,[],[f4932])).

fof(f5015,plain,
    ( spl2_124
    | ~ spl2_112
    | ~ spl2_116 ),
    inference(avatar_split_clause,[],[f4974,f4958,f4919,f5012])).

fof(f5012,plain,
    ( spl2_124
  <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_124])])).

fof(f4919,plain,
    ( spl2_112
  <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_112])])).

fof(f4974,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k1_xboole_0))
    | ~ spl2_112
    | ~ spl2_116 ),
    inference(backward_demodulation,[],[f4921,f4960])).

fof(f4921,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k1_xboole_0))
    | ~ spl2_112 ),
    inference(avatar_component_clause,[],[f4919])).

fof(f5010,plain,
    ( spl2_123
    | ~ spl2_111
    | ~ spl2_116 ),
    inference(avatar_split_clause,[],[f4973,f4958,f4912,f5007])).

fof(f5007,plain,
    ( spl2_123
  <=> k4_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k3_tarski(k2_tarski(sK1,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_123])])).

fof(f4912,plain,
    ( spl2_111
  <=> k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_111])])).

fof(f4973,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k3_tarski(k2_tarski(sK1,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))))
    | ~ spl2_111
    | ~ spl2_116 ),
    inference(backward_demodulation,[],[f4914,f4960])).

fof(f4914,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))))
    | ~ spl2_111 ),
    inference(avatar_component_clause,[],[f4912])).

fof(f5005,plain,
    ( spl2_122
    | ~ spl2_100
    | ~ spl2_116 ),
    inference(avatar_split_clause,[],[f4969,f4958,f4636,f5002])).

fof(f5002,plain,
    ( spl2_122
  <=> r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_122])])).

fof(f4636,plain,
    ( spl2_100
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_100])])).

fof(f4969,plain,
    ( r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | ~ spl2_100
    | ~ spl2_116 ),
    inference(backward_demodulation,[],[f4638,f4960])).

fof(f4638,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | ~ spl2_100 ),
    inference(avatar_component_clause,[],[f4636])).

fof(f5000,plain,
    ( spl2_121
    | ~ spl2_99
    | ~ spl2_116 ),
    inference(avatar_split_clause,[],[f4968,f4958,f4631,f4997])).

fof(f4631,plain,
    ( spl2_99
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_99])])).

fof(f4968,plain,
    ( m1_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_99
    | ~ spl2_116 ),
    inference(backward_demodulation,[],[f4633,f4960])).

fof(f4633,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_99 ),
    inference(avatar_component_clause,[],[f4631])).

fof(f4995,plain,
    ( ~ spl2_120
    | spl2_98
    | ~ spl2_116 ),
    inference(avatar_split_clause,[],[f4967,f4958,f4626,f4992])).

fof(f4992,plain,
    ( spl2_120
  <=> r1_tarski(k2_tops_1(sK0,k1_xboole_0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_120])])).

fof(f4626,plain,
    ( spl2_98
  <=> r1_tarski(k2_tops_1(sK0,k1_xboole_0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).

fof(f4967,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k1_xboole_0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))
    | spl2_98
    | ~ spl2_116 ),
    inference(backward_demodulation,[],[f4628,f4960])).

fof(f4628,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k1_xboole_0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))
    | spl2_98 ),
    inference(avatar_component_clause,[],[f4626])).

fof(f4990,plain,
    ( spl2_119
    | ~ spl2_93
    | ~ spl2_116 ),
    inference(avatar_split_clause,[],[f4964,f4958,f4516,f4987])).

fof(f4987,plain,
    ( spl2_119
  <=> k2_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_119])])).

fof(f4516,plain,
    ( spl2_93
  <=> k2_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_93])])).

fof(f4964,plain,
    ( k2_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_93
    | ~ spl2_116 ),
    inference(backward_demodulation,[],[f4518,f4960])).

fof(f4518,plain,
    ( k2_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_93 ),
    inference(avatar_component_clause,[],[f4516])).

fof(f4985,plain,
    ( spl2_118
    | ~ spl2_91
    | ~ spl2_116 ),
    inference(avatar_split_clause,[],[f4963,f4958,f4506,f4982])).

fof(f4982,plain,
    ( spl2_118
  <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_118])])).

fof(f4506,plain,
    ( spl2_91
  <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_91])])).

fof(f4963,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_91
    | ~ spl2_116 ),
    inference(backward_demodulation,[],[f4508,f4960])).

fof(f4508,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_91 ),
    inference(avatar_component_clause,[],[f4506])).

fof(f4980,plain,
    ( spl2_117
    | ~ spl2_90
    | ~ spl2_116 ),
    inference(avatar_split_clause,[],[f4962,f4958,f4501,f4977])).

fof(f4501,plain,
    ( spl2_90
  <=> k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_90])])).

fof(f4962,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0)) = k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_90
    | ~ spl2_116 ),
    inference(backward_demodulation,[],[f4503,f4960])).

fof(f4503,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_90 ),
    inference(avatar_component_clause,[],[f4501])).

fof(f4961,plain,
    ( spl2_116
    | ~ spl2_92
    | ~ spl2_115 ),
    inference(avatar_split_clause,[],[f4956,f4952,f4511,f4958])).

fof(f4956,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))
    | ~ spl2_92
    | ~ spl2_115 ),
    inference(backward_demodulation,[],[f4513,f4954])).

fof(f4955,plain,
    ( spl2_115
    | ~ spl2_113 ),
    inference(avatar_split_clause,[],[f4946,f4926,f4952])).

fof(f4926,plain,
    ( spl2_113
  <=> k2_tops_1(sK0,k1_xboole_0) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_113])])).

fof(f4946,plain,
    ( k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))
    | ~ spl2_113 ),
    inference(superposition,[],[f102,f4928])).

fof(f4928,plain,
    ( k2_tops_1(sK0,k1_xboole_0) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_113 ),
    inference(avatar_component_clause,[],[f4926])).

fof(f4935,plain,
    ( spl2_114
    | ~ spl2_96
    | ~ spl2_113 ),
    inference(avatar_split_clause,[],[f4930,f4926,f4617,f4932])).

fof(f4617,plain,
    ( spl2_96
  <=> k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_96])])).

fof(f4930,plain,
    ( k2_tops_1(sK0,k1_xboole_0) = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_96
    | ~ spl2_113 ),
    inference(backward_demodulation,[],[f4619,f4928])).

fof(f4619,plain,
    ( k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_96 ),
    inference(avatar_component_clause,[],[f4617])).

fof(f4929,plain,
    ( spl2_113
    | ~ spl2_93
    | ~ spl2_96
    | ~ spl2_99 ),
    inference(avatar_split_clause,[],[f4924,f4631,f4617,f4516,f4926])).

fof(f4924,plain,
    ( k2_tops_1(sK0,k1_xboole_0) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_93
    | ~ spl2_96
    | ~ spl2_99 ),
    inference(forward_demodulation,[],[f4923,f4518])).

fof(f4923,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_96
    | ~ spl2_99 ),
    inference(forward_demodulation,[],[f4908,f4619])).

fof(f4908,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_99 ),
    inference(resolution,[],[f4633,f103])).

fof(f4922,plain,
    ( spl2_112
    | ~ spl2_93
    | ~ spl2_99 ),
    inference(avatar_split_clause,[],[f4917,f4631,f4516,f4919])).

fof(f4917,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k1_xboole_0))
    | ~ spl2_93
    | ~ spl2_99 ),
    inference(forward_demodulation,[],[f4906,f4518])).

fof(f4906,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))))
    | ~ spl2_99 ),
    inference(resolution,[],[f4633,f134])).

fof(f4915,plain,
    ( spl2_111
    | ~ spl2_3
    | ~ spl2_99 ),
    inference(avatar_split_clause,[],[f4903,f4631,f120,f4912])).

fof(f4903,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))))
    | ~ spl2_3
    | ~ spl2_99 ),
    inference(resolution,[],[f4633,f3703])).

fof(f4877,plain,
    ( spl2_110
    | ~ spl2_101
    | ~ spl2_109 ),
    inference(avatar_split_clause,[],[f4868,f4799,f4658,f4874])).

fof(f4874,plain,
    ( spl2_110
  <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_110])])).

fof(f4658,plain,
    ( spl2_101
  <=> k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_101])])).

fof(f4868,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))
    | ~ spl2_101
    | ~ spl2_109 ),
    inference(backward_demodulation,[],[f4660,f4801])).

fof(f4660,plain,
    ( k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))
    | ~ spl2_101 ),
    inference(avatar_component_clause,[],[f4658])).

fof(f4802,plain,
    ( spl2_109
    | ~ spl2_104 ),
    inference(avatar_split_clause,[],[f4791,f4675,f4799])).

fof(f4791,plain,
    ( u1_struct_0(sK0) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))
    | ~ spl2_104 ),
    inference(superposition,[],[f101,f4677])).

fof(f4797,plain,
    ( spl2_108
    | ~ spl2_6
    | ~ spl2_48
    | ~ spl2_104 ),
    inference(avatar_split_clause,[],[f4789,f4675,f2833,f145,f4794])).

fof(f4794,plain,
    ( spl2_108
  <=> r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_108])])).

fof(f145,plain,
    ( spl2_6
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f4789,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ spl2_48
    | ~ spl2_104 ),
    inference(superposition,[],[f3573,f4677])).

fof(f4693,plain,
    ( spl2_107
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f4656,f120,f4690])).

fof(f4656,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1))
    | ~ spl2_3 ),
    inference(resolution,[],[f3703,f122])).

fof(f4688,plain,
    ( spl2_106
    | ~ spl2_3
    | ~ spl2_88 ),
    inference(avatar_split_clause,[],[f4655,f4479,f120,f4685])).

fof(f4685,plain,
    ( spl2_106
  <=> k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,k1_xboole_0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_106])])).

fof(f4655,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,k1_xboole_0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_3
    | ~ spl2_88 ),
    inference(resolution,[],[f3703,f4481])).

fof(f4683,plain,
    ( spl2_105
    | ~ spl2_3
    | ~ spl2_56 ),
    inference(avatar_split_clause,[],[f4654,f3372,f120,f4680])).

fof(f4654,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_3
    | ~ spl2_56 ),
    inference(resolution,[],[f3703,f3374])).

fof(f4678,plain,
    ( spl2_104
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f4673,f2105,f890,f120,f4675])).

fof(f4673,plain,
    ( u1_struct_0(sK0) = k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f4646,f2107])).

fof(f4646,plain,
    ( k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(resolution,[],[f3703,f892])).

fof(f4672,plain,
    ( spl2_103
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f4667,f120,f4669])).

fof(f4669,plain,
    ( spl2_103
  <=> k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k3_tarski(k2_tarski(k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_103])])).

fof(f4667,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k3_tarski(k2_tarski(k1_xboole_0,sK1))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f4645,f77])).

fof(f4645,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k3_tarski(k2_tarski(sK1,k1_xboole_0))
    | ~ spl2_3 ),
    inference(resolution,[],[f3703,f169])).

fof(f4666,plain,
    ( spl2_102
    | ~ spl2_3
    | ~ spl2_68 ),
    inference(avatar_split_clause,[],[f4644,f3680,f120,f4663])).

fof(f4663,plain,
    ( spl2_102
  <=> k4_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k3_tarski(k2_tarski(sK1,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_102])])).

fof(f4644,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k3_tarski(k2_tarski(sK1,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))
    | ~ spl2_3
    | ~ spl2_68 ),
    inference(resolution,[],[f3703,f3682])).

fof(f4661,plain,
    ( spl2_101
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f4642,f120,f4658])).

fof(f4642,plain,
    ( k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))
    | ~ spl2_3 ),
    inference(resolution,[],[f3703,f136])).

fof(f4639,plain,
    ( spl2_100
    | ~ spl2_92 ),
    inference(avatar_split_clause,[],[f4615,f4511,f4636])).

fof(f4615,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | ~ spl2_92 ),
    inference(superposition,[],[f99,f4513])).

fof(f4634,plain,
    ( spl2_99
    | ~ spl2_92 ),
    inference(avatar_split_clause,[],[f4614,f4511,f4631])).

fof(f4614,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_92 ),
    inference(superposition,[],[f76,f4513])).

fof(f4629,plain,
    ( spl2_97
    | ~ spl2_98
    | ~ spl2_92 ),
    inference(avatar_split_clause,[],[f4613,f4511,f4626,f4622])).

fof(f4622,plain,
    ( spl2_97
  <=> k1_xboole_0 = k2_tops_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_97])])).

fof(f4613,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k1_xboole_0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))
    | k1_xboole_0 = k2_tops_1(sK0,k1_xboole_0)
    | ~ spl2_92 ),
    inference(superposition,[],[f104,f4513])).

fof(f4620,plain,
    ( spl2_96
    | ~ spl2_92 ),
    inference(avatar_split_clause,[],[f4611,f4511,f4617])).

fof(f4611,plain,
    ( k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_92 ),
    inference(superposition,[],[f100,f4513])).

fof(f4552,plain,
    ( spl2_95
    | ~ spl2_94 ),
    inference(avatar_split_clause,[],[f4545,f4531,f4549])).

fof(f4531,plain,
    ( spl2_94
  <=> r1_tarski(k2_tops_1(sK0,k1_xboole_0),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_94])])).

fof(f4545,plain,
    ( r1_tarski(k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_94 ),
    inference(resolution,[],[f4533,f106])).

fof(f4533,plain,
    ( r1_tarski(k2_tops_1(sK0,k1_xboole_0),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_94 ),
    inference(avatar_component_clause,[],[f4531])).

fof(f4534,plain,
    ( spl2_94
    | ~ spl2_21
    | ~ spl2_87 ),
    inference(avatar_split_clause,[],[f4527,f4474,f1658,f4531])).

fof(f4527,plain,
    ( r1_tarski(k2_tops_1(sK0,k1_xboole_0),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_21
    | ~ spl2_87 ),
    inference(resolution,[],[f4492,f1660])).

fof(f4519,plain,
    ( spl2_93
    | ~ spl2_88 ),
    inference(avatar_split_clause,[],[f4498,f4479,f4516])).

fof(f4498,plain,
    ( k2_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_88 ),
    inference(resolution,[],[f4481,f86])).

fof(f4514,plain,
    ( spl2_92
    | ~ spl2_88 ),
    inference(avatar_split_clause,[],[f4497,f4479,f4511])).

fof(f4497,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) = k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))
    | ~ spl2_88 ),
    inference(resolution,[],[f4481,f103])).

fof(f4509,plain,
    ( spl2_91
    | ~ spl2_88 ),
    inference(avatar_split_clause,[],[f4495,f4479,f4506])).

fof(f4495,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_88 ),
    inference(resolution,[],[f4481,f134])).

fof(f4504,plain,
    ( spl2_90
    | ~ spl2_4
    | ~ spl2_88 ),
    inference(avatar_split_clause,[],[f4493,f4479,f125,f4501])).

fof(f4493,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))
    | ~ spl2_4
    | ~ spl2_88 ),
    inference(resolution,[],[f4481,f3224])).

fof(f4490,plain,
    ( ~ spl2_89
    | spl2_84 ),
    inference(avatar_split_clause,[],[f4484,f4462,f4487])).

fof(f4487,plain,
    ( spl2_89
  <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_89])])).

fof(f4462,plain,
    ( spl2_84
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_84])])).

fof(f4484,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | spl2_84 ),
    inference(resolution,[],[f4464,f91])).

fof(f4464,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_84 ),
    inference(avatar_component_clause,[],[f4462])).

fof(f4485,plain,(
    spl2_84 ),
    inference(avatar_contradiction_clause,[],[f4483])).

fof(f4483,plain,
    ( $false
    | spl2_84 ),
    inference(resolution,[],[f4464,f136])).

fof(f4482,plain,
    ( ~ spl2_84
    | spl2_88
    | ~ spl2_4
    | ~ spl2_81 ),
    inference(avatar_split_clause,[],[f4460,f4432,f125,f4479,f4462])).

fof(f4460,plain,
    ( m1_subset_1(k2_tops_1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4
    | ~ spl2_81 ),
    inference(superposition,[],[f2451,f4434])).

fof(f2451,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_4 ),
    inference(resolution,[],[f89,f127])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f4477,plain,
    ( ~ spl2_84
    | spl2_87
    | ~ spl2_4
    | ~ spl2_81 ),
    inference(avatar_split_clause,[],[f4459,f4432,f125,f4474,f4462])).

fof(f4459,plain,
    ( r1_tarski(k2_tops_1(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4
    | ~ spl2_81 ),
    inference(superposition,[],[f2655,f4434])).

fof(f2655,plain,
    ( ! [X5] :
        ( r1_tarski(k2_tops_1(sK0,X5),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_4 ),
    inference(resolution,[],[f2451,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f4472,plain,
    ( ~ spl2_84
    | spl2_86
    | ~ spl2_4
    | ~ spl2_81 ),
    inference(avatar_split_clause,[],[f4458,f4432,f125,f4470,f4462])).

fof(f4470,plain,
    ( spl2_86
  <=> ! [X1] : r1_tarski(k1_setfam_1(k2_tarski(k2_tops_1(sK0,k1_xboole_0),X1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_86])])).

fof(f4458,plain,
    ( ! [X1] :
        ( r1_tarski(k1_setfam_1(k2_tarski(k2_tops_1(sK0,k1_xboole_0),X1)),u1_struct_0(sK0))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_4
    | ~ spl2_81 ),
    inference(superposition,[],[f2656,f4434])).

fof(f2656,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_setfam_1(k2_tarski(k2_tops_1(sK0,X0),X1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_4 ),
    inference(resolution,[],[f2655,f161])).

fof(f4468,plain,
    ( ~ spl2_84
    | spl2_85
    | ~ spl2_4
    | ~ spl2_81 ),
    inference(avatar_split_clause,[],[f4457,f4432,f125,f4466,f4462])).

fof(f4466,plain,
    ( spl2_85
  <=> ! [X0] : r1_tarski(k1_setfam_1(k2_tarski(X0,k2_tops_1(sK0,k1_xboole_0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_85])])).

fof(f4457,plain,
    ( ! [X0] :
        ( r1_tarski(k1_setfam_1(k2_tarski(X0,k2_tops_1(sK0,k1_xboole_0))),u1_struct_0(sK0))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_4
    | ~ spl2_81 ),
    inference(superposition,[],[f3949,f4434])).

fof(f3949,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_setfam_1(k2_tarski(X1,k2_tops_1(sK0,X0))),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_4 ),
    inference(superposition,[],[f2656,f77])).

fof(f4456,plain,
    ( spl2_83
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f4429,f125,f120,f4446])).

fof(f4429,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f3224,f122])).

fof(f4455,plain,
    ( spl2_82
    | ~ spl2_4
    | ~ spl2_56
    | ~ spl2_58 ),
    inference(avatar_split_clause,[],[f4454,f3388,f3372,f125,f4438])).

fof(f3388,plain,
    ( spl2_58
  <=> k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).

fof(f4454,plain,
    ( k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_56
    | ~ spl2_58 ),
    inference(forward_demodulation,[],[f4428,f3390])).

fof(f3390,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))
    | ~ spl2_58 ),
    inference(avatar_component_clause,[],[f3388])).

fof(f4428,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_4
    | ~ spl2_56 ),
    inference(resolution,[],[f3224,f3374])).

fof(f4449,plain,
    ( spl2_83
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f4444,f890,f523,f125,f4446])).

fof(f4444,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f4420,f525])).

fof(f4420,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(resolution,[],[f3224,f892])).

fof(f4443,plain,
    ( spl2_81
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f4442,f125,f4432])).

fof(f4442,plain,
    ( k2_tops_1(sK0,u1_struct_0(sK0)) = k2_tops_1(sK0,k1_xboole_0)
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f4419,f856])).

fof(f4419,plain,
    ( k2_tops_1(sK0,k1_xboole_0) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))
    | ~ spl2_4 ),
    inference(resolution,[],[f3224,f169])).

fof(f4441,plain,
    ( spl2_82
    | ~ spl2_4
    | ~ spl2_60
    | ~ spl2_68 ),
    inference(avatar_split_clause,[],[f4436,f3680,f3399,f125,f4438])).

fof(f3399,plain,
    ( spl2_60
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_60])])).

fof(f4436,plain,
    ( k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_60
    | ~ spl2_68 ),
    inference(forward_demodulation,[],[f4418,f3401])).

fof(f3401,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_60 ),
    inference(avatar_component_clause,[],[f3399])).

fof(f4418,plain,
    ( k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))
    | ~ spl2_4
    | ~ spl2_68 ),
    inference(resolution,[],[f3224,f3682])).

fof(f4435,plain,
    ( spl2_81
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f4430,f125,f4432])).

fof(f4430,plain,
    ( k2_tops_1(sK0,u1_struct_0(sK0)) = k2_tops_1(sK0,k1_xboole_0)
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f4416,f855])).

fof(f4416,plain,
    ( k2_tops_1(sK0,u1_struct_0(sK0)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f3224,f136])).

fof(f4350,plain,
    ( spl2_80
    | ~ spl2_79 ),
    inference(avatar_split_clause,[],[f4345,f4328,f4347])).

fof(f4345,plain,
    ( k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_79 ),
    inference(forward_demodulation,[],[f4344,f77])).

fof(f4344,plain,
    ( k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)))
    | ~ spl2_79 ),
    inference(forward_demodulation,[],[f4339,f98])).

fof(f4339,plain,
    ( k1_setfam_1(k2_tarski(k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))) = k6_subset_1(k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),k1_xboole_0)
    | ~ spl2_79 ),
    inference(superposition,[],[f100,f4330])).

fof(f4333,plain,
    ( spl2_79
    | ~ spl2_6
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f4326,f2833,f939,f913,f145,f4328])).

fof(f4326,plain,
    ( k1_xboole_0 = k6_subset_1(k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl2_6
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_48 ),
    inference(resolution,[],[f4314,f104])).

fof(f4314,plain,
    ( ! [X1] : r1_tarski(k6_subset_1(k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)),X1)
    | ~ spl2_6
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_48 ),
    inference(resolution,[],[f4033,f106])).

fof(f4033,plain,
    ( ! [X1] : r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),k3_tarski(k2_tarski(u1_struct_0(sK0),X1)))
    | ~ spl2_6
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_48 ),
    inference(resolution,[],[f3987,f3105])).

fof(f3987,plain,
    ( ! [X0] : r1_tarski(sK1,k3_tarski(k2_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_tarski(k2_tarski(u1_struct_0(sK0),X0)))))
    | ~ spl2_6
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(resolution,[],[f1878,f153])).

fof(f153,plain,
    ( ! [X5] :
        ( ~ r1_tarski(u1_struct_0(sK0),X5)
        | r1_tarski(sK1,X5) )
    | ~ spl2_6 ),
    inference(resolution,[],[f95,f147])).

fof(f147,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f145])).

fof(f1878,plain,
    ( ! [X0] : r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_tarski(k2_tarski(u1_struct_0(sK0),X0)))))
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(resolution,[],[f1317,f1320])).

fof(f4331,plain,
    ( spl2_79
    | ~ spl2_6
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f4324,f2833,f939,f913,f145,f4328])).

fof(f4324,plain,
    ( k1_xboole_0 = k6_subset_1(k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl2_6
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_48 ),
    inference(resolution,[],[f4314,f168])).

fof(f4083,plain,
    ( spl2_78
    | ~ spl2_77 ),
    inference(avatar_split_clause,[],[f4078,f4061,f4080])).

fof(f4080,plain,
    ( spl2_78
  <=> k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).

fof(f4061,plain,
    ( spl2_77
  <=> k1_xboole_0 = k6_subset_1(k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).

fof(f4078,plain,
    ( k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_77 ),
    inference(forward_demodulation,[],[f4077,f77])).

fof(f4077,plain,
    ( k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)))
    | ~ spl2_77 ),
    inference(forward_demodulation,[],[f4072,f98])).

fof(f4072,plain,
    ( k1_setfam_1(k2_tarski(k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))) = k6_subset_1(k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)),k1_xboole_0)
    | ~ spl2_77 ),
    inference(superposition,[],[f100,f4063])).

fof(f4063,plain,
    ( k1_xboole_0 = k6_subset_1(k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl2_77 ),
    inference(avatar_component_clause,[],[f4061])).

fof(f4066,plain,
    ( spl2_77
    | ~ spl2_6
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f4059,f939,f913,f145,f4061])).

fof(f4059,plain,
    ( k1_xboole_0 = k6_subset_1(k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl2_6
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(resolution,[],[f4047,f104])).

fof(f4047,plain,
    ( ! [X1] : r1_tarski(k6_subset_1(k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)),X1)
    | ~ spl2_6
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(resolution,[],[f4039,f106])).

fof(f4039,plain,
    ( ! [X12] : r1_tarski(k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)),k3_tarski(k2_tarski(u1_struct_0(sK0),X12)))
    | ~ spl2_6
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(resolution,[],[f3987,f106])).

fof(f4064,plain,
    ( spl2_77
    | ~ spl2_6
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f4057,f939,f913,f145,f4061])).

fof(f4057,plain,
    ( k1_xboole_0 = k6_subset_1(k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ spl2_6
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(resolution,[],[f4047,f168])).

fof(f3848,plain,
    ( spl2_76
    | ~ spl2_72 ),
    inference(avatar_split_clause,[],[f3843,f3781,f3845])).

fof(f3845,plain,
    ( spl2_76
  <=> k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).

fof(f3781,plain,
    ( spl2_72
  <=> k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).

fof(f3843,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))))
    | ~ spl2_72 ),
    inference(forward_demodulation,[],[f3834,f98])).

fof(f3834,plain,
    ( k6_subset_1(k2_tops_1(sK0,sK1),k1_xboole_0) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))))
    | ~ spl2_72 ),
    inference(superposition,[],[f100,f3783])).

fof(f3783,plain,
    ( k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_72 ),
    inference(avatar_component_clause,[],[f3781])).

fof(f3811,plain,
    ( spl2_74
    | ~ spl2_75
    | ~ spl2_66 ),
    inference(avatar_split_clause,[],[f3794,f3670,f3808,f3804])).

fof(f3804,plain,
    ( spl2_74
  <=> k1_xboole_0 = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).

fof(f3808,plain,
    ( spl2_75
  <=> r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).

fof(f3670,plain,
    ( spl2_66
  <=> k2_tops_1(sK0,sK1) = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).

fof(f3794,plain,
    ( ~ r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | k1_xboole_0 = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))
    | ~ spl2_66 ),
    inference(superposition,[],[f104,f3672])).

fof(f3672,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_66 ),
    inference(avatar_component_clause,[],[f3670])).

fof(f3802,plain,
    ( spl2_73
    | ~ spl2_55
    | ~ spl2_66 ),
    inference(avatar_split_clause,[],[f3797,f3670,f3367,f3799])).

fof(f3799,plain,
    ( spl2_73
  <=> k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).

fof(f3797,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))
    | ~ spl2_55
    | ~ spl2_66 ),
    inference(forward_demodulation,[],[f3792,f3369])).

fof(f3792,plain,
    ( k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))
    | ~ spl2_66 ),
    inference(superposition,[],[f100,f3672])).

fof(f3786,plain,
    ( spl2_72
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f3779,f2833,f1658,f939,f3781])).

fof(f3779,plain,
    ( k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_48 ),
    inference(resolution,[],[f3571,f104])).

fof(f3571,plain,
    ( ! [X4] : r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))),X4)
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_48 ),
    inference(resolution,[],[f3105,f1752])).

fof(f1752,plain,
    ( ! [X0] : r1_tarski(sK1,k3_tarski(k2_tarski(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),X0)))
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(superposition,[],[f1696,f77])).

fof(f1696,plain,
    ( ! [X0] : r1_tarski(sK1,k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))))
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(resolution,[],[f1687,f107])).

fof(f3784,plain,
    ( spl2_72
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f3777,f2833,f1658,f939,f3781])).

fof(f3777,plain,
    ( k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_48 ),
    inference(resolution,[],[f3571,f168])).

fof(f3727,plain,
    ( spl2_71
    | ~ spl2_21
    | ~ spl2_55 ),
    inference(avatar_split_clause,[],[f3722,f3367,f1658,f3724])).

fof(f3724,plain,
    ( spl2_71
  <=> r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).

fof(f3722,plain,
    ( r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_21
    | ~ spl2_55 ),
    inference(resolution,[],[f3659,f1660])).

fof(f3718,plain,
    ( spl2_70
    | ~ spl2_60
    | ~ spl2_68 ),
    inference(avatar_split_clause,[],[f3713,f3680,f3399,f3715])).

fof(f3715,plain,
    ( spl2_70
  <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).

fof(f3713,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ spl2_60
    | ~ spl2_68 ),
    inference(forward_demodulation,[],[f3708,f3401])).

fof(f3708,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))
    | ~ spl2_68 ),
    inference(resolution,[],[f3682,f134])).

fof(f3688,plain,
    ( spl2_69
    | ~ spl2_55 ),
    inference(avatar_split_clause,[],[f3662,f3367,f3685])).

fof(f3685,plain,
    ( spl2_69
  <=> r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).

fof(f3662,plain,
    ( r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl2_55 ),
    inference(superposition,[],[f99,f3369])).

fof(f3683,plain,
    ( spl2_68
    | ~ spl2_55 ),
    inference(avatar_split_clause,[],[f3661,f3367,f3680])).

fof(f3661,plain,
    ( m1_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_55 ),
    inference(superposition,[],[f76,f3369])).

fof(f3678,plain,
    ( spl2_51
    | ~ spl2_67
    | ~ spl2_55 ),
    inference(avatar_split_clause,[],[f3660,f3367,f3675,f3116])).

fof(f3675,plain,
    ( spl2_67
  <=> r1_tarski(k2_tops_1(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).

fof(f3660,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | k1_xboole_0 = k2_tops_1(sK0,sK1)
    | ~ spl2_55 ),
    inference(superposition,[],[f104,f3369])).

fof(f3673,plain,
    ( spl2_66
    | ~ spl2_54
    | ~ spl2_55 ),
    inference(avatar_split_clause,[],[f3668,f3367,f3271,f3670])).

fof(f3271,plain,
    ( spl2_54
  <=> k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f3668,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_54
    | ~ spl2_55 ),
    inference(forward_demodulation,[],[f3658,f3273])).

fof(f3273,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f3271])).

fof(f3658,plain,
    ( k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_55 ),
    inference(superposition,[],[f100,f3369])).

fof(f3667,plain,
    ( ~ spl2_65
    | ~ spl2_52
    | ~ spl2_55 ),
    inference(avatar_split_clause,[],[f3656,f3367,f3121,f3664])).

fof(f3664,plain,
    ( spl2_65
  <=> r1_tarski(sK1,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).

fof(f3656,plain,
    ( ~ r1_tarski(sK1,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_52
    | ~ spl2_55 ),
    inference(superposition,[],[f3122,f3369])).

fof(f3631,plain,
    ( spl2_64
    | ~ spl2_63 ),
    inference(avatar_split_clause,[],[f3626,f3602,f3628])).

fof(f3628,plain,
    ( spl2_64
  <=> k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).

fof(f3602,plain,
    ( spl2_63
  <=> k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).

fof(f3626,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))))
    | ~ spl2_63 ),
    inference(forward_demodulation,[],[f3618,f98])).

fof(f3618,plain,
    ( k6_subset_1(k2_tops_1(sK0,sK1),k1_xboole_0) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))))
    | ~ spl2_63 ),
    inference(superposition,[],[f100,f3604])).

fof(f3604,plain,
    ( k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))
    | ~ spl2_63 ),
    inference(avatar_component_clause,[],[f3602])).

fof(f3607,plain,
    ( spl2_63
    | ~ spl2_13
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f3600,f2833,f1658,f939,f895,f3602])).

fof(f3600,plain,
    ( k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))
    | ~ spl2_13
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_48 ),
    inference(resolution,[],[f3572,f104])).

fof(f3572,plain,
    ( ! [X5] : r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))),X5)
    | ~ spl2_13
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_48 ),
    inference(resolution,[],[f3105,f2476])).

fof(f2476,plain,
    ( ! [X0] : r1_tarski(sK1,k3_tarski(k2_tarski(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),X0)))
    | ~ spl2_13
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(superposition,[],[f2463,f77])).

fof(f2463,plain,
    ( ! [X0] : r1_tarski(sK1,k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))))
    | ~ spl2_13
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(resolution,[],[f2452,f107])).

fof(f2452,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(sK1,X0),k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))
    | ~ spl2_13
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(resolution,[],[f2446,f107])).

fof(f3605,plain,
    ( spl2_63
    | ~ spl2_13
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f3598,f2833,f1658,f939,f895,f3602])).

fof(f3598,plain,
    ( k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))
    | ~ spl2_13
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_48 ),
    inference(resolution,[],[f3572,f168])).

fof(f3477,plain,
    ( ~ spl2_4
    | spl2_62
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f3473,f130,f3475,f125])).

fof(f130,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f3473,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) != X0
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_5 ),
    inference(resolution,[],[f73,f132])).

fof(f132,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f130])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f3408,plain,
    ( spl2_61
    | ~ spl2_57
    | ~ spl2_58 ),
    inference(avatar_split_clause,[],[f3403,f3388,f3382,f3405])).

fof(f3405,plain,
    ( spl2_61
  <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).

fof(f3382,plain,
    ( spl2_57
  <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f3403,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_57
    | ~ spl2_58 ),
    inference(forward_demodulation,[],[f3384,f3390])).

fof(f3384,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_57 ),
    inference(avatar_component_clause,[],[f3382])).

fof(f3402,plain,
    ( spl2_60
    | ~ spl2_58
    | ~ spl2_59 ),
    inference(avatar_split_clause,[],[f3397,f3393,f3388,f3399])).

fof(f3393,plain,
    ( spl2_59
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).

fof(f3397,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_58
    | ~ spl2_59 ),
    inference(backward_demodulation,[],[f3395,f3390])).

fof(f3395,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_59 ),
    inference(avatar_component_clause,[],[f3393])).

fof(f3396,plain,
    ( spl2_59
    | ~ spl2_56 ),
    inference(avatar_split_clause,[],[f3379,f3372,f3393])).

fof(f3379,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_56 ),
    inference(resolution,[],[f3374,f86])).

fof(f3391,plain,
    ( spl2_58
    | ~ spl2_55
    | ~ spl2_56 ),
    inference(avatar_split_clause,[],[f3386,f3372,f3367,f3388])).

fof(f3386,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))
    | ~ spl2_55
    | ~ spl2_56 ),
    inference(forward_demodulation,[],[f3378,f3369])).

fof(f3378,plain,
    ( k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))
    | ~ spl2_56 ),
    inference(resolution,[],[f3374,f103])).

fof(f3385,plain,
    ( spl2_57
    | ~ spl2_56 ),
    inference(avatar_split_clause,[],[f3376,f3372,f3382])).

fof(f3376,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_56 ),
    inference(resolution,[],[f3374,f134])).

fof(f3375,plain,
    ( spl2_56
    | ~ spl2_54 ),
    inference(avatar_split_clause,[],[f3363,f3271,f3372])).

fof(f3363,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_54 ),
    inference(superposition,[],[f163,f3273])).

fof(f3370,plain,
    ( spl2_55
    | ~ spl2_54 ),
    inference(avatar_split_clause,[],[f3361,f3271,f3367])).

fof(f3361,plain,
    ( k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))
    | ~ spl2_54 ),
    inference(superposition,[],[f102,f3273])).

fof(f3274,plain,
    ( spl2_54
    | ~ spl2_53 ),
    inference(avatar_split_clause,[],[f3269,f3252,f3271])).

fof(f3252,plain,
    ( spl2_53
  <=> k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f3269,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))
    | ~ spl2_53 ),
    inference(forward_demodulation,[],[f3268,f77])).

fof(f3268,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)))
    | ~ spl2_53 ),
    inference(forward_demodulation,[],[f3263,f98])).

fof(f3263,plain,
    ( k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))) = k6_subset_1(k2_tops_1(sK0,sK1),k1_xboole_0)
    | ~ spl2_53 ),
    inference(superposition,[],[f100,f3254])).

fof(f3254,plain,
    ( k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_53 ),
    inference(avatar_component_clause,[],[f3252])).

fof(f3257,plain,
    ( spl2_53
    | ~ spl2_16
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f3250,f2833,f939,f3252])).

fof(f3250,plain,
    ( k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_16
    | ~ spl2_48 ),
    inference(resolution,[],[f3238,f104])).

fof(f3238,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),u1_struct_0(sK0)),X0)
    | ~ spl2_16
    | ~ spl2_48 ),
    inference(resolution,[],[f3234,f106])).

fof(f3234,plain,
    ( ! [X1] : r1_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(u1_struct_0(sK0),X1)))
    | ~ spl2_16
    | ~ spl2_48 ),
    inference(superposition,[],[f3144,f171])).

fof(f3144,plain,
    ( ! [X2,X1] : r1_tarski(k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X1)),k3_tarski(k2_tarski(u1_struct_0(sK0),X2)))
    | ~ spl2_16
    | ~ spl2_48 ),
    inference(resolution,[],[f3096,f1320])).

fof(f3096,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(sK1,X2)
        | r1_tarski(k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X3)),X2) )
    | ~ spl2_48 ),
    inference(resolution,[],[f3093,f95])).

fof(f3093,plain,
    ( ! [X0] : r1_tarski(k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X0)),sK1)
    | ~ spl2_48 ),
    inference(resolution,[],[f2835,f161])).

fof(f3255,plain,
    ( spl2_53
    | ~ spl2_16
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f3248,f2833,f939,f3252])).

fof(f3248,plain,
    ( k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_16
    | ~ spl2_48 ),
    inference(resolution,[],[f3238,f168])).

fof(f3223,plain,
    ( spl2_41
    | ~ spl2_40 ),
    inference(avatar_split_clause,[],[f3220,f2794,f2799])).

fof(f2799,plain,
    ( spl2_41
  <=> r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f2794,plain,
    ( spl2_40
  <=> r1_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f3220,plain,
    ( r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_40 ),
    inference(resolution,[],[f2796,f106])).

fof(f2796,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f2794])).

fof(f3168,plain,
    ( spl2_40
    | ~ spl2_21
    | ~ spl2_39 ),
    inference(avatar_split_clause,[],[f3167,f2789,f1658,f2794])).

fof(f2789,plain,
    ( spl2_39
  <=> r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f3167,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_21
    | ~ spl2_39 ),
    inference(resolution,[],[f3159,f1660])).

fof(f3159,plain,
    ( ! [X1] :
        ( ~ r1_tarski(u1_struct_0(sK0),X1)
        | r1_tarski(k2_tops_1(sK0,sK1),X1) )
    | ~ spl2_39 ),
    inference(resolution,[],[f2791,f95])).

fof(f2791,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f2789])).

fof(f3157,plain,
    ( spl2_39
    | ~ spl2_6
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f3156,f2833,f145,f2789])).

fof(f3156,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_6
    | ~ spl2_48 ),
    inference(superposition,[],[f3150,f171])).

fof(f3150,plain,
    ( ! [X13] : r1_tarski(k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X13)),u1_struct_0(sK0))
    | ~ spl2_6
    | ~ spl2_48 ),
    inference(resolution,[],[f3096,f147])).

fof(f3123,plain,
    ( spl2_51
    | spl2_52
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f3106,f2833,f3121,f3116])).

fof(f3106,plain,
    ( ! [X7] :
        ( ~ r1_tarski(sK1,k6_subset_1(X7,k2_tops_1(sK0,sK1)))
        | k1_xboole_0 = k2_tops_1(sK0,sK1) )
    | ~ spl2_48 ),
    inference(resolution,[],[f3094,f104])).

fof(f3119,plain,
    ( spl2_51
    | ~ spl2_50
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f3104,f2833,f3111,f3116])).

fof(f3111,plain,
    ( spl2_50
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f3104,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = k2_tops_1(sK0,sK1)
    | ~ spl2_48 ),
    inference(resolution,[],[f3094,f168])).

fof(f3114,plain,
    ( spl2_49
    | ~ spl2_50
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f3103,f2833,f3111,f3108])).

fof(f3108,plain,
    ( spl2_49
  <=> ! [X4] : k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f3103,plain,
    ( ! [X4] :
        ( ~ r1_tarski(sK1,k1_xboole_0)
        | k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),X4) )
    | ~ spl2_48 ),
    inference(resolution,[],[f3094,f184])).

fof(f3092,plain,
    ( spl2_48
    | ~ spl2_3
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f3091,f125,f110,f120,f2833])).

fof(f3091,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(resolution,[],[f3061,f111])).

fof(f111,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f3061,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k2_tops_1(sK0,X0),X0) )
    | ~ spl2_4 ),
    inference(resolution,[],[f74,f127])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f2836,plain,
    ( spl2_48
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f2787,f1773,f2833])).

fof(f2787,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_22 ),
    inference(superposition,[],[f99,f1774])).

fof(f2831,plain,
    ( spl2_47
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f2786,f1773,f2828])).

fof(f2786,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_22 ),
    inference(superposition,[],[f76,f1774])).

fof(f2826,plain,
    ( spl2_45
    | ~ spl2_46
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f2785,f1773,f2823,f2819])).

fof(f2785,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_22 ),
    inference(superposition,[],[f104,f1774])).

fof(f2817,plain,
    ( spl2_44
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f2783,f1773,f2814])).

fof(f2783,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_22 ),
    inference(superposition,[],[f100,f1774])).

fof(f2812,plain,
    ( spl2_43
    | ~ spl2_13
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f2775,f1773,f1658,f939,f895,f2809])).

fof(f2809,plain,
    ( spl2_43
  <=> r1_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f2775,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))
    | ~ spl2_13
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_22 ),
    inference(superposition,[],[f2452,f1774])).

fof(f2807,plain,
    ( spl2_42
    | ~ spl2_13
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f2774,f1773,f1658,f939,f895,f2804])).

fof(f2804,plain,
    ( spl2_42
  <=> r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f2774,plain,
    ( r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ spl2_13
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_22 ),
    inference(superposition,[],[f2446,f1774])).

fof(f2802,plain,
    ( spl2_41
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f2772,f1773,f1658,f939,f2799])).

fof(f2772,plain,
    ( r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_22 ),
    inference(superposition,[],[f1697,f1774])).

fof(f2797,plain,
    ( spl2_40
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f2771,f1773,f1658,f939,f2794])).

fof(f2771,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_16
    | ~ spl2_21
    | ~ spl2_22 ),
    inference(superposition,[],[f1687,f1774])).

fof(f2792,plain,
    ( spl2_39
    | ~ spl2_16
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f2764,f1773,f939,f2789])).

fof(f2764,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_16
    | ~ spl2_22 ),
    inference(superposition,[],[f1328,f1774])).

fof(f2763,plain,
    ( spl2_22
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f2761,f120,f114,f1773])).

fof(f2761,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f1769,f115])).

fof(f2762,plain,
    ( spl2_22
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f2760,f120,f114,f1773])).

fof(f2760,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f115,f1769])).

fof(f2759,plain,
    ( spl2_38
    | ~ spl2_3
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f2754,f125,f110,f120,f2756])).

fof(f2754,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(resolution,[],[f2753,f111])).

fof(f2753,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl2_4 ),
    inference(resolution,[],[f72,f127])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2608,plain,
    ( spl2_37
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f2592,f2585,f2605])).

fof(f2605,plain,
    ( spl2_37
  <=> sK1 = k3_subset_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),k3_subset_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f2585,plain,
    ( spl2_34
  <=> m1_subset_1(sK1,k1_zfmisc_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f2592,plain,
    ( sK1 = k3_subset_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),k3_subset_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),sK1))
    | ~ spl2_34 ),
    inference(resolution,[],[f2587,f86])).

fof(f2587,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f2585])).

fof(f2603,plain,
    ( spl2_36
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f2591,f2585,f2600])).

fof(f2600,plain,
    ( spl2_36
  <=> k3_subset_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),sK1) = k6_subset_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f2591,plain,
    ( k3_subset_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),sK1) = k6_subset_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),sK1)
    | ~ spl2_34 ),
    inference(resolution,[],[f2587,f103])).

fof(f2598,plain,
    ( spl2_35
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f2589,f2585,f2595])).

fof(f2595,plain,
    ( spl2_35
  <=> k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),sK1,k3_subset_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f2589,plain,
    ( k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),sK1,k3_subset_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),sK1))
    | ~ spl2_34 ),
    inference(resolution,[],[f2587,f134])).

fof(f2588,plain,
    ( spl2_34
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f2577,f2538,f2585])).

fof(f2538,plain,
    ( spl2_33
  <=> sK1 = k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f2577,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))))
    | ~ spl2_33 ),
    inference(superposition,[],[f202,f2540])).

fof(f2540,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))))
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f2538])).

fof(f202,plain,(
    ! [X0,X1] : m1_subset_1(k1_setfam_1(k2_tarski(X1,X0)),k1_zfmisc_1(X0)) ),
    inference(superposition,[],[f163,f77])).

fof(f2541,plain,
    ( spl2_33
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f2536,f2494,f2538])).

fof(f2494,plain,
    ( spl2_32
  <=> k1_xboole_0 = k6_subset_1(sK1,k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f2536,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))))
    | ~ spl2_32 ),
    inference(forward_demodulation,[],[f2517,f98])).

fof(f2517,plain,
    ( k6_subset_1(sK1,k1_xboole_0) = k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))))
    | ~ spl2_32 ),
    inference(superposition,[],[f100,f2496])).

fof(f2496,plain,
    ( k1_xboole_0 = k6_subset_1(sK1,k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f2494])).

fof(f2499,plain,
    ( spl2_32
    | ~ spl2_13
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f2492,f1658,f939,f895,f2494])).

fof(f2492,plain,
    ( k1_xboole_0 = k6_subset_1(sK1,k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))
    | ~ spl2_13
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(resolution,[],[f2480,f104])).

fof(f2480,plain,
    ( ! [X1] : r1_tarski(k6_subset_1(sK1,k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))),X1)
    | ~ spl2_13
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(resolution,[],[f2476,f106])).

fof(f2497,plain,
    ( spl2_32
    | ~ spl2_13
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f2490,f1658,f939,f895,f2494])).

fof(f2490,plain,
    ( k1_xboole_0 = k6_subset_1(sK1,k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))
    | ~ spl2_13
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(resolution,[],[f2480,f168])).

fof(f2450,plain,
    ( ~ spl2_3
    | spl2_31
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f2444,f1658,f939,f2448,f120])).

fof(f2448,plain,
    ( spl2_31
  <=> ! [X0] : r1_tarski(k6_subset_1(k6_subset_1(sK1,X0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f2444,plain,
    ( ! [X0] :
        ( r1_tarski(k6_subset_1(k6_subset_1(sK1,X0),sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(resolution,[],[f1706,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_subset_1(X1,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f84,f90])).

fof(f2113,plain,
    ( spl2_30
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f2093,f1859,f2110])).

fof(f2110,plain,
    ( spl2_30
  <=> k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))) = k4_subset_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),sK1,k3_subset_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f1859,plain,
    ( spl2_25
  <=> m1_subset_1(sK1,k1_zfmisc_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f2093,plain,
    ( k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))) = k4_subset_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),sK1,k3_subset_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),sK1))
    | ~ spl2_25 ),
    inference(resolution,[],[f134,f1861])).

fof(f1861,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))))
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f1859])).

fof(f2108,plain,
    ( spl2_29
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f2092,f120,f2105])).

fof(f2092,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_3 ),
    inference(resolution,[],[f134,f122])).

fof(f2101,plain,
    ( spl2_28
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f2096,f890,f523,f2098])).

fof(f2096,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1)
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f2088,f525])).

fof(f2088,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_12 ),
    inference(resolution,[],[f134,f892])).

fof(f1876,plain,
    ( spl2_27
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f1865,f1859,f1873])).

fof(f1873,plain,
    ( spl2_27
  <=> sK1 = k3_subset_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f1865,plain,
    ( sK1 = k3_subset_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),sK1))
    | ~ spl2_25 ),
    inference(resolution,[],[f1861,f86])).

fof(f1871,plain,
    ( spl2_26
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f1864,f1859,f1868])).

fof(f1868,plain,
    ( spl2_26
  <=> k3_subset_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),sK1) = k6_subset_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f1864,plain,
    ( k3_subset_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),sK1) = k6_subset_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),sK1)
    | ~ spl2_25 ),
    inference(resolution,[],[f1861,f103])).

fof(f1862,plain,
    ( spl2_25
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f1852,f1823,f1859])).

fof(f1823,plain,
    ( spl2_24
  <=> sK1 = k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f1852,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))))
    | ~ spl2_24 ),
    inference(superposition,[],[f202,f1825])).

fof(f1825,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f1823])).

fof(f1826,plain,
    ( spl2_24
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f1821,f1785,f1823])).

fof(f1785,plain,
    ( spl2_23
  <=> k1_xboole_0 = k6_subset_1(sK1,k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f1821,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))))
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f1805,f98])).

fof(f1805,plain,
    ( k6_subset_1(sK1,k1_xboole_0) = k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))))
    | ~ spl2_23 ),
    inference(superposition,[],[f100,f1787])).

fof(f1787,plain,
    ( k1_xboole_0 = k6_subset_1(sK1,k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f1785])).

fof(f1790,plain,
    ( spl2_23
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f1783,f1658,f939,f1785])).

fof(f1783,plain,
    ( k1_xboole_0 = k6_subset_1(sK1,k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(resolution,[],[f1755,f104])).

fof(f1755,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(sK1,k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))),X0)
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(resolution,[],[f1752,f106])).

fof(f1788,plain,
    ( spl2_23
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f1781,f1658,f939,f1785])).

fof(f1781,plain,
    ( k1_xboole_0 = k6_subset_1(sK1,k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_16
    | ~ spl2_21 ),
    inference(resolution,[],[f1755,f168])).

fof(f1776,plain,
    ( ~ spl2_22
    | spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f1771,f120,f114,f1773])).

fof(f1771,plain,
    ( k2_tops_1(sK0,sK1) != k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f116,f1769])).

fof(f116,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f1661,plain,
    ( spl2_21
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f1655,f865,f1658])).

fof(f1655,plain,
    ( r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_8 ),
    inference(resolution,[],[f1316,f135])).

fof(f1316,plain,
    ( ! [X9] :
        ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),X9)
        | r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(sK1,X9))) )
    | ~ spl2_8 ),
    inference(superposition,[],[f107,f867])).

fof(f997,plain,
    ( spl2_20
    | ~ spl2_15
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f992,f956,f913,f994])).

fof(f992,plain,
    ( sK1 = k5_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_15
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f987,f915])).

fof(f987,plain,
    ( k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_17 ),
    inference(superposition,[],[f102,f958])).

fof(f968,plain,
    ( spl2_18
    | ~ spl2_19
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f951,f913,f965,f961])).

fof(f961,plain,
    ( spl2_18
  <=> k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f951,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),sK1)
    | k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl2_15 ),
    inference(superposition,[],[f104,f915])).

fof(f959,plain,
    ( spl2_17
    | ~ spl2_8
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f954,f913,f865,f956])).

fof(f954,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_8
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f949,f867])).

fof(f949,plain,
    ( k6_subset_1(u1_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_15 ),
    inference(superposition,[],[f100,f915])).

fof(f942,plain,
    ( spl2_16
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f937,f907,f939])).

fof(f937,plain,
    ( k1_xboole_0 = k6_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f932,f287])).

fof(f932,plain,
    ( k6_subset_1(sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,sK1)
    | ~ spl2_14 ),
    inference(superposition,[],[f102,f909])).

fof(f916,plain,
    ( spl2_15
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f911,f907,f876,f913])).

fof(f876,plain,
    ( spl2_9
  <=> k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f911,plain,
    ( sK1 = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(backward_demodulation,[],[f878,f909])).

fof(f878,plain,
    ( k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f876])).

fof(f910,plain,
    ( spl2_14
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f905,f890,f876,f523,f907])).

fof(f905,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f904,f525])).

fof(f904,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))
    | ~ spl2_9
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f901,f878])).

fof(f901,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_12 ),
    inference(resolution,[],[f892,f103])).

fof(f898,plain,
    ( spl2_13
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f873,f865,f895])).

fof(f873,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl2_8 ),
    inference(superposition,[],[f99,f867])).

fof(f893,plain,
    ( spl2_12
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f872,f865,f890])).

fof(f872,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_8 ),
    inference(superposition,[],[f76,f867])).

fof(f888,plain,
    ( spl2_10
    | ~ spl2_11
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f871,f865,f885,f881])).

fof(f881,plain,
    ( spl2_10
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f871,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | k1_xboole_0 = sK1
    | ~ spl2_8 ),
    inference(superposition,[],[f104,f867])).

fof(f879,plain,
    ( spl2_9
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f874,f865,f876])).

fof(f874,plain,
    ( k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f869,f77])).

fof(f869,plain,
    ( k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)) = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_8 ),
    inference(superposition,[],[f100,f867])).

fof(f868,plain,
    ( spl2_8
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f854,f120,f865])).

fof(f854,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k6_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl2_3 ),
    inference(resolution,[],[f103,f122])).

fof(f526,plain,
    ( spl2_7
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f521,f120,f523])).

fof(f521,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_3 ),
    inference(resolution,[],[f86,f122])).

fof(f148,plain,
    ( spl2_6
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f141,f120,f145])).

fof(f141,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_3 ),
    inference(resolution,[],[f90,f122])).

fof(f133,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f61,f130])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f56,f58,f57])).

fof(f57,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f128,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f62,f125])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f123,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f63,f120])).

fof(f63,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f59])).

fof(f118,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f64,f114,f110])).

fof(f64,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f117,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f65,f114,f110])).

fof(f65,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:00:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.43  % (7529)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.47  % (7521)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (7522)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (7527)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (7524)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (7525)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (7523)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (7526)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (7532)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (7528)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (7533)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (7530)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (7534)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (7520)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (7536)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.50  % (7537)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (7535)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.50  % (7531)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 5.28/1.02  % (7524)Time limit reached!
% 5.28/1.02  % (7524)------------------------------
% 5.28/1.02  % (7524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.28/1.02  % (7524)Termination reason: Time limit
% 5.28/1.02  
% 5.28/1.02  % (7524)Memory used [KB]: 12025
% 5.28/1.02  % (7524)Time elapsed: 0.614 s
% 5.28/1.02  % (7524)------------------------------
% 5.28/1.02  % (7524)------------------------------
% 12.43/1.93  % (7525)Time limit reached!
% 12.43/1.93  % (7525)------------------------------
% 12.43/1.93  % (7525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.43/1.93  % (7525)Termination reason: Time limit
% 12.43/1.93  
% 12.43/1.93  % (7525)Memory used [KB]: 29423
% 12.43/1.93  % (7525)Time elapsed: 1.523 s
% 12.43/1.93  % (7525)------------------------------
% 12.43/1.93  % (7525)------------------------------
% 12.95/1.98  % (7526)Time limit reached!
% 12.95/1.98  % (7526)------------------------------
% 12.95/1.98  % (7526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.95/1.98  % (7526)Termination reason: Time limit
% 12.95/1.98  % (7526)Termination phase: Saturation
% 12.95/1.98  
% 12.95/1.98  % (7526)Memory used [KB]: 29551
% 12.95/1.98  % (7526)Time elapsed: 1.500 s
% 12.95/1.98  % (7526)------------------------------
% 12.95/1.98  % (7526)------------------------------
% 12.95/2.03  % (7530)Refutation found. Thanks to Tanya!
% 12.95/2.03  % SZS status Theorem for theBenchmark
% 12.95/2.03  % SZS output start Proof for theBenchmark
% 12.95/2.03  fof(f18869,plain,(
% 12.95/2.03    $false),
% 12.95/2.03    inference(avatar_sat_refutation,[],[f117,f118,f123,f128,f133,f148,f526,f868,f879,f888,f893,f898,f910,f916,f942,f959,f968,f997,f1661,f1776,f1788,f1790,f1826,f1862,f1871,f1876,f2101,f2108,f2113,f2450,f2497,f2499,f2541,f2588,f2598,f2603,f2608,f2759,f2762,f2763,f2792,f2797,f2802,f2807,f2812,f2817,f2826,f2831,f2836,f3092,f3114,f3119,f3123,f3157,f3168,f3223,f3255,f3257,f3274,f3370,f3375,f3385,f3391,f3396,f3402,f3408,f3477,f3605,f3607,f3631,f3667,f3673,f3678,f3683,f3688,f3718,f3727,f3784,f3786,f3802,f3811,f3848,f4064,f4066,f4083,f4331,f4333,f4350,f4435,f4441,f4443,f4449,f4455,f4456,f4468,f4472,f4477,f4482,f4485,f4490,f4504,f4509,f4514,f4519,f4534,f4552,f4620,f4629,f4634,f4639,f4661,f4666,f4672,f4678,f4683,f4688,f4693,f4797,f4802,f4877,f4915,f4922,f4929,f4935,f4955,f4961,f4980,f4985,f4990,f4995,f5000,f5005,f5010,f5015,f5020,f5072,f5081,f5179,f5181,f5225,f5269,f5271,f5388,f5390,f5425,f5431,f5437,f5443,f5449,f5455,f5460,f5465,f5627,f5628,f5639,f5645,f5650,f5656,f5662,f5945,f5951,f5957,f5962,f5968,f5974,f5979,f5985,f5991,f6003,f6009,f6221,f6228,f6229,f6235,f6243,f6248,f6253,f6283,f6288,f6293,f6298,f6303,f6305,f6310,f6315,f6320,f6321,f6327,f6329,f6334,f6340,f6354,f6373,f6377,f6426,f6428,f6433,f6438,f6443,f6448,f6450,f6455,f6460,f6489,f6496,f6553,f6693,f6699,f6714,f6719,f6724,f6729,f6734,f6739,f6744,f6760,f6761,f6766,f6825,f6832,f6846,f7071,f7076,f7081,f7086,f7091,f7096,f7101,f7106,f7111,f7116,f7121,f7126,f7131,f7136,f7141,f7146,f7151,f7156,f7312,f7314,f7347,f7485,f7486,f7689,f7704,f7709,f7979,f7981,f8012,f8210,f8225,f8230,f10402,f10521,f10533,f10538,f10562,f10569,f10577,f10582,f10587,f10907,f10910,f11520,f12120,f12137,f12142,f12147,f12802,f13465,f13470,f13475,f13481,f14108,f14111,f14174,f15046,f15353,f15357,f15358,f15362,f15451,f15454,f15461,f15475,f16791,f16793,f16796,f16829,f16832,f16840,f17146,f17157,f17162,f17169,f17175,f17184,f17189,f17194,f17199,f17401,f17410,f17465,f17476,f17481,f17488,f17494,f17503,f17508,f17513,f17518,f17538,f17767,f17773,f17805,f17810,f17815,f17846,f17851,f17856,f17861,f17873,f17878,f17883,f18077,f18085,f18086,f18090,f18237,f18239,f18245,f18338,f18340,f18343,f18385,f18388,f18396,f18433,f18438,f18635,f18662,f18667,f18672,f18677,f18734,f18739,f18744,f18749,f18754,f18759,f18847,f18865,f18868])).
% 12.95/2.03  fof(f18868,plain,(
% 12.95/2.03    spl2_302 | ~spl2_314),
% 12.95/2.03    inference(avatar_split_clause,[],[f18846,f18632,f18070])).
% 12.95/2.03  fof(f18070,plain,(
% 12.95/2.03    spl2_302 <=> k1_xboole_0 = k6_subset_1(sK1,k2_pre_topc(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_302])])).
% 12.95/2.03  fof(f18632,plain,(
% 12.95/2.03    spl2_314 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_314])])).
% 12.95/2.03  fof(f18846,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_314),
% 12.95/2.03    inference(resolution,[],[f18821,f104])).
% 12.95/2.03  fof(f104,plain,(
% 12.95/2.03    ( ! [X0,X1] : (~r1_tarski(X0,k6_subset_1(X1,X0)) | k1_xboole_0 = X0) )),
% 12.95/2.03    inference(definition_unfolding,[],[f88,f78])).
% 12.95/2.03  fof(f78,plain,(
% 12.95/2.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 12.95/2.03    inference(cnf_transformation,[],[f19])).
% 12.95/2.03  fof(f19,axiom,(
% 12.95/2.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 12.95/2.03  fof(f88,plain,(
% 12.95/2.03    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 12.95/2.03    inference(cnf_transformation,[],[f45])).
% 12.95/2.03  fof(f45,plain,(
% 12.95/2.03    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 12.95/2.03    inference(ennf_transformation,[],[f5])).
% 12.95/2.03  fof(f5,axiom,(
% 12.95/2.03    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 12.95/2.03  fof(f18821,plain,(
% 12.95/2.03    ( ! [X37] : (r1_tarski(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),X37)) ) | ~spl2_314),
% 12.95/2.03    inference(resolution,[],[f18776,f1041])).
% 12.95/2.03  fof(f1041,plain,(
% 12.95/2.03    ( ! [X2,X0,X1] : (~r1_tarski(X2,k3_tarski(k2_tarski(X1,X0))) | r1_tarski(k6_subset_1(X2,X0),X1)) )),
% 12.95/2.03    inference(superposition,[],[f106,f77])).
% 12.95/2.03  fof(f77,plain,(
% 12.95/2.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 12.95/2.03    inference(cnf_transformation,[],[f11])).
% 12.95/2.03  fof(f11,axiom,(
% 12.95/2.03    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 12.95/2.03  fof(f106,plain,(
% 12.95/2.03    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 12.95/2.03    inference(definition_unfolding,[],[f93,f78,f80])).
% 12.95/2.03  fof(f80,plain,(
% 12.95/2.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 12.95/2.03    inference(cnf_transformation,[],[f12])).
% 12.95/2.03  fof(f12,axiom,(
% 12.95/2.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 12.95/2.03  fof(f93,plain,(
% 12.95/2.03    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 12.95/2.03    inference(cnf_transformation,[],[f49])).
% 12.95/2.03  fof(f49,plain,(
% 12.95/2.03    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 12.95/2.03    inference(ennf_transformation,[],[f7])).
% 12.95/2.03  fof(f7,axiom,(
% 12.95/2.03    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 12.95/2.03  fof(f18776,plain,(
% 12.95/2.03    ( ! [X0] : (r1_tarski(sK1,k3_tarski(k2_tarski(X0,k2_pre_topc(sK0,sK1))))) ) | ~spl2_314),
% 12.95/2.03    inference(resolution,[],[f18775,f107])).
% 12.95/2.03  fof(f107,plain,(
% 12.95/2.03    ( ! [X2,X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),X2) | r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 12.95/2.03    inference(definition_unfolding,[],[f94,f80,f78])).
% 12.95/2.03  fof(f94,plain,(
% 12.95/2.03    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 12.95/2.03    inference(cnf_transformation,[],[f50])).
% 12.95/2.03  fof(f50,plain,(
% 12.95/2.03    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 12.95/2.03    inference(ennf_transformation,[],[f8])).
% 12.95/2.03  fof(f8,axiom,(
% 12.95/2.03    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 12.95/2.03  fof(f18775,plain,(
% 12.95/2.03    ( ! [X2] : (r1_tarski(k6_subset_1(sK1,X2),k2_pre_topc(sK0,sK1))) ) | ~spl2_314),
% 12.95/2.03    inference(superposition,[],[f18655,f863])).
% 12.95/2.03  fof(f863,plain,(
% 12.95/2.03    ( ! [X2,X1] : (k6_subset_1(X1,X2) = k1_setfam_1(k2_tarski(X1,k6_subset_1(X1,X2)))) )),
% 12.95/2.03    inference(backward_demodulation,[],[f160,f862])).
% 12.95/2.03  fof(f862,plain,(
% 12.95/2.03    ( ! [X8,X9] : (k6_subset_1(X8,X9) = k6_subset_1(X8,k1_setfam_1(k2_tarski(X8,X9)))) )),
% 12.95/2.03    inference(forward_demodulation,[],[f852,f860])).
% 12.95/2.03  fof(f860,plain,(
% 12.95/2.03    ( ! [X6,X7] : (k6_subset_1(X6,X7) = k3_subset_1(X6,k1_setfam_1(k2_tarski(X6,X7)))) )),
% 12.95/2.03    inference(backward_demodulation,[],[f518,f859])).
% 12.95/2.03  fof(f859,plain,(
% 12.95/2.03    ( ! [X6,X7] : (k3_subset_1(X6,k6_subset_1(X6,X7)) = k1_setfam_1(k2_tarski(X6,X7))) )),
% 12.95/2.03    inference(forward_demodulation,[],[f851,f100])).
% 12.95/2.03  fof(f100,plain,(
% 12.95/2.03    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 12.95/2.03    inference(definition_unfolding,[],[f81,f79,f78,f78])).
% 12.95/2.03  fof(f79,plain,(
% 12.95/2.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 12.95/2.03    inference(cnf_transformation,[],[f22])).
% 12.95/2.03  fof(f22,axiom,(
% 12.95/2.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 12.95/2.03  fof(f81,plain,(
% 12.95/2.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 12.95/2.03    inference(cnf_transformation,[],[f9])).
% 12.95/2.03  fof(f9,axiom,(
% 12.95/2.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 12.95/2.03  fof(f851,plain,(
% 12.95/2.03    ( ! [X6,X7] : (k3_subset_1(X6,k6_subset_1(X6,X7)) = k6_subset_1(X6,k6_subset_1(X6,X7))) )),
% 12.95/2.03    inference(resolution,[],[f103,f76])).
% 12.95/2.03  fof(f76,plain,(
% 12.95/2.03    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 12.95/2.03    inference(cnf_transformation,[],[f16])).
% 12.95/2.03  fof(f16,axiom,(
% 12.95/2.03    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 12.95/2.03  fof(f103,plain,(
% 12.95/2.03    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k6_subset_1(X0,X1)) )),
% 12.95/2.03    inference(definition_unfolding,[],[f85,f78])).
% 12.95/2.03  fof(f85,plain,(
% 12.95/2.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 12.95/2.03    inference(cnf_transformation,[],[f42])).
% 12.95/2.03  fof(f42,plain,(
% 12.95/2.03    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 12.95/2.03    inference(ennf_transformation,[],[f14])).
% 12.95/2.03  fof(f14,axiom,(
% 12.95/2.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 12.95/2.03  fof(f518,plain,(
% 12.95/2.03    ( ! [X6,X7] : (k6_subset_1(X6,X7) = k3_subset_1(X6,k3_subset_1(X6,k6_subset_1(X6,X7)))) )),
% 12.95/2.03    inference(resolution,[],[f86,f76])).
% 12.95/2.03  fof(f86,plain,(
% 12.95/2.03    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 12.95/2.03    inference(cnf_transformation,[],[f43])).
% 12.95/2.03  fof(f43,plain,(
% 12.95/2.03    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 12.95/2.03    inference(ennf_transformation,[],[f17])).
% 12.95/2.03  fof(f17,axiom,(
% 12.95/2.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 12.95/2.03  fof(f852,plain,(
% 12.95/2.03    ( ! [X8,X9] : (k3_subset_1(X8,k1_setfam_1(k2_tarski(X8,X9))) = k6_subset_1(X8,k1_setfam_1(k2_tarski(X8,X9)))) )),
% 12.95/2.03    inference(resolution,[],[f103,f163])).
% 12.95/2.03  fof(f163,plain,(
% 12.95/2.03    ( ! [X6,X5] : (m1_subset_1(k1_setfam_1(k2_tarski(X5,X6)),k1_zfmisc_1(X5))) )),
% 12.95/2.03    inference(superposition,[],[f76,f100])).
% 12.95/2.03  fof(f160,plain,(
% 12.95/2.03    ( ! [X2,X1] : (k1_setfam_1(k2_tarski(X1,k6_subset_1(X1,X2))) = k6_subset_1(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 12.95/2.03    inference(superposition,[],[f100,f100])).
% 12.95/2.03  fof(f18655,plain,(
% 12.95/2.03    ( ! [X21] : (r1_tarski(k1_setfam_1(k2_tarski(sK1,X21)),k2_pre_topc(sK0,sK1))) ) | ~spl2_314),
% 12.95/2.03    inference(resolution,[],[f18634,f161])).
% 12.95/2.03  fof(f161,plain,(
% 12.95/2.03    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2)) )),
% 12.95/2.03    inference(superposition,[],[f151,f100])).
% 12.95/2.03  fof(f151,plain,(
% 12.95/2.03    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 12.95/2.03    inference(resolution,[],[f95,f99])).
% 12.95/2.03  fof(f99,plain,(
% 12.95/2.03    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 12.95/2.03    inference(definition_unfolding,[],[f75,f78])).
% 12.95/2.03  fof(f75,plain,(
% 12.95/2.03    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 12.95/2.03    inference(cnf_transformation,[],[f4])).
% 12.95/2.03  fof(f4,axiom,(
% 12.95/2.03    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 12.95/2.03  fof(f95,plain,(
% 12.95/2.03    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 12.95/2.03    inference(cnf_transformation,[],[f52])).
% 12.95/2.03  fof(f52,plain,(
% 12.95/2.03    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 12.95/2.03    inference(flattening,[],[f51])).
% 12.95/2.03  fof(f51,plain,(
% 12.95/2.03    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 12.95/2.03    inference(ennf_transformation,[],[f2])).
% 12.95/2.03  fof(f2,axiom,(
% 12.95/2.03    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 12.95/2.03  fof(f18634,plain,(
% 12.95/2.03    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_314),
% 12.95/2.03    inference(avatar_component_clause,[],[f18632])).
% 12.95/2.03  fof(f18865,plain,(
% 12.95/2.03    spl2_302 | ~spl2_314),
% 12.95/2.03    inference(avatar_split_clause,[],[f18843,f18632,f18070])).
% 12.95/2.03  fof(f18843,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_314),
% 12.95/2.03    inference(resolution,[],[f18821,f168])).
% 12.95/2.03  fof(f168,plain,(
% 12.95/2.03    ( ! [X3] : (~r1_tarski(X3,k1_xboole_0) | k1_xboole_0 = X3) )),
% 12.95/2.03    inference(superposition,[],[f104,f165])).
% 12.95/2.03  fof(f165,plain,(
% 12.95/2.03    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 12.95/2.03    inference(forward_demodulation,[],[f159,f97])).
% 12.95/2.03  fof(f97,plain,(
% 12.95/2.03    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 12.95/2.03    inference(definition_unfolding,[],[f67,f79])).
% 12.95/2.03  fof(f67,plain,(
% 12.95/2.03    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 12.95/2.03    inference(cnf_transformation,[],[f3])).
% 12.95/2.03  fof(f3,axiom,(
% 12.95/2.03    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 12.95/2.03  fof(f159,plain,(
% 12.95/2.03    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k6_subset_1(X0,X0)) )),
% 12.95/2.03    inference(superposition,[],[f100,f98])).
% 12.95/2.03  fof(f98,plain,(
% 12.95/2.03    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 12.95/2.03    inference(definition_unfolding,[],[f68,f78])).
% 12.95/2.03  fof(f68,plain,(
% 12.95/2.03    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.95/2.03    inference(cnf_transformation,[],[f6])).
% 12.95/2.03  fof(f6,axiom,(
% 12.95/2.03    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 12.95/2.03  fof(f18847,plain,(
% 12.95/2.03    spl2_302 | ~spl2_314),
% 12.95/2.03    inference(avatar_split_clause,[],[f18835,f18632,f18070])).
% 12.95/2.03  fof(f18835,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_314),
% 12.95/2.03    inference(resolution,[],[f18821,f162])).
% 12.95/2.03  fof(f162,plain,(
% 12.95/2.03    ( ! [X4,X3] : (~r1_tarski(k6_subset_1(X3,X4),k1_setfam_1(k2_tarski(X3,X4))) | k1_xboole_0 = k6_subset_1(X3,X4)) )),
% 12.95/2.03    inference(superposition,[],[f104,f100])).
% 12.95/2.03  fof(f18759,plain,(
% 12.95/2.03    spl2_324 | ~spl2_265 | ~spl2_317),
% 12.95/2.03    inference(avatar_split_clause,[],[f18723,f18669,f16826,f18756])).
% 12.95/2.03  fof(f18756,plain,(
% 12.95/2.03    spl2_324 <=> k3_subset_1(k2_pre_topc(sK0,sK1),sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_324])])).
% 12.95/2.03  fof(f16826,plain,(
% 12.95/2.03    spl2_265 <=> k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_265])])).
% 12.95/2.03  fof(f18669,plain,(
% 12.95/2.03    spl2_317 <=> k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_317])])).
% 12.95/2.03  fof(f18723,plain,(
% 12.95/2.03    k3_subset_1(k2_pre_topc(sK0,sK1),sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))) | (~spl2_265 | ~spl2_317)),
% 12.95/2.03    inference(backward_demodulation,[],[f16828,f18671])).
% 12.95/2.03  fof(f18671,plain,(
% 12.95/2.03    k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~spl2_317),
% 12.95/2.03    inference(avatar_component_clause,[],[f18669])).
% 12.95/2.03  fof(f16828,plain,(
% 12.95/2.03    k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1))) | ~spl2_265),
% 12.95/2.03    inference(avatar_component_clause,[],[f16826])).
% 12.95/2.03  fof(f18754,plain,(
% 12.95/2.03    spl2_323 | ~spl2_264 | ~spl2_317),
% 12.95/2.03    inference(avatar_split_clause,[],[f18722,f18669,f16788,f18751])).
% 12.95/2.03  fof(f18751,plain,(
% 12.95/2.03    spl2_323 <=> k1_xboole_0 = k6_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_323])])).
% 12.95/2.03  fof(f16788,plain,(
% 12.95/2.03    spl2_264 <=> k1_xboole_0 = k6_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_264])])).
% 12.95/2.03  fof(f18722,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) | (~spl2_264 | ~spl2_317)),
% 12.95/2.03    inference(backward_demodulation,[],[f16790,f18671])).
% 12.95/2.03  fof(f16790,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) | ~spl2_264),
% 12.95/2.03    inference(avatar_component_clause,[],[f16788])).
% 12.95/2.03  fof(f18749,plain,(
% 12.95/2.03    spl2_322 | ~spl2_246 | ~spl2_317),
% 12.95/2.03    inference(avatar_split_clause,[],[f18684,f18669,f12144,f18746])).
% 12.95/2.03  fof(f18746,plain,(
% 12.95/2.03    spl2_322 <=> k2_tops_1(sK0,sK1) = k4_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k3_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_322])])).
% 12.95/2.03  fof(f12144,plain,(
% 12.95/2.03    spl2_246 <=> k2_tops_1(sK0,sK1) = k4_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k3_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_246])])).
% 12.95/2.03  fof(f18684,plain,(
% 12.95/2.03    k2_tops_1(sK0,sK1) = k4_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k3_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))) | (~spl2_246 | ~spl2_317)),
% 12.95/2.03    inference(backward_demodulation,[],[f12146,f18671])).
% 12.95/2.03  fof(f12146,plain,(
% 12.95/2.03    k2_tops_1(sK0,sK1) = k4_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k3_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1))) | ~spl2_246),
% 12.95/2.03    inference(avatar_component_clause,[],[f12144])).
% 12.95/2.03  fof(f18744,plain,(
% 12.95/2.03    spl2_321 | ~spl2_235 | ~spl2_317),
% 12.95/2.03    inference(avatar_split_clause,[],[f18682,f18669,f10535,f18741])).
% 12.95/2.03  fof(f18741,plain,(
% 12.95/2.03    spl2_321 <=> k3_subset_1(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_321])])).
% 12.95/2.03  fof(f10535,plain,(
% 12.95/2.03    spl2_235 <=> k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_235])])).
% 12.95/2.03  fof(f18682,plain,(
% 12.95/2.03    k3_subset_1(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))) | (~spl2_235 | ~spl2_317)),
% 12.95/2.03    inference(backward_demodulation,[],[f10537,f18671])).
% 12.95/2.03  fof(f10537,plain,(
% 12.95/2.03    k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1))) | ~spl2_235),
% 12.95/2.03    inference(avatar_component_clause,[],[f10535])).
% 12.95/2.03  fof(f18739,plain,(
% 12.95/2.03    spl2_320 | ~spl2_234 | ~spl2_317),
% 12.95/2.03    inference(avatar_split_clause,[],[f18681,f18669,f10530,f18736])).
% 12.95/2.03  fof(f18736,plain,(
% 12.95/2.03    spl2_320 <=> k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) = k3_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_320])])).
% 12.95/2.03  fof(f10530,plain,(
% 12.95/2.03    spl2_234 <=> k6_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1)) = k3_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_234])])).
% 12.95/2.03  fof(f18681,plain,(
% 12.95/2.03    k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) = k3_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) | (~spl2_234 | ~spl2_317)),
% 12.95/2.03    inference(backward_demodulation,[],[f10532,f18671])).
% 12.95/2.03  fof(f10532,plain,(
% 12.95/2.03    k6_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1)) = k3_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1)) | ~spl2_234),
% 12.95/2.03    inference(avatar_component_clause,[],[f10530])).
% 12.95/2.03  fof(f18734,plain,(
% 12.95/2.03    spl2_319 | ~spl2_233 | ~spl2_317),
% 12.95/2.03    inference(avatar_split_clause,[],[f18678,f18669,f10518,f18731])).
% 12.95/2.03  fof(f18731,plain,(
% 12.95/2.03    spl2_319 <=> r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_319])])).
% 12.95/2.03  fof(f10518,plain,(
% 12.95/2.03    spl2_233 <=> r1_tarski(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_233])])).
% 12.95/2.03  fof(f18678,plain,(
% 12.95/2.03    r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) | (~spl2_233 | ~spl2_317)),
% 12.95/2.03    inference(backward_demodulation,[],[f10520,f18671])).
% 12.95/2.03  fof(f10520,plain,(
% 12.95/2.03    r1_tarski(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) | ~spl2_233),
% 12.95/2.03    inference(avatar_component_clause,[],[f10518])).
% 12.95/2.03  fof(f18677,plain,(
% 12.95/2.03    spl2_318 | ~spl2_314),
% 12.95/2.03    inference(avatar_split_clause,[],[f18654,f18632,f18674])).
% 12.95/2.03  fof(f18674,plain,(
% 12.95/2.03    spl2_318 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_318])])).
% 12.95/2.03  fof(f18654,plain,(
% 12.95/2.03    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) | ~spl2_314),
% 12.95/2.03    inference(resolution,[],[f18634,f515])).
% 12.95/2.03  fof(f515,plain,(
% 12.95/2.03    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k3_subset_1(X1,k3_subset_1(X1,X2)) = X2) )),
% 12.95/2.03    inference(resolution,[],[f86,f91])).
% 12.95/2.03  fof(f91,plain,(
% 12.95/2.03    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 12.95/2.03    inference(cnf_transformation,[],[f60])).
% 12.95/2.03  fof(f60,plain,(
% 12.95/2.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 12.95/2.03    inference(nnf_transformation,[],[f23])).
% 12.95/2.03  fof(f23,axiom,(
% 12.95/2.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 12.95/2.03  fof(f18672,plain,(
% 12.95/2.03    spl2_317 | ~spl2_314),
% 12.95/2.03    inference(avatar_split_clause,[],[f18653,f18632,f18669])).
% 12.95/2.03  fof(f18653,plain,(
% 12.95/2.03    k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~spl2_314),
% 12.95/2.03    inference(resolution,[],[f18634,f848])).
% 12.95/2.03  fof(f848,plain,(
% 12.95/2.03    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k6_subset_1(X1,X2) = k3_subset_1(X1,X2)) )),
% 12.95/2.03    inference(resolution,[],[f103,f91])).
% 12.95/2.03  fof(f18667,plain,(
% 12.95/2.03    spl2_316 | ~spl2_314),
% 12.95/2.03    inference(avatar_split_clause,[],[f18651,f18632,f18664])).
% 12.95/2.03  fof(f18664,plain,(
% 12.95/2.03    spl2_316 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_316])])).
% 12.95/2.03  fof(f18651,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) | ~spl2_314),
% 12.95/2.03    inference(resolution,[],[f18634,f2085])).
% 12.95/2.03  fof(f2085,plain,(
% 12.95/2.03    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = X1) )),
% 12.95/2.03    inference(resolution,[],[f134,f91])).
% 12.95/2.03  fof(f134,plain,(
% 12.95/2.03    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0) )),
% 12.95/2.03    inference(forward_demodulation,[],[f87,f66])).
% 12.95/2.03  fof(f66,plain,(
% 12.95/2.03    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 12.95/2.03    inference(cnf_transformation,[],[f13])).
% 12.95/2.03  fof(f13,axiom,(
% 12.95/2.03    ! [X0] : k2_subset_1(X0) = X0),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 12.95/2.03  fof(f87,plain,(
% 12.95/2.03    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 12.95/2.03    inference(cnf_transformation,[],[f44])).
% 12.95/2.03  fof(f44,plain,(
% 12.95/2.03    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 12.95/2.03    inference(ennf_transformation,[],[f21])).
% 12.95/2.03  fof(f21,axiom,(
% 12.95/2.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 12.95/2.03  fof(f18662,plain,(
% 12.95/2.03    spl2_315 | ~spl2_15 | ~spl2_202 | ~spl2_314),
% 12.95/2.03    inference(avatar_split_clause,[],[f18657,f18632,f6843,f913,f18659])).
% 12.95/2.03  fof(f18659,plain,(
% 12.95/2.03    spl2_315 <=> r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),sK1))))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_315])])).
% 12.95/2.03  fof(f913,plain,(
% 12.95/2.03    spl2_15 <=> sK1 = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 12.95/2.03  fof(f6843,plain,(
% 12.95/2.03    spl2_202 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1)),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_202])])).
% 12.95/2.03  fof(f18657,plain,(
% 12.95/2.03    r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),sK1)))) | (~spl2_15 | ~spl2_202 | ~spl2_314)),
% 12.95/2.03    inference(forward_demodulation,[],[f18648,f77])).
% 12.95/2.03  fof(f18648,plain,(
% 12.95/2.03    r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),k2_pre_topc(sK0,sK1)))) | (~spl2_15 | ~spl2_202 | ~spl2_314)),
% 12.95/2.03    inference(resolution,[],[f18634,f6902])).
% 12.95/2.03  fof(f6902,plain,(
% 12.95/2.03    ( ! [X10] : (~r1_tarski(sK1,X10) | r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),X10)))) ) | (~spl2_15 | ~spl2_202)),
% 12.95/2.03    inference(backward_demodulation,[],[f1317,f6845])).
% 12.95/2.03  fof(f6845,plain,(
% 12.95/2.03    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) | ~spl2_202),
% 12.95/2.03    inference(avatar_component_clause,[],[f6843])).
% 12.95/2.03  fof(f1317,plain,(
% 12.95/2.03    ( ! [X10] : (~r1_tarski(sK1,X10) | r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(k3_subset_1(u1_struct_0(sK0),sK1),X10)))) ) | ~spl2_15),
% 12.95/2.03    inference(superposition,[],[f107,f915])).
% 12.95/2.03  fof(f915,plain,(
% 12.95/2.03    sK1 = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_15),
% 12.95/2.03    inference(avatar_component_clause,[],[f913])).
% 12.95/2.03  fof(f18635,plain,(
% 12.95/2.03    spl2_314 | ~spl2_160 | ~spl2_223 | ~spl2_251),
% 12.95/2.03    inference(avatar_split_clause,[],[f18630,f13478,f7482,f6225,f18632])).
% 12.95/2.03  fof(f6225,plain,(
% 12.95/2.03    spl2_160 <=> k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_160])])).
% 12.95/2.03  fof(f7482,plain,(
% 12.95/2.03    spl2_223 <=> r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_223])])).
% 12.95/2.03  fof(f13478,plain,(
% 12.95/2.03    spl2_251 <=> k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_251])])).
% 12.95/2.03  fof(f18630,plain,(
% 12.95/2.03    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl2_160 | ~spl2_223 | ~spl2_251)),
% 12.95/2.03    inference(forward_demodulation,[],[f18629,f13480])).
% 12.95/2.03  fof(f13480,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) | ~spl2_251),
% 12.95/2.03    inference(avatar_component_clause,[],[f13478])).
% 12.95/2.03  fof(f18629,plain,(
% 12.95/2.03    r1_tarski(sK1,k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))) | (~spl2_160 | ~spl2_223)),
% 12.95/2.03    inference(forward_demodulation,[],[f18627,f77])).
% 12.95/2.03  fof(f18627,plain,(
% 12.95/2.03    r1_tarski(sK1,k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)))) | (~spl2_160 | ~spl2_223)),
% 12.95/2.03    inference(resolution,[],[f6273,f7484])).
% 12.95/2.03  fof(f7484,plain,(
% 12.95/2.03    r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~spl2_223),
% 12.95/2.03    inference(avatar_component_clause,[],[f7482])).
% 12.95/2.03  fof(f6273,plain,(
% 12.95/2.03    ( ! [X18] : (~r1_tarski(k1_tops_1(sK0,sK1),X18) | r1_tarski(sK1,k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),X18)))) ) | ~spl2_160),
% 12.95/2.03    inference(superposition,[],[f107,f6227])).
% 12.95/2.03  fof(f6227,plain,(
% 12.95/2.03    k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_160),
% 12.95/2.03    inference(avatar_component_clause,[],[f6225])).
% 12.95/2.03  fof(f18438,plain,(
% 12.95/2.03    spl2_313 | ~spl2_15 | ~spl2_202 | ~spl2_290),
% 12.95/2.03    inference(avatar_split_clause,[],[f18421,f17764,f6843,f913,f18435])).
% 12.95/2.03  fof(f18435,plain,(
% 12.95/2.03    spl2_313 <=> r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))))))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_313])])).
% 12.95/2.03  fof(f17764,plain,(
% 12.95/2.03    spl2_290 <=> r1_tarski(sK1,k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_290])])).
% 12.95/2.03  fof(f18421,plain,(
% 12.95/2.03    r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)))))) | (~spl2_15 | ~spl2_202 | ~spl2_290)),
% 12.95/2.03    inference(resolution,[],[f6902,f17766])).
% 12.95/2.03  fof(f17766,plain,(
% 12.95/2.03    r1_tarski(sK1,k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)))) | ~spl2_290),
% 12.95/2.03    inference(avatar_component_clause,[],[f17764])).
% 12.95/2.03  fof(f18433,plain,(
% 12.95/2.03    spl2_312 | ~spl2_15 | ~spl2_202 | ~spl2_291),
% 12.95/2.03    inference(avatar_split_clause,[],[f18420,f17770,f6843,f913,f18430])).
% 12.95/2.03  fof(f18430,plain,(
% 12.95/2.03    spl2_312 <=> r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))))))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_312])])).
% 12.95/2.03  fof(f17770,plain,(
% 12.95/2.03    spl2_291 <=> r1_tarski(sK1,k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_291])])).
% 12.95/2.03  fof(f18420,plain,(
% 12.95/2.03    r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))))) | (~spl2_15 | ~spl2_202 | ~spl2_291)),
% 12.95/2.03    inference(resolution,[],[f6902,f17772])).
% 12.95/2.03  fof(f17772,plain,(
% 12.95/2.03    r1_tarski(sK1,k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))) | ~spl2_291),
% 12.95/2.03    inference(avatar_component_clause,[],[f17770])).
% 12.95/2.03  fof(f18396,plain,(
% 12.95/2.03    spl2_311 | ~spl2_309),
% 12.95/2.03    inference(avatar_split_clause,[],[f18391,f18335,f18393])).
% 12.95/2.03  fof(f18393,plain,(
% 12.95/2.03    spl2_311 <=> k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) = k4_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_xboole_0,k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1)))))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_311])])).
% 12.95/2.03  fof(f18335,plain,(
% 12.95/2.03    spl2_309 <=> k1_xboole_0 = k6_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_309])])).
% 12.95/2.03  fof(f18391,plain,(
% 12.95/2.03    k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) = k4_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_xboole_0,k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1))))) | ~spl2_309),
% 12.95/2.03    inference(forward_demodulation,[],[f18375,f77])).
% 12.95/2.03  fof(f18375,plain,(
% 12.95/2.03    k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) = k4_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_xboole_0,k1_setfam_1(k2_tarski(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)))) | ~spl2_309),
% 12.95/2.03    inference(superposition,[],[f2102,f18337])).
% 12.95/2.03  fof(f18337,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) | ~spl2_309),
% 12.95/2.03    inference(avatar_component_clause,[],[f18335])).
% 12.95/2.03  fof(f2102,plain,(
% 12.95/2.03    ( ! [X6,X7] : (k4_subset_1(X6,k6_subset_1(X6,X7),k1_setfam_1(k2_tarski(X6,X7))) = X6) )),
% 12.95/2.03    inference(forward_demodulation,[],[f2089,f859])).
% 12.95/2.03  fof(f2089,plain,(
% 12.95/2.03    ( ! [X6,X7] : (k4_subset_1(X6,k6_subset_1(X6,X7),k3_subset_1(X6,k6_subset_1(X6,X7))) = X6) )),
% 12.95/2.03    inference(resolution,[],[f134,f76])).
% 12.95/2.03  fof(f18388,plain,(
% 12.95/2.03    spl2_310 | ~spl2_309),
% 12.95/2.03    inference(avatar_split_clause,[],[f18387,f18335,f18382])).
% 12.95/2.03  fof(f18382,plain,(
% 12.95/2.03    spl2_310 <=> k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) = k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1))))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_310])])).
% 12.95/2.03  fof(f18387,plain,(
% 12.95/2.03    k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) = k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1)))) | ~spl2_309),
% 12.95/2.03    inference(forward_demodulation,[],[f18386,f77])).
% 12.95/2.03  fof(f18386,plain,(
% 12.95/2.03    k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) = k1_setfam_1(k2_tarski(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))) | ~spl2_309),
% 12.95/2.03    inference(forward_demodulation,[],[f18371,f856])).
% 12.95/2.03  fof(f856,plain,(
% 12.95/2.03    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 12.95/2.03    inference(backward_demodulation,[],[f514,f855])).
% 12.95/2.03  fof(f855,plain,(
% 12.95/2.03    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 12.95/2.03    inference(forward_demodulation,[],[f847,f165])).
% 12.95/2.03  fof(f847,plain,(
% 12.95/2.03    ( ! [X0] : (k6_subset_1(X0,X0) = k3_subset_1(X0,X0)) )),
% 12.95/2.03    inference(resolution,[],[f103,f136])).
% 12.95/2.03  fof(f136,plain,(
% 12.95/2.03    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 12.95/2.03    inference(superposition,[],[f76,f98])).
% 12.95/2.03  fof(f514,plain,(
% 12.95/2.03    ( ! [X0] : (k3_subset_1(X0,k3_subset_1(X0,X0)) = X0) )),
% 12.95/2.03    inference(resolution,[],[f86,f136])).
% 12.95/2.03  fof(f18371,plain,(
% 12.95/2.03    k1_setfam_1(k2_tarski(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))) = k3_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_xboole_0) | ~spl2_309),
% 12.95/2.03    inference(superposition,[],[f859,f18337])).
% 12.95/2.03  fof(f18385,plain,(
% 12.95/2.03    spl2_310 | ~spl2_309),
% 12.95/2.03    inference(avatar_split_clause,[],[f18380,f18335,f18382])).
% 12.95/2.03  fof(f18380,plain,(
% 12.95/2.03    k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) = k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1)))) | ~spl2_309),
% 12.95/2.03    inference(forward_demodulation,[],[f18379,f98])).
% 12.95/2.03  fof(f18379,plain,(
% 12.95/2.03    k6_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_xboole_0) = k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1)))) | ~spl2_309),
% 12.95/2.03    inference(forward_demodulation,[],[f18366,f77])).
% 12.95/2.03  fof(f18366,plain,(
% 12.95/2.03    k6_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_xboole_0) = k1_setfam_1(k2_tarski(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))) | ~spl2_309),
% 12.95/2.03    inference(superposition,[],[f100,f18337])).
% 12.95/2.03  fof(f18343,plain,(
% 12.95/2.03    spl2_309 | ~spl2_295),
% 12.95/2.03    inference(avatar_split_clause,[],[f18333,f17843,f18335])).
% 12.95/2.03  fof(f17843,plain,(
% 12.95/2.03    spl2_295 <=> r1_tarski(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_295])])).
% 12.95/2.03  fof(f18333,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) | ~spl2_295),
% 12.95/2.03    inference(resolution,[],[f18311,f104])).
% 12.95/2.03  fof(f18311,plain,(
% 12.95/2.03    ( ! [X1] : (r1_tarski(k6_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)),X1)) ) | ~spl2_295),
% 12.95/2.03    inference(resolution,[],[f17997,f1041])).
% 12.95/2.03  fof(f17997,plain,(
% 12.95/2.03    ( ! [X0] : (r1_tarski(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k3_tarski(k2_tarski(X0,k1_tops_1(sK0,sK1))))) ) | ~spl2_295),
% 12.95/2.03    inference(resolution,[],[f17996,f107])).
% 12.95/2.03  fof(f17996,plain,(
% 12.95/2.03    ( ! [X0] : (r1_tarski(k6_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),X0),k1_tops_1(sK0,sK1))) ) | ~spl2_295),
% 12.95/2.03    inference(superposition,[],[f17867,f863])).
% 12.95/2.03  fof(f17867,plain,(
% 12.95/2.03    ( ! [X1] : (r1_tarski(k1_setfam_1(k2_tarski(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),X1)),k1_tops_1(sK0,sK1))) ) | ~spl2_295),
% 12.95/2.03    inference(resolution,[],[f17845,f161])).
% 12.95/2.03  fof(f17845,plain,(
% 12.95/2.03    r1_tarski(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) | ~spl2_295),
% 12.95/2.03    inference(avatar_component_clause,[],[f17843])).
% 12.95/2.03  fof(f18340,plain,(
% 12.95/2.03    spl2_309 | ~spl2_295),
% 12.95/2.03    inference(avatar_split_clause,[],[f18330,f17843,f18335])).
% 12.95/2.03  fof(f18330,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) | ~spl2_295),
% 12.95/2.03    inference(resolution,[],[f18311,f168])).
% 12.95/2.03  fof(f18338,plain,(
% 12.95/2.03    spl2_309 | ~spl2_295),
% 12.95/2.03    inference(avatar_split_clause,[],[f18322,f17843,f18335])).
% 12.95/2.03  fof(f18322,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) | ~spl2_295),
% 12.95/2.03    inference(resolution,[],[f18311,f162])).
% 12.95/2.03  fof(f18245,plain,(
% 12.95/2.03    spl2_308 | ~spl2_302),
% 12.95/2.03    inference(avatar_split_clause,[],[f18201,f18070,f18242])).
% 12.95/2.03  fof(f18242,plain,(
% 12.95/2.03    spl2_308 <=> sK1 = k4_subset_1(sK1,k1_xboole_0,k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1))))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_308])])).
% 12.95/2.03  fof(f18201,plain,(
% 12.95/2.03    sK1 = k4_subset_1(sK1,k1_xboole_0,k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))) | ~spl2_302),
% 12.95/2.03    inference(superposition,[],[f2102,f18072])).
% 12.95/2.03  fof(f18072,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_302),
% 12.95/2.03    inference(avatar_component_clause,[],[f18070])).
% 12.95/2.03  fof(f18239,plain,(
% 12.95/2.03    spl2_307 | ~spl2_302),
% 12.95/2.03    inference(avatar_split_clause,[],[f18238,f18070,f18234])).
% 12.95/2.03  fof(f18234,plain,(
% 12.95/2.03    spl2_307 <=> sK1 = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_307])])).
% 12.95/2.03  fof(f18238,plain,(
% 12.95/2.03    sK1 = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1))) | ~spl2_302),
% 12.95/2.03    inference(forward_demodulation,[],[f18197,f856])).
% 12.95/2.03  fof(f18197,plain,(
% 12.95/2.03    k3_subset_1(sK1,k1_xboole_0) = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1))) | ~spl2_302),
% 12.95/2.03    inference(superposition,[],[f859,f18072])).
% 12.95/2.03  fof(f18237,plain,(
% 12.95/2.03    spl2_307 | ~spl2_302),
% 12.95/2.03    inference(avatar_split_clause,[],[f18232,f18070,f18234])).
% 12.95/2.03  fof(f18232,plain,(
% 12.95/2.03    sK1 = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1))) | ~spl2_302),
% 12.95/2.03    inference(forward_demodulation,[],[f18192,f98])).
% 12.95/2.03  fof(f18192,plain,(
% 12.95/2.03    k6_subset_1(sK1,k1_xboole_0) = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1))) | ~spl2_302),
% 12.95/2.03    inference(superposition,[],[f100,f18072])).
% 12.95/2.03  fof(f18090,plain,(
% 12.95/2.03    spl2_302 | spl2_306 | ~spl2_295),
% 12.95/2.03    inference(avatar_split_clause,[],[f18068,f17843,f18088,f18070])).
% 12.95/2.03  fof(f18088,plain,(
% 12.95/2.03    spl2_306 <=> ! [X15] : ~r1_tarski(k1_tops_1(sK0,sK1),k6_subset_1(X15,k6_subset_1(sK1,k2_pre_topc(sK0,sK1))))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_306])])).
% 12.95/2.03  fof(f18068,plain,(
% 12.95/2.03    ( ! [X15] : (~r1_tarski(k1_tops_1(sK0,sK1),k6_subset_1(X15,k6_subset_1(sK1,k2_pre_topc(sK0,sK1)))) | k1_xboole_0 = k6_subset_1(sK1,k2_pre_topc(sK0,sK1))) ) | ~spl2_295),
% 12.95/2.03    inference(resolution,[],[f17868,f104])).
% 12.95/2.03  fof(f17868,plain,(
% 12.95/2.03    ( ! [X2] : (r1_tarski(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),X2) | ~r1_tarski(k1_tops_1(sK0,sK1),X2)) ) | ~spl2_295),
% 12.95/2.03    inference(resolution,[],[f17845,f95])).
% 12.95/2.03  fof(f18086,plain,(
% 12.95/2.03    spl2_302 | ~spl2_305 | ~spl2_295),
% 12.95/2.03    inference(avatar_split_clause,[],[f18065,f17843,f18082,f18070])).
% 12.95/2.03  fof(f18082,plain,(
% 12.95/2.03    spl2_305 <=> r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0)),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_305])])).
% 12.95/2.03  fof(f18065,plain,(
% 12.95/2.03    ~r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) | k1_xboole_0 = k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_295),
% 12.95/2.03    inference(resolution,[],[f17868,f168])).
% 12.95/2.03  fof(f18085,plain,(
% 12.95/2.03    spl2_304 | ~spl2_305 | ~spl2_295),
% 12.95/2.03    inference(avatar_split_clause,[],[f18064,f17843,f18082,f18079])).
% 12.95/2.03  fof(f18079,plain,(
% 12.95/2.03    spl2_304 <=> ! [X10] : k1_xboole_0 = k6_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),X10)),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_304])])).
% 12.95/2.03  fof(f18064,plain,(
% 12.95/2.03    ( ! [X10] : (~r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) | k1_xboole_0 = k6_subset_1(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),X10)) ) | ~spl2_295),
% 12.95/2.03    inference(resolution,[],[f17868,f184])).
% 12.95/2.03  fof(f184,plain,(
% 12.95/2.03    ( ! [X2,X3] : (~r1_tarski(X2,k1_xboole_0) | k1_xboole_0 = k6_subset_1(X2,X3)) )),
% 12.95/2.03    inference(resolution,[],[f168,f151])).
% 12.95/2.03  fof(f18077,plain,(
% 12.95/2.03    spl2_302 | ~spl2_303 | ~spl2_295),
% 12.95/2.03    inference(avatar_split_clause,[],[f18057,f17843,f18074,f18070])).
% 12.95/2.03  fof(f18074,plain,(
% 12.95/2.03    spl2_303 <=> r1_tarski(k1_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1))))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_303])])).
% 12.95/2.03  fof(f18057,plain,(
% 12.95/2.03    ~r1_tarski(k1_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))) | k1_xboole_0 = k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_295),
% 12.95/2.03    inference(resolution,[],[f17868,f162])).
% 12.95/2.03  fof(f17883,plain,(
% 12.95/2.03    spl2_301 | ~spl2_295),
% 12.95/2.03    inference(avatar_split_clause,[],[f17866,f17843,f17880])).
% 12.95/2.03  fof(f17880,plain,(
% 12.95/2.03    spl2_301 <=> k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) = k3_subset_1(k1_tops_1(sK0,sK1),k3_subset_1(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1))))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_301])])).
% 12.95/2.03  fof(f17866,plain,(
% 12.95/2.03    k6_subset_1(sK1,k2_pre_topc(sK0,sK1)) = k3_subset_1(k1_tops_1(sK0,sK1),k3_subset_1(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1)))) | ~spl2_295),
% 12.95/2.03    inference(resolution,[],[f17845,f515])).
% 12.95/2.03  fof(f17878,plain,(
% 12.95/2.03    spl2_300 | ~spl2_295),
% 12.95/2.03    inference(avatar_split_clause,[],[f17865,f17843,f17875])).
% 12.95/2.03  fof(f17875,plain,(
% 12.95/2.03    spl2_300 <=> k3_subset_1(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1))) = k6_subset_1(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_300])])).
% 12.95/2.03  fof(f17865,plain,(
% 12.95/2.03    k3_subset_1(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1))) = k6_subset_1(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1))) | ~spl2_295),
% 12.95/2.03    inference(resolution,[],[f17845,f848])).
% 12.95/2.03  fof(f17873,plain,(
% 12.95/2.03    spl2_299 | ~spl2_295),
% 12.95/2.03    inference(avatar_split_clause,[],[f17863,f17843,f17870])).
% 12.95/2.03  fof(f17870,plain,(
% 12.95/2.03    spl2_299 <=> k1_tops_1(sK0,sK1) = k4_subset_1(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k3_subset_1(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1))))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_299])])).
% 12.95/2.03  fof(f17863,plain,(
% 12.95/2.03    k1_tops_1(sK0,sK1) = k4_subset_1(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k3_subset_1(k1_tops_1(sK0,sK1),k6_subset_1(sK1,k2_pre_topc(sK0,sK1)))) | ~spl2_295),
% 12.95/2.03    inference(resolution,[],[f17845,f2085])).
% 12.95/2.03  fof(f17861,plain,(
% 12.95/2.03    spl2_298 | ~spl2_291),
% 12.95/2.03    inference(avatar_split_clause,[],[f17837,f17770,f17858])).
% 12.95/2.03  fof(f17858,plain,(
% 12.95/2.03    spl2_298 <=> sK1 = k3_subset_1(k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),k3_subset_1(k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_298])])).
% 12.95/2.03  fof(f17837,plain,(
% 12.95/2.03    sK1 = k3_subset_1(k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),k3_subset_1(k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),sK1)) | ~spl2_291),
% 12.95/2.03    inference(resolution,[],[f17772,f515])).
% 12.95/2.03  fof(f17856,plain,(
% 12.95/2.03    spl2_297 | ~spl2_291),
% 12.95/2.03    inference(avatar_split_clause,[],[f17836,f17770,f17853])).
% 12.95/2.03  fof(f17853,plain,(
% 12.95/2.03    spl2_297 <=> k3_subset_1(k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),sK1) = k6_subset_1(k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),sK1)),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_297])])).
% 12.95/2.03  fof(f17836,plain,(
% 12.95/2.03    k3_subset_1(k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),sK1) = k6_subset_1(k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),sK1) | ~spl2_291),
% 12.95/2.03    inference(resolution,[],[f17772,f848])).
% 12.95/2.03  fof(f17851,plain,(
% 12.95/2.03    spl2_296 | ~spl2_291),
% 12.95/2.03    inference(avatar_split_clause,[],[f17834,f17770,f17848])).
% 12.95/2.03  fof(f17848,plain,(
% 12.95/2.03    spl2_296 <=> k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) = k4_subset_1(k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),sK1,k3_subset_1(k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_296])])).
% 12.95/2.03  fof(f17834,plain,(
% 12.95/2.03    k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) = k4_subset_1(k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),sK1,k3_subset_1(k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),sK1)) | ~spl2_291),
% 12.95/2.03    inference(resolution,[],[f17772,f2085])).
% 12.95/2.03  fof(f17846,plain,(
% 12.95/2.03    spl2_295 | ~spl2_291),
% 12.95/2.03    inference(avatar_split_clause,[],[f17833,f17770,f17843])).
% 12.95/2.03  fof(f17833,plain,(
% 12.95/2.03    r1_tarski(k6_subset_1(sK1,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) | ~spl2_291),
% 12.95/2.03    inference(resolution,[],[f17772,f106])).
% 12.95/2.03  fof(f17815,plain,(
% 12.95/2.03    spl2_294 | ~spl2_290),
% 12.95/2.03    inference(avatar_split_clause,[],[f17795,f17764,f17812])).
% 12.95/2.03  fof(f17812,plain,(
% 12.95/2.03    spl2_294 <=> sK1 = k3_subset_1(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),k3_subset_1(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_294])])).
% 12.95/2.03  fof(f17795,plain,(
% 12.95/2.03    sK1 = k3_subset_1(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),k3_subset_1(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),sK1)) | ~spl2_290),
% 12.95/2.03    inference(resolution,[],[f17766,f515])).
% 12.95/2.03  fof(f17810,plain,(
% 12.95/2.03    spl2_293 | ~spl2_290),
% 12.95/2.03    inference(avatar_split_clause,[],[f17794,f17764,f17807])).
% 12.95/2.03  fof(f17807,plain,(
% 12.95/2.03    spl2_293 <=> k3_subset_1(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),sK1) = k6_subset_1(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),sK1)),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_293])])).
% 12.95/2.03  fof(f17794,plain,(
% 12.95/2.03    k3_subset_1(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),sK1) = k6_subset_1(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),sK1) | ~spl2_290),
% 12.95/2.03    inference(resolution,[],[f17766,f848])).
% 12.95/2.03  fof(f17805,plain,(
% 12.95/2.03    spl2_292 | ~spl2_290),
% 12.95/2.03    inference(avatar_split_clause,[],[f17792,f17764,f17802])).
% 12.95/2.03  fof(f17802,plain,(
% 12.95/2.03    spl2_292 <=> k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) = k4_subset_1(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),sK1,k3_subset_1(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_292])])).
% 12.95/2.03  fof(f17792,plain,(
% 12.95/2.03    k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) = k4_subset_1(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),sK1,k3_subset_1(k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),sK1)) | ~spl2_290),
% 12.95/2.03    inference(resolution,[],[f17766,f2085])).
% 12.95/2.03  fof(f17773,plain,(
% 12.95/2.03    spl2_291 | ~spl2_22 | ~spl2_198),
% 12.95/2.03    inference(avatar_split_clause,[],[f17768,f6757,f1773,f17770])).
% 12.95/2.03  fof(f1773,plain,(
% 12.95/2.03    spl2_22 <=> k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 12.95/2.03  fof(f6757,plain,(
% 12.95/2.03    spl2_198 <=> r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_198])])).
% 12.95/2.03  fof(f17768,plain,(
% 12.95/2.03    r1_tarski(sK1,k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))) | (~spl2_22 | ~spl2_198)),
% 12.95/2.03    inference(forward_demodulation,[],[f17760,f77])).
% 12.95/2.03  fof(f17760,plain,(
% 12.95/2.03    r1_tarski(sK1,k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)))) | (~spl2_22 | ~spl2_198)),
% 12.95/2.03    inference(resolution,[],[f6573,f6759])).
% 12.95/2.03  fof(f6759,plain,(
% 12.95/2.03    r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~spl2_198),
% 12.95/2.03    inference(avatar_component_clause,[],[f6757])).
% 12.95/2.03  fof(f6573,plain,(
% 12.95/2.03    ( ! [X18] : (~r1_tarski(k2_tops_1(sK0,sK1),X18) | r1_tarski(sK1,k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),X18)))) ) | ~spl2_22),
% 12.95/2.03    inference(superposition,[],[f107,f1774])).
% 12.95/2.03  fof(f1774,plain,(
% 12.95/2.03    k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~spl2_22),
% 12.95/2.03    inference(avatar_component_clause,[],[f1773])).
% 12.95/2.03  fof(f17767,plain,(
% 12.95/2.03    spl2_290 | ~spl2_22),
% 12.95/2.03    inference(avatar_split_clause,[],[f17762,f1773,f17764])).
% 12.95/2.03  fof(f17762,plain,(
% 12.95/2.03    r1_tarski(sK1,k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)))) | ~spl2_22),
% 12.95/2.03    inference(forward_demodulation,[],[f17741,f77])).
% 12.95/2.03  fof(f17741,plain,(
% 12.95/2.03    r1_tarski(sK1,k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)))) | ~spl2_22),
% 12.95/2.03    inference(resolution,[],[f6573,f135])).
% 12.95/2.03  fof(f135,plain,(
% 12.95/2.03    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 12.95/2.03    inference(superposition,[],[f99,f98])).
% 12.95/2.03  fof(f17538,plain,(
% 12.95/2.03    spl2_289 | ~spl2_282 | ~spl2_284 | ~spl2_288),
% 12.95/2.03    inference(avatar_split_clause,[],[f17533,f17515,f17491,f17478,f17535])).
% 12.95/2.03  fof(f17535,plain,(
% 12.95/2.03    spl2_289 <=> k1_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_289])])).
% 12.95/2.03  fof(f17478,plain,(
% 12.95/2.03    spl2_282 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_282])])).
% 12.95/2.03  fof(f17491,plain,(
% 12.95/2.03    spl2_284 <=> k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_284])])).
% 12.95/2.03  fof(f17515,plain,(
% 12.95/2.03    spl2_288 <=> k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_288])])).
% 12.95/2.03  fof(f17533,plain,(
% 12.95/2.03    k1_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) | (~spl2_282 | ~spl2_284 | ~spl2_288)),
% 12.95/2.03    inference(forward_demodulation,[],[f17532,f17517])).
% 12.95/2.03  fof(f17517,plain,(
% 12.95/2.03    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) | ~spl2_288),
% 12.95/2.03    inference(avatar_component_clause,[],[f17515])).
% 12.95/2.03  fof(f17532,plain,(
% 12.95/2.03    k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) = k6_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) | (~spl2_282 | ~spl2_284)),
% 12.95/2.03    inference(forward_demodulation,[],[f17526,f17493])).
% 12.95/2.03  fof(f17493,plain,(
% 12.95/2.03    k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_284),
% 12.95/2.03    inference(avatar_component_clause,[],[f17491])).
% 12.95/2.03  fof(f17526,plain,(
% 12.95/2.03    k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) = k6_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) | ~spl2_282),
% 12.95/2.03    inference(resolution,[],[f17480,f850])).
% 12.95/2.03  fof(f850,plain,(
% 12.95/2.03    ( ! [X4,X5] : (~m1_subset_1(X5,k1_zfmisc_1(X4)) | k3_subset_1(X4,k3_subset_1(X4,X5)) = k6_subset_1(X4,k3_subset_1(X4,X5))) )),
% 12.95/2.03    inference(resolution,[],[f103,f84])).
% 12.95/2.03  fof(f84,plain,(
% 12.95/2.03    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 12.95/2.03    inference(cnf_transformation,[],[f41])).
% 12.95/2.03  fof(f41,plain,(
% 12.95/2.03    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 12.95/2.03    inference(ennf_transformation,[],[f15])).
% 12.95/2.03  fof(f15,axiom,(
% 12.95/2.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 12.95/2.03  fof(f17480,plain,(
% 12.95/2.03    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_282),
% 12.95/2.03    inference(avatar_component_clause,[],[f17478])).
% 12.95/2.03  fof(f17518,plain,(
% 12.95/2.03    spl2_288 | ~spl2_226 | ~spl2_284),
% 12.95/2.03    inference(avatar_split_clause,[],[f17498,f17491,f7706,f17515])).
% 12.95/2.03  fof(f7706,plain,(
% 12.95/2.03    spl2_226 <=> k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_226])])).
% 12.95/2.03  fof(f17498,plain,(
% 12.95/2.03    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) | (~spl2_226 | ~spl2_284)),
% 12.95/2.03    inference(backward_demodulation,[],[f7708,f17493])).
% 12.95/2.03  fof(f7708,plain,(
% 12.95/2.03    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) | ~spl2_226),
% 12.95/2.03    inference(avatar_component_clause,[],[f7706])).
% 12.95/2.03  fof(f17513,plain,(
% 12.95/2.03    spl2_287 | ~spl2_245 | ~spl2_284),
% 12.95/2.03    inference(avatar_split_clause,[],[f17497,f17491,f12139,f17510])).
% 12.95/2.03  fof(f17510,plain,(
% 12.95/2.03    spl2_287 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_287])])).
% 12.95/2.03  fof(f12139,plain,(
% 12.95/2.03    spl2_245 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_245])])).
% 12.95/2.03  fof(f17497,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) | (~spl2_245 | ~spl2_284)),
% 12.95/2.03    inference(backward_demodulation,[],[f12141,f17493])).
% 12.95/2.03  fof(f12141,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) | ~spl2_245),
% 12.95/2.03    inference(avatar_component_clause,[],[f12139])).
% 12.95/2.03  fof(f17508,plain,(
% 12.95/2.03    spl2_286 | ~spl2_283 | ~spl2_284),
% 12.95/2.03    inference(avatar_split_clause,[],[f17496,f17491,f17485,f17505])).
% 12.95/2.03  fof(f17505,plain,(
% 12.95/2.03    spl2_286 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_286])])).
% 12.95/2.03  fof(f17485,plain,(
% 12.95/2.03    spl2_283 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_283])])).
% 12.95/2.03  fof(f17496,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | (~spl2_283 | ~spl2_284)),
% 12.95/2.03    inference(backward_demodulation,[],[f17487,f17493])).
% 12.95/2.03  fof(f17487,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | ~spl2_283),
% 12.95/2.03    inference(avatar_component_clause,[],[f17485])).
% 12.95/2.03  fof(f17503,plain,(
% 12.95/2.03    ~spl2_285 | spl2_280 | ~spl2_284),
% 12.95/2.03    inference(avatar_split_clause,[],[f17495,f17491,f17469,f17500])).
% 12.95/2.03  fof(f17500,plain,(
% 12.95/2.03    spl2_285 <=> r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_285])])).
% 12.95/2.03  fof(f17469,plain,(
% 12.95/2.03    spl2_280 <=> r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_280])])).
% 12.95/2.03  fof(f17495,plain,(
% 12.95/2.03    ~r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | (spl2_280 | ~spl2_284)),
% 12.95/2.03    inference(backward_demodulation,[],[f17471,f17493])).
% 12.95/2.03  fof(f17471,plain,(
% 12.95/2.03    ~r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | spl2_280),
% 12.95/2.03    inference(avatar_component_clause,[],[f17469])).
% 12.95/2.03  fof(f17494,plain,(
% 12.95/2.03    spl2_284 | ~spl2_231 | ~spl2_279),
% 12.95/2.03    inference(avatar_split_clause,[],[f17489,f17462,f8227,f17491])).
% 12.95/2.03  fof(f8227,plain,(
% 12.95/2.03    spl2_231 <=> k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k6_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_231])])).
% 12.95/2.03  fof(f17462,plain,(
% 12.95/2.03    spl2_279 <=> k6_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_279])])).
% 12.95/2.03  fof(f17489,plain,(
% 12.95/2.03    k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_231 | ~spl2_279)),
% 12.95/2.03    inference(backward_demodulation,[],[f8229,f17464])).
% 12.95/2.03  fof(f17464,plain,(
% 12.95/2.03    k6_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_279),
% 12.95/2.03    inference(avatar_component_clause,[],[f17462])).
% 12.95/2.03  fof(f8229,plain,(
% 12.95/2.03    k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k6_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_231),
% 12.95/2.03    inference(avatar_component_clause,[],[f8227])).
% 12.95/2.03  fof(f17488,plain,(
% 12.95/2.03    spl2_283 | ~spl2_228 | ~spl2_231),
% 12.95/2.03    inference(avatar_split_clause,[],[f17483,f8227,f8009,f17485])).
% 12.95/2.03  fof(f8009,plain,(
% 12.95/2.03    spl2_228 <=> k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_228])])).
% 12.95/2.03  fof(f17483,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | (~spl2_228 | ~spl2_231)),
% 12.95/2.03    inference(forward_demodulation,[],[f17459,f8229])).
% 12.95/2.03  fof(f17459,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | ~spl2_228),
% 12.95/2.03    inference(superposition,[],[f2102,f8011])).
% 12.95/2.03  fof(f8011,plain,(
% 12.95/2.03    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) | ~spl2_228),
% 12.95/2.03    inference(avatar_component_clause,[],[f8009])).
% 12.95/2.03  fof(f17481,plain,(
% 12.95/2.03    spl2_282 | ~spl2_228),
% 12.95/2.03    inference(avatar_split_clause,[],[f17453,f8009,f17478])).
% 12.95/2.03  fof(f17453,plain,(
% 12.95/2.03    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_228),
% 12.95/2.03    inference(superposition,[],[f163,f8011])).
% 12.95/2.03  fof(f17476,plain,(
% 12.95/2.03    ~spl2_280 | spl2_281 | ~spl2_228 | ~spl2_231),
% 12.95/2.03    inference(avatar_split_clause,[],[f17467,f8227,f8009,f17473,f17469])).
% 12.95/2.03  fof(f17473,plain,(
% 12.95/2.03    spl2_281 <=> k1_xboole_0 = k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_281])])).
% 12.95/2.03  fof(f17467,plain,(
% 12.95/2.03    k1_xboole_0 = k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | (~spl2_228 | ~spl2_231)),
% 12.95/2.03    inference(forward_demodulation,[],[f17466,f8229])).
% 12.95/2.03  fof(f17466,plain,(
% 12.95/2.03    ~r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | k1_xboole_0 = k6_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_228 | ~spl2_231)),
% 12.95/2.03    inference(forward_demodulation,[],[f17452,f8229])).
% 12.95/2.03  fof(f17452,plain,(
% 12.95/2.03    ~r1_tarski(k6_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | k1_xboole_0 = k6_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_228),
% 12.95/2.03    inference(superposition,[],[f162,f8011])).
% 12.95/2.03  fof(f17465,plain,(
% 12.95/2.03    spl2_279 | ~spl2_228),
% 12.95/2.03    inference(avatar_split_clause,[],[f17451,f8009,f17462])).
% 12.95/2.03  fof(f17451,plain,(
% 12.95/2.03    k6_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_228),
% 12.95/2.03    inference(superposition,[],[f102,f8011])).
% 12.95/2.03  fof(f102,plain,(
% 12.95/2.03    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 12.95/2.03    inference(definition_unfolding,[],[f83,f78,f79])).
% 12.95/2.03  fof(f83,plain,(
% 12.95/2.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 12.95/2.03    inference(cnf_transformation,[],[f1])).
% 12.95/2.03  fof(f1,axiom,(
% 12.95/2.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 12.95/2.03  fof(f17410,plain,(
% 12.95/2.03    spl2_278 | ~spl2_189 | ~spl2_237 | ~spl2_240),
% 12.95/2.03    inference(avatar_split_clause,[],[f17405,f10584,f10566,f6690,f17407])).
% 12.95/2.03  fof(f17407,plain,(
% 12.95/2.03    spl2_278 <=> k1_tops_1(sK0,sK1) = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_278])])).
% 12.95/2.03  fof(f6690,plain,(
% 12.95/2.03    spl2_189 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_189])])).
% 12.95/2.03  fof(f10566,plain,(
% 12.95/2.03    spl2_237 <=> k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_237])])).
% 12.95/2.03  fof(f10584,plain,(
% 12.95/2.03    spl2_240 <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_240])])).
% 12.95/2.03  fof(f17405,plain,(
% 12.95/2.03    k1_tops_1(sK0,sK1) = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | (~spl2_189 | ~spl2_237 | ~spl2_240)),
% 12.95/2.03    inference(forward_demodulation,[],[f17404,f10586])).
% 12.95/2.03  fof(f10586,plain,(
% 12.95/2.03    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | ~spl2_240),
% 12.95/2.03    inference(avatar_component_clause,[],[f10584])).
% 12.95/2.03  fof(f17404,plain,(
% 12.95/2.03    k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | (~spl2_189 | ~spl2_237)),
% 12.95/2.03    inference(forward_demodulation,[],[f17363,f10568])).
% 12.95/2.03  fof(f10568,plain,(
% 12.95/2.03    k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~spl2_237),
% 12.95/2.03    inference(avatar_component_clause,[],[f10566])).
% 12.95/2.03  fof(f17363,plain,(
% 12.95/2.03    k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | ~spl2_189),
% 12.95/2.03    inference(resolution,[],[f850,f6692])).
% 12.95/2.03  fof(f6692,plain,(
% 12.95/2.03    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_189),
% 12.95/2.03    inference(avatar_component_clause,[],[f6690])).
% 12.95/2.03  fof(f17401,plain,(
% 12.95/2.03    spl2_277 | ~spl2_270 | ~spl2_272 | ~spl2_276),
% 12.95/2.03    inference(avatar_split_clause,[],[f17396,f17196,f17172,f17159,f17398])).
% 12.95/2.03  fof(f17398,plain,(
% 12.95/2.03    spl2_277 <=> k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_277])])).
% 12.95/2.03  fof(f17159,plain,(
% 12.95/2.03    spl2_270 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_270])])).
% 12.95/2.03  fof(f17172,plain,(
% 12.95/2.03    spl2_272 <=> k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_272])])).
% 12.95/2.03  fof(f17196,plain,(
% 12.95/2.03    spl2_276 <=> k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_276])])).
% 12.95/2.03  fof(f17396,plain,(
% 12.95/2.03    k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) | (~spl2_270 | ~spl2_272 | ~spl2_276)),
% 12.95/2.03    inference(forward_demodulation,[],[f17395,f17198])).
% 12.95/2.03  fof(f17198,plain,(
% 12.95/2.03    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) | ~spl2_276),
% 12.95/2.03    inference(avatar_component_clause,[],[f17196])).
% 12.95/2.03  fof(f17395,plain,(
% 12.95/2.03    k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) = k6_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) | (~spl2_270 | ~spl2_272)),
% 12.95/2.03    inference(forward_demodulation,[],[f17361,f17174])).
% 12.95/2.03  fof(f17174,plain,(
% 12.95/2.03    k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_272),
% 12.95/2.03    inference(avatar_component_clause,[],[f17172])).
% 12.95/2.03  fof(f17361,plain,(
% 12.95/2.03    k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) = k6_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) | ~spl2_270),
% 12.95/2.03    inference(resolution,[],[f850,f17161])).
% 12.95/2.03  fof(f17161,plain,(
% 12.95/2.03    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_270),
% 12.95/2.03    inference(avatar_component_clause,[],[f17159])).
% 12.95/2.03  fof(f17199,plain,(
% 12.95/2.03    spl2_276 | ~spl2_225 | ~spl2_272),
% 12.95/2.03    inference(avatar_split_clause,[],[f17179,f17172,f7701,f17196])).
% 12.95/2.03  fof(f7701,plain,(
% 12.95/2.03    spl2_225 <=> k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_225])])).
% 12.95/2.03  fof(f17179,plain,(
% 12.95/2.03    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) | (~spl2_225 | ~spl2_272)),
% 12.95/2.03    inference(backward_demodulation,[],[f7703,f17174])).
% 12.95/2.03  fof(f7703,plain,(
% 12.95/2.03    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) | ~spl2_225),
% 12.95/2.03    inference(avatar_component_clause,[],[f7701])).
% 12.95/2.03  fof(f17194,plain,(
% 12.95/2.03    spl2_275 | ~spl2_244 | ~spl2_272),
% 12.95/2.03    inference(avatar_split_clause,[],[f17178,f17172,f12134,f17191])).
% 12.95/2.03  fof(f17191,plain,(
% 12.95/2.03    spl2_275 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_275])])).
% 12.95/2.03  fof(f12134,plain,(
% 12.95/2.03    spl2_244 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_244])])).
% 12.95/2.03  fof(f17178,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) | (~spl2_244 | ~spl2_272)),
% 12.95/2.03    inference(backward_demodulation,[],[f12136,f17174])).
% 12.95/2.03  fof(f12136,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) | ~spl2_244),
% 12.95/2.03    inference(avatar_component_clause,[],[f12134])).
% 12.95/2.03  fof(f17189,plain,(
% 12.95/2.03    spl2_274 | ~spl2_271 | ~spl2_272),
% 12.95/2.03    inference(avatar_split_clause,[],[f17177,f17172,f17166,f17186])).
% 12.95/2.03  fof(f17186,plain,(
% 12.95/2.03    spl2_274 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_274])])).
% 12.95/2.03  fof(f17166,plain,(
% 12.95/2.03    spl2_271 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_271])])).
% 12.95/2.03  fof(f17177,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | (~spl2_271 | ~spl2_272)),
% 12.95/2.03    inference(backward_demodulation,[],[f17168,f17174])).
% 12.95/2.03  fof(f17168,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | ~spl2_271),
% 12.95/2.03    inference(avatar_component_clause,[],[f17166])).
% 12.95/2.03  fof(f17184,plain,(
% 12.95/2.03    ~spl2_273 | spl2_268 | ~spl2_272),
% 12.95/2.03    inference(avatar_split_clause,[],[f17176,f17172,f17150,f17181])).
% 12.95/2.03  fof(f17181,plain,(
% 12.95/2.03    spl2_273 <=> r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_273])])).
% 12.95/2.03  fof(f17150,plain,(
% 12.95/2.03    spl2_268 <=> r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_268])])).
% 12.95/2.03  fof(f17176,plain,(
% 12.95/2.03    ~r1_tarski(k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | (spl2_268 | ~spl2_272)),
% 12.95/2.03    inference(backward_demodulation,[],[f17152,f17174])).
% 12.95/2.03  fof(f17152,plain,(
% 12.95/2.03    ~r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | spl2_268),
% 12.95/2.03    inference(avatar_component_clause,[],[f17150])).
% 12.95/2.03  fof(f17175,plain,(
% 12.95/2.03    spl2_272 | ~spl2_230 | ~spl2_267),
% 12.95/2.03    inference(avatar_split_clause,[],[f17170,f17143,f8222,f17172])).
% 12.95/2.03  fof(f8222,plain,(
% 12.95/2.03    spl2_230 <=> k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k6_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_230])])).
% 12.95/2.03  fof(f17143,plain,(
% 12.95/2.03    spl2_267 <=> k6_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_267])])).
% 12.95/2.03  fof(f17170,plain,(
% 12.95/2.03    k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl2_230 | ~spl2_267)),
% 12.95/2.03    inference(backward_demodulation,[],[f8224,f17145])).
% 12.95/2.03  fof(f17145,plain,(
% 12.95/2.03    k6_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_267),
% 12.95/2.03    inference(avatar_component_clause,[],[f17143])).
% 12.95/2.03  fof(f8224,plain,(
% 12.95/2.03    k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k6_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_230),
% 12.95/2.03    inference(avatar_component_clause,[],[f8222])).
% 12.95/2.03  fof(f17169,plain,(
% 12.95/2.03    spl2_271 | ~spl2_222 | ~spl2_230),
% 12.95/2.03    inference(avatar_split_clause,[],[f17164,f8222,f7344,f17166])).
% 12.95/2.03  fof(f7344,plain,(
% 12.95/2.03    spl2_222 <=> k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_222])])).
% 12.95/2.03  fof(f17164,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | (~spl2_222 | ~spl2_230)),
% 12.95/2.03    inference(forward_demodulation,[],[f17141,f8224])).
% 12.95/2.03  fof(f17141,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | ~spl2_222),
% 12.95/2.03    inference(superposition,[],[f2102,f7346])).
% 12.95/2.03  fof(f7346,plain,(
% 12.95/2.03    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) | ~spl2_222),
% 12.95/2.03    inference(avatar_component_clause,[],[f7344])).
% 12.95/2.03  fof(f17162,plain,(
% 12.95/2.03    spl2_270 | ~spl2_222),
% 12.95/2.03    inference(avatar_split_clause,[],[f17135,f7344,f17159])).
% 12.95/2.03  fof(f17135,plain,(
% 12.95/2.03    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_222),
% 12.95/2.03    inference(superposition,[],[f163,f7346])).
% 12.95/2.03  fof(f17157,plain,(
% 12.95/2.03    ~spl2_268 | spl2_269 | ~spl2_222 | ~spl2_230),
% 12.95/2.03    inference(avatar_split_clause,[],[f17148,f8222,f7344,f17154,f17150])).
% 12.95/2.03  fof(f17154,plain,(
% 12.95/2.03    spl2_269 <=> k1_xboole_0 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_269])])).
% 12.95/2.03  fof(f17148,plain,(
% 12.95/2.03    k1_xboole_0 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | (~spl2_222 | ~spl2_230)),
% 12.95/2.03    inference(forward_demodulation,[],[f17147,f8224])).
% 12.95/2.03  fof(f17147,plain,(
% 12.95/2.03    ~r1_tarski(k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | k1_xboole_0 = k6_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl2_222 | ~spl2_230)),
% 12.95/2.03    inference(forward_demodulation,[],[f17134,f8224])).
% 12.95/2.03  fof(f17134,plain,(
% 12.95/2.03    ~r1_tarski(k6_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | k1_xboole_0 = k6_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_222),
% 12.95/2.03    inference(superposition,[],[f162,f7346])).
% 12.95/2.03  fof(f17146,plain,(
% 12.95/2.03    spl2_267 | ~spl2_222),
% 12.95/2.03    inference(avatar_split_clause,[],[f17133,f7344,f17143])).
% 12.95/2.03  fof(f17133,plain,(
% 12.95/2.03    k6_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k5_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_222),
% 12.95/2.03    inference(superposition,[],[f102,f7346])).
% 12.95/2.03  fof(f16840,plain,(
% 12.95/2.03    spl2_266 | ~spl2_264),
% 12.95/2.03    inference(avatar_split_clause,[],[f16835,f16788,f16837])).
% 12.95/2.03  fof(f16837,plain,(
% 12.95/2.03    spl2_266 <=> k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k4_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_xboole_0,k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1))))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_266])])).
% 12.95/2.03  fof(f16835,plain,(
% 12.95/2.03    k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k4_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_xboole_0,k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1)))) | ~spl2_264),
% 12.95/2.03    inference(forward_demodulation,[],[f16822,f77])).
% 12.95/2.03  fof(f16822,plain,(
% 12.95/2.03    k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k4_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_xboole_0,k1_setfam_1(k2_tarski(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1)))) | ~spl2_264),
% 12.95/2.03    inference(superposition,[],[f2102,f16790])).
% 12.95/2.03  fof(f16832,plain,(
% 12.95/2.03    spl2_265 | ~spl2_264),
% 12.95/2.03    inference(avatar_split_clause,[],[f16831,f16788,f16826])).
% 12.95/2.03  fof(f16831,plain,(
% 12.95/2.03    k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1))) | ~spl2_264),
% 12.95/2.03    inference(forward_demodulation,[],[f16830,f77])).
% 12.95/2.03  fof(f16830,plain,(
% 12.95/2.03    k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k1_setfam_1(k2_tarski(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1))) | ~spl2_264),
% 12.95/2.03    inference(forward_demodulation,[],[f16818,f856])).
% 12.95/2.03  fof(f16818,plain,(
% 12.95/2.03    k1_setfam_1(k2_tarski(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1))) = k3_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_xboole_0) | ~spl2_264),
% 12.95/2.03    inference(superposition,[],[f859,f16790])).
% 12.95/2.03  fof(f16829,plain,(
% 12.95/2.03    spl2_265 | ~spl2_264),
% 12.95/2.03    inference(avatar_split_clause,[],[f16824,f16788,f16826])).
% 12.95/2.03  fof(f16824,plain,(
% 12.95/2.03    k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1))) | ~spl2_264),
% 12.95/2.03    inference(forward_demodulation,[],[f16823,f98])).
% 12.95/2.03  fof(f16823,plain,(
% 12.95/2.03    k6_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_xboole_0) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1))) | ~spl2_264),
% 12.95/2.03    inference(forward_demodulation,[],[f16813,f77])).
% 12.95/2.03  fof(f16813,plain,(
% 12.95/2.03    k6_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_xboole_0) = k1_setfam_1(k2_tarski(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1))) | ~spl2_264),
% 12.95/2.03    inference(superposition,[],[f100,f16790])).
% 12.95/2.03  fof(f16796,plain,(
% 12.95/2.03    spl2_264 | ~spl2_233),
% 12.95/2.03    inference(avatar_split_clause,[],[f16786,f10518,f16788])).
% 12.95/2.03  fof(f16786,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) | ~spl2_233),
% 12.95/2.03    inference(resolution,[],[f16762,f104])).
% 12.95/2.03  fof(f16762,plain,(
% 12.95/2.03    ( ! [X1] : (r1_tarski(k6_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1)),X1)) ) | ~spl2_233),
% 12.95/2.03    inference(resolution,[],[f15321,f1041])).
% 12.95/2.03  fof(f15321,plain,(
% 12.95/2.03    ( ! [X0] : (r1_tarski(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k3_tarski(k2_tarski(X0,k2_tops_1(sK0,sK1))))) ) | ~spl2_233),
% 12.95/2.03    inference(resolution,[],[f15320,f107])).
% 12.95/2.03  fof(f15320,plain,(
% 12.95/2.03    ( ! [X0] : (r1_tarski(k6_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),X0),k2_tops_1(sK0,sK1))) ) | ~spl2_233),
% 12.95/2.03    inference(superposition,[],[f10526,f863])).
% 12.95/2.03  fof(f10526,plain,(
% 12.95/2.03    ( ! [X0] : (r1_tarski(k1_setfam_1(k2_tarski(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),X0)),k2_tops_1(sK0,sK1))) ) | ~spl2_233),
% 12.95/2.03    inference(resolution,[],[f10520,f161])).
% 12.95/2.03  fof(f16793,plain,(
% 12.95/2.03    spl2_264 | ~spl2_233),
% 12.95/2.03    inference(avatar_split_clause,[],[f16783,f10518,f16788])).
% 12.95/2.03  fof(f16783,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) | ~spl2_233),
% 12.95/2.03    inference(resolution,[],[f16762,f168])).
% 12.95/2.03  fof(f16791,plain,(
% 12.95/2.03    spl2_264 | ~spl2_233),
% 12.95/2.03    inference(avatar_split_clause,[],[f16775,f10518,f16788])).
% 12.95/2.03  fof(f16775,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) | ~spl2_233),
% 12.95/2.03    inference(resolution,[],[f16762,f162])).
% 12.95/2.03  fof(f15475,plain,(
% 12.95/2.03    ~spl2_263 | ~spl2_48 | spl2_258),
% 12.95/2.03    inference(avatar_split_clause,[],[f15470,f15350,f2833,f15472])).
% 12.95/2.03  fof(f15472,plain,(
% 12.95/2.03    spl2_263 <=> r1_tarski(sK1,k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1))))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_263])])).
% 12.95/2.03  fof(f2833,plain,(
% 12.95/2.03    spl2_48 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 12.95/2.03  fof(f15350,plain,(
% 12.95/2.03    spl2_258 <=> r1_tarski(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1))))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_258])])).
% 12.95/2.03  fof(f15470,plain,(
% 12.95/2.03    ~r1_tarski(sK1,k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))) | (~spl2_48 | spl2_258)),
% 12.95/2.03    inference(resolution,[],[f15352,f3094])).
% 12.95/2.03  fof(f3094,plain,(
% 12.95/2.03    ( ! [X1] : (r1_tarski(k2_tops_1(sK0,sK1),X1) | ~r1_tarski(sK1,X1)) ) | ~spl2_48),
% 12.95/2.03    inference(resolution,[],[f2835,f95])).
% 12.95/2.03  fof(f2835,plain,(
% 12.95/2.03    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_48),
% 12.95/2.03    inference(avatar_component_clause,[],[f2833])).
% 12.95/2.03  fof(f15352,plain,(
% 12.95/2.03    ~r1_tarski(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))) | spl2_258),
% 12.95/2.03    inference(avatar_component_clause,[],[f15350])).
% 12.95/2.03  fof(f15461,plain,(
% 12.95/2.03    spl2_262 | ~spl2_257),
% 12.95/2.03    inference(avatar_split_clause,[],[f15456,f15346,f15458])).
% 12.95/2.03  fof(f15458,plain,(
% 12.95/2.03    spl2_262 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k1_xboole_0,k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1))))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_262])])).
% 12.95/2.03  fof(f15346,plain,(
% 12.95/2.03    spl2_257 <=> k1_xboole_0 = k6_subset_1(k2_pre_topc(sK0,sK1),sK1)),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_257])])).
% 12.95/2.03  fof(f15456,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k1_xboole_0,k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))) | ~spl2_257),
% 12.95/2.03    inference(forward_demodulation,[],[f15442,f77])).
% 12.95/2.03  fof(f15442,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k1_xboole_0,k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),sK1))) | ~spl2_257),
% 12.95/2.03    inference(superposition,[],[f2102,f15348])).
% 12.95/2.03  fof(f15348,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~spl2_257),
% 12.95/2.03    inference(avatar_component_clause,[],[f15346])).
% 12.95/2.03  fof(f15454,plain,(
% 12.95/2.03    spl2_261 | ~spl2_257),
% 12.95/2.03    inference(avatar_split_clause,[],[f15453,f15346,f15448])).
% 12.95/2.03  fof(f15448,plain,(
% 12.95/2.03    spl2_261 <=> k2_pre_topc(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_261])])).
% 12.95/2.03  fof(f15453,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1))) | ~spl2_257),
% 12.95/2.03    inference(forward_demodulation,[],[f15452,f77])).
% 12.95/2.03  fof(f15452,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),sK1)) | ~spl2_257),
% 12.95/2.03    inference(forward_demodulation,[],[f15439,f856])).
% 12.95/2.03  fof(f15439,plain,(
% 12.95/2.03    k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),sK1)) = k3_subset_1(k2_pre_topc(sK0,sK1),k1_xboole_0) | ~spl2_257),
% 12.95/2.03    inference(superposition,[],[f859,f15348])).
% 12.95/2.03  fof(f15451,plain,(
% 12.95/2.03    spl2_261 | ~spl2_257),
% 12.95/2.03    inference(avatar_split_clause,[],[f15446,f15346,f15448])).
% 12.95/2.03  fof(f15446,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1))) | ~spl2_257),
% 12.95/2.03    inference(forward_demodulation,[],[f15445,f98])).
% 12.95/2.03  fof(f15445,plain,(
% 12.95/2.03    k6_subset_1(k2_pre_topc(sK0,sK1),k1_xboole_0) = k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1))) | ~spl2_257),
% 12.95/2.03    inference(forward_demodulation,[],[f15434,f77])).
% 12.95/2.03  fof(f15434,plain,(
% 12.95/2.03    k6_subset_1(k2_pre_topc(sK0,sK1),k1_xboole_0) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),sK1)) | ~spl2_257),
% 12.95/2.03    inference(superposition,[],[f100,f15348])).
% 12.95/2.03  fof(f15362,plain,(
% 12.95/2.03    spl2_257 | spl2_260 | ~spl2_233),
% 12.95/2.03    inference(avatar_split_clause,[],[f15343,f10518,f15360,f15346])).
% 12.95/2.03  fof(f15360,plain,(
% 12.95/2.03    spl2_260 <=> ! [X15] : ~r1_tarski(k2_tops_1(sK0,sK1),k6_subset_1(X15,k6_subset_1(k2_pre_topc(sK0,sK1),sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_260])])).
% 12.95/2.03  fof(f15343,plain,(
% 12.95/2.03    ( ! [X15] : (~r1_tarski(k2_tops_1(sK0,sK1),k6_subset_1(X15,k6_subset_1(k2_pre_topc(sK0,sK1),sK1))) | k1_xboole_0 = k6_subset_1(k2_pre_topc(sK0,sK1),sK1)) ) | ~spl2_233),
% 12.95/2.03    inference(resolution,[],[f10527,f104])).
% 12.95/2.03  fof(f10527,plain,(
% 12.95/2.03    ( ! [X1] : (r1_tarski(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),X1) | ~r1_tarski(k2_tops_1(sK0,sK1),X1)) ) | ~spl2_233),
% 12.95/2.03    inference(resolution,[],[f10520,f95])).
% 12.95/2.03  fof(f15358,plain,(
% 12.95/2.03    spl2_257 | ~spl2_186 | ~spl2_233),
% 12.95/2.03    inference(avatar_split_clause,[],[f15340,f10518,f6486,f15346])).
% 12.95/2.03  fof(f6486,plain,(
% 12.95/2.03    spl2_186 <=> r1_tarski(k2_tops_1(sK0,sK1),k1_xboole_0)),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_186])])).
% 12.95/2.03  fof(f15340,plain,(
% 12.95/2.03    ~r1_tarski(k2_tops_1(sK0,sK1),k1_xboole_0) | k1_xboole_0 = k6_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~spl2_233),
% 12.95/2.03    inference(resolution,[],[f10527,f168])).
% 12.95/2.03  fof(f15357,plain,(
% 12.95/2.03    spl2_259 | ~spl2_186 | ~spl2_233),
% 12.95/2.03    inference(avatar_split_clause,[],[f15339,f10518,f6486,f15355])).
% 12.95/2.03  fof(f15355,plain,(
% 12.95/2.03    spl2_259 <=> ! [X10] : k1_xboole_0 = k6_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),X10)),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_259])])).
% 12.95/2.03  fof(f15339,plain,(
% 12.95/2.03    ( ! [X10] : (~r1_tarski(k2_tops_1(sK0,sK1),k1_xboole_0) | k1_xboole_0 = k6_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),X10)) ) | ~spl2_233),
% 12.95/2.03    inference(resolution,[],[f10527,f184])).
% 12.95/2.03  fof(f15353,plain,(
% 12.95/2.03    spl2_257 | ~spl2_258 | ~spl2_233),
% 12.95/2.03    inference(avatar_split_clause,[],[f15344,f10518,f15350,f15346])).
% 12.95/2.03  fof(f15344,plain,(
% 12.95/2.03    ~r1_tarski(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))) | k1_xboole_0 = k6_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~spl2_233),
% 12.95/2.03    inference(forward_demodulation,[],[f15332,f77])).
% 12.95/2.03  fof(f15332,plain,(
% 12.95/2.03    ~r1_tarski(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),sK1))) | k1_xboole_0 = k6_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~spl2_233),
% 12.95/2.03    inference(resolution,[],[f10527,f162])).
% 12.95/2.03  fof(f15046,plain,(
% 12.95/2.03    ~spl2_255 | spl2_256 | ~spl2_188 | ~spl2_236),
% 12.95/2.03    inference(avatar_split_clause,[],[f15037,f10559,f6550,f15043,f15039])).
% 12.95/2.03  fof(f15039,plain,(
% 12.95/2.03    spl2_255 <=> r1_tarski(k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_255])])).
% 12.95/2.03  fof(f15043,plain,(
% 12.95/2.03    spl2_256 <=> k1_xboole_0 = k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_256])])).
% 12.95/2.03  fof(f6550,plain,(
% 12.95/2.03    spl2_188 <=> k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_188])])).
% 12.95/2.03  fof(f10559,plain,(
% 12.95/2.03    spl2_236 <=> k6_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_236])])).
% 12.95/2.03  fof(f15037,plain,(
% 12.95/2.03    k1_xboole_0 = k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~r1_tarski(k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | (~spl2_188 | ~spl2_236)),
% 12.95/2.03    inference(forward_demodulation,[],[f15036,f10561])).
% 12.95/2.03  fof(f10561,plain,(
% 12.95/2.03    k6_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~spl2_236),
% 12.95/2.03    inference(avatar_component_clause,[],[f10559])).
% 12.95/2.03  fof(f15036,plain,(
% 12.95/2.03    ~r1_tarski(k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | k1_xboole_0 = k6_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | (~spl2_188 | ~spl2_236)),
% 12.95/2.03    inference(forward_demodulation,[],[f15010,f10561])).
% 12.95/2.03  fof(f15010,plain,(
% 12.95/2.03    ~r1_tarski(k6_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | k1_xboole_0 = k6_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~spl2_188),
% 12.95/2.03    inference(superposition,[],[f162,f6552])).
% 12.95/2.03  fof(f6552,plain,(
% 12.95/2.03    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | ~spl2_188),
% 12.95/2.03    inference(avatar_component_clause,[],[f6550])).
% 12.95/2.03  fof(f14174,plain,(
% 12.95/2.03    ~spl2_253 | spl2_254 | ~spl2_175 | ~spl2_200),
% 12.95/2.03    inference(avatar_split_clause,[],[f14162,f6822,f6337,f14171,f14167])).
% 12.95/2.03  fof(f14167,plain,(
% 12.95/2.03    spl2_253 <=> r1_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_253])])).
% 12.95/2.03  fof(f14171,plain,(
% 12.95/2.03    spl2_254 <=> r1_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_254])])).
% 12.95/2.03  fof(f6337,plain,(
% 12.95/2.03    spl2_175 <=> k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_175])])).
% 12.95/2.03  fof(f6822,plain,(
% 12.95/2.03    spl2_200 <=> k6_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1)),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_200])])).
% 12.95/2.03  fof(f14162,plain,(
% 12.95/2.03    r1_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) | ~r1_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) | (~spl2_175 | ~spl2_200)),
% 12.95/2.03    inference(superposition,[],[f6755,f6824])).
% 12.95/2.03  fof(f6824,plain,(
% 12.95/2.03    k6_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) | ~spl2_200),
% 12.95/2.03    inference(avatar_component_clause,[],[f6822])).
% 12.95/2.03  fof(f6755,plain,(
% 12.95/2.03    ( ! [X1] : (r1_tarski(k6_subset_1(X1,sK1),k2_tops_1(sK0,sK1)) | ~r1_tarski(X1,k2_pre_topc(sK0,sK1))) ) | ~spl2_175),
% 12.95/2.03    inference(superposition,[],[f106,f6339])).
% 12.95/2.03  fof(f6339,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_175),
% 12.95/2.03    inference(avatar_component_clause,[],[f6337])).
% 12.95/2.03  fof(f14111,plain,(
% 12.95/2.03    spl2_252 | ~spl2_55),
% 12.95/2.03    inference(avatar_split_clause,[],[f14102,f3367,f14105])).
% 12.95/2.03  fof(f14105,plain,(
% 12.95/2.03    spl2_252 <=> k1_xboole_0 = k6_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),u1_struct_0(sK0))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_252])])).
% 12.95/2.03  fof(f3367,plain,(
% 12.95/2.03    spl2_55 <=> k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).
% 12.95/2.03  fof(f14102,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),u1_struct_0(sK0)) | ~spl2_55),
% 12.95/2.03    inference(resolution,[],[f14079,f104])).
% 12.95/2.03  fof(f14079,plain,(
% 12.95/2.03    ( ! [X0] : (r1_tarski(k6_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),u1_struct_0(sK0)),X0)) ) | ~spl2_55),
% 12.95/2.03    inference(resolution,[],[f5141,f1041])).
% 12.95/2.03  fof(f5141,plain,(
% 12.95/2.03    ( ! [X144] : (r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_tarski(k2_tarski(X144,u1_struct_0(sK0))))) ) | ~spl2_55),
% 12.95/2.03    inference(resolution,[],[f1309,f3659])).
% 12.95/2.03  fof(f3659,plain,(
% 12.95/2.03    ( ! [X1] : (~r1_tarski(u1_struct_0(sK0),X1) | r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),X1)) ) | ~spl2_55),
% 12.95/2.03    inference(superposition,[],[f151,f3369])).
% 12.95/2.03  fof(f3369,plain,(
% 12.95/2.03    k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) | ~spl2_55),
% 12.95/2.03    inference(avatar_component_clause,[],[f3367])).
% 12.95/2.03  fof(f1309,plain,(
% 12.95/2.03    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) )),
% 12.95/2.03    inference(resolution,[],[f107,f99])).
% 12.95/2.03  fof(f14108,plain,(
% 12.95/2.03    spl2_252 | ~spl2_55),
% 12.95/2.03    inference(avatar_split_clause,[],[f14099,f3367,f14105])).
% 12.95/2.03  fof(f14099,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),u1_struct_0(sK0)) | ~spl2_55),
% 12.95/2.03    inference(resolution,[],[f14079,f168])).
% 12.95/2.03  fof(f13481,plain,(
% 12.95/2.03    spl2_251 | ~spl2_175),
% 12.95/2.03    inference(avatar_split_clause,[],[f13476,f6337,f13478])).
% 12.95/2.03  fof(f13476,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) | ~spl2_175),
% 12.95/2.03    inference(forward_demodulation,[],[f13361,f77])).
% 12.95/2.03  fof(f13361,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))) | ~spl2_175),
% 12.95/2.03    inference(superposition,[],[f1504,f6339])).
% 12.95/2.03  fof(f1504,plain,(
% 12.95/2.03    ( ! [X0,X1] : (k3_tarski(k2_tarski(X1,X0)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0))))) )),
% 12.95/2.03    inference(superposition,[],[f101,f77])).
% 12.95/2.03  fof(f101,plain,(
% 12.95/2.03    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) )),
% 12.95/2.03    inference(definition_unfolding,[],[f82,f80,f80,f80])).
% 12.95/2.03  fof(f82,plain,(
% 12.95/2.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 12.95/2.03    inference(cnf_transformation,[],[f10])).
% 12.95/2.03  fof(f10,axiom,(
% 12.95/2.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).
% 12.95/2.03  fof(f13475,plain,(
% 12.95/2.03    spl2_250 | ~spl2_199),
% 12.95/2.03    inference(avatar_split_clause,[],[f13360,f6763,f13472])).
% 12.95/2.03  fof(f13472,plain,(
% 12.95/2.03    spl2_250 <=> k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_250])])).
% 12.95/2.03  fof(f6763,plain,(
% 12.95/2.03    spl2_199 <=> k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_pre_topc(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_199])])).
% 12.95/2.03  fof(f13360,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1))) | ~spl2_199),
% 12.95/2.03    inference(superposition,[],[f1504,f6765])).
% 12.95/2.03  fof(f6765,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_pre_topc(sK0,sK1))) | ~spl2_199),
% 12.95/2.03    inference(avatar_component_clause,[],[f6763])).
% 12.95/2.03  fof(f13470,plain,(
% 12.95/2.03    spl2_249 | ~spl2_109),
% 12.95/2.03    inference(avatar_split_clause,[],[f13359,f4799,f13467])).
% 12.95/2.03  fof(f13467,plain,(
% 12.95/2.03    spl2_249 <=> u1_struct_0(sK0) = k3_tarski(k2_tarski(u1_struct_0(sK0),u1_struct_0(sK0)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_249])])).
% 12.95/2.03  fof(f4799,plain,(
% 12.95/2.03    spl2_109 <=> u1_struct_0(sK0) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_109])])).
% 12.95/2.03  fof(f13359,plain,(
% 12.95/2.03    u1_struct_0(sK0) = k3_tarski(k2_tarski(u1_struct_0(sK0),u1_struct_0(sK0))) | ~spl2_109),
% 12.95/2.03    inference(superposition,[],[f1504,f4801])).
% 12.95/2.03  fof(f4801,plain,(
% 12.95/2.03    u1_struct_0(sK0) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) | ~spl2_109),
% 12.95/2.03    inference(avatar_component_clause,[],[f4799])).
% 12.95/2.03  fof(f13465,plain,(
% 12.95/2.03    spl2_248 | ~spl2_217),
% 12.95/2.03    inference(avatar_split_clause,[],[f13460,f7138,f13462])).
% 12.95/2.03  fof(f13462,plain,(
% 12.95/2.03    spl2_248 <=> u1_struct_0(sK0) = k3_tarski(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_248])])).
% 12.95/2.03  fof(f7138,plain,(
% 12.95/2.03    spl2_217 <=> u1_struct_0(sK0) = k3_tarski(k2_tarski(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_217])])).
% 12.95/2.03  fof(f13460,plain,(
% 12.95/2.03    u1_struct_0(sK0) = k3_tarski(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) | ~spl2_217),
% 12.95/2.03    inference(forward_demodulation,[],[f13358,f77])).
% 12.95/2.03  fof(f13358,plain,(
% 12.95/2.03    u1_struct_0(sK0) = k3_tarski(k2_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))) | ~spl2_217),
% 12.95/2.03    inference(superposition,[],[f1504,f7140])).
% 12.95/2.03  fof(f7140,plain,(
% 12.95/2.03    u1_struct_0(sK0) = k3_tarski(k2_tarski(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))) | ~spl2_217),
% 12.95/2.03    inference(avatar_component_clause,[],[f7138])).
% 12.95/2.03  fof(f12802,plain,(
% 12.95/2.03    spl2_247 | ~spl2_188 | ~spl2_236),
% 12.95/2.03    inference(avatar_split_clause,[],[f12797,f10559,f6550,f12799])).
% 12.95/2.03  fof(f12799,plain,(
% 12.95/2.03    spl2_247 <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_247])])).
% 12.95/2.03  fof(f12797,plain,(
% 12.95/2.03    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | (~spl2_188 | ~spl2_236)),
% 12.95/2.03    inference(forward_demodulation,[],[f12679,f10561])).
% 12.95/2.03  fof(f12679,plain,(
% 12.95/2.03    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | ~spl2_188),
% 12.95/2.03    inference(superposition,[],[f2102,f6552])).
% 12.95/2.03  fof(f12147,plain,(
% 12.95/2.03    spl2_246 | ~spl2_233),
% 12.95/2.03    inference(avatar_split_clause,[],[f12071,f10518,f12144])).
% 12.95/2.03  fof(f12071,plain,(
% 12.95/2.03    k2_tops_1(sK0,sK1) = k4_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k3_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1))) | ~spl2_233),
% 12.95/2.03    inference(resolution,[],[f2085,f10520])).
% 12.95/2.03  fof(f12142,plain,(
% 12.95/2.03    spl2_245 | ~spl2_223),
% 12.95/2.03    inference(avatar_split_clause,[],[f12069,f7482,f12139])).
% 12.95/2.03  fof(f12069,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) | ~spl2_223),
% 12.95/2.03    inference(resolution,[],[f2085,f7484])).
% 12.95/2.03  fof(f12137,plain,(
% 12.95/2.03    spl2_244 | ~spl2_198),
% 12.95/2.03    inference(avatar_split_clause,[],[f12068,f6757,f12134])).
% 12.95/2.03  fof(f12068,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k4_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) | ~spl2_198),
% 12.95/2.03    inference(resolution,[],[f2085,f6759])).
% 12.95/2.03  fof(f12120,plain,(
% 12.95/2.03    spl2_243 | ~spl2_216),
% 12.95/2.03    inference(avatar_split_clause,[],[f11854,f7133,f12117])).
% 12.95/2.03  fof(f12117,plain,(
% 12.95/2.03    spl2_243 <=> k5_xboole_0(u1_struct_0(sK0),sK1) = k4_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1),k3_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_243])])).
% 12.95/2.03  fof(f7133,plain,(
% 12.95/2.03    spl2_216 <=> r1_tarski(k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1),k5_xboole_0(u1_struct_0(sK0),sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_216])])).
% 12.95/2.03  fof(f11854,plain,(
% 12.95/2.03    k5_xboole_0(u1_struct_0(sK0),sK1) = k4_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1),k3_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1))) | ~spl2_216),
% 12.95/2.03    inference(resolution,[],[f2085,f7135])).
% 12.95/2.03  fof(f7135,plain,(
% 12.95/2.03    r1_tarski(k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1),k5_xboole_0(u1_struct_0(sK0),sK1)) | ~spl2_216),
% 12.95/2.03    inference(avatar_component_clause,[],[f7133])).
% 12.95/2.03  fof(f11520,plain,(
% 12.95/2.03    spl2_242 | ~spl2_55 | ~spl2_109),
% 12.95/2.03    inference(avatar_split_clause,[],[f11501,f4799,f3367,f11517])).
% 12.95/2.03  fof(f11517,plain,(
% 12.95/2.03    spl2_242 <=> k1_xboole_0 = k6_subset_1(k6_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1),u1_struct_0(sK0))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_242])])).
% 12.95/2.03  fof(f11501,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k6_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1),u1_struct_0(sK0)) | (~spl2_55 | ~spl2_109)),
% 12.95/2.03    inference(superposition,[],[f11465,f3369])).
% 12.95/2.03  fof(f11465,plain,(
% 12.95/2.03    ( ! [X17] : (k1_xboole_0 = k6_subset_1(k6_subset_1(k6_subset_1(u1_struct_0(sK0),X17),sK1),u1_struct_0(sK0))) ) | ~spl2_109),
% 12.95/2.03    inference(resolution,[],[f11438,f168])).
% 12.95/2.03  fof(f11438,plain,(
% 12.95/2.03    ( ! [X2,X3] : (r1_tarski(k6_subset_1(k6_subset_1(k6_subset_1(u1_struct_0(sK0),X2),sK1),u1_struct_0(sK0)),X3)) ) | ~spl2_109),
% 12.95/2.03    inference(resolution,[],[f10973,f1041])).
% 12.95/2.03  fof(f10973,plain,(
% 12.95/2.03    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k6_subset_1(u1_struct_0(sK0),X0),sK1),k3_tarski(k2_tarski(X1,u1_struct_0(sK0))))) ) | ~spl2_109),
% 12.95/2.03    inference(resolution,[],[f10970,f107])).
% 12.95/2.03  fof(f10970,plain,(
% 12.95/2.03    ( ! [X2,X3] : (r1_tarski(k6_subset_1(k6_subset_1(k6_subset_1(u1_struct_0(sK0),X2),sK1),X3),u1_struct_0(sK0))) ) | ~spl2_109),
% 12.95/2.03    inference(superposition,[],[f10339,f863])).
% 12.95/2.03  fof(f10339,plain,(
% 12.95/2.03    ( ! [X4,X3] : (r1_tarski(k1_setfam_1(k2_tarski(k6_subset_1(k6_subset_1(u1_struct_0(sK0),X3),sK1),X4)),u1_struct_0(sK0))) ) | ~spl2_109),
% 12.95/2.03    inference(resolution,[],[f10325,f161])).
% 12.95/2.03  fof(f10325,plain,(
% 12.95/2.03    ( ! [X4] : (r1_tarski(k6_subset_1(k6_subset_1(u1_struct_0(sK0),X4),sK1),u1_struct_0(sK0))) ) | ~spl2_109),
% 12.95/2.03    inference(superposition,[],[f1037,f4801])).
% 12.95/2.03  fof(f1037,plain,(
% 12.95/2.03    ( ! [X8,X7,X9] : (r1_tarski(k6_subset_1(k6_subset_1(k3_tarski(k2_tarski(X7,X8)),X9),X7),X8)) )),
% 12.95/2.03    inference(resolution,[],[f106,f99])).
% 12.95/2.03  fof(f10910,plain,(
% 12.95/2.03    spl2_241 | ~spl2_92 | ~spl2_116),
% 12.95/2.03    inference(avatar_split_clause,[],[f10902,f4958,f4511,f10904])).
% 12.95/2.03  fof(f10904,plain,(
% 12.95/2.03    spl2_241 <=> k1_xboole_0 = k6_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),u1_struct_0(sK0))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_241])])).
% 12.95/2.03  fof(f4511,plain,(
% 12.95/2.03    spl2_92 <=> k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) = k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_92])])).
% 12.95/2.03  fof(f4958,plain,(
% 12.95/2.03    spl2_116 <=> k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_116])])).
% 12.95/2.03  fof(f10902,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),u1_struct_0(sK0)) | (~spl2_92 | ~spl2_116)),
% 12.95/2.03    inference(resolution,[],[f10884,f104])).
% 12.95/2.03  fof(f10884,plain,(
% 12.95/2.03    ( ! [X0] : (r1_tarski(k6_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),u1_struct_0(sK0)),X0)) ) | (~spl2_92 | ~spl2_116)),
% 12.95/2.03    inference(resolution,[],[f5145,f1041])).
% 12.95/2.03  fof(f5145,plain,(
% 12.95/2.03    ( ! [X150] : (r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k3_tarski(k2_tarski(X150,u1_struct_0(sK0))))) ) | (~spl2_92 | ~spl2_116)),
% 12.95/2.03    inference(resolution,[],[f1309,f4966])).
% 12.95/2.03  fof(f4966,plain,(
% 12.95/2.03    ( ! [X1] : (~r1_tarski(u1_struct_0(sK0),X1) | r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),X1)) ) | (~spl2_92 | ~spl2_116)),
% 12.95/2.03    inference(backward_demodulation,[],[f4612,f4960])).
% 12.95/2.03  fof(f4960,plain,(
% 12.95/2.03    k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) | ~spl2_116),
% 12.95/2.03    inference(avatar_component_clause,[],[f4958])).
% 12.95/2.03  fof(f4612,plain,(
% 12.95/2.03    ( ! [X1] : (r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),X1) | ~r1_tarski(u1_struct_0(sK0),X1)) ) | ~spl2_92),
% 12.95/2.03    inference(superposition,[],[f151,f4513])).
% 12.95/2.03  fof(f4513,plain,(
% 12.95/2.03    k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) = k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) | ~spl2_92),
% 12.95/2.03    inference(avatar_component_clause,[],[f4511])).
% 12.95/2.03  fof(f10907,plain,(
% 12.95/2.03    spl2_241 | ~spl2_92 | ~spl2_116),
% 12.95/2.03    inference(avatar_split_clause,[],[f10899,f4958,f4511,f10904])).
% 12.95/2.03  fof(f10899,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),u1_struct_0(sK0)) | (~spl2_92 | ~spl2_116)),
% 12.95/2.03    inference(resolution,[],[f10884,f168])).
% 12.95/2.03  fof(f10587,plain,(
% 12.95/2.03    spl2_240 | ~spl2_197 | ~spl2_237),
% 12.95/2.03    inference(avatar_split_clause,[],[f10572,f10566,f6741,f10584])).
% 12.95/2.03  fof(f6741,plain,(
% 12.95/2.03    spl2_197 <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_197])])).
% 12.95/2.03  fof(f10572,plain,(
% 12.95/2.03    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | (~spl2_197 | ~spl2_237)),
% 12.95/2.03    inference(backward_demodulation,[],[f6743,f10568])).
% 12.95/2.03  fof(f6743,plain,(
% 12.95/2.03    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | ~spl2_197),
% 12.95/2.03    inference(avatar_component_clause,[],[f6741])).
% 12.95/2.03  fof(f10582,plain,(
% 12.95/2.03    spl2_239 | ~spl2_195 | ~spl2_237),
% 12.95/2.03    inference(avatar_split_clause,[],[f10571,f10566,f6731,f10579])).
% 12.95/2.03  fof(f10579,plain,(
% 12.95/2.03    spl2_239 <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_239])])).
% 12.95/2.03  fof(f6731,plain,(
% 12.95/2.03    spl2_195 <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_195])])).
% 12.95/2.03  fof(f10571,plain,(
% 12.95/2.03    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | (~spl2_195 | ~spl2_237)),
% 12.95/2.03    inference(backward_demodulation,[],[f6733,f10568])).
% 12.95/2.03  fof(f6733,plain,(
% 12.95/2.03    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | ~spl2_195),
% 12.95/2.03    inference(avatar_component_clause,[],[f6731])).
% 12.95/2.03  fof(f10577,plain,(
% 12.95/2.03    spl2_238 | ~spl2_194 | ~spl2_237),
% 12.95/2.03    inference(avatar_split_clause,[],[f10570,f10566,f6726,f10574])).
% 12.95/2.03  fof(f10574,plain,(
% 12.95/2.03    spl2_238 <=> k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_238])])).
% 12.95/2.03  fof(f6726,plain,(
% 12.95/2.03    spl2_194 <=> k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_194])])).
% 12.95/2.03  fof(f10570,plain,(
% 12.95/2.03    k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | (~spl2_194 | ~spl2_237)),
% 12.95/2.03    inference(backward_demodulation,[],[f6728,f10568])).
% 12.95/2.03  fof(f6728,plain,(
% 12.95/2.03    k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | ~spl2_194),
% 12.95/2.03    inference(avatar_component_clause,[],[f6726])).
% 12.95/2.03  fof(f10569,plain,(
% 12.95/2.03    spl2_237 | ~spl2_196 | ~spl2_236),
% 12.95/2.03    inference(avatar_split_clause,[],[f10564,f10559,f6736,f10566])).
% 12.95/2.03  fof(f6736,plain,(
% 12.95/2.03    spl2_196 <=> k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k6_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_196])])).
% 12.95/2.03  fof(f10564,plain,(
% 12.95/2.03    k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | (~spl2_196 | ~spl2_236)),
% 12.95/2.03    inference(backward_demodulation,[],[f6738,f10561])).
% 12.95/2.03  fof(f6738,plain,(
% 12.95/2.03    k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k6_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~spl2_196),
% 12.95/2.03    inference(avatar_component_clause,[],[f6736])).
% 12.95/2.03  fof(f10562,plain,(
% 12.95/2.03    spl2_236 | ~spl2_188),
% 12.95/2.03    inference(avatar_split_clause,[],[f10551,f6550,f10559])).
% 12.95/2.03  fof(f10551,plain,(
% 12.95/2.03    k6_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~spl2_188),
% 12.95/2.03    inference(superposition,[],[f102,f6552])).
% 12.95/2.03  fof(f10538,plain,(
% 12.95/2.03    spl2_235 | ~spl2_233),
% 12.95/2.03    inference(avatar_split_clause,[],[f10525,f10518,f10535])).
% 12.95/2.03  fof(f10525,plain,(
% 12.95/2.03    k6_subset_1(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1))) | ~spl2_233),
% 12.95/2.03    inference(resolution,[],[f10520,f515])).
% 12.95/2.03  fof(f10533,plain,(
% 12.95/2.03    spl2_234 | ~spl2_233),
% 12.95/2.03    inference(avatar_split_clause,[],[f10524,f10518,f10530])).
% 12.95/2.03  fof(f10524,plain,(
% 12.95/2.03    k6_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1)) = k3_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_pre_topc(sK0,sK1),sK1)) | ~spl2_233),
% 12.95/2.03    inference(resolution,[],[f10520,f848])).
% 12.95/2.03  fof(f10521,plain,(
% 12.95/2.03    spl2_233 | ~spl2_175),
% 12.95/2.03    inference(avatar_split_clause,[],[f10513,f6337,f10518])).
% 12.95/2.03  fof(f10513,plain,(
% 12.95/2.03    r1_tarski(k6_subset_1(k2_pre_topc(sK0,sK1),sK1),k2_tops_1(sK0,sK1)) | ~spl2_175),
% 12.95/2.03    inference(superposition,[],[f10327,f98])).
% 12.95/2.03  fof(f10327,plain,(
% 12.95/2.03    ( ! [X6] : (r1_tarski(k6_subset_1(k6_subset_1(k2_pre_topc(sK0,sK1),X6),sK1),k2_tops_1(sK0,sK1))) ) | ~spl2_175),
% 12.95/2.03    inference(superposition,[],[f1037,f6339])).
% 12.95/2.03  fof(f10402,plain,(
% 12.95/2.03    spl2_232 | ~spl2_55 | ~spl2_217),
% 12.95/2.03    inference(avatar_split_clause,[],[f10390,f7138,f3367,f10399])).
% 12.95/2.03  fof(f10399,plain,(
% 12.95/2.03    spl2_232 <=> r1_tarski(k6_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1),k5_xboole_0(u1_struct_0(sK0),sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_232])])).
% 12.95/2.03  fof(f10390,plain,(
% 12.95/2.03    r1_tarski(k6_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),sK1),k5_xboole_0(u1_struct_0(sK0),sK1)) | (~spl2_55 | ~spl2_217)),
% 12.95/2.03    inference(superposition,[],[f10324,f3369])).
% 12.95/2.03  fof(f10324,plain,(
% 12.95/2.03    ( ! [X3] : (r1_tarski(k6_subset_1(k6_subset_1(u1_struct_0(sK0),X3),sK1),k5_xboole_0(u1_struct_0(sK0),sK1))) ) | ~spl2_217),
% 12.95/2.03    inference(superposition,[],[f1037,f7140])).
% 12.95/2.03  fof(f8230,plain,(
% 12.95/2.03    spl2_231 | ~spl2_223),
% 12.95/2.03    inference(avatar_split_clause,[],[f8171,f7482,f8227])).
% 12.95/2.03  fof(f8171,plain,(
% 12.95/2.03    k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k6_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_223),
% 12.95/2.03    inference(resolution,[],[f848,f7484])).
% 12.95/2.03  fof(f8225,plain,(
% 12.95/2.03    spl2_230 | ~spl2_198),
% 12.95/2.03    inference(avatar_split_clause,[],[f8170,f6757,f8222])).
% 12.95/2.03  fof(f8170,plain,(
% 12.95/2.03    k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k6_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_198),
% 12.95/2.03    inference(resolution,[],[f848,f6759])).
% 12.95/2.03  fof(f8210,plain,(
% 12.95/2.03    spl2_229 | ~spl2_216),
% 12.95/2.03    inference(avatar_split_clause,[],[f8022,f7133,f8207])).
% 12.95/2.03  fof(f8207,plain,(
% 12.95/2.03    spl2_229 <=> k3_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1)) = k6_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_229])])).
% 12.95/2.03  fof(f8022,plain,(
% 12.95/2.03    k3_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1)) = k6_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1)) | ~spl2_216),
% 12.95/2.03    inference(resolution,[],[f848,f7135])).
% 12.95/2.03  fof(f8012,plain,(
% 12.95/2.03    spl2_228 | ~spl2_227),
% 12.95/2.03    inference(avatar_split_clause,[],[f8007,f7976,f8009])).
% 12.95/2.03  fof(f7976,plain,(
% 12.95/2.03    spl2_227 <=> k1_xboole_0 = k6_subset_1(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_227])])).
% 12.95/2.03  fof(f8007,plain,(
% 12.95/2.03    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) | ~spl2_227),
% 12.95/2.03    inference(forward_demodulation,[],[f8006,f98])).
% 12.95/2.03  fof(f8006,plain,(
% 12.95/2.03    k6_subset_1(k1_tops_1(sK0,sK1),k1_xboole_0) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) | ~spl2_227),
% 12.95/2.03    inference(forward_demodulation,[],[f7998,f77])).
% 12.95/2.03  fof(f7998,plain,(
% 12.95/2.03    k6_subset_1(k1_tops_1(sK0,sK1),k1_xboole_0) = k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))) | ~spl2_227),
% 12.95/2.03    inference(superposition,[],[f100,f7978])).
% 12.95/2.03  fof(f7978,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~spl2_227),
% 12.95/2.03    inference(avatar_component_clause,[],[f7976])).
% 12.95/2.03  fof(f7981,plain,(
% 12.95/2.03    spl2_227 | ~spl2_199 | ~spl2_201),
% 12.95/2.03    inference(avatar_split_clause,[],[f7974,f6829,f6763,f7976])).
% 12.95/2.03  fof(f6829,plain,(
% 12.95/2.03    spl2_201 <=> k1_xboole_0 = k6_subset_1(k1_tops_1(sK0,sK1),sK1)),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_201])])).
% 12.95/2.03  fof(f7974,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | (~spl2_199 | ~spl2_201)),
% 12.95/2.03    inference(resolution,[],[f7960,f104])).
% 12.95/2.03  fof(f7960,plain,(
% 12.95/2.03    ( ! [X0] : (r1_tarski(k6_subset_1(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)),X0)) ) | (~spl2_199 | ~spl2_201)),
% 12.95/2.03    inference(resolution,[],[f7949,f106])).
% 12.95/2.03  fof(f7949,plain,(
% 12.95/2.03    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK1),k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),X0)))) ) | (~spl2_199 | ~spl2_201)),
% 12.95/2.03    inference(superposition,[],[f7837,f77])).
% 12.95/2.03  fof(f7837,plain,(
% 12.95/2.03    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK1),k3_tarski(k2_tarski(X0,k2_pre_topc(sK0,sK1))))) ) | (~spl2_199 | ~spl2_201)),
% 12.95/2.03    inference(resolution,[],[f7793,f107])).
% 12.95/2.03  fof(f7793,plain,(
% 12.95/2.03    ( ! [X2] : (r1_tarski(k6_subset_1(k1_tops_1(sK0,sK1),X2),k2_pre_topc(sK0,sK1))) ) | (~spl2_199 | ~spl2_201)),
% 12.95/2.03    inference(superposition,[],[f7761,f6765])).
% 12.95/2.03  fof(f7761,plain,(
% 12.95/2.03    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k1_tops_1(sK0,sK1),X1),k3_tarski(k2_tarski(sK1,X0)))) ) | ~spl2_201),
% 12.95/2.03    inference(superposition,[],[f7734,f77])).
% 12.95/2.03  fof(f7734,plain,(
% 12.95/2.03    ( ! [X17,X18] : (r1_tarski(k6_subset_1(k1_tops_1(sK0,sK1),X17),k3_tarski(k2_tarski(X18,sK1)))) ) | ~spl2_201),
% 12.95/2.03    inference(resolution,[],[f7497,f1309])).
% 12.95/2.03  fof(f7497,plain,(
% 12.95/2.03    ( ! [X4,X3] : (~r1_tarski(sK1,X3) | r1_tarski(k6_subset_1(k1_tops_1(sK0,sK1),X4),X3)) ) | ~spl2_201),
% 12.95/2.03    inference(resolution,[],[f7489,f95])).
% 12.95/2.03  fof(f7489,plain,(
% 12.95/2.03    ( ! [X0] : (r1_tarski(k6_subset_1(k1_tops_1(sK0,sK1),X0),sK1)) ) | ~spl2_201),
% 12.95/2.03    inference(resolution,[],[f7472,f106])).
% 12.95/2.03  fof(f7472,plain,(
% 12.95/2.03    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK1),k3_tarski(k2_tarski(X0,sK1)))) ) | ~spl2_201),
% 12.95/2.03    inference(superposition,[],[f7466,f77])).
% 12.95/2.03  fof(f7466,plain,(
% 12.95/2.03    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,X0)))) ) | ~spl2_201),
% 12.95/2.03    inference(resolution,[],[f7160,f170])).
% 12.95/2.03  fof(f170,plain,(
% 12.95/2.03    ( ! [X5] : (r1_tarski(k1_xboole_0,X5)) )),
% 12.95/2.03    inference(superposition,[],[f99,f165])).
% 12.95/2.03  fof(f7160,plain,(
% 12.95/2.03    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | r1_tarski(k1_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,X0)))) ) | ~spl2_201),
% 12.95/2.03    inference(superposition,[],[f107,f6831])).
% 12.95/2.03  fof(f6831,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k1_tops_1(sK0,sK1),sK1) | ~spl2_201),
% 12.95/2.03    inference(avatar_component_clause,[],[f6829])).
% 12.95/2.03  fof(f7979,plain,(
% 12.95/2.03    spl2_227 | ~spl2_199 | ~spl2_201),
% 12.95/2.03    inference(avatar_split_clause,[],[f7972,f6829,f6763,f7976])).
% 12.95/2.03  fof(f7972,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | (~spl2_199 | ~spl2_201)),
% 12.95/2.03    inference(resolution,[],[f7960,f168])).
% 12.95/2.03  fof(f7709,plain,(
% 12.95/2.03    spl2_226 | ~spl2_223),
% 12.95/2.03    inference(avatar_split_clause,[],[f7655,f7482,f7706])).
% 12.95/2.03  fof(f7655,plain,(
% 12.95/2.03    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) | ~spl2_223),
% 12.95/2.03    inference(resolution,[],[f515,f7484])).
% 12.95/2.03  fof(f7704,plain,(
% 12.95/2.03    spl2_225 | ~spl2_198),
% 12.95/2.03    inference(avatar_split_clause,[],[f7654,f6757,f7701])).
% 12.95/2.03  fof(f7654,plain,(
% 12.95/2.03    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) | ~spl2_198),
% 12.95/2.03    inference(resolution,[],[f515,f6759])).
% 12.95/2.03  fof(f7689,plain,(
% 12.95/2.03    spl2_224 | ~spl2_216),
% 12.95/2.03    inference(avatar_split_clause,[],[f7512,f7133,f7686])).
% 12.95/2.03  fof(f7686,plain,(
% 12.95/2.03    spl2_224 <=> k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1) = k3_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k3_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_224])])).
% 12.95/2.03  fof(f7512,plain,(
% 12.95/2.03    k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1) = k3_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k3_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1))) | ~spl2_216),
% 12.95/2.03    inference(resolution,[],[f515,f7135])).
% 12.95/2.03  fof(f7486,plain,(
% 12.95/2.03    spl2_223 | ~spl2_175 | ~spl2_201),
% 12.95/2.03    inference(avatar_split_clause,[],[f7477,f6829,f6337,f7482])).
% 12.95/2.03  fof(f7477,plain,(
% 12.95/2.03    r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | (~spl2_175 | ~spl2_201)),
% 12.95/2.03    inference(superposition,[],[f7466,f6339])).
% 12.95/2.03  fof(f7485,plain,(
% 12.95/2.03    spl2_223 | ~spl2_199 | ~spl2_201),
% 12.95/2.03    inference(avatar_split_clause,[],[f7476,f6829,f6763,f7482])).
% 12.95/2.03  fof(f7476,plain,(
% 12.95/2.03    r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | (~spl2_199 | ~spl2_201)),
% 12.95/2.03    inference(superposition,[],[f7466,f6765])).
% 12.95/2.03  fof(f7347,plain,(
% 12.95/2.03    spl2_222 | ~spl2_221),
% 12.95/2.03    inference(avatar_split_clause,[],[f7342,f7309,f7344])).
% 12.95/2.03  fof(f7309,plain,(
% 12.95/2.03    spl2_221 <=> k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_221])])).
% 12.95/2.03  fof(f7342,plain,(
% 12.95/2.03    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) | ~spl2_221),
% 12.95/2.03    inference(forward_demodulation,[],[f7341,f98])).
% 12.95/2.03  fof(f7341,plain,(
% 12.95/2.03    k6_subset_1(k2_tops_1(sK0,sK1),k1_xboole_0) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) | ~spl2_221),
% 12.95/2.03    inference(forward_demodulation,[],[f7331,f77])).
% 12.95/2.03  fof(f7331,plain,(
% 12.95/2.03    k6_subset_1(k2_tops_1(sK0,sK1),k1_xboole_0) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))) | ~spl2_221),
% 12.95/2.03    inference(superposition,[],[f100,f7311])).
% 12.95/2.03  fof(f7311,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~spl2_221),
% 12.95/2.03    inference(avatar_component_clause,[],[f7309])).
% 12.95/2.03  fof(f7314,plain,(
% 12.95/2.03    spl2_221 | ~spl2_48 | ~spl2_175),
% 12.95/2.03    inference(avatar_split_clause,[],[f7307,f6337,f2833,f7309])).
% 12.95/2.03  fof(f7307,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | (~spl2_48 | ~spl2_175)),
% 12.95/2.03    inference(resolution,[],[f7295,f104])).
% 12.95/2.03  fof(f7295,plain,(
% 12.95/2.03    ( ! [X0] : (r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)),X0)) ) | (~spl2_48 | ~spl2_175)),
% 12.95/2.03    inference(resolution,[],[f7284,f106])).
% 12.95/2.03  fof(f7284,plain,(
% 12.95/2.03    ( ! [X0] : (r1_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(k2_pre_topc(sK0,sK1),X0)))) ) | (~spl2_48 | ~spl2_175)),
% 12.95/2.03    inference(superposition,[],[f6769,f77])).
% 12.95/2.03  fof(f6769,plain,(
% 12.95/2.03    ( ! [X0] : (r1_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(X0,k2_pre_topc(sK0,sK1))))) ) | (~spl2_48 | ~spl2_175)),
% 12.95/2.03    inference(resolution,[],[f6749,f107])).
% 12.95/2.03  fof(f6749,plain,(
% 12.95/2.03    ( ! [X0] : (r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),X0),k2_pre_topc(sK0,sK1))) ) | (~spl2_48 | ~spl2_175)),
% 12.95/2.03    inference(superposition,[],[f5528,f6339])).
% 12.95/2.03  fof(f5528,plain,(
% 12.95/2.03    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),X1),k3_tarski(k2_tarski(sK1,X0)))) ) | ~spl2_48),
% 12.95/2.03    inference(superposition,[],[f5483,f77])).
% 12.95/2.03  fof(f5483,plain,(
% 12.95/2.03    ( ! [X6,X5] : (r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),X5),k3_tarski(k2_tarski(X6,sK1)))) ) | ~spl2_48),
% 12.95/2.03    inference(resolution,[],[f5163,f1309])).
% 12.95/2.03  fof(f5163,plain,(
% 12.95/2.03    ( ! [X4,X3] : (~r1_tarski(sK1,X3) | r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),X4),X3)) ) | ~spl2_48),
% 12.95/2.03    inference(resolution,[],[f5147,f95])).
% 12.95/2.03  fof(f5147,plain,(
% 12.95/2.03    ( ! [X152] : (r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),X152),sK1)) ) | ~spl2_48),
% 12.95/2.03    inference(resolution,[],[f1309,f3105])).
% 12.95/2.03  fof(f3105,plain,(
% 12.95/2.03    ( ! [X6,X5] : (~r1_tarski(sK1,k3_tarski(k2_tarski(X5,X6))) | r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),X5),X6)) ) | ~spl2_48),
% 12.95/2.03    inference(resolution,[],[f3094,f106])).
% 12.95/2.03  fof(f7312,plain,(
% 12.95/2.03    spl2_221 | ~spl2_48 | ~spl2_175),
% 12.95/2.03    inference(avatar_split_clause,[],[f7305,f6337,f2833,f7309])).
% 12.95/2.03  fof(f7305,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | (~spl2_48 | ~spl2_175)),
% 12.95/2.03    inference(resolution,[],[f7295,f168])).
% 12.95/2.03  fof(f7156,plain,(
% 12.95/2.03    spl2_220 | ~spl2_151 | ~spl2_202),
% 12.95/2.03    inference(avatar_split_clause,[],[f7064,f6843,f5965,f7153])).
% 12.95/2.03  fof(f7153,plain,(
% 12.95/2.03    spl2_220 <=> k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_220])])).
% 12.95/2.03  fof(f5965,plain,(
% 12.95/2.03    spl2_151 <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_151])])).
% 12.95/2.03  fof(f7064,plain,(
% 12.95/2.03    k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) | (~spl2_151 | ~spl2_202)),
% 12.95/2.03    inference(backward_demodulation,[],[f5967,f6845])).
% 12.95/2.03  fof(f5967,plain,(
% 12.95/2.03    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) | ~spl2_151),
% 12.95/2.03    inference(avatar_component_clause,[],[f5965])).
% 12.95/2.03  fof(f7151,plain,(
% 12.95/2.03    spl2_219 | ~spl2_137 | ~spl2_202),
% 12.95/2.03    inference(avatar_split_clause,[],[f7059,f6843,f5446,f7148])).
% 12.95/2.03  fof(f7148,plain,(
% 12.95/2.03    spl2_219 <=> k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_219])])).
% 12.95/2.03  fof(f5446,plain,(
% 12.95/2.03    spl2_137 <=> k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_137])])).
% 12.95/2.03  fof(f7059,plain,(
% 12.95/2.03    k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) | (~spl2_137 | ~spl2_202)),
% 12.95/2.03    inference(backward_demodulation,[],[f5448,f6845])).
% 12.95/2.03  fof(f5448,plain,(
% 12.95/2.03    k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) | ~spl2_137),
% 12.95/2.03    inference(avatar_component_clause,[],[f5446])).
% 12.95/2.03  fof(f7146,plain,(
% 12.95/2.03    spl2_218 | ~spl2_132 | ~spl2_202),
% 12.95/2.03    inference(avatar_split_clause,[],[f7058,f6843,f5385,f7143])).
% 12.95/2.03  fof(f7143,plain,(
% 12.95/2.03    spl2_218 <=> k1_xboole_0 = k6_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_218])])).
% 12.95/2.03  fof(f5385,plain,(
% 12.95/2.03    spl2_132 <=> k1_xboole_0 = k6_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_132])])).
% 12.95/2.03  fof(f7058,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (~spl2_132 | ~spl2_202)),
% 12.95/2.03    inference(backward_demodulation,[],[f5387,f6845])).
% 12.95/2.03  fof(f5387,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl2_132),
% 12.95/2.03    inference(avatar_component_clause,[],[f5385])).
% 12.95/2.03  fof(f7141,plain,(
% 12.95/2.03    spl2_217 | ~spl2_104 | ~spl2_202),
% 12.95/2.03    inference(avatar_split_clause,[],[f7029,f6843,f4675,f7138])).
% 12.95/2.03  fof(f4675,plain,(
% 12.95/2.03    spl2_104 <=> u1_struct_0(sK0) = k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_104])])).
% 12.95/2.03  fof(f7029,plain,(
% 12.95/2.03    u1_struct_0(sK0) = k3_tarski(k2_tarski(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))) | (~spl2_104 | ~spl2_202)),
% 12.95/2.03    inference(backward_demodulation,[],[f4677,f6845])).
% 12.95/2.03  fof(f4677,plain,(
% 12.95/2.03    u1_struct_0(sK0) = k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))) | ~spl2_104),
% 12.95/2.03    inference(avatar_component_clause,[],[f4675])).
% 12.95/2.03  fof(f7136,plain,(
% 12.95/2.03    spl2_216 | ~spl2_95 | ~spl2_202),
% 12.95/2.03    inference(avatar_split_clause,[],[f7022,f6843,f4549,f7133])).
% 12.95/2.03  fof(f4549,plain,(
% 12.95/2.03    spl2_95 <=> r1_tarski(k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1),k3_subset_1(u1_struct_0(sK0),sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_95])])).
% 12.95/2.03  fof(f7022,plain,(
% 12.95/2.03    r1_tarski(k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1),k5_xboole_0(u1_struct_0(sK0),sK1)) | (~spl2_95 | ~spl2_202)),
% 12.95/2.03    inference(backward_demodulation,[],[f4551,f6845])).
% 12.95/2.03  fof(f4551,plain,(
% 12.95/2.03    r1_tarski(k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_95),
% 12.95/2.03    inference(avatar_component_clause,[],[f4549])).
% 12.95/2.03  fof(f7131,plain,(
% 12.95/2.03    spl2_215 | ~spl2_83 | ~spl2_202),
% 12.95/2.03    inference(avatar_split_clause,[],[f7019,f6843,f4446,f7128])).
% 12.95/2.03  fof(f7128,plain,(
% 12.95/2.03    spl2_215 <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_215])])).
% 12.95/2.03  fof(f4446,plain,(
% 12.95/2.03    spl2_83 <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_83])])).
% 12.95/2.03  fof(f7019,plain,(
% 12.95/2.03    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) | (~spl2_83 | ~spl2_202)),
% 12.95/2.03    inference(backward_demodulation,[],[f4448,f6845])).
% 12.95/2.03  fof(f4448,plain,(
% 12.95/2.03    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_83),
% 12.95/2.03    inference(avatar_component_clause,[],[f4446])).
% 12.95/2.03  fof(f7126,plain,(
% 12.95/2.03    spl2_214 | ~spl2_80 | ~spl2_202),
% 12.95/2.03    inference(avatar_split_clause,[],[f7012,f6843,f4347,f7123])).
% 12.95/2.03  fof(f7123,plain,(
% 12.95/2.03    spl2_214 <=> k6_subset_1(k2_tops_1(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k6_subset_1(k2_tops_1(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),sK1))))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_214])])).
% 12.95/2.03  fof(f4347,plain,(
% 12.95/2.03    spl2_80 <=> k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).
% 12.95/2.03  fof(f7012,plain,(
% 12.95/2.03    k6_subset_1(k2_tops_1(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k6_subset_1(k2_tops_1(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),sK1)))) | (~spl2_80 | ~spl2_202)),
% 12.95/2.03    inference(backward_demodulation,[],[f4349,f6845])).
% 12.95/2.03  fof(f4349,plain,(
% 12.95/2.03    k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)))) | ~spl2_80),
% 12.95/2.03    inference(avatar_component_clause,[],[f4347])).
% 12.95/2.03  fof(f7121,plain,(
% 12.95/2.03    spl2_213 | ~spl2_79 | ~spl2_202),
% 12.95/2.03    inference(avatar_split_clause,[],[f7011,f6843,f4328,f7118])).
% 12.95/2.03  fof(f7118,plain,(
% 12.95/2.03    spl2_213 <=> k1_xboole_0 = k6_subset_1(k6_subset_1(k2_tops_1(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_213])])).
% 12.95/2.03  fof(f4328,plain,(
% 12.95/2.03    spl2_79 <=> k1_xboole_0 = k6_subset_1(k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_79])])).
% 12.95/2.03  fof(f7011,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k6_subset_1(k2_tops_1(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) | (~spl2_79 | ~spl2_202)),
% 12.95/2.03    inference(backward_demodulation,[],[f4330,f6845])).
% 12.95/2.03  fof(f4330,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) | ~spl2_79),
% 12.95/2.03    inference(avatar_component_clause,[],[f4328])).
% 12.95/2.03  fof(f7116,plain,(
% 12.95/2.03    spl2_212 | ~spl2_29 | ~spl2_202),
% 12.95/2.03    inference(avatar_split_clause,[],[f6922,f6843,f2105,f7113])).
% 12.95/2.03  fof(f7113,plain,(
% 12.95/2.03    spl2_212 <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(u1_struct_0(sK0),sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_212])])).
% 12.95/2.03  fof(f2105,plain,(
% 12.95/2.03    spl2_29 <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 12.95/2.03  fof(f6922,plain,(
% 12.95/2.03    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) | (~spl2_29 | ~spl2_202)),
% 12.95/2.03    inference(backward_demodulation,[],[f2107,f6845])).
% 12.95/2.03  fof(f2107,plain,(
% 12.95/2.03    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_29),
% 12.95/2.03    inference(avatar_component_clause,[],[f2105])).
% 12.95/2.03  fof(f7111,plain,(
% 12.95/2.03    spl2_211 | ~spl2_28 | ~spl2_202),
% 12.95/2.03    inference(avatar_split_clause,[],[f6921,f6843,f2098,f7108])).
% 12.95/2.03  fof(f7108,plain,(
% 12.95/2.03    spl2_211 <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1),sK1)),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_211])])).
% 12.95/2.03  fof(f2098,plain,(
% 12.95/2.03    spl2_28 <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1)),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 12.95/2.03  fof(f6921,plain,(
% 12.95/2.03    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1),sK1) | (~spl2_28 | ~spl2_202)),
% 12.95/2.03    inference(backward_demodulation,[],[f2100,f6845])).
% 12.95/2.03  fof(f2100,plain,(
% 12.95/2.03    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) | ~spl2_28),
% 12.95/2.03    inference(avatar_component_clause,[],[f2098])).
% 12.95/2.03  fof(f7106,plain,(
% 12.95/2.03    spl2_210 | ~spl2_20 | ~spl2_202),
% 12.95/2.03    inference(avatar_split_clause,[],[f6861,f6843,f994,f7103])).
% 12.95/2.03  fof(f7103,plain,(
% 12.95/2.03    spl2_210 <=> sK1 = k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_210])])).
% 12.95/2.03  fof(f994,plain,(
% 12.95/2.03    spl2_20 <=> sK1 = k5_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 12.95/2.03  fof(f6861,plain,(
% 12.95/2.03    sK1 = k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) | (~spl2_20 | ~spl2_202)),
% 12.95/2.03    inference(backward_demodulation,[],[f996,f6845])).
% 12.95/2.03  fof(f996,plain,(
% 12.95/2.03    sK1 = k5_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_20),
% 12.95/2.03    inference(avatar_component_clause,[],[f994])).
% 12.95/2.03  fof(f7101,plain,(
% 12.95/2.03    ~spl2_209 | spl2_19 | ~spl2_202),
% 12.95/2.03    inference(avatar_split_clause,[],[f6855,f6843,f965,f7098])).
% 12.95/2.03  fof(f7098,plain,(
% 12.95/2.03    spl2_209 <=> r1_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),sK1)),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_209])])).
% 12.95/2.03  fof(f965,plain,(
% 12.95/2.03    spl2_19 <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),sK1)),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 12.95/2.03  fof(f6855,plain,(
% 12.95/2.03    ~r1_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),sK1) | (spl2_19 | ~spl2_202)),
% 12.95/2.03    inference(backward_demodulation,[],[f967,f6845])).
% 12.95/2.03  fof(f967,plain,(
% 12.95/2.03    ~r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),sK1) | spl2_19),
% 12.95/2.03    inference(avatar_component_clause,[],[f965])).
% 12.95/2.03  fof(f7096,plain,(
% 12.95/2.03    spl2_208 | ~spl2_17 | ~spl2_202),
% 12.95/2.03    inference(avatar_split_clause,[],[f6854,f6843,f956,f7093])).
% 12.95/2.03  fof(f7093,plain,(
% 12.95/2.03    spl2_208 <=> k5_xboole_0(u1_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_208])])).
% 12.95/2.03  fof(f956,plain,(
% 12.95/2.03    spl2_17 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 12.95/2.03  fof(f6854,plain,(
% 12.95/2.03    k5_xboole_0(u1_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))) | (~spl2_17 | ~spl2_202)),
% 12.95/2.03    inference(backward_demodulation,[],[f958,f6845])).
% 12.95/2.03  fof(f958,plain,(
% 12.95/2.03    k3_subset_1(u1_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) | ~spl2_17),
% 12.95/2.03    inference(avatar_component_clause,[],[f956])).
% 12.95/2.03  fof(f7091,plain,(
% 12.95/2.03    spl2_207 | ~spl2_15 | ~spl2_202),
% 12.95/2.03    inference(avatar_split_clause,[],[f6853,f6843,f913,f7088])).
% 12.95/2.03  fof(f7088,plain,(
% 12.95/2.03    spl2_207 <=> sK1 = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_207])])).
% 12.95/2.03  fof(f6853,plain,(
% 12.95/2.03    sK1 = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) | (~spl2_15 | ~spl2_202)),
% 12.95/2.03    inference(backward_demodulation,[],[f915,f6845])).
% 12.95/2.03  fof(f7086,plain,(
% 12.95/2.03    spl2_206 | ~spl2_13 | ~spl2_202),
% 12.95/2.03    inference(avatar_split_clause,[],[f6851,f6843,f895,f7083])).
% 12.95/2.03  fof(f7083,plain,(
% 12.95/2.03    spl2_206 <=> r1_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_206])])).
% 12.95/2.03  fof(f895,plain,(
% 12.95/2.03    spl2_13 <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 12.95/2.03  fof(f6851,plain,(
% 12.95/2.03    r1_tarski(k5_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (~spl2_13 | ~spl2_202)),
% 12.95/2.03    inference(backward_demodulation,[],[f897,f6845])).
% 12.95/2.03  fof(f897,plain,(
% 12.95/2.03    r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl2_13),
% 12.95/2.03    inference(avatar_component_clause,[],[f895])).
% 12.95/2.03  fof(f7081,plain,(
% 12.95/2.03    spl2_205 | ~spl2_12 | ~spl2_202),
% 12.95/2.03    inference(avatar_split_clause,[],[f6850,f6843,f890,f7078])).
% 12.95/2.03  fof(f7078,plain,(
% 12.95/2.03    spl2_205 <=> m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_205])])).
% 12.95/2.03  fof(f890,plain,(
% 12.95/2.03    spl2_12 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 12.95/2.03  fof(f6850,plain,(
% 12.95/2.03    m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_12 | ~spl2_202)),
% 12.95/2.03    inference(backward_demodulation,[],[f892,f6845])).
% 12.95/2.03  fof(f892,plain,(
% 12.95/2.03    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_12),
% 12.95/2.03    inference(avatar_component_clause,[],[f890])).
% 12.95/2.03  fof(f7076,plain,(
% 12.95/2.03    ~spl2_204 | spl2_11 | ~spl2_202),
% 12.95/2.03    inference(avatar_split_clause,[],[f6849,f6843,f885,f7073])).
% 12.95/2.03  fof(f7073,plain,(
% 12.95/2.03    spl2_204 <=> r1_tarski(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_204])])).
% 12.95/2.03  fof(f885,plain,(
% 12.95/2.03    spl2_11 <=> r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 12.95/2.03  fof(f6849,plain,(
% 12.95/2.03    ~r1_tarski(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) | (spl2_11 | ~spl2_202)),
% 12.95/2.03    inference(backward_demodulation,[],[f887,f6845])).
% 12.95/2.03  fof(f887,plain,(
% 12.95/2.03    ~r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | spl2_11),
% 12.95/2.03    inference(avatar_component_clause,[],[f885])).
% 12.95/2.03  fof(f7071,plain,(
% 12.95/2.03    spl2_203 | ~spl2_7 | ~spl2_202),
% 12.95/2.03    inference(avatar_split_clause,[],[f6847,f6843,f523,f7068])).
% 12.95/2.03  fof(f7068,plain,(
% 12.95/2.03    spl2_203 <=> sK1 = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_203])])).
% 12.95/2.03  fof(f523,plain,(
% 12.95/2.03    spl2_7 <=> sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 12.95/2.03  fof(f6847,plain,(
% 12.95/2.03    sK1 = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) | (~spl2_7 | ~spl2_202)),
% 12.95/2.03    inference(backward_demodulation,[],[f525,f6845])).
% 12.95/2.03  fof(f525,plain,(
% 12.95/2.03    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_7),
% 12.95/2.03    inference(avatar_component_clause,[],[f523])).
% 12.95/2.03  fof(f6846,plain,(
% 12.95/2.03    spl2_202 | ~spl2_8 | ~spl2_200),
% 12.95/2.03    inference(avatar_split_clause,[],[f6841,f6822,f865,f6843])).
% 12.95/2.03  fof(f865,plain,(
% 12.95/2.03    spl2_8 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k6_subset_1(u1_struct_0(sK0),sK1)),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 12.95/2.03  fof(f6841,plain,(
% 12.95/2.03    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) | (~spl2_8 | ~spl2_200)),
% 12.95/2.03    inference(backward_demodulation,[],[f867,f6824])).
% 12.95/2.03  fof(f867,plain,(
% 12.95/2.03    k3_subset_1(u1_struct_0(sK0),sK1) = k6_subset_1(u1_struct_0(sK0),sK1) | ~spl2_8),
% 12.95/2.03    inference(avatar_component_clause,[],[f865])).
% 12.95/2.03  fof(f6832,plain,(
% 12.95/2.03    spl2_201 | ~spl2_173),
% 12.95/2.03    inference(avatar_split_clause,[],[f6827,f6324,f6829])).
% 12.95/2.03  fof(f6324,plain,(
% 12.95/2.03    spl2_173 <=> k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_173])])).
% 12.95/2.03  fof(f6827,plain,(
% 12.95/2.03    k1_xboole_0 = k6_subset_1(k1_tops_1(sK0,sK1),sK1) | ~spl2_173),
% 12.95/2.03    inference(forward_demodulation,[],[f6806,f287])).
% 12.95/2.03  fof(f287,plain,(
% 12.95/2.03    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 12.95/2.03    inference(forward_demodulation,[],[f284,f165])).
% 12.95/2.03  fof(f284,plain,(
% 12.95/2.03    ( ! [X1] : (k6_subset_1(X1,X1) = k5_xboole_0(X1,X1)) )),
% 12.95/2.03    inference(superposition,[],[f102,f171])).
% 12.95/2.03  fof(f171,plain,(
% 12.95/2.03    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 12.95/2.03    inference(forward_demodulation,[],[f166,f98])).
% 12.95/2.03  fof(f166,plain,(
% 12.95/2.03    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = k1_setfam_1(k2_tarski(X0,X0))) )),
% 12.95/2.03    inference(superposition,[],[f100,f165])).
% 12.95/2.03  fof(f6806,plain,(
% 12.95/2.03    k6_subset_1(k1_tops_1(sK0,sK1),sK1) = k5_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_173),
% 12.95/2.03    inference(superposition,[],[f281,f6326])).
% 12.95/2.03  fof(f6326,plain,(
% 12.95/2.03    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) | ~spl2_173),
% 12.95/2.03    inference(avatar_component_clause,[],[f6324])).
% 12.95/2.03  fof(f281,plain,(
% 12.95/2.03    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))) )),
% 12.95/2.03    inference(superposition,[],[f102,f77])).
% 12.95/2.03  fof(f6825,plain,(
% 12.95/2.03    spl2_200 | ~spl2_14),
% 12.95/2.03    inference(avatar_split_clause,[],[f6804,f907,f6822])).
% 12.95/2.03  fof(f907,plain,(
% 12.95/2.03    spl2_14 <=> sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 12.95/2.03  fof(f6804,plain,(
% 12.95/2.03    k6_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) | ~spl2_14),
% 12.95/2.03    inference(superposition,[],[f281,f909])).
% 12.95/2.03  fof(f909,plain,(
% 12.95/2.03    sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) | ~spl2_14),
% 12.95/2.03    inference(avatar_component_clause,[],[f907])).
% 12.95/2.03  fof(f6766,plain,(
% 12.95/2.03    spl2_199 | ~spl2_175),
% 12.95/2.03    inference(avatar_split_clause,[],[f6754,f6337,f6763])).
% 12.95/2.03  fof(f6754,plain,(
% 12.95/2.03    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_pre_topc(sK0,sK1))) | ~spl2_175),
% 12.95/2.03    inference(superposition,[],[f101,f6339])).
% 12.95/2.03  fof(f6761,plain,(
% 12.95/2.03    spl2_198 | ~spl2_175),
% 12.95/2.03    inference(avatar_split_clause,[],[f6751,f6337,f6757])).
% 12.95/2.03  fof(f6751,plain,(
% 12.95/2.03    r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~spl2_175),
% 12.95/2.03    inference(superposition,[],[f1309,f6339])).
% 12.95/2.03  fof(f6760,plain,(
% 12.95/2.03    spl2_198 | ~spl2_48 | ~spl2_175),
% 12.95/2.03    inference(avatar_split_clause,[],[f6750,f6337,f2833,f6757])).
% 12.95/2.03  fof(f6750,plain,(
% 12.95/2.03    r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | (~spl2_48 | ~spl2_175)),
% 12.95/2.03    inference(superposition,[],[f5168,f6339])).
% 12.95/2.03  fof(f5168,plain,(
% 12.95/2.03    ( ! [X0] : (r1_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,X0)))) ) | ~spl2_48),
% 12.95/2.03    inference(resolution,[],[f5146,f107])).
% 12.95/2.03  fof(f5146,plain,(
% 12.95/2.03    ( ! [X151] : (r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),sK1),X151)) ) | ~spl2_48),
% 12.95/2.03    inference(resolution,[],[f1309,f3573])).
% 12.95/2.03  fof(f3573,plain,(
% 12.95/2.03    ( ! [X0,X1] : (~r1_tarski(sK1,k3_tarski(k2_tarski(X1,X0))) | r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),X0),X1)) ) | ~spl2_48),
% 12.95/2.03    inference(superposition,[],[f3105,f77])).
% 12.95/2.03  fof(f6744,plain,(
% 12.95/2.03    spl2_197 | ~spl2_189),
% 12.95/2.03    inference(avatar_split_clause,[],[f6708,f6690,f6741])).
% 12.95/2.03  fof(f6708,plain,(
% 12.95/2.03    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | ~spl2_189),
% 12.95/2.03    inference(resolution,[],[f6692,f86])).
% 12.95/2.03  fof(f6739,plain,(
% 12.95/2.03    spl2_196 | ~spl2_189),
% 12.95/2.03    inference(avatar_split_clause,[],[f6707,f6690,f6736])).
% 12.95/2.03  fof(f6707,plain,(
% 12.95/2.03    k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k6_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~spl2_189),
% 12.95/2.03    inference(resolution,[],[f6692,f103])).
% 12.95/2.03  fof(f6734,plain,(
% 12.95/2.03    spl2_195 | ~spl2_189),
% 12.95/2.03    inference(avatar_split_clause,[],[f6705,f6690,f6731])).
% 12.95/2.03  fof(f6705,plain,(
% 12.95/2.03    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | ~spl2_189),
% 12.95/2.03    inference(resolution,[],[f6692,f134])).
% 12.95/2.03  fof(f6729,plain,(
% 12.95/2.03    spl2_194 | ~spl2_4 | ~spl2_189),
% 12.95/2.03    inference(avatar_split_clause,[],[f6703,f6690,f125,f6726])).
% 12.95/2.03  fof(f125,plain,(
% 12.95/2.03    spl2_4 <=> l1_pre_topc(sK0)),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 12.95/2.03  fof(f6703,plain,(
% 12.95/2.03    k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | (~spl2_4 | ~spl2_189)),
% 12.95/2.03    inference(resolution,[],[f6692,f3224])).
% 12.95/2.03  fof(f3224,plain,(
% 12.95/2.03    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) | ~spl2_4),
% 12.95/2.03    inference(resolution,[],[f69,f127])).
% 12.95/2.03  fof(f127,plain,(
% 12.95/2.03    l1_pre_topc(sK0) | ~spl2_4),
% 12.95/2.03    inference(avatar_component_clause,[],[f125])).
% 12.95/2.03  fof(f69,plain,(
% 12.95/2.03    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))) )),
% 12.95/2.03    inference(cnf_transformation,[],[f34])).
% 12.95/2.03  fof(f34,plain,(
% 12.95/2.03    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 12.95/2.03    inference(ennf_transformation,[],[f26])).
% 12.95/2.03  fof(f26,axiom,(
% 12.95/2.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).
% 12.95/2.03  fof(f6724,plain,(
% 12.95/2.03    spl2_193 | ~spl2_3 | ~spl2_189),
% 12.95/2.03    inference(avatar_split_clause,[],[f6702,f6690,f120,f6721])).
% 12.95/2.03  fof(f6721,plain,(
% 12.95/2.03    spl2_193 <=> k4_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k1_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_193])])).
% 12.95/2.03  fof(f120,plain,(
% 12.95/2.03    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 12.95/2.03  fof(f6702,plain,(
% 12.95/2.03    k4_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k1_tops_1(sK0,sK1))) | (~spl2_3 | ~spl2_189)),
% 12.95/2.03    inference(resolution,[],[f6692,f3703])).
% 12.95/2.03  fof(f3703,plain,(
% 12.95/2.03    ( ! [X27] : (~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X27) = k3_tarski(k2_tarski(sK1,X27))) ) | ~spl2_3),
% 12.95/2.03    inference(resolution,[],[f108,f122])).
% 12.95/2.03  fof(f122,plain,(
% 12.95/2.03    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 12.95/2.03    inference(avatar_component_clause,[],[f120])).
% 12.95/2.03  fof(f108,plain,(
% 12.95/2.03    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))) )),
% 12.95/2.03    inference(definition_unfolding,[],[f96,f80])).
% 12.95/2.03  fof(f96,plain,(
% 12.95/2.03    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 12.95/2.03    inference(cnf_transformation,[],[f54])).
% 12.95/2.03  fof(f54,plain,(
% 12.95/2.03    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 12.95/2.03    inference(flattening,[],[f53])).
% 12.95/2.03  fof(f53,plain,(
% 12.95/2.03    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 12.95/2.03    inference(ennf_transformation,[],[f18])).
% 12.95/2.03  fof(f18,axiom,(
% 12.95/2.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 12.95/2.03  fof(f6719,plain,(
% 12.95/2.03    spl2_192 | ~spl2_4 | ~spl2_189),
% 12.95/2.03    inference(avatar_split_clause,[],[f6701,f6690,f125,f6716])).
% 12.95/2.03  fof(f6716,plain,(
% 12.95/2.03    spl2_192 <=> k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_192])])).
% 12.95/2.03  fof(f6701,plain,(
% 12.95/2.03    k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) | (~spl2_4 | ~spl2_189)),
% 12.95/2.03    inference(resolution,[],[f6692,f3862])).
% 12.95/2.03  fof(f3862,plain,(
% 12.95/2.03    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | ~spl2_4),
% 12.95/2.03    inference(resolution,[],[f70,f127])).
% 12.95/2.03  fof(f70,plain,(
% 12.95/2.03    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 12.95/2.03    inference(cnf_transformation,[],[f35])).
% 12.95/2.03  fof(f35,plain,(
% 12.95/2.03    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 12.95/2.03    inference(ennf_transformation,[],[f29])).
% 12.95/2.03  fof(f29,axiom,(
% 12.95/2.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 12.95/2.03  fof(f6714,plain,(
% 12.95/2.03    spl2_191 | ~spl2_4 | ~spl2_189),
% 12.95/2.03    inference(avatar_split_clause,[],[f6700,f6690,f125,f6711])).
% 12.95/2.03  fof(f6711,plain,(
% 12.95/2.03    spl2_191 <=> k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1)))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_191])])).
% 12.95/2.03  fof(f6700,plain,(
% 12.95/2.03    k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) | (~spl2_4 | ~spl2_189)),
% 12.95/2.03    inference(resolution,[],[f6692,f4111])).
% 12.95/2.03  fof(f4111,plain,(
% 12.95/2.03    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | ~spl2_4),
% 12.95/2.03    inference(resolution,[],[f71,f127])).
% 12.95/2.03  fof(f71,plain,(
% 12.95/2.03    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 12.95/2.03    inference(cnf_transformation,[],[f36])).
% 12.95/2.03  fof(f36,plain,(
% 12.95/2.03    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 12.95/2.03    inference(ennf_transformation,[],[f27])).
% 12.95/2.03  fof(f27,axiom,(
% 12.95/2.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 12.95/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 12.95/2.03  fof(f6699,plain,(
% 12.95/2.03    spl2_190 | ~spl2_22 | ~spl2_173),
% 12.95/2.03    inference(avatar_split_clause,[],[f6694,f6324,f1773,f6696])).
% 12.95/2.03  fof(f6696,plain,(
% 12.95/2.03    spl2_190 <=> k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_190])])).
% 12.95/2.03  fof(f6694,plain,(
% 12.95/2.03    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_22 | ~spl2_173)),
% 12.95/2.03    inference(forward_demodulation,[],[f6684,f1774])).
% 12.95/2.03  fof(f6684,plain,(
% 12.95/2.03    k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_173),
% 12.95/2.03    inference(superposition,[],[f102,f6326])).
% 12.95/2.03  fof(f6693,plain,(
% 12.95/2.03    spl2_189 | ~spl2_16 | ~spl2_173),
% 12.95/2.03    inference(avatar_split_clause,[],[f6679,f6324,f939,f6690])).
% 12.95/2.03  fof(f939,plain,(
% 12.95/2.03    spl2_16 <=> k1_xboole_0 = k6_subset_1(sK1,u1_struct_0(sK0))),
% 12.95/2.03    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 12.95/2.03  fof(f6679,plain,(
% 12.95/2.03    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_16 | ~spl2_173)),
% 12.95/2.03    inference(superposition,[],[f2292,f6326])).
% 12.95/2.03  fof(f2292,plain,(
% 12.95/2.03    ( ! [X60] : (m1_subset_1(k1_setfam_1(k2_tarski(sK1,X60)),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_16),
% 12.95/2.03    inference(superposition,[],[f163,f1409])).
% 12.95/2.03  fof(f1409,plain,(
% 12.95/2.03    ( ! [X2] : (k1_setfam_1(k2_tarski(sK1,X2)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,X2))))) ) | ~spl2_16),
% 12.95/2.03    inference(forward_demodulation,[],[f1408,f77])).
% 12.95/2.03  fof(f1408,plain,(
% 12.95/2.03    ( ! [X2] : (k1_setfam_1(k2_tarski(sK1,X2)) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(sK1,X2)),u1_struct_0(sK0)))) ) | ~spl2_16),
% 12.95/2.04    inference(forward_demodulation,[],[f1402,f98])).
% 12.95/2.04  fof(f1402,plain,(
% 12.95/2.04    ( ! [X2] : (k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(sK1,X2)),u1_struct_0(sK0))) = k6_subset_1(k1_setfam_1(k2_tarski(sK1,X2)),k1_xboole_0)) ) | ~spl2_16),
% 12.95/2.04    inference(superposition,[],[f100,f1379])).
% 12.95/2.04  fof(f1379,plain,(
% 12.95/2.04    ( ! [X10] : (k1_xboole_0 = k6_subset_1(k1_setfam_1(k2_tarski(sK1,X10)),u1_struct_0(sK0))) ) | ~spl2_16),
% 12.95/2.04    inference(resolution,[],[f1365,f168])).
% 12.95/2.04  fof(f1365,plain,(
% 12.95/2.04    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k1_setfam_1(k2_tarski(sK1,X0)),u1_struct_0(sK0)),X1)) ) | ~spl2_16),
% 12.95/2.04    inference(resolution,[],[f1323,f106])).
% 12.95/2.04  fof(f1323,plain,(
% 12.95/2.04    ( ! [X2,X1] : (r1_tarski(k1_setfam_1(k2_tarski(sK1,X1)),k3_tarski(k2_tarski(u1_struct_0(sK0),X2)))) ) | ~spl2_16),
% 12.95/2.04    inference(resolution,[],[f1320,f161])).
% 12.95/2.04  fof(f1320,plain,(
% 12.95/2.04    ( ! [X0] : (r1_tarski(sK1,k3_tarski(k2_tarski(u1_struct_0(sK0),X0)))) ) | ~spl2_16),
% 12.95/2.04    inference(resolution,[],[f1318,f170])).
% 12.95/2.04  fof(f1318,plain,(
% 12.95/2.04    ( ! [X11] : (~r1_tarski(k1_xboole_0,X11) | r1_tarski(sK1,k3_tarski(k2_tarski(u1_struct_0(sK0),X11)))) ) | ~spl2_16),
% 12.95/2.04    inference(superposition,[],[f107,f941])).
% 12.95/2.04  fof(f941,plain,(
% 12.95/2.04    k1_xboole_0 = k6_subset_1(sK1,u1_struct_0(sK0)) | ~spl2_16),
% 12.95/2.04    inference(avatar_component_clause,[],[f939])).
% 12.95/2.04  fof(f6553,plain,(
% 12.95/2.04    spl2_188 | ~spl2_168),
% 12.95/2.04    inference(avatar_split_clause,[],[f6548,f6295,f6550])).
% 12.95/2.04  fof(f6295,plain,(
% 12.95/2.04    spl2_168 <=> k1_xboole_0 = k6_subset_1(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_168])])).
% 12.95/2.04  fof(f6548,plain,(
% 12.95/2.04    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | ~spl2_168),
% 12.95/2.04    inference(forward_demodulation,[],[f6547,f98])).
% 12.95/2.04  fof(f6547,plain,(
% 12.95/2.04    k6_subset_1(k1_tops_1(sK0,sK1),k1_xboole_0) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | ~spl2_168),
% 12.95/2.04    inference(forward_demodulation,[],[f6542,f77])).
% 12.95/2.04  fof(f6542,plain,(
% 12.95/2.04    k6_subset_1(k1_tops_1(sK0,sK1),k1_xboole_0) = k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))) | ~spl2_168),
% 12.95/2.04    inference(superposition,[],[f100,f6297])).
% 12.95/2.04  fof(f6297,plain,(
% 12.95/2.04    k1_xboole_0 = k6_subset_1(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~spl2_168),
% 12.95/2.04    inference(avatar_component_clause,[],[f6295])).
% 12.95/2.04  fof(f6496,plain,(
% 12.95/2.04    spl2_187 | ~spl2_45 | ~spl2_176),
% 12.95/2.04    inference(avatar_split_clause,[],[f6415,f6351,f2819,f6493])).
% 12.95/2.04  fof(f6493,plain,(
% 12.95/2.04    spl2_187 <=> sK1 = k4_subset_1(sK1,k1_xboole_0,k2_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_187])])).
% 12.95/2.04  fof(f2819,plain,(
% 12.95/2.04    spl2_45 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 12.95/2.04  fof(f6351,plain,(
% 12.95/2.04    spl2_176 <=> sK1 = k4_subset_1(sK1,k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_176])])).
% 12.95/2.04  fof(f6415,plain,(
% 12.95/2.04    sK1 = k4_subset_1(sK1,k1_xboole_0,k2_tops_1(sK0,sK1)) | (~spl2_45 | ~spl2_176)),
% 12.95/2.04    inference(backward_demodulation,[],[f6353,f2821])).
% 12.95/2.04  fof(f2821,plain,(
% 12.95/2.04    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_45),
% 12.95/2.04    inference(avatar_component_clause,[],[f2819])).
% 12.95/2.04  fof(f6353,plain,(
% 12.95/2.04    sK1 = k4_subset_1(sK1,k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_176),
% 12.95/2.04    inference(avatar_component_clause,[],[f6351])).
% 12.95/2.04  fof(f6489,plain,(
% 12.95/2.04    ~spl2_186 | ~spl2_45 | spl2_170),
% 12.95/2.04    inference(avatar_split_clause,[],[f6408,f6307,f2819,f6486])).
% 12.95/2.04  fof(f6307,plain,(
% 12.95/2.04    spl2_170 <=> r1_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_170])])).
% 12.95/2.04  fof(f6408,plain,(
% 12.95/2.04    ~r1_tarski(k2_tops_1(sK0,sK1),k1_xboole_0) | (~spl2_45 | spl2_170)),
% 12.95/2.04    inference(backward_demodulation,[],[f6309,f2821])).
% 12.95/2.04  fof(f6309,plain,(
% 12.95/2.04    ~r1_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | spl2_170),
% 12.95/2.04    inference(avatar_component_clause,[],[f6307])).
% 12.95/2.04  fof(f6460,plain,(
% 12.95/2.04    spl2_185 | ~spl2_45 | ~spl2_164),
% 12.95/2.04    inference(avatar_split_clause,[],[f6386,f6250,f2819,f6457])).
% 12.95/2.04  fof(f6457,plain,(
% 12.95/2.04    spl2_185 <=> k1_xboole_0 = k3_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_185])])).
% 12.95/2.04  fof(f6250,plain,(
% 12.95/2.04    spl2_164 <=> k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_164])])).
% 12.95/2.04  fof(f6386,plain,(
% 12.95/2.04    k1_xboole_0 = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | (~spl2_45 | ~spl2_164)),
% 12.95/2.04    inference(backward_demodulation,[],[f6252,f2821])).
% 12.95/2.04  fof(f6252,plain,(
% 12.95/2.04    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_164),
% 12.95/2.04    inference(avatar_component_clause,[],[f6250])).
% 12.95/2.04  fof(f6455,plain,(
% 12.95/2.04    spl2_184 | ~spl2_45 | ~spl2_163),
% 12.95/2.04    inference(avatar_split_clause,[],[f6385,f6245,f2819,f6452])).
% 12.95/2.04  fof(f6452,plain,(
% 12.95/2.04    spl2_184 <=> sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k1_xboole_0)),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_184])])).
% 12.95/2.04  fof(f6245,plain,(
% 12.95/2.04    spl2_163 <=> sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_163])])).
% 12.95/2.04  fof(f6385,plain,(
% 12.95/2.04    sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k1_xboole_0) | (~spl2_45 | ~spl2_163)),
% 12.95/2.04    inference(backward_demodulation,[],[f6247,f2821])).
% 12.95/2.04  fof(f6247,plain,(
% 12.95/2.04    sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_163),
% 12.95/2.04    inference(avatar_component_clause,[],[f6245])).
% 12.95/2.04  fof(f6450,plain,(
% 12.95/2.04    spl2_179 | ~spl2_45 | ~spl2_162),
% 12.95/2.04    inference(avatar_split_clause,[],[f6449,f6240,f2819,f6423])).
% 12.95/2.04  fof(f6423,plain,(
% 12.95/2.04    spl2_179 <=> sK1 = k2_tops_1(sK0,sK1)),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_179])])).
% 12.95/2.04  fof(f6240,plain,(
% 12.95/2.04    spl2_162 <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_162])])).
% 12.95/2.04  fof(f6449,plain,(
% 12.95/2.04    sK1 = k2_tops_1(sK0,sK1) | (~spl2_45 | ~spl2_162)),
% 12.95/2.04    inference(forward_demodulation,[],[f6384,f856])).
% 12.95/2.04  fof(f6384,plain,(
% 12.95/2.04    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_xboole_0) | (~spl2_45 | ~spl2_162)),
% 12.95/2.04    inference(backward_demodulation,[],[f6242,f2821])).
% 12.95/2.04  fof(f6242,plain,(
% 12.95/2.04    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~spl2_162),
% 12.95/2.04    inference(avatar_component_clause,[],[f6240])).
% 12.95/2.04  fof(f6448,plain,(
% 12.95/2.04    spl2_183 | ~spl2_45 | ~spl2_161),
% 12.95/2.04    inference(avatar_split_clause,[],[f6383,f6232,f2819,f6445])).
% 12.95/2.04  fof(f6445,plain,(
% 12.95/2.04    spl2_183 <=> k1_xboole_0 = k5_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_183])])).
% 12.95/2.04  fof(f6232,plain,(
% 12.95/2.04    spl2_161 <=> k1_tops_1(sK0,sK1) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_161])])).
% 12.95/2.04  fof(f6383,plain,(
% 12.95/2.04    k1_xboole_0 = k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_45 | ~spl2_161)),
% 12.95/2.04    inference(backward_demodulation,[],[f6234,f2821])).
% 12.95/2.04  fof(f6234,plain,(
% 12.95/2.04    k1_tops_1(sK0,sK1) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_161),
% 12.95/2.04    inference(avatar_component_clause,[],[f6232])).
% 12.95/2.04  fof(f6443,plain,(
% 12.95/2.04    spl2_182 | ~spl2_45 | ~spl2_160),
% 12.95/2.04    inference(avatar_split_clause,[],[f6382,f6225,f2819,f6440])).
% 12.95/2.04  fof(f6440,plain,(
% 12.95/2.04    spl2_182 <=> k1_xboole_0 = k6_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_182])])).
% 12.95/2.04  fof(f6382,plain,(
% 12.95/2.04    k1_xboole_0 = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | (~spl2_45 | ~spl2_160)),
% 12.95/2.04    inference(backward_demodulation,[],[f6227,f2821])).
% 12.95/2.04  fof(f6438,plain,(
% 12.95/2.04    spl2_181 | ~spl2_45 | ~spl2_140),
% 12.95/2.04    inference(avatar_split_clause,[],[f6381,f5462,f2819,f6435])).
% 12.95/2.04  fof(f6435,plain,(
% 12.95/2.04    spl2_181 <=> k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_181])])).
% 12.95/2.04  fof(f5462,plain,(
% 12.95/2.04    spl2_140 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_140])])).
% 12.95/2.04  fof(f6381,plain,(
% 12.95/2.04    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_45 | ~spl2_140)),
% 12.95/2.04    inference(backward_demodulation,[],[f5464,f2821])).
% 12.95/2.04  fof(f5464,plain,(
% 12.95/2.04    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_140),
% 12.95/2.04    inference(avatar_component_clause,[],[f5462])).
% 12.95/2.04  fof(f6433,plain,(
% 12.95/2.04    ~spl2_180 | ~spl2_45 | spl2_46),
% 12.95/2.04    inference(avatar_split_clause,[],[f6380,f2823,f2819,f6430])).
% 12.95/2.04  fof(f6430,plain,(
% 12.95/2.04    spl2_180 <=> r1_tarski(k1_xboole_0,k2_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_180])])).
% 12.95/2.04  fof(f2823,plain,(
% 12.95/2.04    spl2_46 <=> r1_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 12.95/2.04  fof(f6380,plain,(
% 12.95/2.04    ~r1_tarski(k1_xboole_0,k2_tops_1(sK0,sK1)) | (~spl2_45 | spl2_46)),
% 12.95/2.04    inference(backward_demodulation,[],[f2825,f2821])).
% 12.95/2.04  fof(f2825,plain,(
% 12.95/2.04    ~r1_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | spl2_46),
% 12.95/2.04    inference(avatar_component_clause,[],[f2823])).
% 12.95/2.04  fof(f6428,plain,(
% 12.95/2.04    spl2_179 | ~spl2_22 | ~spl2_45),
% 12.95/2.04    inference(avatar_split_clause,[],[f6427,f2819,f1773,f6423])).
% 12.95/2.04  fof(f6427,plain,(
% 12.95/2.04    sK1 = k2_tops_1(sK0,sK1) | (~spl2_22 | ~spl2_45)),
% 12.95/2.04    inference(forward_demodulation,[],[f6379,f98])).
% 12.95/2.04  fof(f6379,plain,(
% 12.95/2.04    k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_xboole_0) | (~spl2_22 | ~spl2_45)),
% 12.95/2.04    inference(backward_demodulation,[],[f1774,f2821])).
% 12.95/2.04  fof(f6426,plain,(
% 12.95/2.04    spl2_179 | ~spl2_2 | ~spl2_3 | ~spl2_45),
% 12.95/2.04    inference(avatar_split_clause,[],[f6421,f2819,f120,f114,f6423])).
% 12.95/2.04  fof(f114,plain,(
% 12.95/2.04    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 12.95/2.04  fof(f6421,plain,(
% 12.95/2.04    sK1 = k2_tops_1(sK0,sK1) | (~spl2_2 | ~spl2_3 | ~spl2_45)),
% 12.95/2.04    inference(forward_demodulation,[],[f6420,f98])).
% 12.95/2.04  fof(f6420,plain,(
% 12.95/2.04    k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_xboole_0) | (~spl2_2 | ~spl2_3 | ~spl2_45)),
% 12.95/2.04    inference(forward_demodulation,[],[f6378,f1769])).
% 12.95/2.04  fof(f1769,plain,(
% 12.95/2.04    ( ! [X20] : (k7_subset_1(u1_struct_0(sK0),sK1,X20) = k6_subset_1(sK1,X20)) ) | ~spl2_3),
% 12.95/2.04    inference(resolution,[],[f105,f122])).
% 12.95/2.04  fof(f105,plain,(
% 12.95/2.04    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)) )),
% 12.95/2.04    inference(definition_unfolding,[],[f92,f78])).
% 12.95/2.04  fof(f92,plain,(
% 12.95/2.04    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 12.95/2.04    inference(cnf_transformation,[],[f48])).
% 12.95/2.04  fof(f48,plain,(
% 12.95/2.04    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 12.95/2.04    inference(ennf_transformation,[],[f20])).
% 12.95/2.04  fof(f20,axiom,(
% 12.95/2.04    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 12.95/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 12.95/2.04  fof(f6378,plain,(
% 12.95/2.04    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) | (~spl2_2 | ~spl2_45)),
% 12.95/2.04    inference(backward_demodulation,[],[f115,f2821])).
% 12.95/2.04  fof(f115,plain,(
% 12.95/2.04    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 12.95/2.04    inference(avatar_component_clause,[],[f114])).
% 12.95/2.04  fof(f6377,plain,(
% 12.95/2.04    spl2_45 | spl2_178 | ~spl2_160),
% 12.95/2.04    inference(avatar_split_clause,[],[f6368,f6225,f6375,f2819])).
% 12.95/2.04  fof(f6375,plain,(
% 12.95/2.04    spl2_178 <=> ! [X7] : ~r1_tarski(sK1,k6_subset_1(X7,k1_tops_1(sK0,sK1)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_178])])).
% 12.95/2.04  fof(f6368,plain,(
% 12.95/2.04    ( ! [X7] : (~r1_tarski(sK1,k6_subset_1(X7,k1_tops_1(sK0,sK1))) | k1_xboole_0 = k1_tops_1(sK0,sK1)) ) | ~spl2_160),
% 12.95/2.04    inference(resolution,[],[f6275,f104])).
% 12.95/2.04  fof(f6275,plain,(
% 12.95/2.04    ( ! [X19] : (r1_tarski(k1_tops_1(sK0,sK1),X19) | ~r1_tarski(sK1,X19)) ) | ~spl2_160),
% 12.95/2.04    inference(superposition,[],[f151,f6227])).
% 12.95/2.04  fof(f6373,plain,(
% 12.95/2.04    ~spl2_177 | spl2_46 | ~spl2_160),
% 12.95/2.04    inference(avatar_split_clause,[],[f6362,f6225,f2823,f6370])).
% 12.95/2.04  fof(f6370,plain,(
% 12.95/2.04    spl2_177 <=> r1_tarski(sK1,k2_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_177])])).
% 12.95/2.04  fof(f6362,plain,(
% 12.95/2.04    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | (spl2_46 | ~spl2_160)),
% 12.95/2.04    inference(resolution,[],[f6275,f2825])).
% 12.95/2.04  fof(f6354,plain,(
% 12.95/2.04    spl2_176 | ~spl2_162 | ~spl2_171),
% 12.95/2.04    inference(avatar_split_clause,[],[f6349,f6312,f6240,f6351])).
% 12.95/2.04  fof(f6312,plain,(
% 12.95/2.04    spl2_171 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_171])])).
% 12.95/2.04  fof(f6349,plain,(
% 12.95/2.04    sK1 = k4_subset_1(sK1,k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl2_162 | ~spl2_171)),
% 12.95/2.04    inference(forward_demodulation,[],[f6344,f6242])).
% 12.95/2.04  fof(f6344,plain,(
% 12.95/2.04    sK1 = k4_subset_1(sK1,k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) | ~spl2_171),
% 12.95/2.04    inference(resolution,[],[f6314,f134])).
% 12.95/2.04  fof(f6314,plain,(
% 12.95/2.04    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_171),
% 12.95/2.04    inference(avatar_component_clause,[],[f6312])).
% 12.95/2.04  fof(f6340,plain,(
% 12.95/2.04    spl2_175 | ~spl2_105 | ~spl2_174),
% 12.95/2.04    inference(avatar_split_clause,[],[f6335,f6331,f4680,f6337])).
% 12.95/2.04  fof(f4680,plain,(
% 12.95/2.04    spl2_105 <=> k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_105])])).
% 12.95/2.04  fof(f6331,plain,(
% 12.95/2.04    spl2_174 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_174])])).
% 12.95/2.04  fof(f6335,plain,(
% 12.95/2.04    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_105 | ~spl2_174)),
% 12.95/2.04    inference(backward_demodulation,[],[f4682,f6333])).
% 12.95/2.04  fof(f6333,plain,(
% 12.95/2.04    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_174),
% 12.95/2.04    inference(avatar_component_clause,[],[f6331])).
% 12.95/2.04  fof(f4682,plain,(
% 12.95/2.04    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_105),
% 12.95/2.04    inference(avatar_component_clause,[],[f4680])).
% 12.95/2.04  fof(f6334,plain,(
% 12.95/2.04    spl2_174 | ~spl2_3 | ~spl2_4),
% 12.95/2.04    inference(avatar_split_clause,[],[f5939,f125,f120,f6331])).
% 12.95/2.04  fof(f5939,plain,(
% 12.95/2.04    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 12.95/2.04    inference(resolution,[],[f4111,f122])).
% 12.95/2.04  fof(f6329,plain,(
% 12.95/2.04    spl2_38 | ~spl2_3 | ~spl2_4 | ~spl2_154),
% 12.95/2.04    inference(avatar_split_clause,[],[f6328,f5982,f125,f120,f2756])).
% 12.95/2.04  fof(f2756,plain,(
% 12.95/2.04    spl2_38 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 12.95/2.04  fof(f5982,plain,(
% 12.95/2.04    spl2_154 <=> sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_154])])).
% 12.95/2.04  fof(f6328,plain,(
% 12.95/2.04    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_3 | ~spl2_4 | ~spl2_154)),
% 12.95/2.04    inference(forward_demodulation,[],[f5939,f5984])).
% 12.95/2.04  fof(f5984,plain,(
% 12.95/2.04    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_154),
% 12.95/2.04    inference(avatar_component_clause,[],[f5982])).
% 12.95/2.04  fof(f6327,plain,(
% 12.95/2.04    spl2_173 | ~spl2_44 | ~spl2_160),
% 12.95/2.04    inference(avatar_split_clause,[],[f6322,f6225,f2814,f6324])).
% 12.95/2.04  fof(f2814,plain,(
% 12.95/2.04    spl2_44 <=> k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 12.95/2.04  fof(f6322,plain,(
% 12.95/2.04    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) | (~spl2_44 | ~spl2_160)),
% 12.95/2.04    inference(forward_demodulation,[],[f2816,f6227])).
% 12.95/2.04  fof(f2816,plain,(
% 12.95/2.04    k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_44),
% 12.95/2.04    inference(avatar_component_clause,[],[f2814])).
% 12.95/2.04  fof(f6321,plain,(
% 12.95/2.04    spl2_1 | ~spl2_3 | ~spl2_38 | ~spl2_62),
% 12.95/2.04    inference(avatar_split_clause,[],[f3566,f3475,f2756,f120,f110])).
% 12.95/2.04  fof(f110,plain,(
% 12.95/2.04    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 12.95/2.04  fof(f3475,plain,(
% 12.95/2.04    spl2_62 <=> ! [X0] : (k2_pre_topc(sK0,X0) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_62])])).
% 12.95/2.04  fof(f3566,plain,(
% 12.95/2.04    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(sK1,sK0) | (~spl2_38 | ~spl2_62)),
% 12.95/2.04    inference(trivial_inequality_removal,[],[f3565])).
% 12.95/2.04  fof(f3565,plain,(
% 12.95/2.04    sK1 != sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(sK1,sK0) | (~spl2_38 | ~spl2_62)),
% 12.95/2.04    inference(superposition,[],[f3476,f2758])).
% 12.95/2.04  fof(f2758,plain,(
% 12.95/2.04    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_38),
% 12.95/2.04    inference(avatar_component_clause,[],[f2756])).
% 12.95/2.04  fof(f3476,plain,(
% 12.95/2.04    ( ! [X0] : (k2_pre_topc(sK0,X0) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | ~spl2_62),
% 12.95/2.04    inference(avatar_component_clause,[],[f3475])).
% 12.95/2.04  fof(f6320,plain,(
% 12.95/2.04    spl2_172 | ~spl2_160),
% 12.95/2.04    inference(avatar_split_clause,[],[f6278,f6225,f6317])).
% 12.95/2.04  fof(f6317,plain,(
% 12.95/2.04    spl2_172 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_172])])).
% 12.95/2.04  fof(f6278,plain,(
% 12.95/2.04    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_160),
% 12.95/2.04    inference(superposition,[],[f99,f6227])).
% 12.95/2.04  fof(f6315,plain,(
% 12.95/2.04    spl2_171 | ~spl2_160),
% 12.95/2.04    inference(avatar_split_clause,[],[f6277,f6225,f6312])).
% 12.95/2.04  fof(f6277,plain,(
% 12.95/2.04    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_160),
% 12.95/2.04    inference(superposition,[],[f76,f6227])).
% 12.95/2.04  fof(f6310,plain,(
% 12.95/2.04    spl2_51 | ~spl2_170 | ~spl2_160),
% 12.95/2.04    inference(avatar_split_clause,[],[f6276,f6225,f6307,f3116])).
% 12.95/2.04  fof(f3116,plain,(
% 12.95/2.04    spl2_51 <=> k1_xboole_0 = k2_tops_1(sK0,sK1)),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 12.95/2.04  fof(f6276,plain,(
% 12.95/2.04    ~r1_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | k1_xboole_0 = k2_tops_1(sK0,sK1) | ~spl2_160),
% 12.95/2.04    inference(superposition,[],[f104,f6227])).
% 12.95/2.04  fof(f6305,plain,(
% 12.95/2.04    spl2_22 | ~spl2_130 | ~spl2_160),
% 12.95/2.04    inference(avatar_split_clause,[],[f6304,f6225,f5222,f1773])).
% 12.95/2.04  fof(f5222,plain,(
% 12.95/2.04    spl2_130 <=> k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_130])])).
% 12.95/2.04  fof(f6304,plain,(
% 12.95/2.04    k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_130 | ~spl2_160)),
% 12.95/2.04    inference(forward_demodulation,[],[f6274,f5224])).
% 12.95/2.04  fof(f5224,plain,(
% 12.95/2.04    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_130),
% 12.95/2.04    inference(avatar_component_clause,[],[f5222])).
% 12.95/2.04  fof(f6274,plain,(
% 12.95/2.04    k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_160),
% 12.95/2.04    inference(superposition,[],[f100,f6227])).
% 12.95/2.04  fof(f6303,plain,(
% 12.95/2.04    ~spl2_169 | ~spl2_52 | ~spl2_160),
% 12.95/2.04    inference(avatar_split_clause,[],[f6272,f6225,f3121,f6300])).
% 12.95/2.04  fof(f6300,plain,(
% 12.95/2.04    spl2_169 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_169])])).
% 12.95/2.04  fof(f3121,plain,(
% 12.95/2.04    spl2_52 <=> ! [X7] : ~r1_tarski(sK1,k6_subset_1(X7,k2_tops_1(sK0,sK1)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 12.95/2.04  fof(f6272,plain,(
% 12.95/2.04    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl2_52 | ~spl2_160)),
% 12.95/2.04    inference(superposition,[],[f3122,f6227])).
% 12.95/2.04  fof(f3122,plain,(
% 12.95/2.04    ( ! [X7] : (~r1_tarski(sK1,k6_subset_1(X7,k2_tops_1(sK0,sK1)))) ) | ~spl2_52),
% 12.95/2.04    inference(avatar_component_clause,[],[f3121])).
% 12.95/2.04  fof(f6298,plain,(
% 12.95/2.04    spl2_168 | ~spl2_16 | ~spl2_160),
% 12.95/2.04    inference(avatar_split_clause,[],[f6271,f6225,f939,f6295])).
% 12.95/2.04  fof(f6271,plain,(
% 12.95/2.04    k1_xboole_0 = k6_subset_1(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl2_16 | ~spl2_160)),
% 12.95/2.04    inference(superposition,[],[f5324,f6227])).
% 12.95/2.04  fof(f5324,plain,(
% 12.95/2.04    ( ! [X10] : (k1_xboole_0 = k6_subset_1(k6_subset_1(sK1,X10),u1_struct_0(sK0))) ) | ~spl2_16),
% 12.95/2.04    inference(resolution,[],[f5310,f168])).
% 12.95/2.04  fof(f5310,plain,(
% 12.95/2.04    ( ! [X2,X3] : (r1_tarski(k6_subset_1(k6_subset_1(sK1,X2),u1_struct_0(sK0)),X3)) ) | ~spl2_16),
% 12.95/2.04    inference(resolution,[],[f5293,f106])).
% 12.95/2.04  fof(f5293,plain,(
% 12.95/2.04    ( ! [X0,X1] : (r1_tarski(k6_subset_1(sK1,X1),k3_tarski(k2_tarski(u1_struct_0(sK0),X0)))) ) | ~spl2_16),
% 12.95/2.04    inference(superposition,[],[f5128,f77])).
% 12.95/2.04  fof(f5128,plain,(
% 12.95/2.04    ( ! [X114,X115] : (r1_tarski(k6_subset_1(sK1,X114),k3_tarski(k2_tarski(X115,u1_struct_0(sK0))))) ) | ~spl2_16),
% 12.95/2.04    inference(resolution,[],[f1309,f1335])).
% 12.95/2.04  fof(f1335,plain,(
% 12.95/2.04    ( ! [X4,X3] : (~r1_tarski(u1_struct_0(sK0),X3) | r1_tarski(k6_subset_1(sK1,X4),X3)) ) | ~spl2_16),
% 12.95/2.04    inference(resolution,[],[f1328,f95])).
% 12.95/2.04  fof(f1328,plain,(
% 12.95/2.04    ( ! [X0] : (r1_tarski(k6_subset_1(sK1,X0),u1_struct_0(sK0))) ) | ~spl2_16),
% 12.95/2.04    inference(resolution,[],[f1325,f106])).
% 12.95/2.04  fof(f1325,plain,(
% 12.95/2.04    ( ! [X0] : (r1_tarski(sK1,k3_tarski(k2_tarski(X0,u1_struct_0(sK0))))) ) | ~spl2_16),
% 12.95/2.04    inference(superposition,[],[f1320,f77])).
% 12.95/2.04  fof(f6293,plain,(
% 12.95/2.04    spl2_167 | ~spl2_13 | ~spl2_16 | ~spl2_21 | ~spl2_160),
% 12.95/2.04    inference(avatar_split_clause,[],[f6267,f6225,f1658,f939,f895,f6290])).
% 12.95/2.04  fof(f6290,plain,(
% 12.95/2.04    spl2_167 <=> r1_tarski(k6_subset_1(k6_subset_1(k1_tops_1(sK0,sK1),sK1),sK1),k3_subset_1(u1_struct_0(sK0),sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_167])])).
% 12.95/2.04  fof(f1658,plain,(
% 12.95/2.04    spl2_21 <=> r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 12.95/2.04  fof(f6267,plain,(
% 12.95/2.04    r1_tarski(k6_subset_1(k6_subset_1(k1_tops_1(sK0,sK1),sK1),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_13 | ~spl2_16 | ~spl2_21 | ~spl2_160)),
% 12.95/2.04    inference(superposition,[],[f2862,f6227])).
% 12.95/2.04  fof(f2862,plain,(
% 12.95/2.04    ( ! [X1] : (r1_tarski(k6_subset_1(k6_subset_1(k6_subset_1(sK1,X1),sK1),sK1),k3_subset_1(u1_struct_0(sK0),sK1))) ) | (~spl2_13 | ~spl2_16 | ~spl2_21)),
% 12.95/2.04    inference(resolution,[],[f2630,f106])).
% 12.95/2.04  fof(f2630,plain,(
% 12.95/2.04    ( ! [X1] : (r1_tarski(k6_subset_1(k6_subset_1(sK1,X1),sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))) ) | (~spl2_13 | ~spl2_16 | ~spl2_21)),
% 12.95/2.04    inference(resolution,[],[f2454,f1660])).
% 12.95/2.04  fof(f1660,plain,(
% 12.95/2.04    r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))) | ~spl2_21),
% 12.95/2.04    inference(avatar_component_clause,[],[f1658])).
% 12.95/2.04  fof(f2454,plain,(
% 12.95/2.04    ( ! [X4,X3] : (~r1_tarski(u1_struct_0(sK0),X3) | r1_tarski(k6_subset_1(k6_subset_1(sK1,X4),sK1),X3)) ) | (~spl2_13 | ~spl2_16 | ~spl2_21)),
% 12.95/2.04    inference(resolution,[],[f2446,f95])).
% 12.95/2.04  fof(f2446,plain,(
% 12.95/2.04    ( ! [X2] : (r1_tarski(k6_subset_1(k6_subset_1(sK1,X2),sK1),u1_struct_0(sK0))) ) | (~spl2_13 | ~spl2_16 | ~spl2_21)),
% 12.95/2.04    inference(resolution,[],[f1706,f897])).
% 12.95/2.04  fof(f1706,plain,(
% 12.95/2.04    ( ! [X4,X3] : (~r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),X3) | r1_tarski(k6_subset_1(k6_subset_1(sK1,X4),sK1),X3)) ) | (~spl2_16 | ~spl2_21)),
% 12.95/2.04    inference(resolution,[],[f1697,f95])).
% 12.95/2.04  fof(f1697,plain,(
% 12.95/2.04    ( ! [X1] : (r1_tarski(k6_subset_1(k6_subset_1(sK1,X1),sK1),k3_subset_1(u1_struct_0(sK0),sK1))) ) | (~spl2_16 | ~spl2_21)),
% 12.95/2.04    inference(resolution,[],[f1687,f106])).
% 12.95/2.04  fof(f1687,plain,(
% 12.95/2.04    ( ! [X54] : (r1_tarski(k6_subset_1(sK1,X54),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))) ) | (~spl2_16 | ~spl2_21)),
% 12.95/2.04    inference(resolution,[],[f1660,f1335])).
% 12.95/2.04  fof(f6288,plain,(
% 12.95/2.04    spl2_166 | ~spl2_16 | ~spl2_21 | ~spl2_160),
% 12.95/2.04    inference(avatar_split_clause,[],[f6261,f6225,f1658,f939,f6285])).
% 12.95/2.04  fof(f6285,plain,(
% 12.95/2.04    spl2_166 <=> r1_tarski(k6_subset_1(k1_tops_1(sK0,sK1),sK1),k3_subset_1(u1_struct_0(sK0),sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_166])])).
% 12.95/2.04  fof(f6261,plain,(
% 12.95/2.04    r1_tarski(k6_subset_1(k1_tops_1(sK0,sK1),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_16 | ~spl2_21 | ~spl2_160)),
% 12.95/2.04    inference(superposition,[],[f1697,f6227])).
% 12.95/2.04  fof(f6283,plain,(
% 12.95/2.04    spl2_165 | ~spl2_16 | ~spl2_160),
% 12.95/2.04    inference(avatar_split_clause,[],[f6254,f6225,f939,f6280])).
% 12.95/2.04  fof(f6280,plain,(
% 12.95/2.04    spl2_165 <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_165])])).
% 12.95/2.04  fof(f6254,plain,(
% 12.95/2.04    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl2_16 | ~spl2_160)),
% 12.95/2.04    inference(superposition,[],[f1328,f6227])).
% 12.95/2.04  fof(f6253,plain,(
% 12.95/2.04    spl2_164 | ~spl2_143 | ~spl2_161),
% 12.95/2.04    inference(avatar_split_clause,[],[f6238,f6232,f5642,f6250])).
% 12.95/2.04  fof(f5642,plain,(
% 12.95/2.04    spl2_143 <=> k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_143])])).
% 12.95/2.04  fof(f6238,plain,(
% 12.95/2.04    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | (~spl2_143 | ~spl2_161)),
% 12.95/2.04    inference(backward_demodulation,[],[f5644,f6234])).
% 12.95/2.04  fof(f5644,plain,(
% 12.95/2.04    k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_143),
% 12.95/2.04    inference(avatar_component_clause,[],[f5642])).
% 12.95/2.04  fof(f6248,plain,(
% 12.95/2.04    spl2_163 | ~spl2_146 | ~spl2_161),
% 12.95/2.04    inference(avatar_split_clause,[],[f6237,f6232,f5659,f6245])).
% 12.95/2.04  fof(f5659,plain,(
% 12.95/2.04    spl2_146 <=> sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k5_xboole_0(sK1,k2_tops_1(sK0,sK1)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_146])])).
% 12.95/2.04  fof(f6237,plain,(
% 12.95/2.04    sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_146 | ~spl2_161)),
% 12.95/2.04    inference(backward_demodulation,[],[f5661,f6234])).
% 12.95/2.04  fof(f5661,plain,(
% 12.95/2.04    sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k5_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~spl2_146),
% 12.95/2.04    inference(avatar_component_clause,[],[f5659])).
% 12.95/2.04  fof(f6243,plain,(
% 12.95/2.04    spl2_162 | ~spl2_145 | ~spl2_161),
% 12.95/2.04    inference(avatar_split_clause,[],[f6236,f6232,f5653,f6240])).
% 12.95/2.04  fof(f5653,plain,(
% 12.95/2.04    spl2_145 <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_145])])).
% 12.95/2.04  fof(f6236,plain,(
% 12.95/2.04    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_145 | ~spl2_161)),
% 12.95/2.04    inference(backward_demodulation,[],[f5655,f6234])).
% 12.95/2.04  fof(f5655,plain,(
% 12.95/2.04    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~spl2_145),
% 12.95/2.04    inference(avatar_component_clause,[],[f5653])).
% 12.95/2.04  fof(f6235,plain,(
% 12.95/2.04    spl2_161 | ~spl2_141 | ~spl2_160),
% 12.95/2.04    inference(avatar_split_clause,[],[f6230,f6225,f5624,f6232])).
% 12.95/2.04  fof(f5624,plain,(
% 12.95/2.04    spl2_141 <=> k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_141])])).
% 12.95/2.04  fof(f6230,plain,(
% 12.95/2.04    k1_tops_1(sK0,sK1) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_141 | ~spl2_160)),
% 12.95/2.04    inference(backward_demodulation,[],[f5626,f6227])).
% 12.95/2.04  fof(f5626,plain,(
% 12.95/2.04    k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_141),
% 12.95/2.04    inference(avatar_component_clause,[],[f5624])).
% 12.95/2.04  fof(f6229,plain,(
% 12.95/2.04    spl2_160 | ~spl2_3 | ~spl2_140),
% 12.95/2.04    inference(avatar_split_clause,[],[f6223,f5462,f120,f6225])).
% 12.95/2.04  fof(f6223,plain,(
% 12.95/2.04    k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_140)),
% 12.95/2.04    inference(superposition,[],[f1769,f5464])).
% 12.95/2.04  fof(f6228,plain,(
% 12.95/2.04    spl2_160 | ~spl2_3 | ~spl2_140),
% 12.95/2.04    inference(avatar_split_clause,[],[f6222,f5462,f120,f6225])).
% 12.95/2.04  fof(f6222,plain,(
% 12.95/2.04    k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_140)),
% 12.95/2.04    inference(superposition,[],[f5464,f1769])).
% 12.95/2.04  fof(f6221,plain,(
% 12.95/2.04    ~spl2_158 | spl2_159 | ~spl2_8 | ~spl2_155),
% 12.95/2.04    inference(avatar_split_clause,[],[f6210,f5988,f865,f6218,f6214])).
% 12.95/2.04  fof(f6214,plain,(
% 12.95/2.04    spl2_158 <=> r1_tarski(u1_struct_0(sK0),sK1)),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_158])])).
% 12.95/2.04  fof(f6218,plain,(
% 12.95/2.04    spl2_159 <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_159])])).
% 12.95/2.04  fof(f5988,plain,(
% 12.95/2.04    spl2_155 <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_155])])).
% 12.95/2.04  fof(f6210,plain,(
% 12.95/2.04    r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) | ~r1_tarski(u1_struct_0(sK0),sK1) | (~spl2_8 | ~spl2_155)),
% 12.95/2.04    inference(superposition,[],[f5998,f867])).
% 12.95/2.04  fof(f5998,plain,(
% 12.95/2.04    ( ! [X1] : (r1_tarski(k6_subset_1(X1,sK1),k2_tops_1(sK0,sK1)) | ~r1_tarski(X1,sK1)) ) | ~spl2_155),
% 12.95/2.04    inference(superposition,[],[f106,f5990])).
% 12.95/2.04  fof(f5990,plain,(
% 12.95/2.04    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_155),
% 12.95/2.04    inference(avatar_component_clause,[],[f5988])).
% 12.95/2.04  fof(f6009,plain,(
% 12.95/2.04    spl2_157 | ~spl2_107 | ~spl2_156),
% 12.95/2.04    inference(avatar_split_clause,[],[f6004,f6000,f4690,f6006])).
% 12.95/2.04  fof(f6006,plain,(
% 12.95/2.04    spl2_157 <=> sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1)),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_157])])).
% 12.95/2.04  fof(f4690,plain,(
% 12.95/2.04    spl2_107 <=> k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_107])])).
% 12.95/2.04  fof(f6000,plain,(
% 12.95/2.04    spl2_156 <=> sK1 = k3_tarski(k2_tarski(sK1,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_156])])).
% 12.95/2.04  fof(f6004,plain,(
% 12.95/2.04    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1) | (~spl2_107 | ~spl2_156)),
% 12.95/2.04    inference(backward_demodulation,[],[f4692,f6002])).
% 12.95/2.04  fof(f6002,plain,(
% 12.95/2.04    sK1 = k3_tarski(k2_tarski(sK1,sK1)) | ~spl2_156),
% 12.95/2.04    inference(avatar_component_clause,[],[f6000])).
% 12.95/2.04  fof(f4692,plain,(
% 12.95/2.04    k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)) | ~spl2_107),
% 12.95/2.04    inference(avatar_component_clause,[],[f4690])).
% 12.95/2.04  fof(f6003,plain,(
% 12.95/2.04    spl2_156 | ~spl2_155),
% 12.95/2.04    inference(avatar_split_clause,[],[f5997,f5988,f6000])).
% 12.95/2.04  fof(f5997,plain,(
% 12.95/2.04    sK1 = k3_tarski(k2_tarski(sK1,sK1)) | ~spl2_155),
% 12.95/2.04    inference(superposition,[],[f101,f5990])).
% 12.95/2.04  fof(f5991,plain,(
% 12.95/2.04    spl2_155 | ~spl2_105 | ~spl2_154),
% 12.95/2.04    inference(avatar_split_clause,[],[f5986,f5982,f4680,f5988])).
% 12.95/2.04  fof(f5986,plain,(
% 12.95/2.04    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_105 | ~spl2_154)),
% 12.95/2.04    inference(backward_demodulation,[],[f4682,f5984])).
% 12.95/2.04  fof(f5985,plain,(
% 12.95/2.04    spl2_154 | ~spl2_3 | ~spl2_4 | ~spl2_38),
% 12.95/2.04    inference(avatar_split_clause,[],[f5980,f2756,f125,f120,f5982])).
% 12.95/2.04  fof(f5980,plain,(
% 12.95/2.04    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4 | ~spl2_38)),
% 12.95/2.04    inference(forward_demodulation,[],[f5939,f2758])).
% 12.95/2.04  fof(f5979,plain,(
% 12.95/2.04    spl2_153 | ~spl2_4 | ~spl2_88),
% 12.95/2.04    inference(avatar_split_clause,[],[f5938,f4479,f125,f5976])).
% 12.95/2.04  fof(f5976,plain,(
% 12.95/2.04    spl2_153 <=> k2_pre_topc(sK0,k2_tops_1(sK0,k1_xboole_0)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0),k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_153])])).
% 12.95/2.04  fof(f4479,plain,(
% 12.95/2.04    spl2_88 <=> m1_subset_1(k2_tops_1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).
% 12.95/2.04  fof(f5938,plain,(
% 12.95/2.04    k2_pre_topc(sK0,k2_tops_1(sK0,k1_xboole_0)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0),k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0))) | (~spl2_4 | ~spl2_88)),
% 12.95/2.04    inference(resolution,[],[f4111,f4481])).
% 12.95/2.04  fof(f4481,plain,(
% 12.95/2.04    m1_subset_1(k2_tops_1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_88),
% 12.95/2.04    inference(avatar_component_clause,[],[f4479])).
% 12.95/2.04  fof(f5974,plain,(
% 12.95/2.04    spl2_152 | ~spl2_4 | ~spl2_56),
% 12.95/2.04    inference(avatar_split_clause,[],[f5937,f3372,f125,f5971])).
% 12.95/2.04  fof(f5971,plain,(
% 12.95/2.04    spl2_152 <=> k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_152])])).
% 12.95/2.04  fof(f3372,plain,(
% 12.95/2.04    spl2_56 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 12.95/2.04  fof(f5937,plain,(
% 12.95/2.04    k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | (~spl2_4 | ~spl2_56)),
% 12.95/2.04    inference(resolution,[],[f4111,f3374])).
% 12.95/2.04  fof(f3374,plain,(
% 12.95/2.04    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_56),
% 12.95/2.04    inference(avatar_component_clause,[],[f3372])).
% 12.95/2.04  fof(f5968,plain,(
% 12.95/2.04    spl2_151 | ~spl2_4 | ~spl2_12 | ~spl2_83),
% 12.95/2.04    inference(avatar_split_clause,[],[f5963,f4446,f890,f125,f5965])).
% 12.95/2.04  fof(f5963,plain,(
% 12.95/2.04    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) | (~spl2_4 | ~spl2_12 | ~spl2_83)),
% 12.95/2.04    inference(forward_demodulation,[],[f5929,f4448])).
% 12.95/2.04  fof(f5929,plain,(
% 12.95/2.04    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl2_4 | ~spl2_12)),
% 12.95/2.04    inference(resolution,[],[f4111,f892])).
% 12.95/2.04  fof(f5962,plain,(
% 12.95/2.04    spl2_150 | ~spl2_4),
% 12.95/2.04    inference(avatar_split_clause,[],[f5928,f125,f5959])).
% 12.95/2.04  fof(f5959,plain,(
% 12.95/2.04    spl2_150 <=> k2_pre_topc(sK0,k1_xboole_0) = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,k2_tops_1(sK0,k1_xboole_0))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_150])])).
% 12.95/2.04  fof(f5928,plain,(
% 12.95/2.04    k2_pre_topc(sK0,k1_xboole_0) = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,k2_tops_1(sK0,k1_xboole_0)) | ~spl2_4),
% 12.95/2.04    inference(resolution,[],[f4111,f169])).
% 12.95/2.04  fof(f169,plain,(
% 12.95/2.04    ( ! [X4] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X4))) )),
% 12.95/2.04    inference(superposition,[],[f76,f165])).
% 12.95/2.04  fof(f5957,plain,(
% 12.95/2.04    spl2_149 | ~spl2_4 | ~spl2_117 | ~spl2_121),
% 12.95/2.04    inference(avatar_split_clause,[],[f5952,f4997,f4977,f125,f5954])).
% 12.95/2.04  fof(f5954,plain,(
% 12.95/2.04    spl2_149 <=> k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_149])])).
% 12.95/2.04  fof(f4977,plain,(
% 12.95/2.04    spl2_117 <=> k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0)) = k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_117])])).
% 12.95/2.04  fof(f4997,plain,(
% 12.95/2.04    spl2_121 <=> m1_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_121])])).
% 12.95/2.04  fof(f5952,plain,(
% 12.95/2.04    k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0))) | (~spl2_4 | ~spl2_117 | ~spl2_121)),
% 12.95/2.04    inference(forward_demodulation,[],[f5927,f4979])).
% 12.95/2.04  fof(f4979,plain,(
% 12.95/2.04    k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0)) = k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) | ~spl2_117),
% 12.95/2.04    inference(avatar_component_clause,[],[f4977])).
% 12.95/2.04  fof(f5927,plain,(
% 12.95/2.04    k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))) | (~spl2_4 | ~spl2_121)),
% 12.95/2.04    inference(resolution,[],[f4111,f4999])).
% 12.95/2.04  fof(f4999,plain,(
% 12.95/2.04    m1_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_121),
% 12.95/2.04    inference(avatar_component_clause,[],[f4997])).
% 12.95/2.04  fof(f5951,plain,(
% 12.95/2.04    spl2_148 | ~spl2_4 | ~spl2_68 | ~spl2_82),
% 12.95/2.04    inference(avatar_split_clause,[],[f5946,f4438,f3680,f125,f5948])).
% 12.95/2.04  fof(f5948,plain,(
% 12.95/2.04    spl2_148 <=> k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_148])])).
% 12.95/2.04  fof(f3680,plain,(
% 12.95/2.04    spl2_68 <=> m1_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).
% 12.95/2.04  fof(f4438,plain,(
% 12.95/2.04    spl2_82 <=> k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_82])])).
% 12.95/2.04  fof(f5946,plain,(
% 12.95/2.04    k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | (~spl2_4 | ~spl2_68 | ~spl2_82)),
% 12.95/2.04    inference(forward_demodulation,[],[f5926,f4440])).
% 12.95/2.04  fof(f4440,plain,(
% 12.95/2.04    k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) | ~spl2_82),
% 12.95/2.04    inference(avatar_component_clause,[],[f4438])).
% 12.95/2.04  fof(f5926,plain,(
% 12.95/2.04    k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))) | (~spl2_4 | ~spl2_68)),
% 12.95/2.04    inference(resolution,[],[f4111,f3682])).
% 12.95/2.04  fof(f3682,plain,(
% 12.95/2.04    m1_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_68),
% 12.95/2.04    inference(avatar_component_clause,[],[f3680])).
% 12.95/2.04  fof(f5945,plain,(
% 12.95/2.04    spl2_147 | ~spl2_4 | ~spl2_81),
% 12.95/2.04    inference(avatar_split_clause,[],[f5940,f4432,f125,f5942])).
% 12.95/2.04  fof(f5942,plain,(
% 12.95/2.04    spl2_147 <=> k2_pre_topc(sK0,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_147])])).
% 12.95/2.04  fof(f4432,plain,(
% 12.95/2.04    spl2_81 <=> k2_tops_1(sK0,u1_struct_0(sK0)) = k2_tops_1(sK0,k1_xboole_0)),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_81])])).
% 12.95/2.04  fof(f5940,plain,(
% 12.95/2.04    k2_pre_topc(sK0,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) | (~spl2_4 | ~spl2_81)),
% 12.95/2.04    inference(forward_demodulation,[],[f5924,f4434])).
% 12.95/2.04  fof(f4434,plain,(
% 12.95/2.04    k2_tops_1(sK0,u1_struct_0(sK0)) = k2_tops_1(sK0,k1_xboole_0) | ~spl2_81),
% 12.95/2.04    inference(avatar_component_clause,[],[f4432])).
% 12.95/2.04  fof(f5924,plain,(
% 12.95/2.04    k2_pre_topc(sK0,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k2_tops_1(sK0,u1_struct_0(sK0))) | ~spl2_4),
% 12.95/2.04    inference(resolution,[],[f4111,f136])).
% 12.95/2.04  fof(f5662,plain,(
% 12.95/2.04    spl2_146 | ~spl2_142 | ~spl2_143),
% 12.95/2.04    inference(avatar_split_clause,[],[f5657,f5642,f5636,f5659])).
% 12.95/2.04  fof(f5636,plain,(
% 12.95/2.04    spl2_142 <=> sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_142])])).
% 12.95/2.04  fof(f5657,plain,(
% 12.95/2.04    sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k5_xboole_0(sK1,k2_tops_1(sK0,sK1))) | (~spl2_142 | ~spl2_143)),
% 12.95/2.04    inference(forward_demodulation,[],[f5638,f5644])).
% 12.95/2.04  fof(f5638,plain,(
% 12.95/2.04    sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_142),
% 12.95/2.04    inference(avatar_component_clause,[],[f5636])).
% 12.95/2.04  fof(f5656,plain,(
% 12.95/2.04    spl2_145 | ~spl2_143 | ~spl2_144),
% 12.95/2.04    inference(avatar_split_clause,[],[f5651,f5647,f5642,f5653])).
% 12.95/2.04  fof(f5647,plain,(
% 12.95/2.04    spl2_144 <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_144])])).
% 12.95/2.04  fof(f5651,plain,(
% 12.95/2.04    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1))) | (~spl2_143 | ~spl2_144)),
% 12.95/2.04    inference(backward_demodulation,[],[f5649,f5644])).
% 12.95/2.04  fof(f5649,plain,(
% 12.95/2.04    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_144),
% 12.95/2.04    inference(avatar_component_clause,[],[f5647])).
% 12.95/2.04  fof(f5650,plain,(
% 12.95/2.04    spl2_144 | ~spl2_47),
% 12.95/2.04    inference(avatar_split_clause,[],[f5633,f2828,f5647])).
% 12.95/2.04  fof(f2828,plain,(
% 12.95/2.04    spl2_47 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 12.95/2.04  fof(f5633,plain,(
% 12.95/2.04    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_47),
% 12.95/2.04    inference(resolution,[],[f2830,f86])).
% 12.95/2.04  fof(f2830,plain,(
% 12.95/2.04    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_47),
% 12.95/2.04    inference(avatar_component_clause,[],[f2828])).
% 12.95/2.04  fof(f5645,plain,(
% 12.95/2.04    spl2_143 | ~spl2_47 | ~spl2_141),
% 12.95/2.04    inference(avatar_split_clause,[],[f5640,f5624,f2828,f5642])).
% 12.95/2.04  fof(f5640,plain,(
% 12.95/2.04    k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | (~spl2_47 | ~spl2_141)),
% 12.95/2.04    inference(forward_demodulation,[],[f5632,f5626])).
% 12.95/2.04  fof(f5632,plain,(
% 12.95/2.04    k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_47),
% 12.95/2.04    inference(resolution,[],[f2830,f103])).
% 12.95/2.04  fof(f5639,plain,(
% 12.95/2.04    spl2_142 | ~spl2_47),
% 12.95/2.04    inference(avatar_split_clause,[],[f5630,f2828,f5636])).
% 12.95/2.04  fof(f5630,plain,(
% 12.95/2.04    sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_47),
% 12.95/2.04    inference(resolution,[],[f2830,f134])).
% 12.95/2.04  fof(f5628,plain,(
% 12.95/2.04    spl2_47 | ~spl2_130),
% 12.95/2.04    inference(avatar_split_clause,[],[f5618,f5222,f2828])).
% 12.95/2.04  fof(f5618,plain,(
% 12.95/2.04    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_130),
% 12.95/2.04    inference(superposition,[],[f163,f5224])).
% 12.95/2.04  fof(f5627,plain,(
% 12.95/2.04    spl2_141 | ~spl2_130),
% 12.95/2.04    inference(avatar_split_clause,[],[f5616,f5222,f5624])).
% 12.95/2.04  fof(f5616,plain,(
% 12.95/2.04    k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_130),
% 12.95/2.04    inference(superposition,[],[f102,f5224])).
% 12.95/2.04  fof(f5465,plain,(
% 12.95/2.04    spl2_140 | ~spl2_3 | ~spl2_4),
% 12.95/2.04    inference(avatar_split_clause,[],[f5419,f125,f120,f5462])).
% 12.95/2.04  fof(f5419,plain,(
% 12.95/2.04    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 12.95/2.04    inference(resolution,[],[f3862,f122])).
% 12.95/2.04  fof(f5460,plain,(
% 12.95/2.04    spl2_139 | ~spl2_4 | ~spl2_88),
% 12.95/2.04    inference(avatar_split_clause,[],[f5418,f4479,f125,f5457])).
% 12.95/2.04  fof(f5457,plain,(
% 12.95/2.04    spl2_139 <=> k1_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0),k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_139])])).
% 12.95/2.04  fof(f5418,plain,(
% 12.95/2.04    k1_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0),k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0))) | (~spl2_4 | ~spl2_88)),
% 12.95/2.04    inference(resolution,[],[f3862,f4481])).
% 12.95/2.04  fof(f5455,plain,(
% 12.95/2.04    spl2_138 | ~spl2_4 | ~spl2_56),
% 12.95/2.04    inference(avatar_split_clause,[],[f5417,f3372,f125,f5452])).
% 12.95/2.04  fof(f5452,plain,(
% 12.95/2.04    spl2_138 <=> k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_138])])).
% 12.95/2.04  fof(f5417,plain,(
% 12.95/2.04    k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | (~spl2_4 | ~spl2_56)),
% 12.95/2.04    inference(resolution,[],[f3862,f3374])).
% 12.95/2.04  fof(f5449,plain,(
% 12.95/2.04    spl2_137 | ~spl2_4 | ~spl2_12 | ~spl2_83),
% 12.95/2.04    inference(avatar_split_clause,[],[f5444,f4446,f890,f125,f5446])).
% 12.95/2.04  fof(f5444,plain,(
% 12.95/2.04    k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) | (~spl2_4 | ~spl2_12 | ~spl2_83)),
% 12.95/2.04    inference(forward_demodulation,[],[f5409,f4448])).
% 12.95/2.04  fof(f5409,plain,(
% 12.95/2.04    k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl2_4 | ~spl2_12)),
% 12.95/2.04    inference(resolution,[],[f3862,f892])).
% 12.95/2.04  fof(f5443,plain,(
% 12.95/2.04    spl2_136 | ~spl2_4),
% 12.95/2.04    inference(avatar_split_clause,[],[f5438,f125,f5440])).
% 12.95/2.04  fof(f5440,plain,(
% 12.95/2.04    spl2_136 <=> k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_136])])).
% 12.95/2.04  fof(f5438,plain,(
% 12.95/2.04    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) | ~spl2_4),
% 12.95/2.04    inference(forward_demodulation,[],[f5408,f1770])).
% 12.95/2.04  fof(f1770,plain,(
% 12.95/2.04    ( ! [X6,X5] : (k1_xboole_0 = k7_subset_1(X5,k1_xboole_0,X6)) )),
% 12.95/2.04    inference(forward_demodulation,[],[f1763,f182])).
% 12.95/2.04  fof(f182,plain,(
% 12.95/2.04    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)) )),
% 12.95/2.04    inference(resolution,[],[f168,f99])).
% 12.95/2.04  fof(f1763,plain,(
% 12.95/2.04    ( ! [X6,X5] : (k6_subset_1(k1_xboole_0,X6) = k7_subset_1(X5,k1_xboole_0,X6)) )),
% 12.95/2.04    inference(resolution,[],[f105,f169])).
% 12.95/2.04  fof(f5408,plain,(
% 12.95/2.04    k1_tops_1(sK0,k1_xboole_0) = k7_subset_1(u1_struct_0(sK0),k1_xboole_0,k2_tops_1(sK0,k1_xboole_0)) | ~spl2_4),
% 12.95/2.04    inference(resolution,[],[f3862,f169])).
% 12.95/2.04  fof(f5437,plain,(
% 12.95/2.04    spl2_135 | ~spl2_4 | ~spl2_117 | ~spl2_121),
% 12.95/2.04    inference(avatar_split_clause,[],[f5432,f4997,f4977,f125,f5434])).
% 12.95/2.04  fof(f5434,plain,(
% 12.95/2.04    spl2_135 <=> k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_135])])).
% 12.95/2.04  fof(f5432,plain,(
% 12.95/2.04    k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0))) | (~spl2_4 | ~spl2_117 | ~spl2_121)),
% 12.95/2.04    inference(forward_demodulation,[],[f5407,f4979])).
% 12.95/2.04  fof(f5407,plain,(
% 12.95/2.04    k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))) | (~spl2_4 | ~spl2_121)),
% 12.95/2.04    inference(resolution,[],[f3862,f4999])).
% 12.95/2.04  fof(f5431,plain,(
% 12.95/2.04    spl2_134 | ~spl2_4 | ~spl2_68 | ~spl2_82),
% 12.95/2.04    inference(avatar_split_clause,[],[f5426,f4438,f3680,f125,f5428])).
% 12.95/2.04  fof(f5428,plain,(
% 12.95/2.04    spl2_134 <=> k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_134])])).
% 12.95/2.04  fof(f5426,plain,(
% 12.95/2.04    k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | (~spl2_4 | ~spl2_68 | ~spl2_82)),
% 12.95/2.04    inference(forward_demodulation,[],[f5406,f4440])).
% 12.95/2.04  fof(f5406,plain,(
% 12.95/2.04    k1_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))) | (~spl2_4 | ~spl2_68)),
% 12.95/2.04    inference(resolution,[],[f3862,f3682])).
% 12.95/2.04  fof(f5425,plain,(
% 12.95/2.04    spl2_133 | ~spl2_4 | ~spl2_81),
% 12.95/2.04    inference(avatar_split_clause,[],[f5420,f4432,f125,f5422])).
% 12.95/2.04  fof(f5422,plain,(
% 12.95/2.04    spl2_133 <=> k1_tops_1(sK0,u1_struct_0(sK0)) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_133])])).
% 12.95/2.04  fof(f5420,plain,(
% 12.95/2.04    k1_tops_1(sK0,u1_struct_0(sK0)) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) | (~spl2_4 | ~spl2_81)),
% 12.95/2.04    inference(forward_demodulation,[],[f5404,f4434])).
% 12.95/2.04  fof(f5404,plain,(
% 12.95/2.04    k1_tops_1(sK0,u1_struct_0(sK0)) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k2_tops_1(sK0,u1_struct_0(sK0))) | ~spl2_4),
% 12.95/2.04    inference(resolution,[],[f3862,f136])).
% 12.95/2.04  fof(f5390,plain,(
% 12.95/2.04    spl2_132 | ~spl2_8),
% 12.95/2.04    inference(avatar_split_clause,[],[f5383,f865,f5385])).
% 12.95/2.04  fof(f5383,plain,(
% 12.95/2.04    k1_xboole_0 = k6_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl2_8),
% 12.95/2.04    inference(resolution,[],[f5371,f104])).
% 12.95/2.04  fof(f5371,plain,(
% 12.95/2.04    ( ! [X3] : (r1_tarski(k6_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)),X3)) ) | ~spl2_8),
% 12.95/2.04    inference(resolution,[],[f5360,f106])).
% 12.95/2.04  fof(f5360,plain,(
% 12.95/2.04    ( ! [X0] : (r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_tarski(k2_tarski(u1_struct_0(sK0),X0)))) ) | ~spl2_8),
% 12.95/2.04    inference(superposition,[],[f5119,f77])).
% 12.95/2.04  fof(f5119,plain,(
% 12.95/2.04    ( ! [X89] : (r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_tarski(k2_tarski(X89,u1_struct_0(sK0))))) ) | ~spl2_8),
% 12.95/2.04    inference(resolution,[],[f1309,f870])).
% 12.95/2.04  fof(f870,plain,(
% 12.95/2.04    ( ! [X0] : (~r1_tarski(u1_struct_0(sK0),X0) | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),X0)) ) | ~spl2_8),
% 12.95/2.04    inference(superposition,[],[f151,f867])).
% 12.95/2.04  fof(f5388,plain,(
% 12.95/2.04    spl2_132 | ~spl2_8),
% 12.95/2.04    inference(avatar_split_clause,[],[f5381,f865,f5385])).
% 12.95/2.04  fof(f5381,plain,(
% 12.95/2.04    k1_xboole_0 = k6_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl2_8),
% 12.95/2.04    inference(resolution,[],[f5371,f168])).
% 12.95/2.04  fof(f5271,plain,(
% 12.95/2.04    spl2_131 | ~spl2_87),
% 12.95/2.04    inference(avatar_split_clause,[],[f5264,f4474,f5266])).
% 12.95/2.04  fof(f5266,plain,(
% 12.95/2.04    spl2_131 <=> k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,k1_xboole_0),u1_struct_0(sK0))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_131])])).
% 12.95/2.04  fof(f4474,plain,(
% 12.95/2.04    spl2_87 <=> r1_tarski(k2_tops_1(sK0,k1_xboole_0),u1_struct_0(sK0))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).
% 12.95/2.04  fof(f5264,plain,(
% 12.95/2.04    k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~spl2_87),
% 12.95/2.04    inference(resolution,[],[f5252,f104])).
% 12.95/2.04  fof(f5252,plain,(
% 12.95/2.04    ( ! [X0] : (r1_tarski(k6_subset_1(k2_tops_1(sK0,k1_xboole_0),u1_struct_0(sK0)),X0)) ) | ~spl2_87),
% 12.95/2.04    inference(resolution,[],[f5243,f106])).
% 12.95/2.04  fof(f5243,plain,(
% 12.95/2.04    ( ! [X0] : (r1_tarski(k2_tops_1(sK0,k1_xboole_0),k3_tarski(k2_tarski(u1_struct_0(sK0),X0)))) ) | ~spl2_87),
% 12.95/2.04    inference(superposition,[],[f5142,f77])).
% 12.95/2.04  fof(f5142,plain,(
% 12.95/2.04    ( ! [X145] : (r1_tarski(k2_tops_1(sK0,k1_xboole_0),k3_tarski(k2_tarski(X145,u1_struct_0(sK0))))) ) | ~spl2_87),
% 12.95/2.04    inference(resolution,[],[f1309,f4492])).
% 12.95/2.04  fof(f4492,plain,(
% 12.95/2.04    ( ! [X1] : (~r1_tarski(u1_struct_0(sK0),X1) | r1_tarski(k2_tops_1(sK0,k1_xboole_0),X1)) ) | ~spl2_87),
% 12.95/2.04    inference(resolution,[],[f4476,f95])).
% 12.95/2.04  fof(f4476,plain,(
% 12.95/2.04    r1_tarski(k2_tops_1(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~spl2_87),
% 12.95/2.04    inference(avatar_component_clause,[],[f4474])).
% 12.95/2.04  fof(f5269,plain,(
% 12.95/2.04    spl2_131 | ~spl2_87),
% 12.95/2.04    inference(avatar_split_clause,[],[f5262,f4474,f5266])).
% 12.95/2.04  fof(f5262,plain,(
% 12.95/2.04    k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~spl2_87),
% 12.95/2.04    inference(resolution,[],[f5252,f168])).
% 12.95/2.04  fof(f5225,plain,(
% 12.95/2.04    spl2_130 | ~spl2_129),
% 12.95/2.04    inference(avatar_split_clause,[],[f5220,f5176,f5222])).
% 12.95/2.04  fof(f5176,plain,(
% 12.95/2.04    spl2_129 <=> k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),sK1)),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_129])])).
% 12.95/2.04  fof(f5220,plain,(
% 12.95/2.04    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_129),
% 12.95/2.04    inference(forward_demodulation,[],[f5219,f77])).
% 12.95/2.04  fof(f5219,plain,(
% 12.95/2.04    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) | ~spl2_129),
% 12.95/2.04    inference(forward_demodulation,[],[f5206,f98])).
% 12.95/2.04  fof(f5206,plain,(
% 12.95/2.04    k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k6_subset_1(k2_tops_1(sK0,sK1),k1_xboole_0) | ~spl2_129),
% 12.95/2.04    inference(superposition,[],[f100,f5178])).
% 12.95/2.04  fof(f5178,plain,(
% 12.95/2.04    k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),sK1) | ~spl2_129),
% 12.95/2.04    inference(avatar_component_clause,[],[f5176])).
% 12.95/2.04  fof(f5181,plain,(
% 12.95/2.04    spl2_129 | ~spl2_48),
% 12.95/2.04    inference(avatar_split_clause,[],[f5174,f2833,f5176])).
% 12.95/2.04  fof(f5174,plain,(
% 12.95/2.04    k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),sK1) | ~spl2_48),
% 12.95/2.04    inference(resolution,[],[f5146,f104])).
% 12.95/2.04  fof(f5179,plain,(
% 12.95/2.04    spl2_129 | ~spl2_48),
% 12.95/2.04    inference(avatar_split_clause,[],[f5172,f2833,f5176])).
% 12.95/2.04  fof(f5172,plain,(
% 12.95/2.04    k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),sK1) | ~spl2_48),
% 12.95/2.04    inference(resolution,[],[f5146,f168])).
% 12.95/2.04  fof(f5081,plain,(
% 12.95/2.04    spl2_127 | ~spl2_128 | ~spl2_125),
% 12.95/2.04    inference(avatar_split_clause,[],[f5064,f5017,f5078,f5074])).
% 12.95/2.04  fof(f5074,plain,(
% 12.95/2.04    spl2_127 <=> k1_xboole_0 = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_127])])).
% 12.95/2.04  fof(f5078,plain,(
% 12.95/2.04    spl2_128 <=> r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k1_xboole_0))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_128])])).
% 12.95/2.04  fof(f5017,plain,(
% 12.95/2.04    spl2_125 <=> k2_tops_1(sK0,k1_xboole_0) = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_125])])).
% 12.95/2.04  fof(f5064,plain,(
% 12.95/2.04    ~r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k1_xboole_0)) | k1_xboole_0 = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) | ~spl2_125),
% 12.95/2.04    inference(superposition,[],[f104,f5019])).
% 12.95/2.04  fof(f5019,plain,(
% 12.95/2.04    k2_tops_1(sK0,k1_xboole_0) = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) | ~spl2_125),
% 12.95/2.04    inference(avatar_component_clause,[],[f5017])).
% 12.95/2.04  fof(f5072,plain,(
% 12.95/2.04    spl2_126 | ~spl2_115 | ~spl2_125),
% 12.95/2.04    inference(avatar_split_clause,[],[f5067,f5017,f4952,f5069])).
% 12.95/2.04  fof(f5069,plain,(
% 12.95/2.04    spl2_126 <=> k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_126])])).
% 12.95/2.04  fof(f4952,plain,(
% 12.95/2.04    spl2_115 <=> k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_115])])).
% 12.95/2.04  fof(f5067,plain,(
% 12.95/2.04    k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))) | (~spl2_115 | ~spl2_125)),
% 12.95/2.04    inference(forward_demodulation,[],[f5062,f4954])).
% 12.95/2.04  fof(f4954,plain,(
% 12.95/2.04    k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) | ~spl2_115),
% 12.95/2.04    inference(avatar_component_clause,[],[f4952])).
% 12.95/2.04  fof(f5062,plain,(
% 12.95/2.04    k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))) | ~spl2_125),
% 12.95/2.04    inference(superposition,[],[f100,f5019])).
% 12.95/2.04  fof(f5020,plain,(
% 12.95/2.04    spl2_125 | ~spl2_114 | ~spl2_116),
% 12.95/2.04    inference(avatar_split_clause,[],[f4975,f4958,f4932,f5017])).
% 12.95/2.04  fof(f4932,plain,(
% 12.95/2.04    spl2_114 <=> k2_tops_1(sK0,k1_xboole_0) = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_114])])).
% 12.95/2.04  fof(f4975,plain,(
% 12.95/2.04    k2_tops_1(sK0,k1_xboole_0) = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) | (~spl2_114 | ~spl2_116)),
% 12.95/2.04    inference(backward_demodulation,[],[f4934,f4960])).
% 12.95/2.04  fof(f4934,plain,(
% 12.95/2.04    k2_tops_1(sK0,k1_xboole_0) = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) | ~spl2_114),
% 12.95/2.04    inference(avatar_component_clause,[],[f4932])).
% 12.95/2.04  fof(f5015,plain,(
% 12.95/2.04    spl2_124 | ~spl2_112 | ~spl2_116),
% 12.95/2.04    inference(avatar_split_clause,[],[f4974,f4958,f4919,f5012])).
% 12.95/2.04  fof(f5012,plain,(
% 12.95/2.04    spl2_124 <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k1_xboole_0))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_124])])).
% 12.95/2.04  fof(f4919,plain,(
% 12.95/2.04    spl2_112 <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k1_xboole_0))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_112])])).
% 12.95/2.04  fof(f4974,plain,(
% 12.95/2.04    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k1_xboole_0)) | (~spl2_112 | ~spl2_116)),
% 12.95/2.04    inference(backward_demodulation,[],[f4921,f4960])).
% 12.95/2.04  fof(f4921,plain,(
% 12.95/2.04    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k1_xboole_0)) | ~spl2_112),
% 12.95/2.04    inference(avatar_component_clause,[],[f4919])).
% 12.95/2.04  fof(f5010,plain,(
% 12.95/2.04    spl2_123 | ~spl2_111 | ~spl2_116),
% 12.95/2.04    inference(avatar_split_clause,[],[f4973,f4958,f4912,f5007])).
% 12.95/2.04  fof(f5007,plain,(
% 12.95/2.04    spl2_123 <=> k4_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k3_tarski(k2_tarski(sK1,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_123])])).
% 12.95/2.04  fof(f4912,plain,(
% 12.95/2.04    spl2_111 <=> k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_111])])).
% 12.95/2.04  fof(f4973,plain,(
% 12.95/2.04    k4_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k3_tarski(k2_tarski(sK1,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))) | (~spl2_111 | ~spl2_116)),
% 12.95/2.04    inference(backward_demodulation,[],[f4914,f4960])).
% 12.95/2.04  fof(f4914,plain,(
% 12.95/2.04    k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))) | ~spl2_111),
% 12.95/2.04    inference(avatar_component_clause,[],[f4912])).
% 12.95/2.04  fof(f5005,plain,(
% 12.95/2.04    spl2_122 | ~spl2_100 | ~spl2_116),
% 12.95/2.04    inference(avatar_split_clause,[],[f4969,f4958,f4636,f5002])).
% 12.95/2.04  fof(f5002,plain,(
% 12.95/2.04    spl2_122 <=> r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),u1_struct_0(sK0))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_122])])).
% 12.95/2.04  fof(f4636,plain,(
% 12.95/2.04    spl2_100 <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),u1_struct_0(sK0))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_100])])).
% 12.95/2.04  fof(f4969,plain,(
% 12.95/2.04    r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),u1_struct_0(sK0)) | (~spl2_100 | ~spl2_116)),
% 12.95/2.04    inference(backward_demodulation,[],[f4638,f4960])).
% 12.95/2.04  fof(f4638,plain,(
% 12.95/2.04    r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),u1_struct_0(sK0)) | ~spl2_100),
% 12.95/2.04    inference(avatar_component_clause,[],[f4636])).
% 12.95/2.04  fof(f5000,plain,(
% 12.95/2.04    spl2_121 | ~spl2_99 | ~spl2_116),
% 12.95/2.04    inference(avatar_split_clause,[],[f4968,f4958,f4631,f4997])).
% 12.95/2.04  fof(f4631,plain,(
% 12.95/2.04    spl2_99 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_99])])).
% 12.95/2.04  fof(f4968,plain,(
% 12.95/2.04    m1_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_99 | ~spl2_116)),
% 12.95/2.04    inference(backward_demodulation,[],[f4633,f4960])).
% 12.95/2.04  fof(f4633,plain,(
% 12.95/2.04    m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_99),
% 12.95/2.04    inference(avatar_component_clause,[],[f4631])).
% 12.95/2.04  fof(f4995,plain,(
% 12.95/2.04    ~spl2_120 | spl2_98 | ~spl2_116),
% 12.95/2.04    inference(avatar_split_clause,[],[f4967,f4958,f4626,f4992])).
% 12.95/2.04  fof(f4992,plain,(
% 12.95/2.04    spl2_120 <=> r1_tarski(k2_tops_1(sK0,k1_xboole_0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_120])])).
% 12.95/2.04  fof(f4626,plain,(
% 12.95/2.04    spl2_98 <=> r1_tarski(k2_tops_1(sK0,k1_xboole_0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).
% 12.95/2.04  fof(f4967,plain,(
% 12.95/2.04    ~r1_tarski(k2_tops_1(sK0,k1_xboole_0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) | (spl2_98 | ~spl2_116)),
% 12.95/2.04    inference(backward_demodulation,[],[f4628,f4960])).
% 12.95/2.04  fof(f4628,plain,(
% 12.95/2.04    ~r1_tarski(k2_tops_1(sK0,k1_xboole_0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) | spl2_98),
% 12.95/2.04    inference(avatar_component_clause,[],[f4626])).
% 12.95/2.04  fof(f4990,plain,(
% 12.95/2.04    spl2_119 | ~spl2_93 | ~spl2_116),
% 12.95/2.04    inference(avatar_split_clause,[],[f4964,f4958,f4516,f4987])).
% 12.95/2.04  fof(f4987,plain,(
% 12.95/2.04    spl2_119 <=> k2_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_119])])).
% 12.95/2.04  fof(f4516,plain,(
% 12.95/2.04    spl2_93 <=> k2_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_93])])).
% 12.95/2.04  fof(f4964,plain,(
% 12.95/2.04    k2_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) | (~spl2_93 | ~spl2_116)),
% 12.95/2.04    inference(backward_demodulation,[],[f4518,f4960])).
% 12.95/2.04  fof(f4518,plain,(
% 12.95/2.04    k2_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) | ~spl2_93),
% 12.95/2.04    inference(avatar_component_clause,[],[f4516])).
% 12.95/2.04  fof(f4985,plain,(
% 12.95/2.04    spl2_118 | ~spl2_91 | ~spl2_116),
% 12.95/2.04    inference(avatar_split_clause,[],[f4963,f4958,f4506,f4982])).
% 12.95/2.04  fof(f4982,plain,(
% 12.95/2.04    spl2_118 <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_118])])).
% 12.95/2.04  fof(f4506,plain,(
% 12.95/2.04    spl2_91 <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_91])])).
% 12.95/2.04  fof(f4963,plain,(
% 12.95/2.04    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) | (~spl2_91 | ~spl2_116)),
% 12.95/2.04    inference(backward_demodulation,[],[f4508,f4960])).
% 12.95/2.04  fof(f4508,plain,(
% 12.95/2.04    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) | ~spl2_91),
% 12.95/2.04    inference(avatar_component_clause,[],[f4506])).
% 12.95/2.04  fof(f4980,plain,(
% 12.95/2.04    spl2_117 | ~spl2_90 | ~spl2_116),
% 12.95/2.04    inference(avatar_split_clause,[],[f4962,f4958,f4501,f4977])).
% 12.95/2.04  fof(f4501,plain,(
% 12.95/2.04    spl2_90 <=> k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_90])])).
% 12.95/2.04  fof(f4962,plain,(
% 12.95/2.04    k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0)) = k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) | (~spl2_90 | ~spl2_116)),
% 12.95/2.04    inference(backward_demodulation,[],[f4503,f4960])).
% 12.95/2.04  fof(f4503,plain,(
% 12.95/2.04    k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) | ~spl2_90),
% 12.95/2.04    inference(avatar_component_clause,[],[f4501])).
% 12.95/2.04  fof(f4961,plain,(
% 12.95/2.04    spl2_116 | ~spl2_92 | ~spl2_115),
% 12.95/2.04    inference(avatar_split_clause,[],[f4956,f4952,f4511,f4958])).
% 12.95/2.04  fof(f4956,plain,(
% 12.95/2.04    k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) | (~spl2_92 | ~spl2_115)),
% 12.95/2.04    inference(backward_demodulation,[],[f4513,f4954])).
% 12.95/2.04  fof(f4955,plain,(
% 12.95/2.04    spl2_115 | ~spl2_113),
% 12.95/2.04    inference(avatar_split_clause,[],[f4946,f4926,f4952])).
% 12.95/2.04  fof(f4926,plain,(
% 12.95/2.04    spl2_113 <=> k2_tops_1(sK0,k1_xboole_0) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_113])])).
% 12.95/2.04  fof(f4946,plain,(
% 12.95/2.04    k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) | ~spl2_113),
% 12.95/2.04    inference(superposition,[],[f102,f4928])).
% 12.95/2.04  fof(f4928,plain,(
% 12.95/2.04    k2_tops_1(sK0,k1_xboole_0) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) | ~spl2_113),
% 12.95/2.04    inference(avatar_component_clause,[],[f4926])).
% 12.95/2.04  fof(f4935,plain,(
% 12.95/2.04    spl2_114 | ~spl2_96 | ~spl2_113),
% 12.95/2.04    inference(avatar_split_clause,[],[f4930,f4926,f4617,f4932])).
% 12.95/2.04  fof(f4617,plain,(
% 12.95/2.04    spl2_96 <=> k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_96])])).
% 12.95/2.04  fof(f4930,plain,(
% 12.95/2.04    k2_tops_1(sK0,k1_xboole_0) = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) | (~spl2_96 | ~spl2_113)),
% 12.95/2.04    inference(backward_demodulation,[],[f4619,f4928])).
% 12.95/2.04  fof(f4619,plain,(
% 12.95/2.04    k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) | ~spl2_96),
% 12.95/2.04    inference(avatar_component_clause,[],[f4617])).
% 12.95/2.04  fof(f4929,plain,(
% 12.95/2.04    spl2_113 | ~spl2_93 | ~spl2_96 | ~spl2_99),
% 12.95/2.04    inference(avatar_split_clause,[],[f4924,f4631,f4617,f4516,f4926])).
% 12.95/2.04  fof(f4924,plain,(
% 12.95/2.04    k2_tops_1(sK0,k1_xboole_0) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) | (~spl2_93 | ~spl2_96 | ~spl2_99)),
% 12.95/2.04    inference(forward_demodulation,[],[f4923,f4518])).
% 12.95/2.04  fof(f4923,plain,(
% 12.95/2.04    k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) | (~spl2_96 | ~spl2_99)),
% 12.95/2.04    inference(forward_demodulation,[],[f4908,f4619])).
% 12.95/2.04  fof(f4908,plain,(
% 12.95/2.04    k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) | ~spl2_99),
% 12.95/2.04    inference(resolution,[],[f4633,f103])).
% 12.95/2.04  fof(f4922,plain,(
% 12.95/2.04    spl2_112 | ~spl2_93 | ~spl2_99),
% 12.95/2.04    inference(avatar_split_clause,[],[f4917,f4631,f4516,f4919])).
% 12.95/2.04  fof(f4917,plain,(
% 12.95/2.04    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k2_tops_1(sK0,k1_xboole_0)) | (~spl2_93 | ~spl2_99)),
% 12.95/2.04    inference(forward_demodulation,[],[f4906,f4518])).
% 12.95/2.04  fof(f4906,plain,(
% 12.95/2.04    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))) | ~spl2_99),
% 12.95/2.04    inference(resolution,[],[f4633,f134])).
% 12.95/2.04  fof(f4915,plain,(
% 12.95/2.04    spl2_111 | ~spl2_3 | ~spl2_99),
% 12.95/2.04    inference(avatar_split_clause,[],[f4903,f4631,f120,f4912])).
% 12.95/2.04  fof(f4903,plain,(
% 12.95/2.04    k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)))) | (~spl2_3 | ~spl2_99)),
% 12.95/2.04    inference(resolution,[],[f4633,f3703])).
% 12.95/2.04  fof(f4877,plain,(
% 12.95/2.04    spl2_110 | ~spl2_101 | ~spl2_109),
% 12.95/2.04    inference(avatar_split_clause,[],[f4868,f4799,f4658,f4874])).
% 12.95/2.04  fof(f4874,plain,(
% 12.95/2.04    spl2_110 <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_110])])).
% 12.95/2.04  fof(f4658,plain,(
% 12.95/2.04    spl2_101 <=> k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_101])])).
% 12.95/2.04  fof(f4868,plain,(
% 12.95/2.04    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) | (~spl2_101 | ~spl2_109)),
% 12.95/2.04    inference(backward_demodulation,[],[f4660,f4801])).
% 12.95/2.04  fof(f4660,plain,(
% 12.95/2.04    k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) | ~spl2_101),
% 12.95/2.04    inference(avatar_component_clause,[],[f4658])).
% 12.95/2.04  fof(f4802,plain,(
% 12.95/2.04    spl2_109 | ~spl2_104),
% 12.95/2.04    inference(avatar_split_clause,[],[f4791,f4675,f4799])).
% 12.95/2.04  fof(f4791,plain,(
% 12.95/2.04    u1_struct_0(sK0) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) | ~spl2_104),
% 12.95/2.04    inference(superposition,[],[f101,f4677])).
% 12.95/2.04  fof(f4797,plain,(
% 12.95/2.04    spl2_108 | ~spl2_6 | ~spl2_48 | ~spl2_104),
% 12.95/2.04    inference(avatar_split_clause,[],[f4789,f4675,f2833,f145,f4794])).
% 12.95/2.04  fof(f4794,plain,(
% 12.95/2.04    spl2_108 <=> r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),sK1)),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_108])])).
% 12.95/2.04  fof(f145,plain,(
% 12.95/2.04    spl2_6 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 12.95/2.04  fof(f4789,plain,(
% 12.95/2.04    ~r1_tarski(sK1,u1_struct_0(sK0)) | r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),sK1) | (~spl2_48 | ~spl2_104)),
% 12.95/2.04    inference(superposition,[],[f3573,f4677])).
% 12.95/2.04  fof(f4693,plain,(
% 12.95/2.04    spl2_107 | ~spl2_3),
% 12.95/2.04    inference(avatar_split_clause,[],[f4656,f120,f4690])).
% 12.95/2.04  fof(f4656,plain,(
% 12.95/2.04    k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)) | ~spl2_3),
% 12.95/2.04    inference(resolution,[],[f3703,f122])).
% 12.95/2.04  fof(f4688,plain,(
% 12.95/2.04    spl2_106 | ~spl2_3 | ~spl2_88),
% 12.95/2.04    inference(avatar_split_clause,[],[f4655,f4479,f120,f4685])).
% 12.95/2.04  fof(f4685,plain,(
% 12.95/2.04    spl2_106 <=> k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,k1_xboole_0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,k1_xboole_0)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_106])])).
% 12.95/2.04  fof(f4655,plain,(
% 12.95/2.04    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,k1_xboole_0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,k1_xboole_0))) | (~spl2_3 | ~spl2_88)),
% 12.95/2.04    inference(resolution,[],[f3703,f4481])).
% 12.95/2.04  fof(f4683,plain,(
% 12.95/2.04    spl2_105 | ~spl2_3 | ~spl2_56),
% 12.95/2.04    inference(avatar_split_clause,[],[f4654,f3372,f120,f4680])).
% 12.95/2.04  fof(f4654,plain,(
% 12.95/2.04    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_3 | ~spl2_56)),
% 12.95/2.04    inference(resolution,[],[f3703,f3374])).
% 12.95/2.04  fof(f4678,plain,(
% 12.95/2.04    spl2_104 | ~spl2_3 | ~spl2_12 | ~spl2_29),
% 12.95/2.04    inference(avatar_split_clause,[],[f4673,f2105,f890,f120,f4675])).
% 12.95/2.04  fof(f4673,plain,(
% 12.95/2.04    u1_struct_0(sK0) = k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl2_3 | ~spl2_12 | ~spl2_29)),
% 12.95/2.04    inference(forward_demodulation,[],[f4646,f2107])).
% 12.95/2.04  fof(f4646,plain,(
% 12.95/2.04    k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_3 | ~spl2_12)),
% 12.95/2.04    inference(resolution,[],[f3703,f892])).
% 12.95/2.04  fof(f4672,plain,(
% 12.95/2.04    spl2_103 | ~spl2_3),
% 12.95/2.04    inference(avatar_split_clause,[],[f4667,f120,f4669])).
% 12.95/2.04  fof(f4669,plain,(
% 12.95/2.04    spl2_103 <=> k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k3_tarski(k2_tarski(k1_xboole_0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_103])])).
% 12.95/2.04  fof(f4667,plain,(
% 12.95/2.04    k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k3_tarski(k2_tarski(k1_xboole_0,sK1)) | ~spl2_3),
% 12.95/2.04    inference(forward_demodulation,[],[f4645,f77])).
% 12.95/2.04  fof(f4645,plain,(
% 12.95/2.04    k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k3_tarski(k2_tarski(sK1,k1_xboole_0)) | ~spl2_3),
% 12.95/2.04    inference(resolution,[],[f3703,f169])).
% 12.95/2.04  fof(f4666,plain,(
% 12.95/2.04    spl2_102 | ~spl2_3 | ~spl2_68),
% 12.95/2.04    inference(avatar_split_clause,[],[f4644,f3680,f120,f4663])).
% 12.95/2.04  fof(f4663,plain,(
% 12.95/2.04    spl2_102 <=> k4_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k3_tarski(k2_tarski(sK1,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_102])])).
% 12.95/2.04  fof(f4644,plain,(
% 12.95/2.04    k4_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k3_tarski(k2_tarski(sK1,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))) | (~spl2_3 | ~spl2_68)),
% 12.95/2.04    inference(resolution,[],[f3703,f3682])).
% 12.95/2.04  fof(f4661,plain,(
% 12.95/2.04    spl2_101 | ~spl2_3),
% 12.95/2.04    inference(avatar_split_clause,[],[f4642,f120,f4658])).
% 12.95/2.04  fof(f4642,plain,(
% 12.95/2.04    k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) | ~spl2_3),
% 12.95/2.04    inference(resolution,[],[f3703,f136])).
% 12.95/2.04  fof(f4639,plain,(
% 12.95/2.04    spl2_100 | ~spl2_92),
% 12.95/2.04    inference(avatar_split_clause,[],[f4615,f4511,f4636])).
% 12.95/2.04  fof(f4615,plain,(
% 12.95/2.04    r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),u1_struct_0(sK0)) | ~spl2_92),
% 12.95/2.04    inference(superposition,[],[f99,f4513])).
% 12.95/2.04  fof(f4634,plain,(
% 12.95/2.04    spl2_99 | ~spl2_92),
% 12.95/2.04    inference(avatar_split_clause,[],[f4614,f4511,f4631])).
% 12.95/2.04  fof(f4614,plain,(
% 12.95/2.04    m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_92),
% 12.95/2.04    inference(superposition,[],[f76,f4513])).
% 12.95/2.04  fof(f4629,plain,(
% 12.95/2.04    spl2_97 | ~spl2_98 | ~spl2_92),
% 12.95/2.04    inference(avatar_split_clause,[],[f4613,f4511,f4626,f4622])).
% 12.95/2.04  fof(f4622,plain,(
% 12.95/2.04    spl2_97 <=> k1_xboole_0 = k2_tops_1(sK0,k1_xboole_0)),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_97])])).
% 12.95/2.04  fof(f4613,plain,(
% 12.95/2.04    ~r1_tarski(k2_tops_1(sK0,k1_xboole_0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) | k1_xboole_0 = k2_tops_1(sK0,k1_xboole_0) | ~spl2_92),
% 12.95/2.04    inference(superposition,[],[f104,f4513])).
% 12.95/2.04  fof(f4620,plain,(
% 12.95/2.04    spl2_96 | ~spl2_92),
% 12.95/2.04    inference(avatar_split_clause,[],[f4611,f4511,f4617])).
% 12.95/2.04  fof(f4611,plain,(
% 12.95/2.04    k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) | ~spl2_92),
% 12.95/2.04    inference(superposition,[],[f100,f4513])).
% 12.95/2.04  fof(f4552,plain,(
% 12.95/2.04    spl2_95 | ~spl2_94),
% 12.95/2.04    inference(avatar_split_clause,[],[f4545,f4531,f4549])).
% 12.95/2.04  fof(f4531,plain,(
% 12.95/2.04    spl2_94 <=> r1_tarski(k2_tops_1(sK0,k1_xboole_0),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_94])])).
% 12.95/2.04  fof(f4545,plain,(
% 12.95/2.04    r1_tarski(k6_subset_1(k2_tops_1(sK0,k1_xboole_0),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_94),
% 12.95/2.04    inference(resolution,[],[f4533,f106])).
% 12.95/2.04  fof(f4533,plain,(
% 12.95/2.04    r1_tarski(k2_tops_1(sK0,k1_xboole_0),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))) | ~spl2_94),
% 12.95/2.04    inference(avatar_component_clause,[],[f4531])).
% 12.95/2.04  fof(f4534,plain,(
% 12.95/2.04    spl2_94 | ~spl2_21 | ~spl2_87),
% 12.95/2.04    inference(avatar_split_clause,[],[f4527,f4474,f1658,f4531])).
% 12.95/2.04  fof(f4527,plain,(
% 12.95/2.04    r1_tarski(k2_tops_1(sK0,k1_xboole_0),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))) | (~spl2_21 | ~spl2_87)),
% 12.95/2.04    inference(resolution,[],[f4492,f1660])).
% 12.95/2.04  fof(f4519,plain,(
% 12.95/2.04    spl2_93 | ~spl2_88),
% 12.95/2.04    inference(avatar_split_clause,[],[f4498,f4479,f4516])).
% 12.95/2.04  fof(f4498,plain,(
% 12.95/2.04    k2_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) | ~spl2_88),
% 12.95/2.04    inference(resolution,[],[f4481,f86])).
% 12.95/2.04  fof(f4514,plain,(
% 12.95/2.04    spl2_92 | ~spl2_88),
% 12.95/2.04    inference(avatar_split_clause,[],[f4497,f4479,f4511])).
% 12.95/2.04  fof(f4497,plain,(
% 12.95/2.04    k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) = k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0)) | ~spl2_88),
% 12.95/2.04    inference(resolution,[],[f4481,f103])).
% 12.95/2.04  fof(f4509,plain,(
% 12.95/2.04    spl2_91 | ~spl2_88),
% 12.95/2.04    inference(avatar_split_clause,[],[f4495,f4479,f4506])).
% 12.95/2.04  fof(f4495,plain,(
% 12.95/2.04    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) | ~spl2_88),
% 12.95/2.04    inference(resolution,[],[f4481,f134])).
% 12.95/2.04  fof(f4504,plain,(
% 12.95/2.04    spl2_90 | ~spl2_4 | ~spl2_88),
% 12.95/2.04    inference(avatar_split_clause,[],[f4493,f4479,f125,f4501])).
% 12.95/2.04  fof(f4493,plain,(
% 12.95/2.04    k2_tops_1(sK0,k2_tops_1(sK0,k1_xboole_0)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k1_xboole_0))) | (~spl2_4 | ~spl2_88)),
% 12.95/2.04    inference(resolution,[],[f4481,f3224])).
% 12.95/2.04  fof(f4490,plain,(
% 12.95/2.04    ~spl2_89 | spl2_84),
% 12.95/2.04    inference(avatar_split_clause,[],[f4484,f4462,f4487])).
% 12.95/2.04  fof(f4487,plain,(
% 12.95/2.04    spl2_89 <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_89])])).
% 12.95/2.04  fof(f4462,plain,(
% 12.95/2.04    spl2_84 <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_84])])).
% 12.95/2.04  fof(f4484,plain,(
% 12.95/2.04    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | spl2_84),
% 12.95/2.04    inference(resolution,[],[f4464,f91])).
% 12.95/2.04  fof(f4464,plain,(
% 12.95/2.04    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_84),
% 12.95/2.04    inference(avatar_component_clause,[],[f4462])).
% 12.95/2.04  fof(f4485,plain,(
% 12.95/2.04    spl2_84),
% 12.95/2.04    inference(avatar_contradiction_clause,[],[f4483])).
% 12.95/2.04  fof(f4483,plain,(
% 12.95/2.04    $false | spl2_84),
% 12.95/2.04    inference(resolution,[],[f4464,f136])).
% 12.95/2.04  fof(f4482,plain,(
% 12.95/2.04    ~spl2_84 | spl2_88 | ~spl2_4 | ~spl2_81),
% 12.95/2.04    inference(avatar_split_clause,[],[f4460,f4432,f125,f4479,f4462])).
% 12.95/2.04  fof(f4460,plain,(
% 12.95/2.04    m1_subset_1(k2_tops_1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_4 | ~spl2_81)),
% 12.95/2.04    inference(superposition,[],[f2451,f4434])).
% 12.95/2.04  fof(f2451,plain,(
% 12.95/2.04    ( ! [X0] : (m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_4),
% 12.95/2.04    inference(resolution,[],[f89,f127])).
% 12.95/2.04  fof(f89,plain,(
% 12.95/2.04    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 12.95/2.04    inference(cnf_transformation,[],[f47])).
% 12.95/2.04  fof(f47,plain,(
% 12.95/2.04    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 12.95/2.04    inference(flattening,[],[f46])).
% 12.95/2.04  fof(f46,plain,(
% 12.95/2.04    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 12.95/2.04    inference(ennf_transformation,[],[f25])).
% 12.95/2.04  fof(f25,axiom,(
% 12.95/2.04    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 12.95/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 12.95/2.04  fof(f4477,plain,(
% 12.95/2.04    ~spl2_84 | spl2_87 | ~spl2_4 | ~spl2_81),
% 12.95/2.04    inference(avatar_split_clause,[],[f4459,f4432,f125,f4474,f4462])).
% 12.95/2.04  fof(f4459,plain,(
% 12.95/2.04    r1_tarski(k2_tops_1(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_4 | ~spl2_81)),
% 12.95/2.04    inference(superposition,[],[f2655,f4434])).
% 12.95/2.04  fof(f2655,plain,(
% 12.95/2.04    ( ! [X5] : (r1_tarski(k2_tops_1(sK0,X5),u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_4),
% 12.95/2.04    inference(resolution,[],[f2451,f90])).
% 12.95/2.04  fof(f90,plain,(
% 12.95/2.04    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 12.95/2.04    inference(cnf_transformation,[],[f60])).
% 12.95/2.04  fof(f4472,plain,(
% 12.95/2.04    ~spl2_84 | spl2_86 | ~spl2_4 | ~spl2_81),
% 12.95/2.04    inference(avatar_split_clause,[],[f4458,f4432,f125,f4470,f4462])).
% 12.95/2.04  fof(f4470,plain,(
% 12.95/2.04    spl2_86 <=> ! [X1] : r1_tarski(k1_setfam_1(k2_tarski(k2_tops_1(sK0,k1_xboole_0),X1)),u1_struct_0(sK0))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_86])])).
% 12.95/2.04  fof(f4458,plain,(
% 12.95/2.04    ( ! [X1] : (r1_tarski(k1_setfam_1(k2_tarski(k2_tops_1(sK0,k1_xboole_0),X1)),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_4 | ~spl2_81)),
% 12.95/2.04    inference(superposition,[],[f2656,f4434])).
% 12.95/2.04  fof(f2656,plain,(
% 12.95/2.04    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(k2_tops_1(sK0,X0),X1)),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_4),
% 12.95/2.04    inference(resolution,[],[f2655,f161])).
% 12.95/2.04  fof(f4468,plain,(
% 12.95/2.04    ~spl2_84 | spl2_85 | ~spl2_4 | ~spl2_81),
% 12.95/2.04    inference(avatar_split_clause,[],[f4457,f4432,f125,f4466,f4462])).
% 12.95/2.04  fof(f4466,plain,(
% 12.95/2.04    spl2_85 <=> ! [X0] : r1_tarski(k1_setfam_1(k2_tarski(X0,k2_tops_1(sK0,k1_xboole_0))),u1_struct_0(sK0))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_85])])).
% 12.95/2.04  fof(f4457,plain,(
% 12.95/2.04    ( ! [X0] : (r1_tarski(k1_setfam_1(k2_tarski(X0,k2_tops_1(sK0,k1_xboole_0))),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_4 | ~spl2_81)),
% 12.95/2.04    inference(superposition,[],[f3949,f4434])).
% 12.95/2.04  fof(f3949,plain,(
% 12.95/2.04    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,k2_tops_1(sK0,X0))),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_4),
% 12.95/2.04    inference(superposition,[],[f2656,f77])).
% 12.95/2.04  fof(f4456,plain,(
% 12.95/2.04    spl2_83 | ~spl2_3 | ~spl2_4),
% 12.95/2.04    inference(avatar_split_clause,[],[f4429,f125,f120,f4446])).
% 12.95/2.04  fof(f4429,plain,(
% 12.95/2.04    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_3 | ~spl2_4)),
% 12.95/2.04    inference(resolution,[],[f3224,f122])).
% 12.95/2.04  fof(f4455,plain,(
% 12.95/2.04    spl2_82 | ~spl2_4 | ~spl2_56 | ~spl2_58),
% 12.95/2.04    inference(avatar_split_clause,[],[f4454,f3388,f3372,f125,f4438])).
% 12.95/2.04  fof(f3388,plain,(
% 12.95/2.04    spl2_58 <=> k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).
% 12.95/2.04  fof(f4454,plain,(
% 12.95/2.04    k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) | (~spl2_4 | ~spl2_56 | ~spl2_58)),
% 12.95/2.04    inference(forward_demodulation,[],[f4428,f3390])).
% 12.95/2.04  fof(f3390,plain,(
% 12.95/2.04    k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) | ~spl2_58),
% 12.95/2.04    inference(avatar_component_clause,[],[f3388])).
% 12.95/2.04  fof(f4428,plain,(
% 12.95/2.04    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | (~spl2_4 | ~spl2_56)),
% 12.95/2.04    inference(resolution,[],[f3224,f3374])).
% 12.95/2.04  fof(f4449,plain,(
% 12.95/2.04    spl2_83 | ~spl2_4 | ~spl2_7 | ~spl2_12),
% 12.95/2.04    inference(avatar_split_clause,[],[f4444,f890,f523,f125,f4446])).
% 12.95/2.04  fof(f4444,plain,(
% 12.95/2.04    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_4 | ~spl2_7 | ~spl2_12)),
% 12.95/2.04    inference(forward_demodulation,[],[f4420,f525])).
% 12.95/2.04  fof(f4420,plain,(
% 12.95/2.04    k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl2_4 | ~spl2_12)),
% 12.95/2.04    inference(resolution,[],[f3224,f892])).
% 12.95/2.04  fof(f4443,plain,(
% 12.95/2.04    spl2_81 | ~spl2_4),
% 12.95/2.04    inference(avatar_split_clause,[],[f4442,f125,f4432])).
% 12.95/2.04  fof(f4442,plain,(
% 12.95/2.04    k2_tops_1(sK0,u1_struct_0(sK0)) = k2_tops_1(sK0,k1_xboole_0) | ~spl2_4),
% 12.95/2.04    inference(forward_demodulation,[],[f4419,f856])).
% 12.95/2.04  fof(f4419,plain,(
% 12.95/2.04    k2_tops_1(sK0,k1_xboole_0) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) | ~spl2_4),
% 12.95/2.04    inference(resolution,[],[f3224,f169])).
% 12.95/2.04  fof(f4441,plain,(
% 12.95/2.04    spl2_82 | ~spl2_4 | ~spl2_60 | ~spl2_68),
% 12.95/2.04    inference(avatar_split_clause,[],[f4436,f3680,f3399,f125,f4438])).
% 12.95/2.04  fof(f3399,plain,(
% 12.95/2.04    spl2_60 <=> k2_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 12.95/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_60])])).
% 12.95/2.04  fof(f4436,plain,(
% 12.95/2.04    k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) | (~spl2_4 | ~spl2_60 | ~spl2_68)),
% 12.95/2.04    inference(forward_demodulation,[],[f4418,f3401])).
% 12.95/2.04  fof(f3401,plain,(
% 12.95/2.04    k2_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | ~spl2_60),
% 12.95/2.04    inference(avatar_component_clause,[],[f3399])).
% 12.95/2.04  fof(f4418,plain,(
% 12.95/2.04    k2_tops_1(sK0,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))) | (~spl2_4 | ~spl2_68)),
% 12.95/2.04    inference(resolution,[],[f3224,f3682])).
% 12.95/2.04  fof(f4435,plain,(
% 12.95/2.04    spl2_81 | ~spl2_4),
% 12.95/2.04    inference(avatar_split_clause,[],[f4430,f125,f4432])).
% 12.95/2.04  fof(f4430,plain,(
% 12.95/2.04    k2_tops_1(sK0,u1_struct_0(sK0)) = k2_tops_1(sK0,k1_xboole_0) | ~spl2_4),
% 12.95/2.04    inference(forward_demodulation,[],[f4416,f855])).
% 12.95/2.04  fof(f4416,plain,(
% 12.95/2.04    k2_tops_1(sK0,u1_struct_0(sK0)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) | ~spl2_4),
% 12.95/2.04    inference(resolution,[],[f3224,f136])).
% 12.95/2.04  fof(f4350,plain,(
% 12.95/2.04    spl2_80 | ~spl2_79),
% 12.95/2.04    inference(avatar_split_clause,[],[f4345,f4328,f4347])).
% 12.95/2.05  fof(f4345,plain,(
% 12.95/2.05    k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)))) | ~spl2_79),
% 12.95/2.05    inference(forward_demodulation,[],[f4344,f77])).
% 12.95/2.05  fof(f4344,plain,(
% 12.95/2.05    k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))) | ~spl2_79),
% 12.95/2.05    inference(forward_demodulation,[],[f4339,f98])).
% 12.95/2.05  fof(f4339,plain,(
% 12.95/2.05    k1_setfam_1(k2_tarski(k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))) = k6_subset_1(k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),k1_xboole_0) | ~spl2_79),
% 12.95/2.05    inference(superposition,[],[f100,f4330])).
% 12.95/2.05  fof(f4333,plain,(
% 12.95/2.05    spl2_79 | ~spl2_6 | ~spl2_15 | ~spl2_16 | ~spl2_48),
% 12.95/2.05    inference(avatar_split_clause,[],[f4326,f2833,f939,f913,f145,f4328])).
% 12.95/2.05  fof(f4326,plain,(
% 12.95/2.05    k1_xboole_0 = k6_subset_1(k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) | (~spl2_6 | ~spl2_15 | ~spl2_16 | ~spl2_48)),
% 12.95/2.05    inference(resolution,[],[f4314,f104])).
% 12.95/2.05  fof(f4314,plain,(
% 12.95/2.05    ( ! [X1] : (r1_tarski(k6_subset_1(k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)),X1)) ) | (~spl2_6 | ~spl2_15 | ~spl2_16 | ~spl2_48)),
% 12.95/2.05    inference(resolution,[],[f4033,f106])).
% 12.95/2.05  fof(f4033,plain,(
% 12.95/2.05    ( ! [X1] : (r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),k3_tarski(k2_tarski(u1_struct_0(sK0),X1)))) ) | (~spl2_6 | ~spl2_15 | ~spl2_16 | ~spl2_48)),
% 12.95/2.05    inference(resolution,[],[f3987,f3105])).
% 12.95/2.05  fof(f3987,plain,(
% 12.95/2.05    ( ! [X0] : (r1_tarski(sK1,k3_tarski(k2_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_tarski(k2_tarski(u1_struct_0(sK0),X0)))))) ) | (~spl2_6 | ~spl2_15 | ~spl2_16)),
% 12.95/2.05    inference(resolution,[],[f1878,f153])).
% 12.95/2.05  fof(f153,plain,(
% 12.95/2.05    ( ! [X5] : (~r1_tarski(u1_struct_0(sK0),X5) | r1_tarski(sK1,X5)) ) | ~spl2_6),
% 12.95/2.05    inference(resolution,[],[f95,f147])).
% 12.95/2.05  fof(f147,plain,(
% 12.95/2.05    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_6),
% 12.95/2.05    inference(avatar_component_clause,[],[f145])).
% 12.95/2.05  fof(f1878,plain,(
% 12.95/2.05    ( ! [X0] : (r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_tarski(k2_tarski(u1_struct_0(sK0),X0)))))) ) | (~spl2_15 | ~spl2_16)),
% 12.95/2.05    inference(resolution,[],[f1317,f1320])).
% 12.95/2.05  fof(f4331,plain,(
% 12.95/2.05    spl2_79 | ~spl2_6 | ~spl2_15 | ~spl2_16 | ~spl2_48),
% 12.95/2.05    inference(avatar_split_clause,[],[f4324,f2833,f939,f913,f145,f4328])).
% 12.95/2.05  fof(f4324,plain,(
% 12.95/2.05    k1_xboole_0 = k6_subset_1(k6_subset_1(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) | (~spl2_6 | ~spl2_15 | ~spl2_16 | ~spl2_48)),
% 12.95/2.05    inference(resolution,[],[f4314,f168])).
% 12.95/2.05  fof(f4083,plain,(
% 12.95/2.05    spl2_78 | ~spl2_77),
% 12.95/2.05    inference(avatar_split_clause,[],[f4078,f4061,f4080])).
% 12.95/2.05  fof(f4080,plain,(
% 12.95/2.05    spl2_78 <=> k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).
% 12.95/2.05  fof(f4061,plain,(
% 12.95/2.05    spl2_77 <=> k1_xboole_0 = k6_subset_1(k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).
% 12.95/2.05  fof(f4078,plain,(
% 12.95/2.05    k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))) | ~spl2_77),
% 12.95/2.05    inference(forward_demodulation,[],[f4077,f77])).
% 12.95/2.05  fof(f4077,plain,(
% 12.95/2.05    k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))) | ~spl2_77),
% 12.95/2.05    inference(forward_demodulation,[],[f4072,f98])).
% 12.95/2.05  fof(f4072,plain,(
% 12.95/2.05    k1_setfam_1(k2_tarski(k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))) = k6_subset_1(k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)),k1_xboole_0) | ~spl2_77),
% 12.95/2.05    inference(superposition,[],[f100,f4063])).
% 12.95/2.05  fof(f4063,plain,(
% 12.95/2.05    k1_xboole_0 = k6_subset_1(k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) | ~spl2_77),
% 12.95/2.05    inference(avatar_component_clause,[],[f4061])).
% 12.95/2.05  fof(f4066,plain,(
% 12.95/2.05    spl2_77 | ~spl2_6 | ~spl2_15 | ~spl2_16),
% 12.95/2.05    inference(avatar_split_clause,[],[f4059,f939,f913,f145,f4061])).
% 12.95/2.05  fof(f4059,plain,(
% 12.95/2.05    k1_xboole_0 = k6_subset_1(k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) | (~spl2_6 | ~spl2_15 | ~spl2_16)),
% 12.95/2.05    inference(resolution,[],[f4047,f104])).
% 12.95/2.05  fof(f4047,plain,(
% 12.95/2.05    ( ! [X1] : (r1_tarski(k6_subset_1(k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)),X1)) ) | (~spl2_6 | ~spl2_15 | ~spl2_16)),
% 12.95/2.05    inference(resolution,[],[f4039,f106])).
% 12.95/2.05  fof(f4039,plain,(
% 12.95/2.05    ( ! [X12] : (r1_tarski(k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)),k3_tarski(k2_tarski(u1_struct_0(sK0),X12)))) ) | (~spl2_6 | ~spl2_15 | ~spl2_16)),
% 12.95/2.05    inference(resolution,[],[f3987,f106])).
% 12.95/2.05  fof(f4064,plain,(
% 12.95/2.05    spl2_77 | ~spl2_6 | ~spl2_15 | ~spl2_16),
% 12.95/2.05    inference(avatar_split_clause,[],[f4057,f939,f913,f145,f4061])).
% 12.95/2.05  fof(f4057,plain,(
% 12.95/2.05    k1_xboole_0 = k6_subset_1(k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) | (~spl2_6 | ~spl2_15 | ~spl2_16)),
% 12.95/2.05    inference(resolution,[],[f4047,f168])).
% 12.95/2.05  fof(f3848,plain,(
% 12.95/2.05    spl2_76 | ~spl2_72),
% 12.95/2.05    inference(avatar_split_clause,[],[f3843,f3781,f3845])).
% 12.95/2.05  fof(f3845,plain,(
% 12.95/2.05    spl2_76 <=> k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).
% 12.95/2.05  fof(f3781,plain,(
% 12.95/2.05    spl2_72 <=> k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).
% 12.95/2.05  fof(f3843,plain,(
% 12.95/2.05    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))) | ~spl2_72),
% 12.95/2.05    inference(forward_demodulation,[],[f3834,f98])).
% 12.95/2.05  fof(f3834,plain,(
% 12.95/2.05    k6_subset_1(k2_tops_1(sK0,sK1),k1_xboole_0) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))) | ~spl2_72),
% 12.95/2.05    inference(superposition,[],[f100,f3783])).
% 12.95/2.05  fof(f3783,plain,(
% 12.95/2.05    k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))) | ~spl2_72),
% 12.95/2.05    inference(avatar_component_clause,[],[f3781])).
% 12.95/2.05  fof(f3811,plain,(
% 12.95/2.05    spl2_74 | ~spl2_75 | ~spl2_66),
% 12.95/2.05    inference(avatar_split_clause,[],[f3794,f3670,f3808,f3804])).
% 12.95/2.05  fof(f3804,plain,(
% 12.95/2.05    spl2_74 <=> k1_xboole_0 = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).
% 12.95/2.05  fof(f3808,plain,(
% 12.95/2.05    spl2_75 <=> r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).
% 12.95/2.05  fof(f3670,plain,(
% 12.95/2.05    spl2_66 <=> k2_tops_1(sK0,sK1) = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).
% 12.95/2.05  fof(f3794,plain,(
% 12.95/2.05    ~r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | k1_xboole_0 = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) | ~spl2_66),
% 12.95/2.05    inference(superposition,[],[f104,f3672])).
% 12.95/2.05  fof(f3672,plain,(
% 12.95/2.05    k2_tops_1(sK0,sK1) = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | ~spl2_66),
% 12.95/2.05    inference(avatar_component_clause,[],[f3670])).
% 12.95/2.05  fof(f3802,plain,(
% 12.95/2.05    spl2_73 | ~spl2_55 | ~spl2_66),
% 12.95/2.05    inference(avatar_split_clause,[],[f3797,f3670,f3367,f3799])).
% 12.95/2.05  fof(f3799,plain,(
% 12.95/2.05    spl2_73 <=> k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).
% 12.95/2.05  fof(f3797,plain,(
% 12.95/2.05    k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))) | (~spl2_55 | ~spl2_66)),
% 12.95/2.05    inference(forward_demodulation,[],[f3792,f3369])).
% 12.95/2.05  fof(f3792,plain,(
% 12.95/2.05    k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))) | ~spl2_66),
% 12.95/2.05    inference(superposition,[],[f100,f3672])).
% 12.95/2.05  fof(f3786,plain,(
% 12.95/2.05    spl2_72 | ~spl2_16 | ~spl2_21 | ~spl2_48),
% 12.95/2.05    inference(avatar_split_clause,[],[f3779,f2833,f1658,f939,f3781])).
% 12.95/2.05  fof(f3779,plain,(
% 12.95/2.05    k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))) | (~spl2_16 | ~spl2_21 | ~spl2_48)),
% 12.95/2.05    inference(resolution,[],[f3571,f104])).
% 12.95/2.05  fof(f3571,plain,(
% 12.95/2.05    ( ! [X4] : (r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))),X4)) ) | (~spl2_16 | ~spl2_21 | ~spl2_48)),
% 12.95/2.05    inference(resolution,[],[f3105,f1752])).
% 12.95/2.05  fof(f1752,plain,(
% 12.95/2.05    ( ! [X0] : (r1_tarski(sK1,k3_tarski(k2_tarski(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),X0)))) ) | (~spl2_16 | ~spl2_21)),
% 12.95/2.05    inference(superposition,[],[f1696,f77])).
% 12.95/2.05  fof(f1696,plain,(
% 12.95/2.05    ( ! [X0] : (r1_tarski(sK1,k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))))) ) | (~spl2_16 | ~spl2_21)),
% 12.95/2.05    inference(resolution,[],[f1687,f107])).
% 12.95/2.05  fof(f3784,plain,(
% 12.95/2.05    spl2_72 | ~spl2_16 | ~spl2_21 | ~spl2_48),
% 12.95/2.05    inference(avatar_split_clause,[],[f3777,f2833,f1658,f939,f3781])).
% 12.95/2.05  fof(f3777,plain,(
% 12.95/2.05    k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))) | (~spl2_16 | ~spl2_21 | ~spl2_48)),
% 12.95/2.05    inference(resolution,[],[f3571,f168])).
% 12.95/2.05  fof(f3727,plain,(
% 12.95/2.05    spl2_71 | ~spl2_21 | ~spl2_55),
% 12.95/2.05    inference(avatar_split_clause,[],[f3722,f3367,f1658,f3724])).
% 12.95/2.05  fof(f3724,plain,(
% 12.95/2.05    spl2_71 <=> r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).
% 12.95/2.05  fof(f3722,plain,(
% 12.95/2.05    r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))) | (~spl2_21 | ~spl2_55)),
% 12.95/2.05    inference(resolution,[],[f3659,f1660])).
% 12.95/2.05  fof(f3718,plain,(
% 12.95/2.05    spl2_70 | ~spl2_60 | ~spl2_68),
% 12.95/2.05    inference(avatar_split_clause,[],[f3713,f3680,f3399,f3715])).
% 12.95/2.05  fof(f3715,plain,(
% 12.95/2.05    spl2_70 <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).
% 12.95/2.05  fof(f3713,plain,(
% 12.95/2.05    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | (~spl2_60 | ~spl2_68)),
% 12.95/2.05    inference(forward_demodulation,[],[f3708,f3401])).
% 12.95/2.05  fof(f3708,plain,(
% 12.95/2.05    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))) | ~spl2_68),
% 12.95/2.05    inference(resolution,[],[f3682,f134])).
% 12.95/2.05  fof(f3688,plain,(
% 12.95/2.05    spl2_69 | ~spl2_55),
% 12.95/2.05    inference(avatar_split_clause,[],[f3662,f3367,f3685])).
% 12.95/2.05  fof(f3685,plain,(
% 12.95/2.05    spl2_69 <=> r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),u1_struct_0(sK0))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).
% 12.95/2.05  fof(f3662,plain,(
% 12.95/2.05    r1_tarski(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),u1_struct_0(sK0)) | ~spl2_55),
% 12.95/2.05    inference(superposition,[],[f99,f3369])).
% 12.95/2.05  fof(f3683,plain,(
% 12.95/2.05    spl2_68 | ~spl2_55),
% 12.95/2.05    inference(avatar_split_clause,[],[f3661,f3367,f3680])).
% 12.95/2.05  fof(f3661,plain,(
% 12.95/2.05    m1_subset_1(k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_55),
% 12.95/2.05    inference(superposition,[],[f76,f3369])).
% 12.95/2.05  fof(f3678,plain,(
% 12.95/2.05    spl2_51 | ~spl2_67 | ~spl2_55),
% 12.95/2.05    inference(avatar_split_clause,[],[f3660,f3367,f3675,f3116])).
% 12.95/2.05  fof(f3675,plain,(
% 12.95/2.05    spl2_67 <=> r1_tarski(k2_tops_1(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).
% 12.95/2.05  fof(f3660,plain,(
% 12.95/2.05    ~r1_tarski(k2_tops_1(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | k1_xboole_0 = k2_tops_1(sK0,sK1) | ~spl2_55),
% 12.95/2.05    inference(superposition,[],[f104,f3369])).
% 12.95/2.05  fof(f3673,plain,(
% 12.95/2.05    spl2_66 | ~spl2_54 | ~spl2_55),
% 12.95/2.05    inference(avatar_split_clause,[],[f3668,f3367,f3271,f3670])).
% 12.95/2.05  fof(f3271,plain,(
% 12.95/2.05    spl2_54 <=> k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 12.95/2.05  fof(f3668,plain,(
% 12.95/2.05    k2_tops_1(sK0,sK1) = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | (~spl2_54 | ~spl2_55)),
% 12.95/2.05    inference(forward_demodulation,[],[f3658,f3273])).
% 12.95/2.05  fof(f3273,plain,(
% 12.95/2.05    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | ~spl2_54),
% 12.95/2.05    inference(avatar_component_clause,[],[f3271])).
% 12.95/2.05  fof(f3658,plain,(
% 12.95/2.05    k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | ~spl2_55),
% 12.95/2.05    inference(superposition,[],[f100,f3369])).
% 12.95/2.05  fof(f3667,plain,(
% 12.95/2.05    ~spl2_65 | ~spl2_52 | ~spl2_55),
% 12.95/2.05    inference(avatar_split_clause,[],[f3656,f3367,f3121,f3664])).
% 12.95/2.05  fof(f3664,plain,(
% 12.95/2.05    spl2_65 <=> r1_tarski(sK1,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).
% 12.95/2.05  fof(f3656,plain,(
% 12.95/2.05    ~r1_tarski(sK1,k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | (~spl2_52 | ~spl2_55)),
% 12.95/2.05    inference(superposition,[],[f3122,f3369])).
% 12.95/2.05  fof(f3631,plain,(
% 12.95/2.05    spl2_64 | ~spl2_63),
% 12.95/2.05    inference(avatar_split_clause,[],[f3626,f3602,f3628])).
% 12.95/2.05  fof(f3628,plain,(
% 12.95/2.05    spl2_64 <=> k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).
% 12.95/2.05  fof(f3602,plain,(
% 12.95/2.05    spl2_63 <=> k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).
% 12.95/2.05  fof(f3626,plain,(
% 12.95/2.05    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))) | ~spl2_63),
% 12.95/2.05    inference(forward_demodulation,[],[f3618,f98])).
% 12.95/2.05  fof(f3618,plain,(
% 12.95/2.05    k6_subset_1(k2_tops_1(sK0,sK1),k1_xboole_0) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))) | ~spl2_63),
% 12.95/2.05    inference(superposition,[],[f100,f3604])).
% 12.95/2.05  fof(f3604,plain,(
% 12.95/2.05    k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))) | ~spl2_63),
% 12.95/2.05    inference(avatar_component_clause,[],[f3602])).
% 12.95/2.05  fof(f3607,plain,(
% 12.95/2.05    spl2_63 | ~spl2_13 | ~spl2_16 | ~spl2_21 | ~spl2_48),
% 12.95/2.05    inference(avatar_split_clause,[],[f3600,f2833,f1658,f939,f895,f3602])).
% 12.95/2.05  fof(f3600,plain,(
% 12.95/2.05    k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))) | (~spl2_13 | ~spl2_16 | ~spl2_21 | ~spl2_48)),
% 12.95/2.05    inference(resolution,[],[f3572,f104])).
% 12.95/2.05  fof(f3572,plain,(
% 12.95/2.05    ( ! [X5] : (r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))),X5)) ) | (~spl2_13 | ~spl2_16 | ~spl2_21 | ~spl2_48)),
% 12.95/2.05    inference(resolution,[],[f3105,f2476])).
% 12.95/2.05  fof(f2476,plain,(
% 12.95/2.05    ( ! [X0] : (r1_tarski(sK1,k3_tarski(k2_tarski(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),X0)))) ) | (~spl2_13 | ~spl2_16 | ~spl2_21)),
% 12.95/2.05    inference(superposition,[],[f2463,f77])).
% 12.95/2.05  fof(f2463,plain,(
% 12.95/2.05    ( ! [X0] : (r1_tarski(sK1,k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))))) ) | (~spl2_13 | ~spl2_16 | ~spl2_21)),
% 12.95/2.05    inference(resolution,[],[f2452,f107])).
% 12.95/2.05  fof(f2452,plain,(
% 12.95/2.05    ( ! [X0] : (r1_tarski(k6_subset_1(sK1,X0),k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))) ) | (~spl2_13 | ~spl2_16 | ~spl2_21)),
% 12.95/2.05    inference(resolution,[],[f2446,f107])).
% 12.95/2.05  fof(f3605,plain,(
% 12.95/2.05    spl2_63 | ~spl2_13 | ~spl2_16 | ~spl2_21 | ~spl2_48),
% 12.95/2.05    inference(avatar_split_clause,[],[f3598,f2833,f1658,f939,f895,f3602])).
% 12.95/2.05  fof(f3598,plain,(
% 12.95/2.05    k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))) | (~spl2_13 | ~spl2_16 | ~spl2_21 | ~spl2_48)),
% 12.95/2.05    inference(resolution,[],[f3572,f168])).
% 12.95/2.05  fof(f3477,plain,(
% 12.95/2.05    ~spl2_4 | spl2_62 | ~spl2_5),
% 12.95/2.05    inference(avatar_split_clause,[],[f3473,f130,f3475,f125])).
% 12.95/2.05  fof(f130,plain,(
% 12.95/2.05    spl2_5 <=> v2_pre_topc(sK0)),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 12.95/2.05  fof(f3473,plain,(
% 12.95/2.05    ( ! [X0] : (k2_pre_topc(sK0,X0) != X0 | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl2_5),
% 12.95/2.05    inference(resolution,[],[f73,f132])).
% 12.95/2.05  fof(f132,plain,(
% 12.95/2.05    v2_pre_topc(sK0) | ~spl2_5),
% 12.95/2.05    inference(avatar_component_clause,[],[f130])).
% 12.95/2.05  fof(f73,plain,(
% 12.95/2.05    ( ! [X0,X1] : (~v2_pre_topc(X0) | k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 12.95/2.05    inference(cnf_transformation,[],[f38])).
% 12.95/2.05  fof(f38,plain,(
% 12.95/2.05    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 12.95/2.05    inference(flattening,[],[f37])).
% 12.95/2.05  fof(f37,plain,(
% 12.95/2.05    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 12.95/2.05    inference(ennf_transformation,[],[f24])).
% 12.95/2.05  fof(f24,axiom,(
% 12.95/2.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 12.95/2.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 12.95/2.05  fof(f3408,plain,(
% 12.95/2.05    spl2_61 | ~spl2_57 | ~spl2_58),
% 12.95/2.05    inference(avatar_split_clause,[],[f3403,f3388,f3382,f3405])).
% 12.95/2.05  fof(f3405,plain,(
% 12.95/2.05    spl2_61 <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).
% 12.95/2.05  fof(f3382,plain,(
% 12.95/2.05    spl2_57 <=> u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 12.95/2.05  fof(f3403,plain,(
% 12.95/2.05    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | (~spl2_57 | ~spl2_58)),
% 12.95/2.05    inference(forward_demodulation,[],[f3384,f3390])).
% 12.95/2.05  fof(f3384,plain,(
% 12.95/2.05    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | ~spl2_57),
% 12.95/2.05    inference(avatar_component_clause,[],[f3382])).
% 12.95/2.05  fof(f3402,plain,(
% 12.95/2.05    spl2_60 | ~spl2_58 | ~spl2_59),
% 12.95/2.05    inference(avatar_split_clause,[],[f3397,f3393,f3388,f3399])).
% 12.95/2.05  fof(f3393,plain,(
% 12.95/2.05    spl2_59 <=> k2_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).
% 12.95/2.05  fof(f3397,plain,(
% 12.95/2.05    k2_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | (~spl2_58 | ~spl2_59)),
% 12.95/2.05    inference(backward_demodulation,[],[f3395,f3390])).
% 12.95/2.05  fof(f3395,plain,(
% 12.95/2.05    k2_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | ~spl2_59),
% 12.95/2.05    inference(avatar_component_clause,[],[f3393])).
% 12.95/2.05  fof(f3396,plain,(
% 12.95/2.05    spl2_59 | ~spl2_56),
% 12.95/2.05    inference(avatar_split_clause,[],[f3379,f3372,f3393])).
% 12.95/2.05  fof(f3379,plain,(
% 12.95/2.05    k2_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | ~spl2_56),
% 12.95/2.05    inference(resolution,[],[f3374,f86])).
% 12.95/2.05  fof(f3391,plain,(
% 12.95/2.05    spl2_58 | ~spl2_55 | ~spl2_56),
% 12.95/2.05    inference(avatar_split_clause,[],[f3386,f3372,f3367,f3388])).
% 12.95/2.05  fof(f3386,plain,(
% 12.95/2.05    k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) | (~spl2_55 | ~spl2_56)),
% 12.95/2.05    inference(forward_demodulation,[],[f3378,f3369])).
% 12.95/2.05  fof(f3378,plain,(
% 12.95/2.05    k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) | ~spl2_56),
% 12.95/2.05    inference(resolution,[],[f3374,f103])).
% 12.95/2.05  fof(f3385,plain,(
% 12.95/2.05    spl2_57 | ~spl2_56),
% 12.95/2.05    inference(avatar_split_clause,[],[f3376,f3372,f3382])).
% 12.95/2.05  fof(f3376,plain,(
% 12.95/2.05    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | ~spl2_56),
% 12.95/2.05    inference(resolution,[],[f3374,f134])).
% 12.95/2.05  fof(f3375,plain,(
% 12.95/2.05    spl2_56 | ~spl2_54),
% 12.95/2.05    inference(avatar_split_clause,[],[f3363,f3271,f3372])).
% 12.95/2.05  fof(f3363,plain,(
% 12.95/2.05    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_54),
% 12.95/2.05    inference(superposition,[],[f163,f3273])).
% 12.95/2.05  fof(f3370,plain,(
% 12.95/2.05    spl2_55 | ~spl2_54),
% 12.95/2.05    inference(avatar_split_clause,[],[f3361,f3271,f3367])).
% 12.95/2.05  fof(f3361,plain,(
% 12.95/2.05    k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) | ~spl2_54),
% 12.95/2.05    inference(superposition,[],[f102,f3273])).
% 12.95/2.05  fof(f3274,plain,(
% 12.95/2.05    spl2_54 | ~spl2_53),
% 12.95/2.05    inference(avatar_split_clause,[],[f3269,f3252,f3271])).
% 12.95/2.05  fof(f3252,plain,(
% 12.95/2.05    spl2_53 <=> k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 12.95/2.05  fof(f3269,plain,(
% 12.95/2.05    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) | ~spl2_53),
% 12.95/2.05    inference(forward_demodulation,[],[f3268,f77])).
% 12.95/2.05  fof(f3268,plain,(
% 12.95/2.05    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))) | ~spl2_53),
% 12.95/2.05    inference(forward_demodulation,[],[f3263,f98])).
% 12.95/2.05  fof(f3263,plain,(
% 12.95/2.05    k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))) = k6_subset_1(k2_tops_1(sK0,sK1),k1_xboole_0) | ~spl2_53),
% 12.95/2.05    inference(superposition,[],[f100,f3254])).
% 12.95/2.05  fof(f3254,plain,(
% 12.95/2.05    k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~spl2_53),
% 12.95/2.05    inference(avatar_component_clause,[],[f3252])).
% 12.95/2.05  fof(f3257,plain,(
% 12.95/2.05    spl2_53 | ~spl2_16 | ~spl2_48),
% 12.95/2.05    inference(avatar_split_clause,[],[f3250,f2833,f939,f3252])).
% 12.95/2.05  fof(f3250,plain,(
% 12.95/2.05    k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl2_16 | ~spl2_48)),
% 12.95/2.05    inference(resolution,[],[f3238,f104])).
% 12.95/2.05  fof(f3238,plain,(
% 12.95/2.05    ( ! [X0] : (r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),u1_struct_0(sK0)),X0)) ) | (~spl2_16 | ~spl2_48)),
% 12.95/2.05    inference(resolution,[],[f3234,f106])).
% 12.95/2.05  fof(f3234,plain,(
% 12.95/2.05    ( ! [X1] : (r1_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(u1_struct_0(sK0),X1)))) ) | (~spl2_16 | ~spl2_48)),
% 12.95/2.05    inference(superposition,[],[f3144,f171])).
% 12.95/2.05  fof(f3144,plain,(
% 12.95/2.05    ( ! [X2,X1] : (r1_tarski(k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X1)),k3_tarski(k2_tarski(u1_struct_0(sK0),X2)))) ) | (~spl2_16 | ~spl2_48)),
% 12.95/2.05    inference(resolution,[],[f3096,f1320])).
% 12.95/2.05  fof(f3096,plain,(
% 12.95/2.05    ( ! [X2,X3] : (~r1_tarski(sK1,X2) | r1_tarski(k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X3)),X2)) ) | ~spl2_48),
% 12.95/2.05    inference(resolution,[],[f3093,f95])).
% 12.95/2.05  fof(f3093,plain,(
% 12.95/2.05    ( ! [X0] : (r1_tarski(k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X0)),sK1)) ) | ~spl2_48),
% 12.95/2.05    inference(resolution,[],[f2835,f161])).
% 12.95/2.05  fof(f3255,plain,(
% 12.95/2.05    spl2_53 | ~spl2_16 | ~spl2_48),
% 12.95/2.05    inference(avatar_split_clause,[],[f3248,f2833,f939,f3252])).
% 12.95/2.05  fof(f3248,plain,(
% 12.95/2.05    k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl2_16 | ~spl2_48)),
% 12.95/2.05    inference(resolution,[],[f3238,f168])).
% 12.95/2.05  fof(f3223,plain,(
% 12.95/2.05    spl2_41 | ~spl2_40),
% 12.95/2.05    inference(avatar_split_clause,[],[f3220,f2794,f2799])).
% 12.95/2.05  fof(f2799,plain,(
% 12.95/2.05    spl2_41 <=> r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),sK1),k3_subset_1(u1_struct_0(sK0),sK1))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 12.95/2.05  fof(f2794,plain,(
% 12.95/2.05    spl2_40 <=> r1_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 12.95/2.05  fof(f3220,plain,(
% 12.95/2.05    r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_40),
% 12.95/2.05    inference(resolution,[],[f2796,f106])).
% 12.95/2.05  fof(f2796,plain,(
% 12.95/2.05    r1_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))) | ~spl2_40),
% 12.95/2.05    inference(avatar_component_clause,[],[f2794])).
% 12.95/2.05  fof(f3168,plain,(
% 12.95/2.05    spl2_40 | ~spl2_21 | ~spl2_39),
% 12.95/2.05    inference(avatar_split_clause,[],[f3167,f2789,f1658,f2794])).
% 12.95/2.05  fof(f2789,plain,(
% 12.95/2.05    spl2_39 <=> r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 12.95/2.05  fof(f3167,plain,(
% 12.95/2.05    r1_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))) | (~spl2_21 | ~spl2_39)),
% 12.95/2.05    inference(resolution,[],[f3159,f1660])).
% 12.95/2.05  fof(f3159,plain,(
% 12.95/2.05    ( ! [X1] : (~r1_tarski(u1_struct_0(sK0),X1) | r1_tarski(k2_tops_1(sK0,sK1),X1)) ) | ~spl2_39),
% 12.95/2.05    inference(resolution,[],[f2791,f95])).
% 12.95/2.05  fof(f2791,plain,(
% 12.95/2.05    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~spl2_39),
% 12.95/2.05    inference(avatar_component_clause,[],[f2789])).
% 12.95/2.05  fof(f3157,plain,(
% 12.95/2.05    spl2_39 | ~spl2_6 | ~spl2_48),
% 12.95/2.05    inference(avatar_split_clause,[],[f3156,f2833,f145,f2789])).
% 12.95/2.05  fof(f3156,plain,(
% 12.95/2.05    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl2_6 | ~spl2_48)),
% 12.95/2.05    inference(superposition,[],[f3150,f171])).
% 12.95/2.05  fof(f3150,plain,(
% 12.95/2.05    ( ! [X13] : (r1_tarski(k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X13)),u1_struct_0(sK0))) ) | (~spl2_6 | ~spl2_48)),
% 12.95/2.05    inference(resolution,[],[f3096,f147])).
% 12.95/2.05  fof(f3123,plain,(
% 12.95/2.05    spl2_51 | spl2_52 | ~spl2_48),
% 12.95/2.05    inference(avatar_split_clause,[],[f3106,f2833,f3121,f3116])).
% 12.95/2.05  fof(f3106,plain,(
% 12.95/2.05    ( ! [X7] : (~r1_tarski(sK1,k6_subset_1(X7,k2_tops_1(sK0,sK1))) | k1_xboole_0 = k2_tops_1(sK0,sK1)) ) | ~spl2_48),
% 12.95/2.05    inference(resolution,[],[f3094,f104])).
% 12.95/2.05  fof(f3119,plain,(
% 12.95/2.05    spl2_51 | ~spl2_50 | ~spl2_48),
% 12.95/2.05    inference(avatar_split_clause,[],[f3104,f2833,f3111,f3116])).
% 12.95/2.05  fof(f3111,plain,(
% 12.95/2.05    spl2_50 <=> r1_tarski(sK1,k1_xboole_0)),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 12.95/2.05  fof(f3104,plain,(
% 12.95/2.05    ~r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = k2_tops_1(sK0,sK1) | ~spl2_48),
% 12.95/2.05    inference(resolution,[],[f3094,f168])).
% 12.95/2.05  fof(f3114,plain,(
% 12.95/2.05    spl2_49 | ~spl2_50 | ~spl2_48),
% 12.95/2.05    inference(avatar_split_clause,[],[f3103,f2833,f3111,f3108])).
% 12.95/2.05  fof(f3108,plain,(
% 12.95/2.05    spl2_49 <=> ! [X4] : k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),X4)),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 12.95/2.05  fof(f3103,plain,(
% 12.95/2.05    ( ! [X4] : (~r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),X4)) ) | ~spl2_48),
% 12.95/2.05    inference(resolution,[],[f3094,f184])).
% 12.95/2.05  fof(f3092,plain,(
% 12.95/2.05    spl2_48 | ~spl2_3 | ~spl2_1 | ~spl2_4),
% 12.95/2.05    inference(avatar_split_clause,[],[f3091,f125,f110,f120,f2833])).
% 12.95/2.05  fof(f3091,plain,(
% 12.95/2.05    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_1 | ~spl2_4)),
% 12.95/2.05    inference(resolution,[],[f3061,f111])).
% 12.95/2.05  fof(f111,plain,(
% 12.95/2.05    v4_pre_topc(sK1,sK0) | ~spl2_1),
% 12.95/2.05    inference(avatar_component_clause,[],[f110])).
% 12.95/2.05  fof(f3061,plain,(
% 12.95/2.05    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_tops_1(sK0,X0),X0)) ) | ~spl2_4),
% 12.95/2.05    inference(resolution,[],[f74,f127])).
% 12.95/2.05  fof(f74,plain,(
% 12.95/2.05    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_tops_1(X0,X1),X1)) )),
% 12.95/2.05    inference(cnf_transformation,[],[f40])).
% 12.95/2.05  fof(f40,plain,(
% 12.95/2.05    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 12.95/2.05    inference(flattening,[],[f39])).
% 12.95/2.05  fof(f39,plain,(
% 12.95/2.05    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 12.95/2.05    inference(ennf_transformation,[],[f28])).
% 12.95/2.05  fof(f28,axiom,(
% 12.95/2.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 12.95/2.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 12.95/2.05  fof(f2836,plain,(
% 12.95/2.05    spl2_48 | ~spl2_22),
% 12.95/2.05    inference(avatar_split_clause,[],[f2787,f1773,f2833])).
% 12.95/2.05  fof(f2787,plain,(
% 12.95/2.05    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_22),
% 12.95/2.05    inference(superposition,[],[f99,f1774])).
% 12.95/2.05  fof(f2831,plain,(
% 12.95/2.05    spl2_47 | ~spl2_22),
% 12.95/2.05    inference(avatar_split_clause,[],[f2786,f1773,f2828])).
% 12.95/2.05  fof(f2786,plain,(
% 12.95/2.05    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_22),
% 12.95/2.05    inference(superposition,[],[f76,f1774])).
% 12.95/2.05  fof(f2826,plain,(
% 12.95/2.05    spl2_45 | ~spl2_46 | ~spl2_22),
% 12.95/2.05    inference(avatar_split_clause,[],[f2785,f1773,f2823,f2819])).
% 12.95/2.05  fof(f2785,plain,(
% 12.95/2.05    ~r1_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_22),
% 12.95/2.05    inference(superposition,[],[f104,f1774])).
% 12.95/2.05  fof(f2817,plain,(
% 12.95/2.05    spl2_44 | ~spl2_22),
% 12.95/2.05    inference(avatar_split_clause,[],[f2783,f1773,f2814])).
% 12.95/2.05  fof(f2783,plain,(
% 12.95/2.05    k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_22),
% 12.95/2.05    inference(superposition,[],[f100,f1774])).
% 12.95/2.05  fof(f2812,plain,(
% 12.95/2.05    spl2_43 | ~spl2_13 | ~spl2_16 | ~spl2_21 | ~spl2_22),
% 12.95/2.05    inference(avatar_split_clause,[],[f2775,f1773,f1658,f939,f895,f2809])).
% 12.95/2.05  fof(f2809,plain,(
% 12.95/2.05    spl2_43 <=> r1_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 12.95/2.05  fof(f2775,plain,(
% 12.95/2.05    r1_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))) | (~spl2_13 | ~spl2_16 | ~spl2_21 | ~spl2_22)),
% 12.95/2.05    inference(superposition,[],[f2452,f1774])).
% 12.95/2.05  fof(f2807,plain,(
% 12.95/2.05    spl2_42 | ~spl2_13 | ~spl2_16 | ~spl2_21 | ~spl2_22),
% 12.95/2.05    inference(avatar_split_clause,[],[f2774,f1773,f1658,f939,f895,f2804])).
% 12.95/2.05  fof(f2804,plain,(
% 12.95/2.05    spl2_42 <=> r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),sK1),u1_struct_0(sK0))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 12.95/2.05  fof(f2774,plain,(
% 12.95/2.05    r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),sK1),u1_struct_0(sK0)) | (~spl2_13 | ~spl2_16 | ~spl2_21 | ~spl2_22)),
% 12.95/2.05    inference(superposition,[],[f2446,f1774])).
% 12.95/2.05  fof(f2802,plain,(
% 12.95/2.05    spl2_41 | ~spl2_16 | ~spl2_21 | ~spl2_22),
% 12.95/2.05    inference(avatar_split_clause,[],[f2772,f1773,f1658,f939,f2799])).
% 12.95/2.05  fof(f2772,plain,(
% 12.95/2.05    r1_tarski(k6_subset_1(k2_tops_1(sK0,sK1),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_16 | ~spl2_21 | ~spl2_22)),
% 12.95/2.05    inference(superposition,[],[f1697,f1774])).
% 12.95/2.05  fof(f2797,plain,(
% 12.95/2.05    spl2_40 | ~spl2_16 | ~spl2_21 | ~spl2_22),
% 12.95/2.05    inference(avatar_split_clause,[],[f2771,f1773,f1658,f939,f2794])).
% 12.95/2.05  fof(f2771,plain,(
% 12.95/2.05    r1_tarski(k2_tops_1(sK0,sK1),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))) | (~spl2_16 | ~spl2_21 | ~spl2_22)),
% 12.95/2.05    inference(superposition,[],[f1687,f1774])).
% 12.95/2.05  fof(f2792,plain,(
% 12.95/2.05    spl2_39 | ~spl2_16 | ~spl2_22),
% 12.95/2.05    inference(avatar_split_clause,[],[f2764,f1773,f939,f2789])).
% 12.95/2.05  fof(f2764,plain,(
% 12.95/2.05    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl2_16 | ~spl2_22)),
% 12.95/2.05    inference(superposition,[],[f1328,f1774])).
% 12.95/2.05  fof(f2763,plain,(
% 12.95/2.05    spl2_22 | ~spl2_2 | ~spl2_3),
% 12.95/2.05    inference(avatar_split_clause,[],[f2761,f120,f114,f1773])).
% 12.95/2.05  fof(f2761,plain,(
% 12.95/2.05    k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 12.95/2.05    inference(superposition,[],[f1769,f115])).
% 12.95/2.05  fof(f2762,plain,(
% 12.95/2.05    spl2_22 | ~spl2_2 | ~spl2_3),
% 12.95/2.05    inference(avatar_split_clause,[],[f2760,f120,f114,f1773])).
% 12.95/2.05  fof(f2760,plain,(
% 12.95/2.05    k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 12.95/2.05    inference(superposition,[],[f115,f1769])).
% 12.95/2.05  fof(f2759,plain,(
% 12.95/2.05    spl2_38 | ~spl2_3 | ~spl2_1 | ~spl2_4),
% 12.95/2.05    inference(avatar_split_clause,[],[f2754,f125,f110,f120,f2756])).
% 12.95/2.05  fof(f2754,plain,(
% 12.95/2.05    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1) | (~spl2_1 | ~spl2_4)),
% 12.95/2.05    inference(resolution,[],[f2753,f111])).
% 12.95/2.05  fof(f2753,plain,(
% 12.95/2.05    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | ~spl2_4),
% 12.95/2.05    inference(resolution,[],[f72,f127])).
% 12.95/2.05  fof(f72,plain,(
% 12.95/2.05    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 12.95/2.05    inference(cnf_transformation,[],[f38])).
% 12.95/2.05  fof(f2608,plain,(
% 12.95/2.05    spl2_37 | ~spl2_34),
% 12.95/2.05    inference(avatar_split_clause,[],[f2592,f2585,f2605])).
% 12.95/2.05  fof(f2605,plain,(
% 12.95/2.05    spl2_37 <=> sK1 = k3_subset_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),k3_subset_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),sK1))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 12.95/2.05  fof(f2585,plain,(
% 12.95/2.05    spl2_34 <=> m1_subset_1(sK1,k1_zfmisc_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 12.95/2.05  fof(f2592,plain,(
% 12.95/2.05    sK1 = k3_subset_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),k3_subset_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),sK1)) | ~spl2_34),
% 12.95/2.05    inference(resolution,[],[f2587,f86])).
% 12.95/2.05  fof(f2587,plain,(
% 12.95/2.05    m1_subset_1(sK1,k1_zfmisc_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))) | ~spl2_34),
% 12.95/2.05    inference(avatar_component_clause,[],[f2585])).
% 12.95/2.05  fof(f2603,plain,(
% 12.95/2.05    spl2_36 | ~spl2_34),
% 12.95/2.05    inference(avatar_split_clause,[],[f2591,f2585,f2600])).
% 12.95/2.05  fof(f2600,plain,(
% 12.95/2.05    spl2_36 <=> k3_subset_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),sK1) = k6_subset_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),sK1)),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 12.95/2.05  fof(f2591,plain,(
% 12.95/2.05    k3_subset_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),sK1) = k6_subset_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),sK1) | ~spl2_34),
% 12.95/2.05    inference(resolution,[],[f2587,f103])).
% 12.95/2.05  fof(f2598,plain,(
% 12.95/2.05    spl2_35 | ~spl2_34),
% 12.95/2.05    inference(avatar_split_clause,[],[f2589,f2585,f2595])).
% 12.95/2.05  fof(f2595,plain,(
% 12.95/2.05    spl2_35 <=> k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),sK1,k3_subset_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),sK1))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 12.95/2.05  fof(f2589,plain,(
% 12.95/2.05    k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),sK1,k3_subset_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))),sK1)) | ~spl2_34),
% 12.95/2.05    inference(resolution,[],[f2587,f134])).
% 12.95/2.05  fof(f2588,plain,(
% 12.95/2.05    spl2_34 | ~spl2_33),
% 12.95/2.05    inference(avatar_split_clause,[],[f2577,f2538,f2585])).
% 12.95/2.05  fof(f2538,plain,(
% 12.95/2.05    spl2_33 <=> sK1 = k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 12.95/2.05  fof(f2577,plain,(
% 12.95/2.05    m1_subset_1(sK1,k1_zfmisc_1(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))) | ~spl2_33),
% 12.95/2.05    inference(superposition,[],[f202,f2540])).
% 12.95/2.05  fof(f2540,plain,(
% 12.95/2.05    sK1 = k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))) | ~spl2_33),
% 12.95/2.05    inference(avatar_component_clause,[],[f2538])).
% 12.95/2.05  fof(f202,plain,(
% 12.95/2.05    ( ! [X0,X1] : (m1_subset_1(k1_setfam_1(k2_tarski(X1,X0)),k1_zfmisc_1(X0))) )),
% 12.95/2.05    inference(superposition,[],[f163,f77])).
% 12.95/2.05  fof(f2541,plain,(
% 12.95/2.05    spl2_33 | ~spl2_32),
% 12.95/2.05    inference(avatar_split_clause,[],[f2536,f2494,f2538])).
% 12.95/2.05  fof(f2494,plain,(
% 12.95/2.05    spl2_32 <=> k1_xboole_0 = k6_subset_1(sK1,k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 12.95/2.05  fof(f2536,plain,(
% 12.95/2.05    sK1 = k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))) | ~spl2_32),
% 12.95/2.05    inference(forward_demodulation,[],[f2517,f98])).
% 12.95/2.05  fof(f2517,plain,(
% 12.95/2.05    k6_subset_1(sK1,k1_xboole_0) = k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))) | ~spl2_32),
% 12.95/2.05    inference(superposition,[],[f100,f2496])).
% 12.95/2.05  fof(f2496,plain,(
% 12.95/2.05    k1_xboole_0 = k6_subset_1(sK1,k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))) | ~spl2_32),
% 12.95/2.05    inference(avatar_component_clause,[],[f2494])).
% 12.95/2.05  fof(f2499,plain,(
% 12.95/2.05    spl2_32 | ~spl2_13 | ~spl2_16 | ~spl2_21),
% 12.95/2.05    inference(avatar_split_clause,[],[f2492,f1658,f939,f895,f2494])).
% 12.95/2.05  fof(f2492,plain,(
% 12.95/2.05    k1_xboole_0 = k6_subset_1(sK1,k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))) | (~spl2_13 | ~spl2_16 | ~spl2_21)),
% 12.95/2.05    inference(resolution,[],[f2480,f104])).
% 12.95/2.05  fof(f2480,plain,(
% 12.95/2.05    ( ! [X1] : (r1_tarski(k6_subset_1(sK1,k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))),X1)) ) | (~spl2_13 | ~spl2_16 | ~spl2_21)),
% 12.95/2.05    inference(resolution,[],[f2476,f106])).
% 12.95/2.05  fof(f2497,plain,(
% 12.95/2.05    spl2_32 | ~spl2_13 | ~spl2_16 | ~spl2_21),
% 12.95/2.05    inference(avatar_split_clause,[],[f2490,f1658,f939,f895,f2494])).
% 12.95/2.05  fof(f2490,plain,(
% 12.95/2.05    k1_xboole_0 = k6_subset_1(sK1,k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))) | (~spl2_13 | ~spl2_16 | ~spl2_21)),
% 12.95/2.05    inference(resolution,[],[f2480,f168])).
% 12.95/2.05  fof(f2450,plain,(
% 12.95/2.05    ~spl2_3 | spl2_31 | ~spl2_16 | ~spl2_21),
% 12.95/2.05    inference(avatar_split_clause,[],[f2444,f1658,f939,f2448,f120])).
% 12.95/2.05  fof(f2448,plain,(
% 12.95/2.05    spl2_31 <=> ! [X0] : r1_tarski(k6_subset_1(k6_subset_1(sK1,X0),sK1),u1_struct_0(sK0))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 12.95/2.05  fof(f2444,plain,(
% 12.95/2.05    ( ! [X0] : (r1_tarski(k6_subset_1(k6_subset_1(sK1,X0),sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_16 | ~spl2_21)),
% 12.95/2.05    inference(resolution,[],[f1706,f158])).
% 12.95/2.05  fof(f158,plain,(
% 12.95/2.05    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X1,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 12.95/2.05    inference(resolution,[],[f84,f90])).
% 12.95/2.05  fof(f2113,plain,(
% 12.95/2.05    spl2_30 | ~spl2_25),
% 12.95/2.05    inference(avatar_split_clause,[],[f2093,f1859,f2110])).
% 12.95/2.05  fof(f2110,plain,(
% 12.95/2.05    spl2_30 <=> k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))) = k4_subset_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),sK1,k3_subset_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),sK1))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 12.95/2.05  fof(f1859,plain,(
% 12.95/2.05    spl2_25 <=> m1_subset_1(sK1,k1_zfmisc_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 12.95/2.05  fof(f2093,plain,(
% 12.95/2.05    k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))) = k4_subset_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),sK1,k3_subset_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),sK1)) | ~spl2_25),
% 12.95/2.05    inference(resolution,[],[f134,f1861])).
% 12.95/2.05  fof(f1861,plain,(
% 12.95/2.05    m1_subset_1(sK1,k1_zfmisc_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))) | ~spl2_25),
% 12.95/2.05    inference(avatar_component_clause,[],[f1859])).
% 12.95/2.05  fof(f2108,plain,(
% 12.95/2.05    spl2_29 | ~spl2_3),
% 12.95/2.05    inference(avatar_split_clause,[],[f2092,f120,f2105])).
% 12.95/2.05  fof(f2092,plain,(
% 12.95/2.05    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_3),
% 12.95/2.05    inference(resolution,[],[f134,f122])).
% 12.95/2.05  fof(f2101,plain,(
% 12.95/2.05    spl2_28 | ~spl2_7 | ~spl2_12),
% 12.95/2.05    inference(avatar_split_clause,[],[f2096,f890,f523,f2098])).
% 12.95/2.05  fof(f2096,plain,(
% 12.95/2.05    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) | (~spl2_7 | ~spl2_12)),
% 12.95/2.05    inference(forward_demodulation,[],[f2088,f525])).
% 12.95/2.05  fof(f2088,plain,(
% 12.95/2.05    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) | ~spl2_12),
% 12.95/2.05    inference(resolution,[],[f134,f892])).
% 12.95/2.05  fof(f1876,plain,(
% 12.95/2.05    spl2_27 | ~spl2_25),
% 12.95/2.05    inference(avatar_split_clause,[],[f1865,f1859,f1873])).
% 12.95/2.05  fof(f1873,plain,(
% 12.95/2.05    spl2_27 <=> sK1 = k3_subset_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),sK1))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 12.95/2.05  fof(f1865,plain,(
% 12.95/2.05    sK1 = k3_subset_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),sK1)) | ~spl2_25),
% 12.95/2.05    inference(resolution,[],[f1861,f86])).
% 12.95/2.05  fof(f1871,plain,(
% 12.95/2.05    spl2_26 | ~spl2_25),
% 12.95/2.05    inference(avatar_split_clause,[],[f1864,f1859,f1868])).
% 12.95/2.05  fof(f1868,plain,(
% 12.95/2.05    spl2_26 <=> k3_subset_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),sK1) = k6_subset_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),sK1)),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 12.95/2.05  fof(f1864,plain,(
% 12.95/2.05    k3_subset_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),sK1) = k6_subset_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))),sK1) | ~spl2_25),
% 12.95/2.05    inference(resolution,[],[f1861,f103])).
% 12.95/2.05  fof(f1862,plain,(
% 12.95/2.05    spl2_25 | ~spl2_24),
% 12.95/2.05    inference(avatar_split_clause,[],[f1852,f1823,f1859])).
% 12.95/2.05  fof(f1823,plain,(
% 12.95/2.05    spl2_24 <=> sK1 = k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 12.95/2.05  fof(f1852,plain,(
% 12.95/2.05    m1_subset_1(sK1,k1_zfmisc_1(k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))) | ~spl2_24),
% 12.95/2.05    inference(superposition,[],[f202,f1825])).
% 12.95/2.05  fof(f1825,plain,(
% 12.95/2.05    sK1 = k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))) | ~spl2_24),
% 12.95/2.05    inference(avatar_component_clause,[],[f1823])).
% 12.95/2.05  fof(f1826,plain,(
% 12.95/2.05    spl2_24 | ~spl2_23),
% 12.95/2.05    inference(avatar_split_clause,[],[f1821,f1785,f1823])).
% 12.95/2.05  fof(f1785,plain,(
% 12.95/2.05    spl2_23 <=> k1_xboole_0 = k6_subset_1(sK1,k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 12.95/2.05  fof(f1821,plain,(
% 12.95/2.05    sK1 = k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))) | ~spl2_23),
% 12.95/2.05    inference(forward_demodulation,[],[f1805,f98])).
% 12.95/2.05  fof(f1805,plain,(
% 12.95/2.05    k6_subset_1(sK1,k1_xboole_0) = k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))) | ~spl2_23),
% 12.95/2.05    inference(superposition,[],[f100,f1787])).
% 12.95/2.05  fof(f1787,plain,(
% 12.95/2.05    k1_xboole_0 = k6_subset_1(sK1,k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))) | ~spl2_23),
% 12.95/2.05    inference(avatar_component_clause,[],[f1785])).
% 12.95/2.05  fof(f1790,plain,(
% 12.95/2.05    spl2_23 | ~spl2_16 | ~spl2_21),
% 12.95/2.05    inference(avatar_split_clause,[],[f1783,f1658,f939,f1785])).
% 12.95/2.05  fof(f1783,plain,(
% 12.95/2.05    k1_xboole_0 = k6_subset_1(sK1,k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))) | (~spl2_16 | ~spl2_21)),
% 12.95/2.05    inference(resolution,[],[f1755,f104])).
% 12.95/2.05  fof(f1755,plain,(
% 12.95/2.05    ( ! [X0] : (r1_tarski(k6_subset_1(sK1,k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))),X0)) ) | (~spl2_16 | ~spl2_21)),
% 12.95/2.05    inference(resolution,[],[f1752,f106])).
% 12.95/2.05  fof(f1788,plain,(
% 12.95/2.05    spl2_23 | ~spl2_16 | ~spl2_21),
% 12.95/2.05    inference(avatar_split_clause,[],[f1781,f1658,f939,f1785])).
% 12.95/2.05  fof(f1781,plain,(
% 12.95/2.05    k1_xboole_0 = k6_subset_1(sK1,k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))) | (~spl2_16 | ~spl2_21)),
% 12.95/2.05    inference(resolution,[],[f1755,f168])).
% 12.95/2.05  fof(f1776,plain,(
% 12.95/2.05    ~spl2_22 | spl2_2 | ~spl2_3),
% 12.95/2.05    inference(avatar_split_clause,[],[f1771,f120,f114,f1773])).
% 12.95/2.05  fof(f1771,plain,(
% 12.95/2.05    k2_tops_1(sK0,sK1) != k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | (spl2_2 | ~spl2_3)),
% 12.95/2.05    inference(superposition,[],[f116,f1769])).
% 12.95/2.05  fof(f116,plain,(
% 12.95/2.05    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_2),
% 12.95/2.05    inference(avatar_component_clause,[],[f114])).
% 12.95/2.05  fof(f1661,plain,(
% 12.95/2.05    spl2_21 | ~spl2_8),
% 12.95/2.05    inference(avatar_split_clause,[],[f1655,f865,f1658])).
% 12.95/2.05  fof(f1655,plain,(
% 12.95/2.05    r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))) | ~spl2_8),
% 12.95/2.05    inference(resolution,[],[f1316,f135])).
% 12.95/2.05  fof(f1316,plain,(
% 12.95/2.05    ( ! [X9] : (~r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),X9) | r1_tarski(u1_struct_0(sK0),k3_tarski(k2_tarski(sK1,X9)))) ) | ~spl2_8),
% 12.95/2.05    inference(superposition,[],[f107,f867])).
% 12.95/2.05  fof(f997,plain,(
% 12.95/2.05    spl2_20 | ~spl2_15 | ~spl2_17),
% 12.95/2.05    inference(avatar_split_clause,[],[f992,f956,f913,f994])).
% 12.95/2.05  fof(f992,plain,(
% 12.95/2.05    sK1 = k5_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_15 | ~spl2_17)),
% 12.95/2.05    inference(forward_demodulation,[],[f987,f915])).
% 12.95/2.05  fof(f987,plain,(
% 12.95/2.05    k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_17),
% 12.95/2.05    inference(superposition,[],[f102,f958])).
% 12.95/2.05  fof(f968,plain,(
% 12.95/2.05    spl2_18 | ~spl2_19 | ~spl2_15),
% 12.95/2.05    inference(avatar_split_clause,[],[f951,f913,f965,f961])).
% 12.95/2.05  fof(f961,plain,(
% 12.95/2.05    spl2_18 <=> k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),sK1)),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 12.95/2.05  fof(f951,plain,(
% 12.95/2.05    ~r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),sK1) | k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),sK1) | ~spl2_15),
% 12.95/2.05    inference(superposition,[],[f104,f915])).
% 12.95/2.05  fof(f959,plain,(
% 12.95/2.05    spl2_17 | ~spl2_8 | ~spl2_15),
% 12.95/2.05    inference(avatar_split_clause,[],[f954,f913,f865,f956])).
% 12.95/2.05  fof(f954,plain,(
% 12.95/2.05    k3_subset_1(u1_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl2_8 | ~spl2_15)),
% 12.95/2.05    inference(forward_demodulation,[],[f949,f867])).
% 12.95/2.05  fof(f949,plain,(
% 12.95/2.05    k6_subset_1(u1_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) | ~spl2_15),
% 12.95/2.05    inference(superposition,[],[f100,f915])).
% 12.95/2.05  fof(f942,plain,(
% 12.95/2.05    spl2_16 | ~spl2_14),
% 12.95/2.05    inference(avatar_split_clause,[],[f937,f907,f939])).
% 12.95/2.05  fof(f937,plain,(
% 12.95/2.05    k1_xboole_0 = k6_subset_1(sK1,u1_struct_0(sK0)) | ~spl2_14),
% 12.95/2.05    inference(forward_demodulation,[],[f932,f287])).
% 12.95/2.05  fof(f932,plain,(
% 12.95/2.05    k6_subset_1(sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,sK1) | ~spl2_14),
% 12.95/2.05    inference(superposition,[],[f102,f909])).
% 12.95/2.05  fof(f916,plain,(
% 12.95/2.05    spl2_15 | ~spl2_9 | ~spl2_14),
% 12.95/2.05    inference(avatar_split_clause,[],[f911,f907,f876,f913])).
% 12.95/2.05  fof(f876,plain,(
% 12.95/2.05    spl2_9 <=> k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 12.95/2.05  fof(f911,plain,(
% 12.95/2.05    sK1 = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_9 | ~spl2_14)),
% 12.95/2.05    inference(backward_demodulation,[],[f878,f909])).
% 12.95/2.05  fof(f878,plain,(
% 12.95/2.05    k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) | ~spl2_9),
% 12.95/2.05    inference(avatar_component_clause,[],[f876])).
% 12.95/2.05  fof(f910,plain,(
% 12.95/2.05    spl2_14 | ~spl2_7 | ~spl2_9 | ~spl2_12),
% 12.95/2.05    inference(avatar_split_clause,[],[f905,f890,f876,f523,f907])).
% 12.95/2.05  fof(f905,plain,(
% 12.95/2.05    sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) | (~spl2_7 | ~spl2_9 | ~spl2_12)),
% 12.95/2.05    inference(forward_demodulation,[],[f904,f525])).
% 12.95/2.05  fof(f904,plain,(
% 12.95/2.05    k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) | (~spl2_9 | ~spl2_12)),
% 12.95/2.05    inference(forward_demodulation,[],[f901,f878])).
% 12.95/2.05  fof(f901,plain,(
% 12.95/2.05    k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_12),
% 12.95/2.05    inference(resolution,[],[f892,f103])).
% 12.95/2.05  fof(f898,plain,(
% 12.95/2.05    spl2_13 | ~spl2_8),
% 12.95/2.05    inference(avatar_split_clause,[],[f873,f865,f895])).
% 12.95/2.05  fof(f873,plain,(
% 12.95/2.05    r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl2_8),
% 12.95/2.05    inference(superposition,[],[f99,f867])).
% 12.95/2.05  fof(f893,plain,(
% 12.95/2.05    spl2_12 | ~spl2_8),
% 12.95/2.05    inference(avatar_split_clause,[],[f872,f865,f890])).
% 12.95/2.05  fof(f872,plain,(
% 12.95/2.05    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_8),
% 12.95/2.05    inference(superposition,[],[f76,f867])).
% 12.95/2.05  fof(f888,plain,(
% 12.95/2.05    spl2_10 | ~spl2_11 | ~spl2_8),
% 12.95/2.05    inference(avatar_split_clause,[],[f871,f865,f885,f881])).
% 12.95/2.05  fof(f881,plain,(
% 12.95/2.05    spl2_10 <=> k1_xboole_0 = sK1),
% 12.95/2.05    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 12.95/2.05  fof(f871,plain,(
% 12.95/2.05    ~r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) | k1_xboole_0 = sK1 | ~spl2_8),
% 12.95/2.05    inference(superposition,[],[f104,f867])).
% 12.95/2.05  fof(f879,plain,(
% 12.95/2.05    spl2_9 | ~spl2_8),
% 12.95/2.05    inference(avatar_split_clause,[],[f874,f865,f876])).
% 12.95/2.05  fof(f874,plain,(
% 12.95/2.05    k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) | ~spl2_8),
% 12.95/2.05    inference(forward_demodulation,[],[f869,f77])).
% 12.95/2.05  fof(f869,plain,(
% 12.95/2.05    k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)) = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_8),
% 12.95/2.05    inference(superposition,[],[f100,f867])).
% 12.95/2.05  fof(f868,plain,(
% 12.95/2.05    spl2_8 | ~spl2_3),
% 12.95/2.05    inference(avatar_split_clause,[],[f854,f120,f865])).
% 12.95/2.05  fof(f854,plain,(
% 12.95/2.05    k3_subset_1(u1_struct_0(sK0),sK1) = k6_subset_1(u1_struct_0(sK0),sK1) | ~spl2_3),
% 12.95/2.05    inference(resolution,[],[f103,f122])).
% 12.95/2.05  fof(f526,plain,(
% 12.95/2.05    spl2_7 | ~spl2_3),
% 12.95/2.05    inference(avatar_split_clause,[],[f521,f120,f523])).
% 12.95/2.05  fof(f521,plain,(
% 12.95/2.05    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_3),
% 12.95/2.05    inference(resolution,[],[f86,f122])).
% 12.95/2.05  fof(f148,plain,(
% 12.95/2.05    spl2_6 | ~spl2_3),
% 12.95/2.05    inference(avatar_split_clause,[],[f141,f120,f145])).
% 12.95/2.05  fof(f141,plain,(
% 12.95/2.05    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_3),
% 12.95/2.05    inference(resolution,[],[f90,f122])).
% 12.95/2.05  fof(f133,plain,(
% 12.95/2.05    spl2_5),
% 12.95/2.05    inference(avatar_split_clause,[],[f61,f130])).
% 12.95/2.05  fof(f61,plain,(
% 12.95/2.05    v2_pre_topc(sK0)),
% 12.95/2.05    inference(cnf_transformation,[],[f59])).
% 12.95/2.05  fof(f59,plain,(
% 12.95/2.05    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 12.95/2.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f56,f58,f57])).
% 12.95/2.05  fof(f57,plain,(
% 12.95/2.05    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 12.95/2.05    introduced(choice_axiom,[])).
% 12.95/2.05  fof(f58,plain,(
% 12.95/2.05    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 12.95/2.05    introduced(choice_axiom,[])).
% 12.95/2.05  fof(f56,plain,(
% 12.95/2.05    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 12.95/2.05    inference(flattening,[],[f55])).
% 12.95/2.05  fof(f55,plain,(
% 12.95/2.05    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 12.95/2.05    inference(nnf_transformation,[],[f33])).
% 12.95/2.05  fof(f33,plain,(
% 12.95/2.05    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 12.95/2.05    inference(flattening,[],[f32])).
% 12.95/2.05  fof(f32,plain,(
% 12.95/2.05    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 12.95/2.05    inference(ennf_transformation,[],[f31])).
% 12.95/2.05  fof(f31,negated_conjecture,(
% 12.95/2.05    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 12.95/2.05    inference(negated_conjecture,[],[f30])).
% 12.95/2.05  fof(f30,conjecture,(
% 12.95/2.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 12.95/2.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 12.95/2.05  fof(f128,plain,(
% 12.95/2.05    spl2_4),
% 12.95/2.05    inference(avatar_split_clause,[],[f62,f125])).
% 12.95/2.05  fof(f62,plain,(
% 12.95/2.05    l1_pre_topc(sK0)),
% 12.95/2.05    inference(cnf_transformation,[],[f59])).
% 12.95/2.05  fof(f123,plain,(
% 12.95/2.05    spl2_3),
% 12.95/2.05    inference(avatar_split_clause,[],[f63,f120])).
% 12.95/2.05  fof(f63,plain,(
% 12.95/2.05    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.95/2.05    inference(cnf_transformation,[],[f59])).
% 12.95/2.05  fof(f118,plain,(
% 12.95/2.05    spl2_1 | spl2_2),
% 12.95/2.05    inference(avatar_split_clause,[],[f64,f114,f110])).
% 12.95/2.05  fof(f64,plain,(
% 12.95/2.05    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 12.95/2.05    inference(cnf_transformation,[],[f59])).
% 12.95/2.05  fof(f117,plain,(
% 12.95/2.05    ~spl2_1 | ~spl2_2),
% 12.95/2.05    inference(avatar_split_clause,[],[f65,f114,f110])).
% 12.95/2.05  fof(f65,plain,(
% 12.95/2.05    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 12.95/2.05    inference(cnf_transformation,[],[f59])).
% 12.95/2.05  % SZS output end Proof for theBenchmark
% 12.95/2.05  % (7530)------------------------------
% 12.95/2.05  % (7530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.95/2.05  % (7530)Termination reason: Refutation
% 12.95/2.05  
% 12.95/2.05  % (7530)Memory used [KB]: 19573
% 12.95/2.05  % (7530)Time elapsed: 1.611 s
% 12.95/2.05  % (7530)------------------------------
% 12.95/2.05  % (7530)------------------------------
% 12.95/2.05  % (7519)Success in time 1.689 s
%------------------------------------------------------------------------------
