%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t66_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:54 EDT 2019

% Result     : Theorem 1.12s
% Output     : Refutation 1.12s
% Verified   : 
% Statistics : Number of formulae       : 2326 (7317 expanded)
%              Number of leaves         :  621 (3114 expanded)
%              Depth                    :   13
%              Number of atoms          : 5554 (17590 expanded)
%              Number of equality atoms :   42 ( 159 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7297,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f692,f699,f706,f713,f720,f727,f734,f741,f748,f755,f762,f769,f776,f783,f790,f797,f804,f811,f818,f825,f832,f839,f846,f853,f860,f867,f874,f881,f888,f895,f902,f909,f916,f923,f930,f937,f944,f951,f958,f965,f972,f979,f986,f993,f1004,f1011,f1019,f1033,f1048,f1055,f1062,f1079,f1088,f1095,f1102,f1123,f1131,f1146,f1154,f1199,f1209,f1223,f1233,f1243,f1253,f1272,f1282,f1300,f1310,f1326,f1333,f1341,f1349,f1357,f1365,f1373,f1381,f1389,f1397,f1421,f1428,f1436,f1444,f1452,f1460,f1492,f1500,f1507,f1515,f1538,f1554,f1570,f1588,f1599,f1610,f1626,f1633,f1658,f1665,f1673,f1702,f1740,f1812,f1822,f1843,f1853,f1874,f1884,f1905,f1915,f1936,f1946,f1957,f1965,f1984,f1992,f2012,f2020,f2040,f2048,f2096,f2150,f2168,f2178,f2200,f2207,f2209,f2216,f2223,f2236,f2246,f2260,f2270,f2280,f2296,f2306,f2321,f2331,f2341,f2357,f2365,f2378,f2388,f2403,f2413,f2423,f2439,f2447,f2460,f2479,f2489,f2511,f2525,f2534,f2541,f2548,f2561,f2579,f2587,f2611,f2620,f2633,f2643,f2655,f2669,f2687,f2695,f2719,f2729,f2750,f2783,f2817,f2824,f2831,f2850,f2859,f2898,f2934,f2941,f2948,f2961,f2991,f2999,f3007,f3015,f3024,f3032,f3040,f3048,f3062,f3070,f3078,f3086,f3094,f3102,f3110,f3118,f3126,f3134,f3142,f3151,f3159,f3167,f3175,f3183,f3202,f3206,f3221,f3230,f3238,f3246,f3254,f3262,f3270,f3278,f3297,f3301,f3316,f3324,f3368,f3386,f3388,f3395,f3397,f3404,f3406,f3416,f3423,f3424,f3457,f3466,f3473,f3483,f3514,f3524,f3534,f3544,f3560,f3570,f3581,f3589,f3617,f3625,f3646,f3653,f3661,f3671,f3679,f3687,f3695,f3703,f3711,f3719,f3727,f3735,f3743,f3751,f3760,f3768,f3776,f3784,f3792,f3813,f3820,f3828,f3839,f3847,f3855,f3863,f3871,f3879,f3887,f3895,f3904,f3912,f3920,f3928,f4032,f4042,f4064,f4072,f4147,f4155,f4216,f4226,f4237,f4245,f4286,f4293,f4305,f4317,f4325,f4343,f4354,f4365,f4373,f4391,f4401,f4412,f4420,f4439,f4447,f4467,f4475,f4495,f4503,f4522,f4532,f4553,f4565,f4586,f4596,f4617,f4627,f4648,f4658,f4679,f4691,f4712,f4722,f4743,f4753,f4774,f4784,f4805,f4817,f4838,f4848,f4869,f4879,f4901,f4909,f4929,f4945,f4964,f4971,f4983,f4990,f4997,f5004,f5068,f5070,f5085,f5093,f5101,f5109,f5117,f5134,f5153,f5173,f5181,f5189,f5197,f5205,f5213,f5221,f5252,f5273,f5282,f5302,f5311,f5331,f5340,f5364,f5373,f5400,f5418,f5428,f5446,f5456,f5467,f5475,f5496,f5506,f5527,f5537,f5558,f5568,f5589,f5599,f5623,f5633,f5654,f5664,f5685,f5695,f5716,f5726,f5740,f5748,f5766,f5776,f5797,f5807,f5828,f5838,f5862,f5872,f5893,f5903,f5924,f5934,f5945,f5953,f5974,f5984,f6005,f6015,f6036,f6046,f6067,f6077,f6101,f6110,f6130,f6139,f6159,f6168,f6188,f6197,f6223,f6232,f6252,f6261,f6281,f6290,f6310,f6319,f6345,f6354,f6363,f6371,f6379,f6387,f6395,f6403,f6417,f6425,f6433,f6441,f6449,f6457,f6465,f6473,f6484,f6492,f6500,f6508,f6516,f6524,f6532,f6549,f6557,f6565,f6573,f6581,f6589,f6597,f6605,f6616,f6624,f6632,f6640,f6648,f6667,f6676,f6696,f6705,f6728,f6737,f6757,f6766,f6786,f6795,f6815,f6824,f6838,f6846,f6854,f6862,f6870,f6878,f6886,f6900,f6908,f6916,f6924,f6932,f6940,f6948,f6956,f6970,f6978,f6986,f6994,f7002,f7010,f7018,f7026,f7034,f7042,f7050,f7058,f7066,f7074,f7082,f7090,f7098,f7106,f7114,f7122,f7130,f7138,f7146,f7154,f7162,f7188,f7216,f7242,f7268,f7293,f7296])).

fof(f7296,plain,
    ( spl44_1
    | ~ spl44_2
    | ~ spl44_4
    | ~ spl44_6
    | ~ spl44_1040
    | ~ spl44_1042 ),
    inference(avatar_contradiction_clause,[],[f7295])).

fof(f7295,plain,
    ( $false
    | ~ spl44_1
    | ~ spl44_2
    | ~ spl44_4
    | ~ spl44_6
    | ~ spl44_1040
    | ~ spl44_1042 ),
    inference(subsumption_resolution,[],[f7294,f7276])).

fof(f7276,plain,
    ( m1_subset_1(sK15(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl44_1
    | ~ spl44_2
    | ~ spl44_4
    | ~ spl44_6
    | ~ spl44_1040 ),
    inference(subsumption_resolution,[],[f7275,f691])).

fof(f691,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl44_1 ),
    inference(avatar_component_clause,[],[f690])).

fof(f690,plain,
    ( spl44_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1])])).

fof(f7275,plain,
    ( m1_subset_1(sK15(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl44_2
    | ~ spl44_4
    | ~ spl44_6
    | ~ spl44_1040 ),
    inference(subsumption_resolution,[],[f7274,f698])).

fof(f698,plain,
    ( v2_pre_topc(sK0)
    | ~ spl44_2 ),
    inference(avatar_component_clause,[],[f697])).

fof(f697,plain,
    ( spl44_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_2])])).

fof(f7274,plain,
    ( m1_subset_1(sK15(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl44_4
    | ~ spl44_6
    | ~ spl44_1040 ),
    inference(subsumption_resolution,[],[f7273,f705])).

fof(f705,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl44_4 ),
    inference(avatar_component_clause,[],[f704])).

fof(f704,plain,
    ( spl44_4
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_4])])).

fof(f7273,plain,
    ( m1_subset_1(sK15(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl44_6
    | ~ spl44_1040 ),
    inference(subsumption_resolution,[],[f7272,f712])).

fof(f712,plain,
    ( l1_pre_topc(sK0)
    | ~ spl44_6 ),
    inference(avatar_component_clause,[],[f711])).

fof(f711,plain,
    ( spl44_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_6])])).

fof(f7272,plain,
    ( m1_subset_1(sK15(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl44_1040 ),
    inference(subsumption_resolution,[],[f7269,f1036])).

fof(f1036,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(superposition,[],[f606,f1023])).

fof(f1023,plain,(
    ! [X1] : k1_xboole_0 = sK24(X1) ),
    inference(resolution,[],[f505,f607])).

fof(f607,plain,(
    ! [X0] : v1_xboole_0(sK24(X0)) ),
    inference(cnf_transformation,[],[f384])).

fof(f384,plain,(
    ! [X0] :
      ( v1_xboole_0(sK24(X0))
      & m1_subset_1(sK24(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK24])],[f105,f383])).

fof(f383,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK24(X0))
        & m1_subset_1(sK24(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f105,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',rc2_subset_1)).

fof(f505,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f226])).

fof(f226,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f137])).

fof(f137,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',t6_boole)).

fof(f606,plain,(
    ! [X0] : m1_subset_1(sK24(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f384])).

fof(f7269,plain,
    ( m1_subset_1(sK15(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl44_1040 ),
    inference(resolution,[],[f7267,f551])).

fof(f551,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | m1_subset_1(sK15(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f366])).

fof(f366,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(sK15(X0,X1),X0)
            & r1_tarski(X1,sK15(X0,X1))
            & m1_subset_1(sK15(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f266,f365])).

fof(f365,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_tex_2(sK15(X0,X1),X0)
        & r1_tarski(X1,sK15(X0,X1))
        & m1_subset_1(sK15(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f266,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f265])).

fof(f265,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f136])).

fof(f136,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( v3_tex_2(X2,X0)
                      & r1_tarski(X1,X2) ) )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',t65_tex_2)).

fof(f7267,plain,
    ( v2_tex_2(k1_xboole_0,sK0)
    | ~ spl44_1040 ),
    inference(avatar_component_clause,[],[f7266])).

fof(f7266,plain,
    ( spl44_1040
  <=> v2_tex_2(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1040])])).

fof(f7294,plain,
    ( ~ m1_subset_1(sK15(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl44_1042 ),
    inference(resolution,[],[f7292,f427])).

fof(f427,plain,(
    ! [X1] :
      ( ~ v3_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f336])).

fof(f336,plain,
    ( ! [X1] :
        ( ~ v3_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f154,f335])).

fof(f335,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ v3_tex_2(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ! [X1] :
          ( ~ v3_tex_2(X1,sK0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f154,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f153])).

fof(f153,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',t66_tex_2)).

fof(f7292,plain,
    ( v3_tex_2(sK15(sK0,k1_xboole_0),sK0)
    | ~ spl44_1042 ),
    inference(avatar_component_clause,[],[f7291])).

fof(f7291,plain,
    ( spl44_1042
  <=> v3_tex_2(sK15(sK0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1042])])).

fof(f7293,plain,
    ( spl44_1042
    | spl44_1
    | ~ spl44_2
    | ~ spl44_4
    | ~ spl44_6
    | ~ spl44_1040 ),
    inference(avatar_split_clause,[],[f7281,f7266,f711,f704,f697,f690,f7291])).

fof(f7281,plain,
    ( v3_tex_2(sK15(sK0,k1_xboole_0),sK0)
    | ~ spl44_1
    | ~ spl44_2
    | ~ spl44_4
    | ~ spl44_6
    | ~ spl44_1040 ),
    inference(subsumption_resolution,[],[f7280,f691])).

fof(f7280,plain,
    ( v3_tex_2(sK15(sK0,k1_xboole_0),sK0)
    | v2_struct_0(sK0)
    | ~ spl44_2
    | ~ spl44_4
    | ~ spl44_6
    | ~ spl44_1040 ),
    inference(subsumption_resolution,[],[f7279,f698])).

fof(f7279,plain,
    ( v3_tex_2(sK15(sK0,k1_xboole_0),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl44_4
    | ~ spl44_6
    | ~ spl44_1040 ),
    inference(subsumption_resolution,[],[f7278,f705])).

fof(f7278,plain,
    ( v3_tex_2(sK15(sK0,k1_xboole_0),sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl44_6
    | ~ spl44_1040 ),
    inference(subsumption_resolution,[],[f7277,f712])).

fof(f7277,plain,
    ( v3_tex_2(sK15(sK0,k1_xboole_0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl44_1040 ),
    inference(subsumption_resolution,[],[f7270,f1036])).

fof(f7270,plain,
    ( v3_tex_2(sK15(sK0,k1_xboole_0),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl44_1040 ),
    inference(resolution,[],[f7267,f553])).

fof(f553,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | v3_tex_2(sK15(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f366])).

fof(f7268,plain,
    ( spl44_1040
    | spl44_1
    | ~ spl44_2
    | ~ spl44_6
    | ~ spl44_8 ),
    inference(avatar_split_clause,[],[f7249,f718,f711,f697,f690,f7266])).

fof(f718,plain,
    ( spl44_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_8])])).

fof(f7249,plain,
    ( v2_tex_2(k1_xboole_0,sK0)
    | ~ spl44_1
    | ~ spl44_2
    | ~ spl44_6
    | ~ spl44_8 ),
    inference(subsumption_resolution,[],[f7244,f1036])).

fof(f7244,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(k1_xboole_0,sK0)
    | ~ spl44_1
    | ~ spl44_2
    | ~ spl44_6
    | ~ spl44_8 ),
    inference(resolution,[],[f6538,f719])).

fof(f719,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl44_8 ),
    inference(avatar_component_clause,[],[f718])).

fof(f6538,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | ~ spl44_1
    | ~ spl44_2
    | ~ spl44_6 ),
    inference(subsumption_resolution,[],[f6537,f691])).

fof(f6537,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X0)
        | v2_tex_2(X0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl44_2
    | ~ spl44_6 ),
    inference(subsumption_resolution,[],[f6534,f712])).

fof(f6534,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X0)
        | ~ l1_pre_topc(sK0)
        | v2_tex_2(X0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl44_2 ),
    inference(resolution,[],[f537,f698])).

fof(f537,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f256])).

fof(f256,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f255])).

fof(f255,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f132])).

fof(f132,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',t35_tex_2)).

fof(f7242,plain,
    ( spl44_1038
    | ~ spl44_2
    | ~ spl44_6
    | ~ spl44_8 ),
    inference(avatar_split_clause,[],[f7223,f718,f711,f697,f7240])).

fof(f7240,plain,
    ( spl44_1038
  <=> v4_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1038])])).

fof(f7223,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl44_2
    | ~ spl44_6
    | ~ spl44_8 ),
    inference(subsumption_resolution,[],[f7218,f1036])).

fof(f7218,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl44_2
    | ~ spl44_6
    | ~ spl44_8 ),
    inference(resolution,[],[f6407,f719])).

fof(f6407,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl44_2
    | ~ spl44_6 ),
    inference(subsumption_resolution,[],[f6404,f712])).

fof(f6404,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | v4_pre_topc(X0,sK0) )
    | ~ spl44_2 ),
    inference(resolution,[],[f575,f698])).

fof(f575,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f292])).

fof(f292,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f291])).

fof(f291,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',cc2_pre_topc)).

fof(f7216,plain,
    ( spl44_1036
    | ~ spl44_2
    | ~ spl44_6
    | ~ spl44_8 ),
    inference(avatar_split_clause,[],[f7197,f718,f711,f697,f7214])).

fof(f7214,plain,
    ( spl44_1036
  <=> v3_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1036])])).

fof(f7197,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ spl44_2
    | ~ spl44_6
    | ~ spl44_8 ),
    inference(subsumption_resolution,[],[f7192,f1036])).

fof(f7192,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k1_xboole_0,sK0)
    | ~ spl44_2
    | ~ spl44_6
    | ~ spl44_8 ),
    inference(resolution,[],[f6324,f719])).

fof(f6324,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,sK0) )
    | ~ spl44_2
    | ~ spl44_6 ),
    inference(subsumption_resolution,[],[f6321,f712])).

fof(f6321,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | v3_pre_topc(X0,sK0) )
    | ~ spl44_2 ),
    inference(resolution,[],[f574,f698])).

fof(f574,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f290])).

fof(f290,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f289])).

fof(f289,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',cc1_tops_1)).

fof(f7188,plain,
    ( spl44_1034
    | ~ spl44_2
    | ~ spl44_6
    | ~ spl44_8 ),
    inference(avatar_split_clause,[],[f7169,f718,f711,f697,f7186])).

fof(f7186,plain,
    ( spl44_1034
  <=> v3_tops_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1034])])).

fof(f7169,plain,
    ( v3_tops_1(k1_xboole_0,sK0)
    | ~ spl44_2
    | ~ spl44_6
    | ~ spl44_8 ),
    inference(subsumption_resolution,[],[f7164,f1036])).

fof(f7164,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_1(k1_xboole_0,sK0)
    | ~ spl44_2
    | ~ spl44_6
    | ~ spl44_8 ),
    inference(resolution,[],[f6202,f719])).

fof(f6202,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tops_1(X0,sK0) )
    | ~ spl44_2
    | ~ spl44_6 ),
    inference(subsumption_resolution,[],[f6199,f712])).

fof(f6199,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | v3_tops_1(X0,sK0) )
    | ~ spl44_2 ),
    inference(resolution,[],[f573,f698])).

fof(f573,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f288])).

fof(f288,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f287])).

fof(f287,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',cc3_tops_1)).

fof(f7162,plain,
    ( spl44_1032
    | ~ spl44_822 ),
    inference(avatar_split_clause,[],[f7155,f6065,f7160])).

fof(f7160,plain,
    ( spl44_1032
  <=> v1_relat_1(sK23(sK25(sK4(sK25(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1032])])).

fof(f6065,plain,
    ( spl44_822
  <=> v4_funct_1(sK25(sK4(sK25(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_822])])).

fof(f7155,plain,
    ( v1_relat_1(sK23(sK25(sK4(sK25(sK31)))))
    | ~ spl44_822 ),
    inference(resolution,[],[f6070,f605])).

fof(f605,plain,(
    ! [X0] : m1_subset_1(sK23(X0),X0) ),
    inference(cnf_transformation,[],[f382])).

fof(f382,plain,(
    ! [X0] : m1_subset_1(sK23(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23])],[f81,f381])).

fof(f381,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK23(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f81,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',existence_m1_subset_1)).

fof(f6070,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK4(sK25(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_822 ),
    inference(resolution,[],[f6066,f446])).

fof(f446,plain,(
    ! [X0,X1] :
      ( ~ v4_funct_1(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f165])).

fof(f165,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
          | ~ m1_subset_1(X1,X0) )
      | ~ v4_funct_1(X0) ) ),
    inference(ennf_transformation,[],[f67])).

fof(f67,axiom,(
    ! [X0] :
      ( v4_funct_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ( v1_funct_1(X1)
            & v1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',cc9_funct_1)).

fof(f6066,plain,
    ( v4_funct_1(sK25(sK4(sK25(sK31))))
    | ~ spl44_822 ),
    inference(avatar_component_clause,[],[f6065])).

fof(f7154,plain,
    ( spl44_1030
    | ~ spl44_822 ),
    inference(avatar_split_clause,[],[f7147,f6065,f7152])).

fof(f7152,plain,
    ( spl44_1030
  <=> v1_funct_1(sK23(sK25(sK4(sK25(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1030])])).

fof(f7147,plain,
    ( v1_funct_1(sK23(sK25(sK4(sK25(sK31)))))
    | ~ spl44_822 ),
    inference(resolution,[],[f6069,f605])).

fof(f6069,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK4(sK25(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_822 ),
    inference(resolution,[],[f6066,f447])).

fof(f447,plain,(
    ! [X0,X1] :
      ( ~ v4_funct_1(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f165])).

fof(f7146,plain,
    ( spl44_1028
    | ~ spl44_818 ),
    inference(avatar_split_clause,[],[f7139,f6034,f7144])).

fof(f7144,plain,
    ( spl44_1028
  <=> v1_relat_1(sK23(sK25(sK3(sK25(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1028])])).

fof(f6034,plain,
    ( spl44_818
  <=> v4_funct_1(sK25(sK3(sK25(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_818])])).

fof(f7139,plain,
    ( v1_relat_1(sK23(sK25(sK3(sK25(sK31)))))
    | ~ spl44_818 ),
    inference(resolution,[],[f6039,f605])).

fof(f6039,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK3(sK25(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_818 ),
    inference(resolution,[],[f6035,f446])).

fof(f6035,plain,
    ( v4_funct_1(sK25(sK3(sK25(sK31))))
    | ~ spl44_818 ),
    inference(avatar_component_clause,[],[f6034])).

fof(f7138,plain,
    ( spl44_1026
    | ~ spl44_818 ),
    inference(avatar_split_clause,[],[f7131,f6034,f7136])).

fof(f7136,plain,
    ( spl44_1026
  <=> v1_funct_1(sK23(sK25(sK3(sK25(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1026])])).

fof(f7131,plain,
    ( v1_funct_1(sK23(sK25(sK3(sK25(sK31)))))
    | ~ spl44_818 ),
    inference(resolution,[],[f6038,f605])).

fof(f6038,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK3(sK25(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_818 ),
    inference(resolution,[],[f6035,f447])).

fof(f7130,plain,
    ( spl44_1024
    | ~ spl44_814 ),
    inference(avatar_split_clause,[],[f7123,f6003,f7128])).

fof(f7128,plain,
    ( spl44_1024
  <=> v1_relat_1(sK23(sK25(sK2(sK25(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1024])])).

fof(f6003,plain,
    ( spl44_814
  <=> v4_funct_1(sK25(sK2(sK25(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_814])])).

fof(f7123,plain,
    ( v1_relat_1(sK23(sK25(sK2(sK25(sK31)))))
    | ~ spl44_814 ),
    inference(resolution,[],[f6008,f605])).

fof(f6008,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK2(sK25(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_814 ),
    inference(resolution,[],[f6004,f446])).

fof(f6004,plain,
    ( v4_funct_1(sK25(sK2(sK25(sK31))))
    | ~ spl44_814 ),
    inference(avatar_component_clause,[],[f6003])).

fof(f7122,plain,
    ( spl44_1022
    | ~ spl44_814 ),
    inference(avatar_split_clause,[],[f7115,f6003,f7120])).

fof(f7120,plain,
    ( spl44_1022
  <=> v1_funct_1(sK23(sK25(sK2(sK25(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1022])])).

fof(f7115,plain,
    ( v1_funct_1(sK23(sK25(sK2(sK25(sK31)))))
    | ~ spl44_814 ),
    inference(resolution,[],[f6007,f605])).

fof(f6007,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK2(sK25(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_814 ),
    inference(resolution,[],[f6004,f447])).

fof(f7114,plain,
    ( spl44_1020
    | ~ spl44_810 ),
    inference(avatar_split_clause,[],[f7107,f5972,f7112])).

fof(f7112,plain,
    ( spl44_1020
  <=> v1_relat_1(sK23(sK25(sK1(sK25(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1020])])).

fof(f5972,plain,
    ( spl44_810
  <=> v4_funct_1(sK25(sK1(sK25(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_810])])).

fof(f7107,plain,
    ( v1_relat_1(sK23(sK25(sK1(sK25(sK31)))))
    | ~ spl44_810 ),
    inference(resolution,[],[f5977,f605])).

fof(f5977,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK1(sK25(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_810 ),
    inference(resolution,[],[f5973,f446])).

fof(f5973,plain,
    ( v4_funct_1(sK25(sK1(sK25(sK31))))
    | ~ spl44_810 ),
    inference(avatar_component_clause,[],[f5972])).

fof(f7106,plain,
    ( spl44_1018
    | ~ spl44_810 ),
    inference(avatar_split_clause,[],[f7099,f5972,f7104])).

fof(f7104,plain,
    ( spl44_1018
  <=> v1_funct_1(sK23(sK25(sK1(sK25(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1018])])).

fof(f7099,plain,
    ( v1_funct_1(sK23(sK25(sK1(sK25(sK31)))))
    | ~ spl44_810 ),
    inference(resolution,[],[f5976,f605])).

fof(f5976,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK1(sK25(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_810 ),
    inference(resolution,[],[f5973,f447])).

fof(f7098,plain,
    ( spl44_1016
    | ~ spl44_802 ),
    inference(avatar_split_clause,[],[f7091,f5922,f7096])).

fof(f7096,plain,
    ( spl44_1016
  <=> v1_relat_1(sK23(sK25(sK17(sK17(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1016])])).

fof(f5922,plain,
    ( spl44_802
  <=> v4_funct_1(sK25(sK17(sK17(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_802])])).

fof(f7091,plain,
    ( v1_relat_1(sK23(sK25(sK17(sK17(sK31)))))
    | ~ spl44_802 ),
    inference(resolution,[],[f5927,f605])).

fof(f5927,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK17(sK17(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_802 ),
    inference(resolution,[],[f5923,f446])).

fof(f5923,plain,
    ( v4_funct_1(sK25(sK17(sK17(sK31))))
    | ~ spl44_802 ),
    inference(avatar_component_clause,[],[f5922])).

fof(f7090,plain,
    ( spl44_1014
    | ~ spl44_802 ),
    inference(avatar_split_clause,[],[f7083,f5922,f7088])).

fof(f7088,plain,
    ( spl44_1014
  <=> v1_funct_1(sK23(sK25(sK17(sK17(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1014])])).

fof(f7083,plain,
    ( v1_funct_1(sK23(sK25(sK17(sK17(sK31)))))
    | ~ spl44_802 ),
    inference(resolution,[],[f5926,f605])).

fof(f5926,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK17(sK17(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_802 ),
    inference(resolution,[],[f5923,f447])).

fof(f7082,plain,
    ( spl44_1012
    | ~ spl44_798 ),
    inference(avatar_split_clause,[],[f7075,f5891,f7080])).

fof(f7080,plain,
    ( spl44_1012
  <=> v1_relat_1(sK23(sK25(sK16(sK17(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1012])])).

fof(f5891,plain,
    ( spl44_798
  <=> v4_funct_1(sK25(sK16(sK17(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_798])])).

fof(f7075,plain,
    ( v1_relat_1(sK23(sK25(sK16(sK17(sK31)))))
    | ~ spl44_798 ),
    inference(resolution,[],[f5896,f605])).

fof(f5896,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK16(sK17(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_798 ),
    inference(resolution,[],[f5892,f446])).

fof(f5892,plain,
    ( v4_funct_1(sK25(sK16(sK17(sK31))))
    | ~ spl44_798 ),
    inference(avatar_component_clause,[],[f5891])).

fof(f7074,plain,
    ( spl44_1010
    | ~ spl44_798 ),
    inference(avatar_split_clause,[],[f7067,f5891,f7072])).

fof(f7072,plain,
    ( spl44_1010
  <=> v1_funct_1(sK23(sK25(sK16(sK17(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1010])])).

fof(f7067,plain,
    ( v1_funct_1(sK23(sK25(sK16(sK17(sK31)))))
    | ~ spl44_798 ),
    inference(resolution,[],[f5895,f605])).

fof(f5895,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK16(sK17(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_798 ),
    inference(resolution,[],[f5892,f447])).

fof(f7066,plain,
    ( spl44_1008
    | ~ spl44_794 ),
    inference(avatar_split_clause,[],[f7059,f5860,f7064])).

fof(f7064,plain,
    ( spl44_1008
  <=> v1_relat_1(sK23(sK25(sK4(sK17(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1008])])).

fof(f5860,plain,
    ( spl44_794
  <=> v4_funct_1(sK25(sK4(sK17(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_794])])).

fof(f7059,plain,
    ( v1_relat_1(sK23(sK25(sK4(sK17(sK31)))))
    | ~ spl44_794 ),
    inference(resolution,[],[f5865,f605])).

fof(f5865,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK4(sK17(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_794 ),
    inference(resolution,[],[f5861,f446])).

fof(f5861,plain,
    ( v4_funct_1(sK25(sK4(sK17(sK31))))
    | ~ spl44_794 ),
    inference(avatar_component_clause,[],[f5860])).

fof(f7058,plain,
    ( spl44_1006
    | ~ spl44_794 ),
    inference(avatar_split_clause,[],[f7051,f5860,f7056])).

fof(f7056,plain,
    ( spl44_1006
  <=> v1_funct_1(sK23(sK25(sK4(sK17(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1006])])).

fof(f7051,plain,
    ( v1_funct_1(sK23(sK25(sK4(sK17(sK31)))))
    | ~ spl44_794 ),
    inference(resolution,[],[f5864,f605])).

fof(f5864,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK4(sK17(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_794 ),
    inference(resolution,[],[f5861,f447])).

fof(f7050,plain,
    ( spl44_1004
    | ~ spl44_790 ),
    inference(avatar_split_clause,[],[f7043,f5826,f7048])).

fof(f7048,plain,
    ( spl44_1004
  <=> v1_relat_1(sK23(sK25(sK3(sK17(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1004])])).

fof(f5826,plain,
    ( spl44_790
  <=> v4_funct_1(sK25(sK3(sK17(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_790])])).

fof(f7043,plain,
    ( v1_relat_1(sK23(sK25(sK3(sK17(sK31)))))
    | ~ spl44_790 ),
    inference(resolution,[],[f5831,f605])).

fof(f5831,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK3(sK17(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_790 ),
    inference(resolution,[],[f5827,f446])).

fof(f5827,plain,
    ( v4_funct_1(sK25(sK3(sK17(sK31))))
    | ~ spl44_790 ),
    inference(avatar_component_clause,[],[f5826])).

fof(f7042,plain,
    ( spl44_1002
    | ~ spl44_790 ),
    inference(avatar_split_clause,[],[f7035,f5826,f7040])).

fof(f7040,plain,
    ( spl44_1002
  <=> v1_funct_1(sK23(sK25(sK3(sK17(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1002])])).

fof(f7035,plain,
    ( v1_funct_1(sK23(sK25(sK3(sK17(sK31)))))
    | ~ spl44_790 ),
    inference(resolution,[],[f5830,f605])).

fof(f5830,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK3(sK17(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_790 ),
    inference(resolution,[],[f5827,f447])).

fof(f7034,plain,
    ( spl44_1000
    | ~ spl44_786 ),
    inference(avatar_split_clause,[],[f7027,f5795,f7032])).

fof(f7032,plain,
    ( spl44_1000
  <=> v1_relat_1(sK23(sK25(sK2(sK17(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1000])])).

fof(f5795,plain,
    ( spl44_786
  <=> v4_funct_1(sK25(sK2(sK17(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_786])])).

fof(f7027,plain,
    ( v1_relat_1(sK23(sK25(sK2(sK17(sK31)))))
    | ~ spl44_786 ),
    inference(resolution,[],[f5800,f605])).

fof(f5800,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK2(sK17(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_786 ),
    inference(resolution,[],[f5796,f446])).

fof(f5796,plain,
    ( v4_funct_1(sK25(sK2(sK17(sK31))))
    | ~ spl44_786 ),
    inference(avatar_component_clause,[],[f5795])).

fof(f7026,plain,
    ( spl44_998
    | ~ spl44_786 ),
    inference(avatar_split_clause,[],[f7019,f5795,f7024])).

fof(f7024,plain,
    ( spl44_998
  <=> v1_funct_1(sK23(sK25(sK2(sK17(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_998])])).

fof(f7019,plain,
    ( v1_funct_1(sK23(sK25(sK2(sK17(sK31)))))
    | ~ spl44_786 ),
    inference(resolution,[],[f5799,f605])).

fof(f5799,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK2(sK17(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_786 ),
    inference(resolution,[],[f5796,f447])).

fof(f7018,plain,
    ( spl44_996
    | ~ spl44_782 ),
    inference(avatar_split_clause,[],[f7011,f5764,f7016])).

fof(f7016,plain,
    ( spl44_996
  <=> v1_relat_1(sK23(sK25(sK1(sK17(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_996])])).

fof(f5764,plain,
    ( spl44_782
  <=> v4_funct_1(sK25(sK1(sK17(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_782])])).

fof(f7011,plain,
    ( v1_relat_1(sK23(sK25(sK1(sK17(sK31)))))
    | ~ spl44_782 ),
    inference(resolution,[],[f5769,f605])).

fof(f5769,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK1(sK17(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_782 ),
    inference(resolution,[],[f5765,f446])).

fof(f5765,plain,
    ( v4_funct_1(sK25(sK1(sK17(sK31))))
    | ~ spl44_782 ),
    inference(avatar_component_clause,[],[f5764])).

fof(f7010,plain,
    ( spl44_994
    | ~ spl44_782 ),
    inference(avatar_split_clause,[],[f7003,f5764,f7008])).

fof(f7008,plain,
    ( spl44_994
  <=> v1_funct_1(sK23(sK25(sK1(sK17(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_994])])).

fof(f7003,plain,
    ( v1_funct_1(sK23(sK25(sK1(sK17(sK31)))))
    | ~ spl44_782 ),
    inference(resolution,[],[f5768,f605])).

fof(f5768,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK1(sK17(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_782 ),
    inference(resolution,[],[f5765,f447])).

fof(f7002,plain,
    ( spl44_992
    | ~ spl44_774 ),
    inference(avatar_split_clause,[],[f6995,f5714,f7000])).

fof(f7000,plain,
    ( spl44_992
  <=> v1_relat_1(sK23(sK25(sK4(sK4(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_992])])).

fof(f5714,plain,
    ( spl44_774
  <=> v4_funct_1(sK25(sK4(sK4(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_774])])).

fof(f6995,plain,
    ( v1_relat_1(sK23(sK25(sK4(sK4(sK31)))))
    | ~ spl44_774 ),
    inference(resolution,[],[f5719,f605])).

fof(f5719,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK4(sK4(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_774 ),
    inference(resolution,[],[f5715,f446])).

fof(f5715,plain,
    ( v4_funct_1(sK25(sK4(sK4(sK31))))
    | ~ spl44_774 ),
    inference(avatar_component_clause,[],[f5714])).

fof(f6994,plain,
    ( spl44_990
    | ~ spl44_774 ),
    inference(avatar_split_clause,[],[f6987,f5714,f6992])).

fof(f6992,plain,
    ( spl44_990
  <=> v1_funct_1(sK23(sK25(sK4(sK4(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_990])])).

fof(f6987,plain,
    ( v1_funct_1(sK23(sK25(sK4(sK4(sK31)))))
    | ~ spl44_774 ),
    inference(resolution,[],[f5718,f605])).

fof(f5718,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK4(sK4(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_774 ),
    inference(resolution,[],[f5715,f447])).

fof(f6986,plain,
    ( spl44_988
    | ~ spl44_770 ),
    inference(avatar_split_clause,[],[f6979,f5683,f6984])).

fof(f6984,plain,
    ( spl44_988
  <=> v1_relat_1(sK23(sK25(sK3(sK4(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_988])])).

fof(f5683,plain,
    ( spl44_770
  <=> v4_funct_1(sK25(sK3(sK4(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_770])])).

fof(f6979,plain,
    ( v1_relat_1(sK23(sK25(sK3(sK4(sK31)))))
    | ~ spl44_770 ),
    inference(resolution,[],[f5688,f605])).

fof(f5688,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK3(sK4(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_770 ),
    inference(resolution,[],[f5684,f446])).

fof(f5684,plain,
    ( v4_funct_1(sK25(sK3(sK4(sK31))))
    | ~ spl44_770 ),
    inference(avatar_component_clause,[],[f5683])).

fof(f6978,plain,
    ( spl44_986
    | ~ spl44_770 ),
    inference(avatar_split_clause,[],[f6971,f5683,f6976])).

fof(f6976,plain,
    ( spl44_986
  <=> v1_funct_1(sK23(sK25(sK3(sK4(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_986])])).

fof(f6971,plain,
    ( v1_funct_1(sK23(sK25(sK3(sK4(sK31)))))
    | ~ spl44_770 ),
    inference(resolution,[],[f5687,f605])).

fof(f5687,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK3(sK4(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_770 ),
    inference(resolution,[],[f5684,f447])).

fof(f6970,plain,
    ( spl44_984
    | ~ spl44_766 ),
    inference(avatar_split_clause,[],[f6957,f5652,f6968])).

fof(f6968,plain,
    ( spl44_984
  <=> v1_relat_1(sK23(sK25(sK2(sK4(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_984])])).

fof(f5652,plain,
    ( spl44_766
  <=> v4_funct_1(sK25(sK2(sK4(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_766])])).

fof(f6957,plain,
    ( v1_relat_1(sK23(sK25(sK2(sK4(sK31)))))
    | ~ spl44_766 ),
    inference(resolution,[],[f5657,f605])).

fof(f5657,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK2(sK4(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_766 ),
    inference(resolution,[],[f5653,f446])).

fof(f5653,plain,
    ( v4_funct_1(sK25(sK2(sK4(sK31))))
    | ~ spl44_766 ),
    inference(avatar_component_clause,[],[f5652])).

fof(f6956,plain,
    ( spl44_982
    | ~ spl44_766 ),
    inference(avatar_split_clause,[],[f6949,f5652,f6954])).

fof(f6954,plain,
    ( spl44_982
  <=> v1_funct_1(sK23(sK25(sK2(sK4(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_982])])).

fof(f6949,plain,
    ( v1_funct_1(sK23(sK25(sK2(sK4(sK31)))))
    | ~ spl44_766 ),
    inference(resolution,[],[f5656,f605])).

fof(f5656,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK2(sK4(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_766 ),
    inference(resolution,[],[f5653,f447])).

fof(f6948,plain,
    ( spl44_980
    | ~ spl44_762 ),
    inference(avatar_split_clause,[],[f6941,f5621,f6946])).

fof(f6946,plain,
    ( spl44_980
  <=> v1_relat_1(sK23(sK25(sK1(sK4(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_980])])).

fof(f5621,plain,
    ( spl44_762
  <=> v4_funct_1(sK25(sK1(sK4(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_762])])).

fof(f6941,plain,
    ( v1_relat_1(sK23(sK25(sK1(sK4(sK31)))))
    | ~ spl44_762 ),
    inference(resolution,[],[f5626,f605])).

fof(f5626,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK1(sK4(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_762 ),
    inference(resolution,[],[f5622,f446])).

fof(f5622,plain,
    ( v4_funct_1(sK25(sK1(sK4(sK31))))
    | ~ spl44_762 ),
    inference(avatar_component_clause,[],[f5621])).

fof(f6940,plain,
    ( spl44_978
    | ~ spl44_762 ),
    inference(avatar_split_clause,[],[f6933,f5621,f6938])).

fof(f6938,plain,
    ( spl44_978
  <=> v1_funct_1(sK23(sK25(sK1(sK4(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_978])])).

fof(f6933,plain,
    ( v1_funct_1(sK23(sK25(sK1(sK4(sK31)))))
    | ~ spl44_762 ),
    inference(resolution,[],[f5625,f605])).

fof(f5625,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK1(sK4(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_762 ),
    inference(resolution,[],[f5622,f447])).

fof(f6932,plain,
    ( spl44_976
    | ~ spl44_758 ),
    inference(avatar_split_clause,[],[f6925,f5587,f6930])).

fof(f6930,plain,
    ( spl44_976
  <=> v1_relat_1(sK23(sK25(sK17(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_976])])).

fof(f5587,plain,
    ( spl44_758
  <=> v4_funct_1(sK25(sK17(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_758])])).

fof(f6925,plain,
    ( v1_relat_1(sK23(sK25(sK17(sK3(sK31)))))
    | ~ spl44_758 ),
    inference(resolution,[],[f5592,f605])).

fof(f5592,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK17(sK3(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_758 ),
    inference(resolution,[],[f5588,f446])).

fof(f5588,plain,
    ( v4_funct_1(sK25(sK17(sK3(sK31))))
    | ~ spl44_758 ),
    inference(avatar_component_clause,[],[f5587])).

fof(f6924,plain,
    ( spl44_974
    | ~ spl44_758 ),
    inference(avatar_split_clause,[],[f6917,f5587,f6922])).

fof(f6922,plain,
    ( spl44_974
  <=> v1_funct_1(sK23(sK25(sK17(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_974])])).

fof(f6917,plain,
    ( v1_funct_1(sK23(sK25(sK17(sK3(sK31)))))
    | ~ spl44_758 ),
    inference(resolution,[],[f5591,f605])).

fof(f5591,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK17(sK3(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_758 ),
    inference(resolution,[],[f5588,f447])).

fof(f6916,plain,
    ( spl44_972
    | ~ spl44_754 ),
    inference(avatar_split_clause,[],[f6909,f5556,f6914])).

fof(f6914,plain,
    ( spl44_972
  <=> v1_relat_1(sK23(sK25(sK16(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_972])])).

fof(f5556,plain,
    ( spl44_754
  <=> v4_funct_1(sK25(sK16(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_754])])).

fof(f6909,plain,
    ( v1_relat_1(sK23(sK25(sK16(sK3(sK31)))))
    | ~ spl44_754 ),
    inference(resolution,[],[f5561,f605])).

fof(f5561,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK16(sK3(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_754 ),
    inference(resolution,[],[f5557,f446])).

fof(f5557,plain,
    ( v4_funct_1(sK25(sK16(sK3(sK31))))
    | ~ spl44_754 ),
    inference(avatar_component_clause,[],[f5556])).

fof(f6908,plain,
    ( spl44_970
    | ~ spl44_754 ),
    inference(avatar_split_clause,[],[f6901,f5556,f6906])).

fof(f6906,plain,
    ( spl44_970
  <=> v1_funct_1(sK23(sK25(sK16(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_970])])).

fof(f6901,plain,
    ( v1_funct_1(sK23(sK25(sK16(sK3(sK31)))))
    | ~ spl44_754 ),
    inference(resolution,[],[f5560,f605])).

fof(f5560,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK16(sK3(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_754 ),
    inference(resolution,[],[f5557,f447])).

fof(f6900,plain,
    ( spl44_968
    | ~ spl44_750 ),
    inference(avatar_split_clause,[],[f6887,f5525,f6898])).

fof(f6898,plain,
    ( spl44_968
  <=> v1_relat_1(sK23(sK25(sK17(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_968])])).

fof(f5525,plain,
    ( spl44_750
  <=> v4_funct_1(sK25(sK17(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_750])])).

fof(f6887,plain,
    ( v1_relat_1(sK23(sK25(sK17(sK2(sK31)))))
    | ~ spl44_750 ),
    inference(resolution,[],[f5530,f605])).

fof(f5530,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK17(sK2(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_750 ),
    inference(resolution,[],[f5526,f446])).

fof(f5526,plain,
    ( v4_funct_1(sK25(sK17(sK2(sK31))))
    | ~ spl44_750 ),
    inference(avatar_component_clause,[],[f5525])).

fof(f6886,plain,
    ( spl44_966
    | ~ spl44_750 ),
    inference(avatar_split_clause,[],[f6879,f5525,f6884])).

fof(f6884,plain,
    ( spl44_966
  <=> v1_funct_1(sK23(sK25(sK17(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_966])])).

fof(f6879,plain,
    ( v1_funct_1(sK23(sK25(sK17(sK2(sK31)))))
    | ~ spl44_750 ),
    inference(resolution,[],[f5529,f605])).

fof(f5529,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK17(sK2(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_750 ),
    inference(resolution,[],[f5526,f447])).

fof(f6878,plain,
    ( spl44_964
    | ~ spl44_746 ),
    inference(avatar_split_clause,[],[f6871,f5494,f6876])).

fof(f6876,plain,
    ( spl44_964
  <=> v1_relat_1(sK23(sK25(sK16(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_964])])).

fof(f5494,plain,
    ( spl44_746
  <=> v4_funct_1(sK25(sK16(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_746])])).

fof(f6871,plain,
    ( v1_relat_1(sK23(sK25(sK16(sK2(sK31)))))
    | ~ spl44_746 ),
    inference(resolution,[],[f5499,f605])).

fof(f5499,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK16(sK2(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_746 ),
    inference(resolution,[],[f5495,f446])).

fof(f5495,plain,
    ( v4_funct_1(sK25(sK16(sK2(sK31))))
    | ~ spl44_746 ),
    inference(avatar_component_clause,[],[f5494])).

fof(f6870,plain,
    ( spl44_962
    | ~ spl44_746 ),
    inference(avatar_split_clause,[],[f6863,f5494,f6868])).

fof(f6868,plain,
    ( spl44_962
  <=> v1_funct_1(sK23(sK25(sK16(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_962])])).

fof(f6863,plain,
    ( v1_funct_1(sK23(sK25(sK16(sK2(sK31)))))
    | ~ spl44_746 ),
    inference(resolution,[],[f5498,f605])).

fof(f5498,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK16(sK2(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_746 ),
    inference(resolution,[],[f5495,f447])).

fof(f6862,plain,
    ( spl44_960
    | ~ spl44_738 ),
    inference(avatar_split_clause,[],[f6855,f5444,f6860])).

fof(f6860,plain,
    ( spl44_960
  <=> v1_relat_1(sK23(sK25(sK25(sK17(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_960])])).

fof(f5444,plain,
    ( spl44_738
  <=> v4_funct_1(sK25(sK25(sK17(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_738])])).

fof(f6855,plain,
    ( v1_relat_1(sK23(sK25(sK25(sK17(sK31)))))
    | ~ spl44_738 ),
    inference(resolution,[],[f5449,f605])).

fof(f5449,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK25(sK17(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_738 ),
    inference(resolution,[],[f5445,f446])).

fof(f5445,plain,
    ( v4_funct_1(sK25(sK25(sK17(sK31))))
    | ~ spl44_738 ),
    inference(avatar_component_clause,[],[f5444])).

fof(f6854,plain,
    ( spl44_958
    | ~ spl44_738 ),
    inference(avatar_split_clause,[],[f6847,f5444,f6852])).

fof(f6852,plain,
    ( spl44_958
  <=> v1_funct_1(sK23(sK25(sK25(sK17(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_958])])).

fof(f6847,plain,
    ( v1_funct_1(sK23(sK25(sK25(sK17(sK31)))))
    | ~ spl44_738 ),
    inference(resolution,[],[f5448,f605])).

fof(f5448,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK25(sK17(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_738 ),
    inference(resolution,[],[f5445,f447])).

fof(f6846,plain,
    ( spl44_956
    | ~ spl44_734 ),
    inference(avatar_split_clause,[],[f6839,f5416,f6844])).

fof(f6844,plain,
    ( spl44_956
  <=> v1_relat_1(sK23(sK25(sK25(sK16(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_956])])).

fof(f5416,plain,
    ( spl44_734
  <=> v4_funct_1(sK25(sK25(sK16(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_734])])).

fof(f6839,plain,
    ( v1_relat_1(sK23(sK25(sK25(sK16(sK31)))))
    | ~ spl44_734 ),
    inference(resolution,[],[f5421,f605])).

fof(f5421,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK25(sK16(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_734 ),
    inference(resolution,[],[f5417,f446])).

fof(f5417,plain,
    ( v4_funct_1(sK25(sK25(sK16(sK31))))
    | ~ spl44_734 ),
    inference(avatar_component_clause,[],[f5416])).

fof(f6838,plain,
    ( spl44_954
    | ~ spl44_734 ),
    inference(avatar_split_clause,[],[f6831,f5416,f6836])).

fof(f6836,plain,
    ( spl44_954
  <=> v1_funct_1(sK23(sK25(sK25(sK16(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_954])])).

fof(f6831,plain,
    ( v1_funct_1(sK23(sK25(sK25(sK16(sK31)))))
    | ~ spl44_734 ),
    inference(resolution,[],[f5420,f605])).

fof(f5420,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK25(sK16(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_734 ),
    inference(resolution,[],[f5417,f447])).

fof(f6824,plain,
    ( spl44_952
    | ~ spl44_712 ),
    inference(avatar_split_clause,[],[f6805,f5219,f6822])).

fof(f6822,plain,
    ( spl44_952
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK4(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_952])])).

fof(f5219,plain,
    ( spl44_712
  <=> v1_zfmisc_1(sK4(sK3(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_712])])).

fof(f6805,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK4(sK3(sK31)))))
    | ~ spl44_712 ),
    inference(resolution,[],[f5226,f605])).

fof(f5226,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK3(sK31))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_712 ),
    inference(resolution,[],[f5220,f499])).

fof(f499,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_zfmisc_1(X1) ) ),
    inference(cnf_transformation,[],[f220])).

fof(f220,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_zfmisc_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_zfmisc_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',cc5_funct_1)).

fof(f5220,plain,
    ( v1_zfmisc_1(sK4(sK3(sK31)))
    | ~ spl44_712 ),
    inference(avatar_component_clause,[],[f5219])).

fof(f6815,plain,
    ( spl44_950
    | ~ spl44_712 ),
    inference(avatar_split_clause,[],[f6807,f5219,f6813])).

fof(f6813,plain,
    ( spl44_950
  <=> v1_zfmisc_1(sK25(sK4(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_950])])).

fof(f6807,plain,
    ( v1_zfmisc_1(sK25(sK4(sK3(sK31))))
    | ~ spl44_712 ),
    inference(resolution,[],[f5226,f608])).

fof(f608,plain,(
    ! [X0] : m1_subset_1(sK25(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f386])).

fof(f386,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK25(X0),X0)
      & m1_subset_1(sK25(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK25])],[f112,f385])).

fof(f385,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK25(X0),X0)
        & m1_subset_1(sK25(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f112,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',rc3_subset_1)).

fof(f6795,plain,
    ( spl44_948
    | ~ spl44_710 ),
    inference(avatar_split_clause,[],[f6776,f5211,f6793])).

fof(f6793,plain,
    ( spl44_948
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK1(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_948])])).

fof(f5211,plain,
    ( spl44_710
  <=> v1_zfmisc_1(sK1(sK3(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_710])])).

fof(f6776,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK1(sK3(sK31)))))
    | ~ spl44_710 ),
    inference(resolution,[],[f5214,f605])).

fof(f5214,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK3(sK31))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_710 ),
    inference(resolution,[],[f5212,f499])).

fof(f5212,plain,
    ( v1_zfmisc_1(sK1(sK3(sK31)))
    | ~ spl44_710 ),
    inference(avatar_component_clause,[],[f5211])).

fof(f6786,plain,
    ( spl44_946
    | ~ spl44_710 ),
    inference(avatar_split_clause,[],[f6778,f5211,f6784])).

fof(f6784,plain,
    ( spl44_946
  <=> v1_zfmisc_1(sK25(sK1(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_946])])).

fof(f6778,plain,
    ( v1_zfmisc_1(sK25(sK1(sK3(sK31))))
    | ~ spl44_710 ),
    inference(resolution,[],[f5214,f608])).

fof(f6766,plain,
    ( spl44_944
    | ~ spl44_708 ),
    inference(avatar_split_clause,[],[f6747,f5203,f6764])).

fof(f6764,plain,
    ( spl44_944
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK4(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_944])])).

fof(f5203,plain,
    ( spl44_708
  <=> v1_zfmisc_1(sK4(sK2(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_708])])).

fof(f6747,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK4(sK2(sK31)))))
    | ~ spl44_708 ),
    inference(resolution,[],[f5206,f605])).

fof(f5206,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK2(sK31))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_708 ),
    inference(resolution,[],[f5204,f499])).

fof(f5204,plain,
    ( v1_zfmisc_1(sK4(sK2(sK31)))
    | ~ spl44_708 ),
    inference(avatar_component_clause,[],[f5203])).

fof(f6757,plain,
    ( spl44_942
    | ~ spl44_708 ),
    inference(avatar_split_clause,[],[f6749,f5203,f6755])).

fof(f6755,plain,
    ( spl44_942
  <=> v1_zfmisc_1(sK25(sK4(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_942])])).

fof(f6749,plain,
    ( v1_zfmisc_1(sK25(sK4(sK2(sK31))))
    | ~ spl44_708 ),
    inference(resolution,[],[f5206,f608])).

fof(f6737,plain,
    ( spl44_940
    | ~ spl44_706 ),
    inference(avatar_split_clause,[],[f6718,f5195,f6735])).

fof(f6735,plain,
    ( spl44_940
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK1(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_940])])).

fof(f5195,plain,
    ( spl44_706
  <=> v1_zfmisc_1(sK1(sK2(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_706])])).

fof(f6718,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK1(sK2(sK31)))))
    | ~ spl44_706 ),
    inference(resolution,[],[f5198,f605])).

fof(f5198,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK2(sK31))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_706 ),
    inference(resolution,[],[f5196,f499])).

fof(f5196,plain,
    ( v1_zfmisc_1(sK1(sK2(sK31)))
    | ~ spl44_706 ),
    inference(avatar_component_clause,[],[f5195])).

fof(f6728,plain,
    ( spl44_938
    | ~ spl44_706 ),
    inference(avatar_split_clause,[],[f6720,f5195,f6726])).

fof(f6726,plain,
    ( spl44_938
  <=> v1_zfmisc_1(sK25(sK1(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_938])])).

fof(f6720,plain,
    ( v1_zfmisc_1(sK25(sK1(sK2(sK31))))
    | ~ spl44_706 ),
    inference(resolution,[],[f5198,f608])).

fof(f6705,plain,
    ( spl44_936
    | ~ spl44_704 ),
    inference(avatar_split_clause,[],[f6686,f5187,f6703])).

fof(f6703,plain,
    ( spl44_936
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK4(sK25(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_936])])).

fof(f5187,plain,
    ( spl44_704
  <=> v1_zfmisc_1(sK4(sK25(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_704])])).

fof(f6686,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK4(sK25(sK31)))))
    | ~ spl44_704 ),
    inference(resolution,[],[f5190,f605])).

fof(f5190,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK25(sK31))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_704 ),
    inference(resolution,[],[f5188,f499])).

fof(f5188,plain,
    ( v1_zfmisc_1(sK4(sK25(sK31)))
    | ~ spl44_704 ),
    inference(avatar_component_clause,[],[f5187])).

fof(f6696,plain,
    ( spl44_934
    | ~ spl44_704 ),
    inference(avatar_split_clause,[],[f6688,f5187,f6694])).

fof(f6694,plain,
    ( spl44_934
  <=> v1_zfmisc_1(sK25(sK4(sK25(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_934])])).

fof(f6688,plain,
    ( v1_zfmisc_1(sK25(sK4(sK25(sK31))))
    | ~ spl44_704 ),
    inference(resolution,[],[f5190,f608])).

fof(f6676,plain,
    ( spl44_932
    | ~ spl44_702 ),
    inference(avatar_split_clause,[],[f6657,f5179,f6674])).

fof(f6674,plain,
    ( spl44_932
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK1(sK25(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_932])])).

fof(f5179,plain,
    ( spl44_702
  <=> v1_zfmisc_1(sK1(sK25(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_702])])).

fof(f6657,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK1(sK25(sK31)))))
    | ~ spl44_702 ),
    inference(resolution,[],[f5182,f605])).

fof(f5182,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK25(sK31))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_702 ),
    inference(resolution,[],[f5180,f499])).

fof(f5180,plain,
    ( v1_zfmisc_1(sK1(sK25(sK31)))
    | ~ spl44_702 ),
    inference(avatar_component_clause,[],[f5179])).

fof(f6667,plain,
    ( spl44_930
    | ~ spl44_702 ),
    inference(avatar_split_clause,[],[f6659,f5179,f6665])).

fof(f6665,plain,
    ( spl44_930
  <=> v1_zfmisc_1(sK25(sK1(sK25(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_930])])).

fof(f6659,plain,
    ( v1_zfmisc_1(sK25(sK1(sK25(sK31))))
    | ~ spl44_702 ),
    inference(resolution,[],[f5182,f608])).

fof(f6648,plain,
    ( spl44_928
    | ~ spl44_676 ),
    inference(avatar_split_clause,[],[f6641,f4969,f6646])).

fof(f6646,plain,
    ( spl44_928
  <=> v1_relat_1(sK23(sK25(sK25(sK25(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_928])])).

fof(f4969,plain,
    ( spl44_676
  <=> v4_funct_1(sK25(sK25(sK25(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_676])])).

fof(f6641,plain,
    ( v1_relat_1(sK23(sK25(sK25(sK25(sK31)))))
    | ~ spl44_676 ),
    inference(resolution,[],[f4976,f605])).

fof(f4976,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK25(sK25(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_676 ),
    inference(resolution,[],[f4970,f446])).

fof(f4970,plain,
    ( v4_funct_1(sK25(sK25(sK25(sK31))))
    | ~ spl44_676 ),
    inference(avatar_component_clause,[],[f4969])).

fof(f6640,plain,
    ( spl44_926
    | ~ spl44_676 ),
    inference(avatar_split_clause,[],[f6633,f4969,f6638])).

fof(f6638,plain,
    ( spl44_926
  <=> v1_funct_1(sK23(sK25(sK25(sK25(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_926])])).

fof(f6633,plain,
    ( v1_funct_1(sK23(sK25(sK25(sK25(sK31)))))
    | ~ spl44_676 ),
    inference(resolution,[],[f4975,f605])).

fof(f4975,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK25(sK25(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_676 ),
    inference(resolution,[],[f4970,f447])).

fof(f6632,plain,
    ( spl44_924
    | ~ spl44_664 ),
    inference(avatar_split_clause,[],[f6625,f4867,f6630])).

fof(f6630,plain,
    ( spl44_924
  <=> v1_relat_1(sK23(sK25(sK4(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_924])])).

fof(f4867,plain,
    ( spl44_664
  <=> v4_funct_1(sK25(sK4(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_664])])).

fof(f6625,plain,
    ( v1_relat_1(sK23(sK25(sK4(sK3(sK31)))))
    | ~ spl44_664 ),
    inference(resolution,[],[f4872,f605])).

fof(f4872,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK4(sK3(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_664 ),
    inference(resolution,[],[f4868,f446])).

fof(f4868,plain,
    ( v4_funct_1(sK25(sK4(sK3(sK31))))
    | ~ spl44_664 ),
    inference(avatar_component_clause,[],[f4867])).

fof(f6624,plain,
    ( spl44_922
    | ~ spl44_664 ),
    inference(avatar_split_clause,[],[f6617,f4867,f6622])).

fof(f6622,plain,
    ( spl44_922
  <=> v1_funct_1(sK23(sK25(sK4(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_922])])).

fof(f6617,plain,
    ( v1_funct_1(sK23(sK25(sK4(sK3(sK31)))))
    | ~ spl44_664 ),
    inference(resolution,[],[f4871,f605])).

fof(f4871,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK4(sK3(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_664 ),
    inference(resolution,[],[f4868,f447])).

fof(f6616,plain,
    ( spl44_920
    | ~ spl44_660 ),
    inference(avatar_split_clause,[],[f6606,f4836,f6614])).

fof(f6614,plain,
    ( spl44_920
  <=> v1_relat_1(sK23(sK25(sK3(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_920])])).

fof(f4836,plain,
    ( spl44_660
  <=> v4_funct_1(sK25(sK3(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_660])])).

fof(f6606,plain,
    ( v1_relat_1(sK23(sK25(sK3(sK3(sK31)))))
    | ~ spl44_660 ),
    inference(resolution,[],[f4841,f605])).

fof(f4841,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK3(sK3(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_660 ),
    inference(resolution,[],[f4837,f446])).

fof(f4837,plain,
    ( v4_funct_1(sK25(sK3(sK3(sK31))))
    | ~ spl44_660 ),
    inference(avatar_component_clause,[],[f4836])).

fof(f6605,plain,
    ( spl44_918
    | ~ spl44_660 ),
    inference(avatar_split_clause,[],[f6598,f4836,f6603])).

fof(f6603,plain,
    ( spl44_918
  <=> v1_funct_1(sK23(sK25(sK3(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_918])])).

fof(f6598,plain,
    ( v1_funct_1(sK23(sK25(sK3(sK3(sK31)))))
    | ~ spl44_660 ),
    inference(resolution,[],[f4840,f605])).

fof(f4840,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK3(sK3(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_660 ),
    inference(resolution,[],[f4837,f447])).

fof(f6597,plain,
    ( spl44_916
    | ~ spl44_656 ),
    inference(avatar_split_clause,[],[f6590,f4803,f6595])).

fof(f6595,plain,
    ( spl44_916
  <=> v1_relat_1(sK23(sK25(sK2(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_916])])).

fof(f4803,plain,
    ( spl44_656
  <=> v4_funct_1(sK25(sK2(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_656])])).

fof(f6590,plain,
    ( v1_relat_1(sK23(sK25(sK2(sK3(sK31)))))
    | ~ spl44_656 ),
    inference(resolution,[],[f4810,f605])).

fof(f4810,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK2(sK3(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_656 ),
    inference(resolution,[],[f4804,f446])).

fof(f4804,plain,
    ( v4_funct_1(sK25(sK2(sK3(sK31))))
    | ~ spl44_656 ),
    inference(avatar_component_clause,[],[f4803])).

fof(f6589,plain,
    ( spl44_914
    | ~ spl44_656 ),
    inference(avatar_split_clause,[],[f6582,f4803,f6587])).

fof(f6587,plain,
    ( spl44_914
  <=> v1_funct_1(sK23(sK25(sK2(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_914])])).

fof(f6582,plain,
    ( v1_funct_1(sK23(sK25(sK2(sK3(sK31)))))
    | ~ spl44_656 ),
    inference(resolution,[],[f4809,f605])).

fof(f4809,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK2(sK3(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_656 ),
    inference(resolution,[],[f4804,f447])).

fof(f6581,plain,
    ( spl44_912
    | ~ spl44_652 ),
    inference(avatar_split_clause,[],[f6574,f4772,f6579])).

fof(f6579,plain,
    ( spl44_912
  <=> v1_relat_1(sK23(sK25(sK1(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_912])])).

fof(f4772,plain,
    ( spl44_652
  <=> v4_funct_1(sK25(sK1(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_652])])).

fof(f6574,plain,
    ( v1_relat_1(sK23(sK25(sK1(sK3(sK31)))))
    | ~ spl44_652 ),
    inference(resolution,[],[f4777,f605])).

fof(f4777,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK1(sK3(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_652 ),
    inference(resolution,[],[f4773,f446])).

fof(f4773,plain,
    ( v4_funct_1(sK25(sK1(sK3(sK31))))
    | ~ spl44_652 ),
    inference(avatar_component_clause,[],[f4772])).

fof(f6573,plain,
    ( spl44_910
    | ~ spl44_652 ),
    inference(avatar_split_clause,[],[f6566,f4772,f6571])).

fof(f6571,plain,
    ( spl44_910
  <=> v1_funct_1(sK23(sK25(sK1(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_910])])).

fof(f6566,plain,
    ( v1_funct_1(sK23(sK25(sK1(sK3(sK31)))))
    | ~ spl44_652 ),
    inference(resolution,[],[f4776,f605])).

fof(f4776,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK1(sK3(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_652 ),
    inference(resolution,[],[f4773,f447])).

fof(f6565,plain,
    ( spl44_908
    | ~ spl44_648 ),
    inference(avatar_split_clause,[],[f6558,f4741,f6563])).

fof(f6563,plain,
    ( spl44_908
  <=> v1_relat_1(sK23(sK25(sK4(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_908])])).

fof(f4741,plain,
    ( spl44_648
  <=> v4_funct_1(sK25(sK4(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_648])])).

fof(f6558,plain,
    ( v1_relat_1(sK23(sK25(sK4(sK2(sK31)))))
    | ~ spl44_648 ),
    inference(resolution,[],[f4746,f605])).

fof(f4746,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK4(sK2(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_648 ),
    inference(resolution,[],[f4742,f446])).

fof(f4742,plain,
    ( v4_funct_1(sK25(sK4(sK2(sK31))))
    | ~ spl44_648 ),
    inference(avatar_component_clause,[],[f4741])).

fof(f6557,plain,
    ( spl44_906
    | ~ spl44_648 ),
    inference(avatar_split_clause,[],[f6550,f4741,f6555])).

fof(f6555,plain,
    ( spl44_906
  <=> v1_funct_1(sK23(sK25(sK4(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_906])])).

fof(f6550,plain,
    ( v1_funct_1(sK23(sK25(sK4(sK2(sK31)))))
    | ~ spl44_648 ),
    inference(resolution,[],[f4745,f605])).

fof(f4745,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK4(sK2(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_648 ),
    inference(resolution,[],[f4742,f447])).

fof(f6549,plain,
    ( spl44_904
    | ~ spl44_644 ),
    inference(avatar_split_clause,[],[f6533,f4710,f6547])).

fof(f6547,plain,
    ( spl44_904
  <=> v1_relat_1(sK23(sK25(sK3(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_904])])).

fof(f4710,plain,
    ( spl44_644
  <=> v4_funct_1(sK25(sK3(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_644])])).

fof(f6533,plain,
    ( v1_relat_1(sK23(sK25(sK3(sK2(sK31)))))
    | ~ spl44_644 ),
    inference(resolution,[],[f4715,f605])).

fof(f4715,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK3(sK2(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_644 ),
    inference(resolution,[],[f4711,f446])).

fof(f4711,plain,
    ( v4_funct_1(sK25(sK3(sK2(sK31))))
    | ~ spl44_644 ),
    inference(avatar_component_clause,[],[f4710])).

fof(f6532,plain,
    ( spl44_902
    | ~ spl44_644 ),
    inference(avatar_split_clause,[],[f6525,f4710,f6530])).

fof(f6530,plain,
    ( spl44_902
  <=> v1_funct_1(sK23(sK25(sK3(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_902])])).

fof(f6525,plain,
    ( v1_funct_1(sK23(sK25(sK3(sK2(sK31)))))
    | ~ spl44_644 ),
    inference(resolution,[],[f4714,f605])).

fof(f4714,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK3(sK2(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_644 ),
    inference(resolution,[],[f4711,f447])).

fof(f6524,plain,
    ( spl44_900
    | ~ spl44_640 ),
    inference(avatar_split_clause,[],[f6517,f4677,f6522])).

fof(f6522,plain,
    ( spl44_900
  <=> v1_relat_1(sK23(sK25(sK2(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_900])])).

fof(f4677,plain,
    ( spl44_640
  <=> v4_funct_1(sK25(sK2(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_640])])).

fof(f6517,plain,
    ( v1_relat_1(sK23(sK25(sK2(sK2(sK31)))))
    | ~ spl44_640 ),
    inference(resolution,[],[f4684,f605])).

fof(f4684,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK2(sK2(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_640 ),
    inference(resolution,[],[f4678,f446])).

fof(f4678,plain,
    ( v4_funct_1(sK25(sK2(sK2(sK31))))
    | ~ spl44_640 ),
    inference(avatar_component_clause,[],[f4677])).

fof(f6516,plain,
    ( spl44_898
    | ~ spl44_640 ),
    inference(avatar_split_clause,[],[f6509,f4677,f6514])).

fof(f6514,plain,
    ( spl44_898
  <=> v1_funct_1(sK23(sK25(sK2(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_898])])).

fof(f6509,plain,
    ( v1_funct_1(sK23(sK25(sK2(sK2(sK31)))))
    | ~ spl44_640 ),
    inference(resolution,[],[f4683,f605])).

fof(f4683,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK2(sK2(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_640 ),
    inference(resolution,[],[f4678,f447])).

fof(f6508,plain,
    ( spl44_896
    | ~ spl44_636 ),
    inference(avatar_split_clause,[],[f6501,f4646,f6506])).

fof(f6506,plain,
    ( spl44_896
  <=> v1_relat_1(sK23(sK25(sK1(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_896])])).

fof(f4646,plain,
    ( spl44_636
  <=> v4_funct_1(sK25(sK1(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_636])])).

fof(f6501,plain,
    ( v1_relat_1(sK23(sK25(sK1(sK2(sK31)))))
    | ~ spl44_636 ),
    inference(resolution,[],[f4651,f605])).

fof(f4651,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK1(sK2(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_636 ),
    inference(resolution,[],[f4647,f446])).

fof(f4647,plain,
    ( v4_funct_1(sK25(sK1(sK2(sK31))))
    | ~ spl44_636 ),
    inference(avatar_component_clause,[],[f4646])).

fof(f6500,plain,
    ( spl44_894
    | ~ spl44_636 ),
    inference(avatar_split_clause,[],[f6493,f4646,f6498])).

fof(f6498,plain,
    ( spl44_894
  <=> v1_funct_1(sK23(sK25(sK1(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_894])])).

fof(f6493,plain,
    ( v1_funct_1(sK23(sK25(sK1(sK2(sK31)))))
    | ~ spl44_636 ),
    inference(resolution,[],[f4650,f605])).

fof(f4650,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK1(sK2(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_636 ),
    inference(resolution,[],[f4647,f447])).

fof(f6492,plain,
    ( spl44_892
    | ~ spl44_632 ),
    inference(avatar_split_clause,[],[f6485,f4615,f6490])).

fof(f6490,plain,
    ( spl44_892
  <=> v1_relat_1(sK23(sK25(sK4(sK1(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_892])])).

fof(f4615,plain,
    ( spl44_632
  <=> v4_funct_1(sK25(sK4(sK1(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_632])])).

fof(f6485,plain,
    ( v1_relat_1(sK23(sK25(sK4(sK1(sK31)))))
    | ~ spl44_632 ),
    inference(resolution,[],[f4620,f605])).

fof(f4620,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK4(sK1(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_632 ),
    inference(resolution,[],[f4616,f446])).

fof(f4616,plain,
    ( v4_funct_1(sK25(sK4(sK1(sK31))))
    | ~ spl44_632 ),
    inference(avatar_component_clause,[],[f4615])).

fof(f6484,plain,
    ( spl44_890
    | ~ spl44_632 ),
    inference(avatar_split_clause,[],[f6477,f4615,f6482])).

fof(f6482,plain,
    ( spl44_890
  <=> v1_funct_1(sK23(sK25(sK4(sK1(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_890])])).

fof(f6477,plain,
    ( v1_funct_1(sK23(sK25(sK4(sK1(sK31)))))
    | ~ spl44_632 ),
    inference(resolution,[],[f4619,f605])).

fof(f4619,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK4(sK1(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_632 ),
    inference(resolution,[],[f4616,f447])).

fof(f6473,plain,
    ( spl44_888
    | ~ spl44_628 ),
    inference(avatar_split_clause,[],[f6466,f4584,f6471])).

fof(f6471,plain,
    ( spl44_888
  <=> v1_relat_1(sK23(sK25(sK3(sK1(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_888])])).

fof(f4584,plain,
    ( spl44_628
  <=> v4_funct_1(sK25(sK3(sK1(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_628])])).

fof(f6466,plain,
    ( v1_relat_1(sK23(sK25(sK3(sK1(sK31)))))
    | ~ spl44_628 ),
    inference(resolution,[],[f4589,f605])).

fof(f4589,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK3(sK1(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_628 ),
    inference(resolution,[],[f4585,f446])).

fof(f4585,plain,
    ( v4_funct_1(sK25(sK3(sK1(sK31))))
    | ~ spl44_628 ),
    inference(avatar_component_clause,[],[f4584])).

fof(f6465,plain,
    ( spl44_886
    | ~ spl44_628 ),
    inference(avatar_split_clause,[],[f6458,f4584,f6463])).

fof(f6463,plain,
    ( spl44_886
  <=> v1_funct_1(sK23(sK25(sK3(sK1(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_886])])).

fof(f6458,plain,
    ( v1_funct_1(sK23(sK25(sK3(sK1(sK31)))))
    | ~ spl44_628 ),
    inference(resolution,[],[f4588,f605])).

fof(f4588,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK3(sK1(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_628 ),
    inference(resolution,[],[f4585,f447])).

fof(f6457,plain,
    ( spl44_884
    | ~ spl44_624 ),
    inference(avatar_split_clause,[],[f6450,f4551,f6455])).

fof(f6455,plain,
    ( spl44_884
  <=> v1_relat_1(sK23(sK25(sK2(sK1(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_884])])).

fof(f4551,plain,
    ( spl44_624
  <=> v4_funct_1(sK25(sK2(sK1(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_624])])).

fof(f6450,plain,
    ( v1_relat_1(sK23(sK25(sK2(sK1(sK31)))))
    | ~ spl44_624 ),
    inference(resolution,[],[f4558,f605])).

fof(f4558,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK2(sK1(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_624 ),
    inference(resolution,[],[f4552,f446])).

fof(f4552,plain,
    ( v4_funct_1(sK25(sK2(sK1(sK31))))
    | ~ spl44_624 ),
    inference(avatar_component_clause,[],[f4551])).

fof(f6449,plain,
    ( spl44_882
    | ~ spl44_624 ),
    inference(avatar_split_clause,[],[f6442,f4551,f6447])).

fof(f6447,plain,
    ( spl44_882
  <=> v1_funct_1(sK23(sK25(sK2(sK1(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_882])])).

fof(f6442,plain,
    ( v1_funct_1(sK23(sK25(sK2(sK1(sK31)))))
    | ~ spl44_624 ),
    inference(resolution,[],[f4557,f605])).

fof(f4557,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK2(sK1(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_624 ),
    inference(resolution,[],[f4552,f447])).

fof(f6441,plain,
    ( spl44_880
    | ~ spl44_620 ),
    inference(avatar_split_clause,[],[f6434,f4520,f6439])).

fof(f6439,plain,
    ( spl44_880
  <=> v1_relat_1(sK23(sK25(sK1(sK1(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_880])])).

fof(f4520,plain,
    ( spl44_620
  <=> v4_funct_1(sK25(sK1(sK1(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_620])])).

fof(f6434,plain,
    ( v1_relat_1(sK23(sK25(sK1(sK1(sK31)))))
    | ~ spl44_620 ),
    inference(resolution,[],[f4525,f605])).

fof(f4525,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK1(sK1(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_620 ),
    inference(resolution,[],[f4521,f446])).

fof(f4521,plain,
    ( v4_funct_1(sK25(sK1(sK1(sK31))))
    | ~ spl44_620 ),
    inference(avatar_component_clause,[],[f4520])).

fof(f6433,plain,
    ( spl44_878
    | ~ spl44_620 ),
    inference(avatar_split_clause,[],[f6426,f4520,f6431])).

fof(f6431,plain,
    ( spl44_878
  <=> v1_funct_1(sK23(sK25(sK1(sK1(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_878])])).

fof(f6426,plain,
    ( v1_funct_1(sK23(sK25(sK1(sK1(sK31)))))
    | ~ spl44_620 ),
    inference(resolution,[],[f4524,f605])).

fof(f4524,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK1(sK1(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_620 ),
    inference(resolution,[],[f4521,f447])).

fof(f6425,plain,
    ( spl44_876
    | ~ spl44_600 ),
    inference(avatar_split_clause,[],[f6418,f4389,f6423])).

fof(f6423,plain,
    ( spl44_876
  <=> v1_relat_1(sK23(sK25(sK25(sK4(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_876])])).

fof(f4389,plain,
    ( spl44_600
  <=> v4_funct_1(sK25(sK25(sK4(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_600])])).

fof(f6418,plain,
    ( v1_relat_1(sK23(sK25(sK25(sK4(sK31)))))
    | ~ spl44_600 ),
    inference(resolution,[],[f4394,f605])).

fof(f4394,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK25(sK4(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_600 ),
    inference(resolution,[],[f4390,f446])).

fof(f4390,plain,
    ( v4_funct_1(sK25(sK25(sK4(sK31))))
    | ~ spl44_600 ),
    inference(avatar_component_clause,[],[f4389])).

fof(f6417,plain,
    ( spl44_874
    | ~ spl44_600 ),
    inference(avatar_split_clause,[],[f6410,f4389,f6415])).

fof(f6415,plain,
    ( spl44_874
  <=> v1_funct_1(sK23(sK25(sK25(sK4(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_874])])).

fof(f6410,plain,
    ( v1_funct_1(sK23(sK25(sK25(sK4(sK31)))))
    | ~ spl44_600 ),
    inference(resolution,[],[f4393,f605])).

fof(f4393,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK25(sK4(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_600 ),
    inference(resolution,[],[f4390,f447])).

fof(f6403,plain,
    ( spl44_872
    | ~ spl44_592 ),
    inference(avatar_split_clause,[],[f6396,f4341,f6401])).

fof(f6401,plain,
    ( spl44_872
  <=> v1_relat_1(sK23(sK25(sK25(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_872])])).

fof(f4341,plain,
    ( spl44_592
  <=> v4_funct_1(sK25(sK25(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_592])])).

fof(f6396,plain,
    ( v1_relat_1(sK23(sK25(sK25(sK3(sK31)))))
    | ~ spl44_592 ),
    inference(resolution,[],[f4347,f605])).

fof(f4347,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK25(sK3(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_592 ),
    inference(resolution,[],[f4342,f446])).

fof(f4342,plain,
    ( v4_funct_1(sK25(sK25(sK3(sK31))))
    | ~ spl44_592 ),
    inference(avatar_component_clause,[],[f4341])).

fof(f6395,plain,
    ( spl44_870
    | ~ spl44_592 ),
    inference(avatar_split_clause,[],[f6388,f4341,f6393])).

fof(f6393,plain,
    ( spl44_870
  <=> v1_funct_1(sK23(sK25(sK25(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_870])])).

fof(f6388,plain,
    ( v1_funct_1(sK23(sK25(sK25(sK3(sK31)))))
    | ~ spl44_592 ),
    inference(resolution,[],[f4346,f605])).

fof(f4346,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK25(sK3(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_592 ),
    inference(resolution,[],[f4342,f447])).

fof(f6387,plain,
    ( spl44_868
    | ~ spl44_584 ),
    inference(avatar_split_clause,[],[f6380,f4291,f6385])).

fof(f6385,plain,
    ( spl44_868
  <=> v1_relat_1(sK23(sK25(sK25(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_868])])).

fof(f4291,plain,
    ( spl44_584
  <=> v4_funct_1(sK25(sK25(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_584])])).

fof(f6380,plain,
    ( v1_relat_1(sK23(sK25(sK25(sK2(sK31)))))
    | ~ spl44_584 ),
    inference(resolution,[],[f4296,f605])).

fof(f4296,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK25(sK2(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_584 ),
    inference(resolution,[],[f4292,f446])).

fof(f4292,plain,
    ( v4_funct_1(sK25(sK25(sK2(sK31))))
    | ~ spl44_584 ),
    inference(avatar_component_clause,[],[f4291])).

fof(f6379,plain,
    ( spl44_866
    | ~ spl44_584 ),
    inference(avatar_split_clause,[],[f6372,f4291,f6377])).

fof(f6377,plain,
    ( spl44_866
  <=> v1_funct_1(sK23(sK25(sK25(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_866])])).

fof(f6372,plain,
    ( v1_funct_1(sK23(sK25(sK25(sK2(sK31)))))
    | ~ spl44_584 ),
    inference(resolution,[],[f4295,f605])).

fof(f4295,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK25(sK2(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_584 ),
    inference(resolution,[],[f4292,f447])).

fof(f6371,plain,
    ( spl44_864
    | ~ spl44_572 ),
    inference(avatar_split_clause,[],[f6364,f4214,f6369])).

fof(f6369,plain,
    ( spl44_864
  <=> v1_relat_1(sK23(sK25(sK25(sK1(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_864])])).

fof(f4214,plain,
    ( spl44_572
  <=> v4_funct_1(sK25(sK25(sK1(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_572])])).

fof(f6364,plain,
    ( v1_relat_1(sK23(sK25(sK25(sK1(sK31)))))
    | ~ spl44_572 ),
    inference(resolution,[],[f4219,f605])).

fof(f4219,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK25(sK1(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_572 ),
    inference(resolution,[],[f4215,f446])).

fof(f4215,plain,
    ( v4_funct_1(sK25(sK25(sK1(sK31))))
    | ~ spl44_572 ),
    inference(avatar_component_clause,[],[f4214])).

fof(f6363,plain,
    ( spl44_862
    | ~ spl44_572 ),
    inference(avatar_split_clause,[],[f6356,f4214,f6361])).

fof(f6361,plain,
    ( spl44_862
  <=> v1_funct_1(sK23(sK25(sK25(sK1(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_862])])).

fof(f6356,plain,
    ( v1_funct_1(sK23(sK25(sK25(sK1(sK31)))))
    | ~ spl44_572 ),
    inference(resolution,[],[f4218,f605])).

fof(f4218,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK25(sK1(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_572 ),
    inference(resolution,[],[f4215,f447])).

fof(f6354,plain,
    ( spl44_860
    | ~ spl44_534 ),
    inference(avatar_split_clause,[],[f6335,f3826,f6352])).

fof(f6352,plain,
    ( spl44_860
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK4(sK4(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_860])])).

fof(f3826,plain,
    ( spl44_534
  <=> v1_zfmisc_1(sK4(sK4(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_534])])).

fof(f6335,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK4(sK4(sK31)))))
    | ~ spl44_534 ),
    inference(resolution,[],[f3829,f605])).

fof(f3829,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK4(sK31))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_534 ),
    inference(resolution,[],[f3827,f499])).

fof(f3827,plain,
    ( v1_zfmisc_1(sK4(sK4(sK31)))
    | ~ spl44_534 ),
    inference(avatar_component_clause,[],[f3826])).

fof(f6345,plain,
    ( spl44_858
    | ~ spl44_534 ),
    inference(avatar_split_clause,[],[f6337,f3826,f6343])).

fof(f6343,plain,
    ( spl44_858
  <=> v1_zfmisc_1(sK25(sK4(sK4(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_858])])).

fof(f6337,plain,
    ( v1_zfmisc_1(sK25(sK4(sK4(sK31))))
    | ~ spl44_534 ),
    inference(resolution,[],[f3829,f608])).

fof(f6319,plain,
    ( spl44_856
    | ~ spl44_532 ),
    inference(avatar_split_clause,[],[f6300,f3818,f6317])).

fof(f6317,plain,
    ( spl44_856
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK1(sK4(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_856])])).

fof(f3818,plain,
    ( spl44_532
  <=> v1_zfmisc_1(sK1(sK4(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_532])])).

fof(f6300,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK1(sK4(sK31)))))
    | ~ spl44_532 ),
    inference(resolution,[],[f3821,f605])).

fof(f3821,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK4(sK31))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_532 ),
    inference(resolution,[],[f3819,f499])).

fof(f3819,plain,
    ( v1_zfmisc_1(sK1(sK4(sK31)))
    | ~ spl44_532 ),
    inference(avatar_component_clause,[],[f3818])).

fof(f6310,plain,
    ( spl44_854
    | ~ spl44_532 ),
    inference(avatar_split_clause,[],[f6302,f3818,f6308])).

fof(f6308,plain,
    ( spl44_854
  <=> v1_zfmisc_1(sK25(sK1(sK4(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_854])])).

fof(f6302,plain,
    ( v1_zfmisc_1(sK25(sK1(sK4(sK31))))
    | ~ spl44_532 ),
    inference(resolution,[],[f3821,f608])).

fof(f6290,plain,
    ( spl44_852
    | ~ spl44_496 ),
    inference(avatar_split_clause,[],[f6271,f3659,f6288])).

fof(f6288,plain,
    ( spl44_852
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK4(sK1(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_852])])).

fof(f3659,plain,
    ( spl44_496
  <=> v1_zfmisc_1(sK4(sK1(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_496])])).

fof(f6271,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK4(sK1(sK31)))))
    | ~ spl44_496 ),
    inference(resolution,[],[f3662,f605])).

fof(f3662,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK1(sK31))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_496 ),
    inference(resolution,[],[f3660,f499])).

fof(f3660,plain,
    ( v1_zfmisc_1(sK4(sK1(sK31)))
    | ~ spl44_496 ),
    inference(avatar_component_clause,[],[f3659])).

fof(f6281,plain,
    ( spl44_850
    | ~ spl44_496 ),
    inference(avatar_split_clause,[],[f6273,f3659,f6279])).

fof(f6279,plain,
    ( spl44_850
  <=> v1_zfmisc_1(sK25(sK4(sK1(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_850])])).

fof(f6273,plain,
    ( v1_zfmisc_1(sK25(sK4(sK1(sK31))))
    | ~ spl44_496 ),
    inference(resolution,[],[f3662,f608])).

fof(f6261,plain,
    ( spl44_848
    | ~ spl44_494 ),
    inference(avatar_split_clause,[],[f6242,f3651,f6259])).

fof(f6259,plain,
    ( spl44_848
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK1(sK1(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_848])])).

fof(f3651,plain,
    ( spl44_494
  <=> v1_zfmisc_1(sK1(sK1(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_494])])).

fof(f6242,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK1(sK1(sK31)))))
    | ~ spl44_494 ),
    inference(resolution,[],[f3654,f605])).

fof(f3654,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK1(sK31))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_494 ),
    inference(resolution,[],[f3652,f499])).

fof(f3652,plain,
    ( v1_zfmisc_1(sK1(sK1(sK31)))
    | ~ spl44_494 ),
    inference(avatar_component_clause,[],[f3651])).

fof(f6252,plain,
    ( spl44_846
    | ~ spl44_494 ),
    inference(avatar_split_clause,[],[f6244,f3651,f6250])).

fof(f6250,plain,
    ( spl44_846
  <=> v1_zfmisc_1(sK25(sK1(sK1(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_846])])).

fof(f6244,plain,
    ( v1_zfmisc_1(sK25(sK1(sK1(sK31))))
    | ~ spl44_494 ),
    inference(resolution,[],[f3654,f608])).

fof(f6232,plain,
    ( spl44_844
    | ~ spl44_450 ),
    inference(avatar_split_clause,[],[f6213,f3366,f6230])).

fof(f6230,plain,
    ( spl44_844
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK25(sK4(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_844])])).

fof(f3366,plain,
    ( spl44_450
  <=> v1_zfmisc_1(sK25(sK4(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_450])])).

fof(f6213,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK25(sK4(sK31)))))
    | ~ spl44_450 ),
    inference(resolution,[],[f3459,f605])).

fof(f3459,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK25(sK4(sK31))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_450 ),
    inference(resolution,[],[f3367,f499])).

fof(f3367,plain,
    ( v1_zfmisc_1(sK25(sK4(sK31)))
    | ~ spl44_450 ),
    inference(avatar_component_clause,[],[f3366])).

fof(f6223,plain,
    ( spl44_842
    | ~ spl44_450 ),
    inference(avatar_split_clause,[],[f6215,f3366,f6221])).

fof(f6221,plain,
    ( spl44_842
  <=> v1_zfmisc_1(sK25(sK25(sK4(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_842])])).

fof(f6215,plain,
    ( v1_zfmisc_1(sK25(sK25(sK4(sK31))))
    | ~ spl44_450 ),
    inference(resolution,[],[f3459,f608])).

fof(f6197,plain,
    ( spl44_840
    | ~ spl44_444 ),
    inference(avatar_split_clause,[],[f6178,f3295,f6195])).

fof(f6195,plain,
    ( spl44_840
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK25(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_840])])).

fof(f3295,plain,
    ( spl44_444
  <=> v1_zfmisc_1(sK25(sK3(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_444])])).

fof(f6178,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK25(sK3(sK31)))))
    | ~ spl44_444 ),
    inference(resolution,[],[f3308,f605])).

fof(f3308,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK25(sK3(sK31))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_444 ),
    inference(resolution,[],[f3296,f499])).

fof(f3296,plain,
    ( v1_zfmisc_1(sK25(sK3(sK31)))
    | ~ spl44_444 ),
    inference(avatar_component_clause,[],[f3295])).

fof(f6188,plain,
    ( spl44_838
    | ~ spl44_444 ),
    inference(avatar_split_clause,[],[f6180,f3295,f6186])).

fof(f6186,plain,
    ( spl44_838
  <=> v1_zfmisc_1(sK25(sK25(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_838])])).

fof(f6180,plain,
    ( v1_zfmisc_1(sK25(sK25(sK3(sK31))))
    | ~ spl44_444 ),
    inference(resolution,[],[f3308,f608])).

fof(f6168,plain,
    ( spl44_836
    | ~ spl44_426 ),
    inference(avatar_split_clause,[],[f6149,f3200,f6166])).

fof(f6166,plain,
    ( spl44_836
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK25(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_836])])).

fof(f3200,plain,
    ( spl44_426
  <=> v1_zfmisc_1(sK25(sK2(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_426])])).

fof(f6149,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK25(sK2(sK31)))))
    | ~ spl44_426 ),
    inference(resolution,[],[f3213,f605])).

fof(f3213,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK25(sK2(sK31))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_426 ),
    inference(resolution,[],[f3201,f499])).

fof(f3201,plain,
    ( v1_zfmisc_1(sK25(sK2(sK31)))
    | ~ spl44_426 ),
    inference(avatar_component_clause,[],[f3200])).

fof(f6159,plain,
    ( spl44_834
    | ~ spl44_426 ),
    inference(avatar_split_clause,[],[f6151,f3200,f6157])).

fof(f6157,plain,
    ( spl44_834
  <=> v1_zfmisc_1(sK25(sK25(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_834])])).

fof(f6151,plain,
    ( v1_zfmisc_1(sK25(sK25(sK2(sK31))))
    | ~ spl44_426 ),
    inference(resolution,[],[f3213,f608])).

fof(f6139,plain,
    ( spl44_832
    | ~ spl44_360 ),
    inference(avatar_split_clause,[],[f6120,f2848,f6137])).

fof(f6137,plain,
    ( spl44_832
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK25(sK1(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_832])])).

fof(f2848,plain,
    ( spl44_360
  <=> v1_zfmisc_1(sK25(sK1(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_360])])).

fof(f6120,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK25(sK1(sK31)))))
    | ~ spl44_360 ),
    inference(resolution,[],[f2903,f605])).

fof(f2903,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK25(sK1(sK31))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_360 ),
    inference(resolution,[],[f2849,f499])).

fof(f2849,plain,
    ( v1_zfmisc_1(sK25(sK1(sK31)))
    | ~ spl44_360 ),
    inference(avatar_component_clause,[],[f2848])).

fof(f6130,plain,
    ( spl44_830
    | ~ spl44_360 ),
    inference(avatar_split_clause,[],[f6122,f2848,f6128])).

fof(f6128,plain,
    ( spl44_830
  <=> v1_zfmisc_1(sK25(sK25(sK1(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_830])])).

fof(f6122,plain,
    ( v1_zfmisc_1(sK25(sK25(sK1(sK31))))
    | ~ spl44_360 ),
    inference(resolution,[],[f2903,f608])).

fof(f6110,plain,
    ( spl44_828
    | ~ spl44_350 ),
    inference(avatar_split_clause,[],[f6091,f2748,f6108])).

fof(f6108,plain,
    ( spl44_828
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK25(sK25(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_828])])).

fof(f2748,plain,
    ( spl44_350
  <=> v1_zfmisc_1(sK25(sK25(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_350])])).

fof(f6091,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK25(sK25(sK31)))))
    | ~ spl44_350 ),
    inference(resolution,[],[f2786,f605])).

fof(f2786,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK25(sK25(sK31))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_350 ),
    inference(resolution,[],[f2749,f499])).

fof(f2749,plain,
    ( v1_zfmisc_1(sK25(sK25(sK31)))
    | ~ spl44_350 ),
    inference(avatar_component_clause,[],[f2748])).

fof(f6101,plain,
    ( spl44_826
    | ~ spl44_350 ),
    inference(avatar_split_clause,[],[f6093,f2748,f6099])).

fof(f6099,plain,
    ( spl44_826
  <=> v1_zfmisc_1(sK25(sK25(sK25(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_826])])).

fof(f6093,plain,
    ( v1_zfmisc_1(sK25(sK25(sK25(sK31))))
    | ~ spl44_350 ),
    inference(resolution,[],[f2786,f608])).

fof(f6077,plain,
    ( spl44_824
    | ~ spl44_262 ),
    inference(avatar_split_clause,[],[f6058,f2221,f6075])).

fof(f6075,plain,
    ( spl44_824
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK4(sK25(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_824])])).

fof(f2221,plain,
    ( spl44_262
  <=> v4_funct_1(sK4(sK25(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_262])])).

fof(f6058,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK4(sK25(sK31)))))
    | ~ spl44_262 ),
    inference(resolution,[],[f4955,f605])).

fof(f4955,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK25(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_262 ),
    inference(resolution,[],[f2222,f448])).

fof(f448,plain,(
    ! [X0,X1] :
      ( ~ v4_funct_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v4_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f166])).

fof(f166,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v4_funct_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v4_funct_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v4_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',cc10_funct_1)).

fof(f2222,plain,
    ( v4_funct_1(sK4(sK25(sK31)))
    | ~ spl44_262 ),
    inference(avatar_component_clause,[],[f2221])).

fof(f6067,plain,
    ( spl44_822
    | ~ spl44_262 ),
    inference(avatar_split_clause,[],[f6060,f2221,f6065])).

fof(f6060,plain,
    ( v4_funct_1(sK25(sK4(sK25(sK31))))
    | ~ spl44_262 ),
    inference(resolution,[],[f4955,f608])).

fof(f6046,plain,
    ( spl44_820
    | ~ spl44_260 ),
    inference(avatar_split_clause,[],[f6027,f2214,f6044])).

fof(f6044,plain,
    ( spl44_820
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK3(sK25(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_820])])).

fof(f2214,plain,
    ( spl44_260
  <=> v4_funct_1(sK3(sK25(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_260])])).

fof(f6027,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK3(sK25(sK31)))))
    | ~ spl44_260 ),
    inference(resolution,[],[f4952,f605])).

fof(f4952,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3(sK25(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_260 ),
    inference(resolution,[],[f2215,f448])).

fof(f2215,plain,
    ( v4_funct_1(sK3(sK25(sK31)))
    | ~ spl44_260 ),
    inference(avatar_component_clause,[],[f2214])).

fof(f6036,plain,
    ( spl44_818
    | ~ spl44_260 ),
    inference(avatar_split_clause,[],[f6029,f2214,f6034])).

fof(f6029,plain,
    ( v4_funct_1(sK25(sK3(sK25(sK31))))
    | ~ spl44_260 ),
    inference(resolution,[],[f4952,f608])).

fof(f6015,plain,
    ( spl44_816
    | ~ spl44_254 ),
    inference(avatar_split_clause,[],[f5996,f2176,f6013])).

fof(f6013,plain,
    ( spl44_816
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK2(sK25(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_816])])).

fof(f2176,plain,
    ( spl44_254
  <=> v4_funct_1(sK2(sK25(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_254])])).

fof(f5996,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK2(sK25(sK31)))))
    | ~ spl44_254 ),
    inference(resolution,[],[f4949,f605])).

fof(f4949,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2(sK25(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_254 ),
    inference(resolution,[],[f2177,f448])).

fof(f2177,plain,
    ( v4_funct_1(sK2(sK25(sK31)))
    | ~ spl44_254 ),
    inference(avatar_component_clause,[],[f2176])).

fof(f6005,plain,
    ( spl44_814
    | ~ spl44_254 ),
    inference(avatar_split_clause,[],[f5998,f2176,f6003])).

fof(f5998,plain,
    ( v4_funct_1(sK25(sK2(sK25(sK31))))
    | ~ spl44_254 ),
    inference(resolution,[],[f4949,f608])).

fof(f5984,plain,
    ( spl44_812
    | ~ spl44_250 ),
    inference(avatar_split_clause,[],[f5965,f2148,f5982])).

fof(f5982,plain,
    ( spl44_812
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK1(sK25(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_812])])).

fof(f2148,plain,
    ( spl44_250
  <=> v4_funct_1(sK1(sK25(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_250])])).

fof(f5965,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK1(sK25(sK31)))))
    | ~ spl44_250 ),
    inference(resolution,[],[f4946,f605])).

fof(f4946,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK25(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_250 ),
    inference(resolution,[],[f2149,f448])).

fof(f2149,plain,
    ( v4_funct_1(sK1(sK25(sK31)))
    | ~ spl44_250 ),
    inference(avatar_component_clause,[],[f2148])).

fof(f5974,plain,
    ( spl44_810
    | ~ spl44_250 ),
    inference(avatar_split_clause,[],[f5967,f2148,f5972])).

fof(f5967,plain,
    ( v4_funct_1(sK25(sK1(sK25(sK31))))
    | ~ spl44_250 ),
    inference(resolution,[],[f4946,f608])).

fof(f5953,plain,
    ( spl44_808
    | ~ spl44_560 ),
    inference(avatar_split_clause,[],[f5946,f4030,f5951])).

fof(f5951,plain,
    ( spl44_808
  <=> v1_relat_1(sK23(sK25(sK23(k1_zfmisc_1(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_808])])).

fof(f4030,plain,
    ( spl44_560
  <=> v4_funct_1(sK25(sK23(k1_zfmisc_1(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_560])])).

fof(f5946,plain,
    ( v1_relat_1(sK23(sK25(sK23(k1_zfmisc_1(sK31)))))
    | ~ spl44_560 ),
    inference(resolution,[],[f4035,f605])).

fof(f4035,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK23(k1_zfmisc_1(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_560 ),
    inference(resolution,[],[f4031,f446])).

fof(f4031,plain,
    ( v4_funct_1(sK25(sK23(k1_zfmisc_1(sK31))))
    | ~ spl44_560 ),
    inference(avatar_component_clause,[],[f4030])).

fof(f5945,plain,
    ( spl44_806
    | ~ spl44_560 ),
    inference(avatar_split_clause,[],[f5938,f4030,f5943])).

fof(f5943,plain,
    ( spl44_806
  <=> v1_funct_1(sK23(sK25(sK23(k1_zfmisc_1(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_806])])).

fof(f5938,plain,
    ( v1_funct_1(sK23(sK25(sK23(k1_zfmisc_1(sK31)))))
    | ~ spl44_560 ),
    inference(resolution,[],[f4034,f605])).

fof(f4034,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK23(k1_zfmisc_1(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_560 ),
    inference(resolution,[],[f4031,f447])).

fof(f5934,plain,
    ( spl44_804
    | ~ spl44_482 ),
    inference(avatar_split_clause,[],[f5915,f3568,f5932])).

fof(f5932,plain,
    ( spl44_804
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK17(sK17(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_804])])).

fof(f3568,plain,
    ( spl44_482
  <=> v4_funct_1(sK17(sK17(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_482])])).

fof(f5915,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK17(sK17(sK31)))))
    | ~ spl44_482 ),
    inference(resolution,[],[f3571,f605])).

fof(f3571,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK17(sK17(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_482 ),
    inference(resolution,[],[f3569,f448])).

fof(f3569,plain,
    ( v4_funct_1(sK17(sK17(sK31)))
    | ~ spl44_482 ),
    inference(avatar_component_clause,[],[f3568])).

fof(f5924,plain,
    ( spl44_802
    | ~ spl44_482 ),
    inference(avatar_split_clause,[],[f5917,f3568,f5922])).

fof(f5917,plain,
    ( v4_funct_1(sK25(sK17(sK17(sK31))))
    | ~ spl44_482 ),
    inference(resolution,[],[f3571,f608])).

fof(f5903,plain,
    ( spl44_800
    | ~ spl44_480 ),
    inference(avatar_split_clause,[],[f5884,f3558,f5901])).

fof(f5901,plain,
    ( spl44_800
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK16(sK17(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_800])])).

fof(f3558,plain,
    ( spl44_480
  <=> v4_funct_1(sK16(sK17(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_480])])).

fof(f5884,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK16(sK17(sK31)))))
    | ~ spl44_480 ),
    inference(resolution,[],[f3561,f605])).

fof(f3561,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK16(sK17(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_480 ),
    inference(resolution,[],[f3559,f448])).

fof(f3559,plain,
    ( v4_funct_1(sK16(sK17(sK31)))
    | ~ spl44_480 ),
    inference(avatar_component_clause,[],[f3558])).

fof(f5893,plain,
    ( spl44_798
    | ~ spl44_480 ),
    inference(avatar_split_clause,[],[f5886,f3558,f5891])).

fof(f5886,plain,
    ( v4_funct_1(sK25(sK16(sK17(sK31))))
    | ~ spl44_480 ),
    inference(resolution,[],[f3561,f608])).

fof(f5872,plain,
    ( spl44_796
    | ~ spl44_476 ),
    inference(avatar_split_clause,[],[f5853,f3542,f5870])).

fof(f5870,plain,
    ( spl44_796
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK4(sK17(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_796])])).

fof(f3542,plain,
    ( spl44_476
  <=> v4_funct_1(sK4(sK17(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_476])])).

fof(f5853,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK4(sK17(sK31)))))
    | ~ spl44_476 ),
    inference(resolution,[],[f3545,f605])).

fof(f3545,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK17(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_476 ),
    inference(resolution,[],[f3543,f448])).

fof(f3543,plain,
    ( v4_funct_1(sK4(sK17(sK31)))
    | ~ spl44_476 ),
    inference(avatar_component_clause,[],[f3542])).

fof(f5862,plain,
    ( spl44_794
    | ~ spl44_476 ),
    inference(avatar_split_clause,[],[f5855,f3542,f5860])).

fof(f5855,plain,
    ( v4_funct_1(sK25(sK4(sK17(sK31))))
    | ~ spl44_476 ),
    inference(resolution,[],[f3545,f608])).

fof(f5838,plain,
    ( spl44_792
    | ~ spl44_474 ),
    inference(avatar_split_clause,[],[f5819,f3532,f5836])).

fof(f5836,plain,
    ( spl44_792
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK3(sK17(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_792])])).

fof(f3532,plain,
    ( spl44_474
  <=> v4_funct_1(sK3(sK17(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_474])])).

fof(f5819,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK3(sK17(sK31)))))
    | ~ spl44_474 ),
    inference(resolution,[],[f3535,f605])).

fof(f3535,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3(sK17(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_474 ),
    inference(resolution,[],[f3533,f448])).

fof(f3533,plain,
    ( v4_funct_1(sK3(sK17(sK31)))
    | ~ spl44_474 ),
    inference(avatar_component_clause,[],[f3532])).

fof(f5828,plain,
    ( spl44_790
    | ~ spl44_474 ),
    inference(avatar_split_clause,[],[f5821,f3532,f5826])).

fof(f5821,plain,
    ( v4_funct_1(sK25(sK3(sK17(sK31))))
    | ~ spl44_474 ),
    inference(resolution,[],[f3535,f608])).

fof(f5807,plain,
    ( spl44_788
    | ~ spl44_472 ),
    inference(avatar_split_clause,[],[f5788,f3522,f5805])).

fof(f5805,plain,
    ( spl44_788
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK2(sK17(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_788])])).

fof(f3522,plain,
    ( spl44_472
  <=> v4_funct_1(sK2(sK17(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_472])])).

fof(f5788,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK2(sK17(sK31)))))
    | ~ spl44_472 ),
    inference(resolution,[],[f3525,f605])).

fof(f3525,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2(sK17(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_472 ),
    inference(resolution,[],[f3523,f448])).

fof(f3523,plain,
    ( v4_funct_1(sK2(sK17(sK31)))
    | ~ spl44_472 ),
    inference(avatar_component_clause,[],[f3522])).

fof(f5797,plain,
    ( spl44_786
    | ~ spl44_472 ),
    inference(avatar_split_clause,[],[f5790,f3522,f5795])).

fof(f5790,plain,
    ( v4_funct_1(sK25(sK2(sK17(sK31))))
    | ~ spl44_472 ),
    inference(resolution,[],[f3525,f608])).

fof(f5776,plain,
    ( spl44_784
    | ~ spl44_470 ),
    inference(avatar_split_clause,[],[f5757,f3512,f5774])).

fof(f5774,plain,
    ( spl44_784
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK1(sK17(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_784])])).

fof(f3512,plain,
    ( spl44_470
  <=> v4_funct_1(sK1(sK17(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_470])])).

fof(f5757,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK1(sK17(sK31)))))
    | ~ spl44_470 ),
    inference(resolution,[],[f3515,f605])).

fof(f3515,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK17(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_470 ),
    inference(resolution,[],[f3513,f448])).

fof(f3513,plain,
    ( v4_funct_1(sK1(sK17(sK31)))
    | ~ spl44_470 ),
    inference(avatar_component_clause,[],[f3512])).

fof(f5766,plain,
    ( spl44_782
    | ~ spl44_470 ),
    inference(avatar_split_clause,[],[f5759,f3512,f5764])).

fof(f5759,plain,
    ( v4_funct_1(sK25(sK1(sK17(sK31))))
    | ~ spl44_470 ),
    inference(resolution,[],[f3515,f608])).

fof(f5748,plain,
    ( spl44_780
    | ~ spl44_362 ),
    inference(avatar_split_clause,[],[f5741,f2896,f5746])).

fof(f5746,plain,
    ( spl44_780
  <=> v1_relat_1(sK23(sK23(k1_zfmisc_1(sK17(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_780])])).

fof(f2896,plain,
    ( spl44_362
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK17(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_362])])).

fof(f5741,plain,
    ( v1_relat_1(sK23(sK23(k1_zfmisc_1(sK17(sK31)))))
    | ~ spl44_362 ),
    inference(resolution,[],[f3409,f605])).

fof(f3409,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK23(k1_zfmisc_1(sK17(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_362 ),
    inference(resolution,[],[f2897,f446])).

fof(f2897,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK17(sK31))))
    | ~ spl44_362 ),
    inference(avatar_component_clause,[],[f2896])).

fof(f5740,plain,
    ( spl44_778
    | ~ spl44_362 ),
    inference(avatar_split_clause,[],[f5733,f2896,f5738])).

fof(f5738,plain,
    ( spl44_778
  <=> v1_funct_1(sK23(sK23(k1_zfmisc_1(sK17(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_778])])).

fof(f5733,plain,
    ( v1_funct_1(sK23(sK23(k1_zfmisc_1(sK17(sK31)))))
    | ~ spl44_362 ),
    inference(resolution,[],[f3408,f605])).

fof(f3408,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK23(k1_zfmisc_1(sK17(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_362 ),
    inference(resolution,[],[f2897,f447])).

fof(f5726,plain,
    ( spl44_776
    | ~ spl44_318 ),
    inference(avatar_split_clause,[],[f5707,f2546,f5724])).

fof(f5724,plain,
    ( spl44_776
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK4(sK4(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_776])])).

fof(f2546,plain,
    ( spl44_318
  <=> v4_funct_1(sK4(sK4(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_318])])).

fof(f5707,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK4(sK4(sK31)))))
    | ~ spl44_318 ),
    inference(resolution,[],[f3336,f605])).

fof(f3336,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK4(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_318 ),
    inference(resolution,[],[f2547,f448])).

fof(f2547,plain,
    ( v4_funct_1(sK4(sK4(sK31)))
    | ~ spl44_318 ),
    inference(avatar_component_clause,[],[f2546])).

fof(f5716,plain,
    ( spl44_774
    | ~ spl44_318 ),
    inference(avatar_split_clause,[],[f5709,f2546,f5714])).

fof(f5709,plain,
    ( v4_funct_1(sK25(sK4(sK4(sK31))))
    | ~ spl44_318 ),
    inference(resolution,[],[f3336,f608])).

fof(f5695,plain,
    ( spl44_772
    | ~ spl44_316 ),
    inference(avatar_split_clause,[],[f5676,f2539,f5693])).

fof(f5693,plain,
    ( spl44_772
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK3(sK4(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_772])])).

fof(f2539,plain,
    ( spl44_316
  <=> v4_funct_1(sK3(sK4(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_316])])).

fof(f5676,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK3(sK4(sK31)))))
    | ~ spl44_316 ),
    inference(resolution,[],[f3333,f605])).

fof(f3333,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3(sK4(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_316 ),
    inference(resolution,[],[f2540,f448])).

fof(f2540,plain,
    ( v4_funct_1(sK3(sK4(sK31)))
    | ~ spl44_316 ),
    inference(avatar_component_clause,[],[f2539])).

fof(f5685,plain,
    ( spl44_770
    | ~ spl44_316 ),
    inference(avatar_split_clause,[],[f5678,f2539,f5683])).

fof(f5678,plain,
    ( v4_funct_1(sK25(sK3(sK4(sK31))))
    | ~ spl44_316 ),
    inference(resolution,[],[f3333,f608])).

fof(f5664,plain,
    ( spl44_768
    | ~ spl44_312 ),
    inference(avatar_split_clause,[],[f5645,f2487,f5662])).

fof(f5662,plain,
    ( spl44_768
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK2(sK4(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_768])])).

fof(f2487,plain,
    ( spl44_312
  <=> v4_funct_1(sK2(sK4(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_312])])).

fof(f5645,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK2(sK4(sK31)))))
    | ~ spl44_312 ),
    inference(resolution,[],[f3330,f605])).

fof(f3330,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2(sK4(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_312 ),
    inference(resolution,[],[f2488,f448])).

fof(f2488,plain,
    ( v4_funct_1(sK2(sK4(sK31)))
    | ~ spl44_312 ),
    inference(avatar_component_clause,[],[f2487])).

fof(f5654,plain,
    ( spl44_766
    | ~ spl44_312 ),
    inference(avatar_split_clause,[],[f5647,f2487,f5652])).

fof(f5647,plain,
    ( v4_funct_1(sK25(sK2(sK4(sK31))))
    | ~ spl44_312 ),
    inference(resolution,[],[f3330,f608])).

fof(f5633,plain,
    ( spl44_764
    | ~ spl44_308 ),
    inference(avatar_split_clause,[],[f5614,f2458,f5631])).

fof(f5631,plain,
    ( spl44_764
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK1(sK4(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_764])])).

fof(f2458,plain,
    ( spl44_308
  <=> v4_funct_1(sK1(sK4(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_308])])).

fof(f5614,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK1(sK4(sK31)))))
    | ~ spl44_308 ),
    inference(resolution,[],[f3327,f605])).

fof(f3327,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK4(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_308 ),
    inference(resolution,[],[f2459,f448])).

fof(f2459,plain,
    ( v4_funct_1(sK1(sK4(sK31)))
    | ~ spl44_308 ),
    inference(avatar_component_clause,[],[f2458])).

fof(f5623,plain,
    ( spl44_762
    | ~ spl44_308 ),
    inference(avatar_split_clause,[],[f5616,f2458,f5621])).

fof(f5616,plain,
    ( v4_funct_1(sK25(sK1(sK4(sK31))))
    | ~ spl44_308 ),
    inference(resolution,[],[f3327,f608])).

fof(f5599,plain,
    ( spl44_760
    | ~ spl44_304 ),
    inference(avatar_split_clause,[],[f5580,f2445,f5597])).

fof(f5597,plain,
    ( spl44_760
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK17(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_760])])).

fof(f2445,plain,
    ( spl44_304
  <=> v4_funct_1(sK17(sK3(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_304])])).

fof(f5580,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK17(sK3(sK31)))))
    | ~ spl44_304 ),
    inference(resolution,[],[f3305,f605])).

fof(f3305,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK17(sK3(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_304 ),
    inference(resolution,[],[f2446,f448])).

fof(f2446,plain,
    ( v4_funct_1(sK17(sK3(sK31)))
    | ~ spl44_304 ),
    inference(avatar_component_clause,[],[f2445])).

fof(f5589,plain,
    ( spl44_758
    | ~ spl44_304 ),
    inference(avatar_split_clause,[],[f5582,f2445,f5587])).

fof(f5582,plain,
    ( v4_funct_1(sK25(sK17(sK3(sK31))))
    | ~ spl44_304 ),
    inference(resolution,[],[f3305,f608])).

fof(f5568,plain,
    ( spl44_756
    | ~ spl44_302 ),
    inference(avatar_split_clause,[],[f5549,f2437,f5566])).

fof(f5566,plain,
    ( spl44_756
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK16(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_756])])).

fof(f2437,plain,
    ( spl44_302
  <=> v4_funct_1(sK16(sK3(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_302])])).

fof(f5549,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK16(sK3(sK31)))))
    | ~ spl44_302 ),
    inference(resolution,[],[f3302,f605])).

fof(f3302,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK16(sK3(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_302 ),
    inference(resolution,[],[f2438,f448])).

fof(f2438,plain,
    ( v4_funct_1(sK16(sK3(sK31)))
    | ~ spl44_302 ),
    inference(avatar_component_clause,[],[f2437])).

fof(f5558,plain,
    ( spl44_754
    | ~ spl44_302 ),
    inference(avatar_split_clause,[],[f5551,f2437,f5556])).

fof(f5551,plain,
    ( v4_funct_1(sK25(sK16(sK3(sK31))))
    | ~ spl44_302 ),
    inference(resolution,[],[f3302,f608])).

fof(f5537,plain,
    ( spl44_752
    | ~ spl44_288 ),
    inference(avatar_split_clause,[],[f5518,f2363,f5535])).

fof(f5535,plain,
    ( spl44_752
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK17(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_752])])).

fof(f2363,plain,
    ( spl44_288
  <=> v4_funct_1(sK17(sK2(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_288])])).

fof(f5518,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK17(sK2(sK31)))))
    | ~ spl44_288 ),
    inference(resolution,[],[f3210,f605])).

fof(f3210,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK17(sK2(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_288 ),
    inference(resolution,[],[f2364,f448])).

fof(f2364,plain,
    ( v4_funct_1(sK17(sK2(sK31)))
    | ~ spl44_288 ),
    inference(avatar_component_clause,[],[f2363])).

fof(f5527,plain,
    ( spl44_750
    | ~ spl44_288 ),
    inference(avatar_split_clause,[],[f5520,f2363,f5525])).

fof(f5520,plain,
    ( v4_funct_1(sK25(sK17(sK2(sK31))))
    | ~ spl44_288 ),
    inference(resolution,[],[f3210,f608])).

fof(f5506,plain,
    ( spl44_748
    | ~ spl44_286 ),
    inference(avatar_split_clause,[],[f5487,f2355,f5504])).

fof(f5504,plain,
    ( spl44_748
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK16(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_748])])).

fof(f2355,plain,
    ( spl44_286
  <=> v4_funct_1(sK16(sK2(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_286])])).

fof(f5487,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK16(sK2(sK31)))))
    | ~ spl44_286 ),
    inference(resolution,[],[f3207,f605])).

fof(f3207,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK16(sK2(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_286 ),
    inference(resolution,[],[f2356,f448])).

fof(f2356,plain,
    ( v4_funct_1(sK16(sK2(sK31)))
    | ~ spl44_286 ),
    inference(avatar_component_clause,[],[f2355])).

fof(f5496,plain,
    ( spl44_746
    | ~ spl44_286 ),
    inference(avatar_split_clause,[],[f5489,f2355,f5494])).

fof(f5489,plain,
    ( v4_funct_1(sK25(sK16(sK2(sK31))))
    | ~ spl44_286 ),
    inference(resolution,[],[f3207,f608])).

fof(f5475,plain,
    ( spl44_744
    | ~ spl44_352 ),
    inference(avatar_split_clause,[],[f5468,f2781,f5473])).

fof(f5473,plain,
    ( spl44_744
  <=> v1_relat_1(sK23(sK23(k1_zfmisc_1(sK16(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_744])])).

fof(f2781,plain,
    ( spl44_352
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK16(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_352])])).

fof(f5468,plain,
    ( v1_relat_1(sK23(sK23(k1_zfmisc_1(sK16(sK31)))))
    | ~ spl44_352 ),
    inference(resolution,[],[f2865,f605])).

fof(f2865,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK23(k1_zfmisc_1(sK16(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_352 ),
    inference(resolution,[],[f2782,f446])).

fof(f2782,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK16(sK31))))
    | ~ spl44_352 ),
    inference(avatar_component_clause,[],[f2781])).

fof(f5467,plain,
    ( spl44_742
    | ~ spl44_352 ),
    inference(avatar_split_clause,[],[f5460,f2781,f5465])).

fof(f5465,plain,
    ( spl44_742
  <=> v1_funct_1(sK23(sK23(k1_zfmisc_1(sK16(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_742])])).

fof(f5460,plain,
    ( v1_funct_1(sK23(sK23(k1_zfmisc_1(sK16(sK31)))))
    | ~ spl44_352 ),
    inference(resolution,[],[f2864,f605])).

fof(f2864,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK23(k1_zfmisc_1(sK16(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_352 ),
    inference(resolution,[],[f2782,f447])).

fof(f5456,plain,
    ( spl44_740
    | ~ spl44_354 ),
    inference(avatar_split_clause,[],[f5437,f2815,f5454])).

fof(f5454,plain,
    ( spl44_740
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK25(sK17(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_740])])).

fof(f2815,plain,
    ( spl44_354
  <=> v4_funct_1(sK25(sK17(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_354])])).

fof(f5437,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK25(sK17(sK31)))))
    | ~ spl44_354 ),
    inference(resolution,[],[f2860,f605])).

fof(f2860,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK25(sK17(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_354 ),
    inference(resolution,[],[f2816,f448])).

fof(f2816,plain,
    ( v4_funct_1(sK25(sK17(sK31)))
    | ~ spl44_354 ),
    inference(avatar_component_clause,[],[f2815])).

fof(f5446,plain,
    ( spl44_738
    | ~ spl44_354 ),
    inference(avatar_split_clause,[],[f5439,f2815,f5444])).

fof(f5439,plain,
    ( v4_funct_1(sK25(sK25(sK17(sK31))))
    | ~ spl44_354 ),
    inference(resolution,[],[f2860,f608])).

fof(f5428,plain,
    ( spl44_736
    | ~ spl44_246 ),
    inference(avatar_split_clause,[],[f5409,f2094,f5426])).

fof(f5426,plain,
    ( spl44_736
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK25(sK16(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_736])])).

fof(f2094,plain,
    ( spl44_246
  <=> v4_funct_1(sK25(sK16(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_246])])).

fof(f5409,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK25(sK16(sK31)))))
    | ~ spl44_246 ),
    inference(resolution,[],[f2759,f605])).

fof(f2759,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK25(sK16(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_246 ),
    inference(resolution,[],[f2095,f448])).

fof(f2095,plain,
    ( v4_funct_1(sK25(sK16(sK31)))
    | ~ spl44_246 ),
    inference(avatar_component_clause,[],[f2094])).

fof(f5418,plain,
    ( spl44_734
    | ~ spl44_246 ),
    inference(avatar_split_clause,[],[f5411,f2094,f5416])).

fof(f5411,plain,
    ( v4_funct_1(sK25(sK25(sK16(sK31))))
    | ~ spl44_246 ),
    inference(resolution,[],[f2759,f608])).

fof(f5400,plain,
    ( spl44_732
    | ~ spl44_6
    | ~ spl44_8 ),
    inference(avatar_split_clause,[],[f5381,f718,f711,f5398])).

fof(f5398,plain,
    ( spl44_732
  <=> v2_tops_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_732])])).

fof(f5381,plain,
    ( v2_tops_1(k1_xboole_0,sK0)
    | ~ spl44_6
    | ~ spl44_8 ),
    inference(subsumption_resolution,[],[f5376,f1036])).

fof(f5376,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tops_1(k1_xboole_0,sK0)
    | ~ spl44_6
    | ~ spl44_8 ),
    inference(resolution,[],[f5354,f719])).

fof(f5354,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tops_1(X0,sK0) )
    | ~ spl44_6 ),
    inference(resolution,[],[f494,f712])).

fof(f494,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f216])).

fof(f216,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f215])).

fof(f215,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',cc2_tops_1)).

fof(f5373,plain,
    ( spl44_730
    | ~ spl44_344 ),
    inference(avatar_split_clause,[],[f5350,f2693,f5371])).

fof(f5371,plain,
    ( spl44_730
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK4(sK4(sK34))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_730])])).

fof(f2693,plain,
    ( spl44_344
  <=> v1_zfmisc_1(sK4(sK4(sK34))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_344])])).

fof(f5350,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK4(sK4(sK34)))))
    | ~ spl44_344 ),
    inference(resolution,[],[f2721,f605])).

fof(f2721,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK4(sK34))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_344 ),
    inference(resolution,[],[f2694,f499])).

fof(f2694,plain,
    ( v1_zfmisc_1(sK4(sK4(sK34)))
    | ~ spl44_344 ),
    inference(avatar_component_clause,[],[f2693])).

fof(f5364,plain,
    ( spl44_728
    | ~ spl44_344 ),
    inference(avatar_split_clause,[],[f5352,f2693,f5362])).

fof(f5362,plain,
    ( spl44_728
  <=> v1_zfmisc_1(sK25(sK4(sK4(sK34)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_728])])).

fof(f5352,plain,
    ( v1_zfmisc_1(sK25(sK4(sK4(sK34))))
    | ~ spl44_344 ),
    inference(resolution,[],[f2721,f608])).

fof(f5340,plain,
    ( spl44_726
    | ~ spl44_340 ),
    inference(avatar_split_clause,[],[f5321,f2667,f5338])).

fof(f5338,plain,
    ( spl44_726
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK1(sK4(sK34))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_726])])).

fof(f2667,plain,
    ( spl44_340
  <=> v1_zfmisc_1(sK1(sK4(sK34))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_340])])).

fof(f5321,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK1(sK4(sK34)))))
    | ~ spl44_340 ),
    inference(resolution,[],[f2688,f605])).

fof(f2688,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK4(sK34))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_340 ),
    inference(resolution,[],[f2668,f499])).

fof(f2668,plain,
    ( v1_zfmisc_1(sK1(sK4(sK34)))
    | ~ spl44_340 ),
    inference(avatar_component_clause,[],[f2667])).

fof(f5331,plain,
    ( spl44_724
    | ~ spl44_340 ),
    inference(avatar_split_clause,[],[f5323,f2667,f5329])).

fof(f5329,plain,
    ( spl44_724
  <=> v1_zfmisc_1(sK25(sK1(sK4(sK34)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_724])])).

fof(f5323,plain,
    ( v1_zfmisc_1(sK25(sK1(sK4(sK34))))
    | ~ spl44_340 ),
    inference(resolution,[],[f2688,f608])).

fof(f5311,plain,
    ( spl44_722
    | ~ spl44_336 ),
    inference(avatar_split_clause,[],[f5292,f2653,f5309])).

fof(f5309,plain,
    ( spl44_722
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK4(sK1(sK34))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_722])])).

fof(f2653,plain,
    ( spl44_336
  <=> v1_zfmisc_1(sK4(sK1(sK34))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_336])])).

fof(f5292,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK4(sK1(sK34)))))
    | ~ spl44_336 ),
    inference(resolution,[],[f2656,f605])).

fof(f2656,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK1(sK34))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_336 ),
    inference(resolution,[],[f2654,f499])).

fof(f2654,plain,
    ( v1_zfmisc_1(sK4(sK1(sK34)))
    | ~ spl44_336 ),
    inference(avatar_component_clause,[],[f2653])).

fof(f5302,plain,
    ( spl44_720
    | ~ spl44_336 ),
    inference(avatar_split_clause,[],[f5294,f2653,f5300])).

fof(f5300,plain,
    ( spl44_720
  <=> v1_zfmisc_1(sK25(sK4(sK1(sK34)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_720])])).

fof(f5294,plain,
    ( v1_zfmisc_1(sK25(sK4(sK1(sK34))))
    | ~ spl44_336 ),
    inference(resolution,[],[f2656,f608])).

fof(f5282,plain,
    ( spl44_718
    | ~ spl44_334 ),
    inference(avatar_split_clause,[],[f5263,f2631,f5280])).

fof(f5280,plain,
    ( spl44_718
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK1(sK1(sK34))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_718])])).

fof(f2631,plain,
    ( spl44_334
  <=> v1_zfmisc_1(sK1(sK1(sK34))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_334])])).

fof(f5263,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK1(sK1(sK34)))))
    | ~ spl44_334 ),
    inference(resolution,[],[f2648,f605])).

fof(f2648,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK1(sK34))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_334 ),
    inference(resolution,[],[f2632,f499])).

fof(f2632,plain,
    ( v1_zfmisc_1(sK1(sK1(sK34)))
    | ~ spl44_334 ),
    inference(avatar_component_clause,[],[f2631])).

fof(f5273,plain,
    ( spl44_716
    | ~ spl44_334 ),
    inference(avatar_split_clause,[],[f5265,f2631,f5271])).

fof(f5271,plain,
    ( spl44_716
  <=> v1_zfmisc_1(sK25(sK1(sK1(sK34)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_716])])).

fof(f5265,plain,
    ( v1_zfmisc_1(sK25(sK1(sK1(sK34))))
    | ~ spl44_334 ),
    inference(resolution,[],[f2648,f608])).

fof(f5252,plain,
    ( spl44_714
    | ~ spl44_6
    | ~ spl44_8 ),
    inference(avatar_split_clause,[],[f5233,f718,f711,f5250])).

fof(f5250,plain,
    ( spl44_714
  <=> v2_compts_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_714])])).

fof(f5233,plain,
    ( v2_compts_1(k1_xboole_0,sK0)
    | ~ spl44_6
    | ~ spl44_8 ),
    inference(subsumption_resolution,[],[f5228,f1036])).

fof(f5228,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_compts_1(k1_xboole_0,sK0)
    | ~ spl44_6
    | ~ spl44_8 ),
    inference(resolution,[],[f5222,f719])).

fof(f5222,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_compts_1(X0,sK0) )
    | ~ spl44_6 ),
    inference(resolution,[],[f493,f712])).

fof(f493,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_compts_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f214])).

fof(f214,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f213])).

fof(f213,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v2_compts_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',cc1_compts_1)).

fof(f5221,plain,
    ( spl44_290
    | spl44_712
    | ~ spl44_300 ),
    inference(avatar_split_clause,[],[f5160,f2431,f5219,f2370])).

fof(f2370,plain,
    ( spl44_290
  <=> v1_xboole_0(sK3(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_290])])).

fof(f2431,plain,
    ( spl44_300
  <=> v1_zfmisc_1(sK3(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_300])])).

fof(f5160,plain,
    ( v1_zfmisc_1(sK4(sK3(sK31)))
    | v1_xboole_0(sK3(sK31))
    | ~ spl44_300 ),
    inference(resolution,[],[f5071,f444])).

fof(f444,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f344])).

fof(f344,plain,(
    ! [X0] :
      ( ( v1_subset_1(sK4(X0),X0)
        & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f164,f343])).

fof(f343,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_subset_1(sK4(X0),X0)
        & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f164,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f117])).

fof(f117,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',rc4_subset_1)).

fof(f5071,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3(sK31)))
        | v1_zfmisc_1(X0) )
    | ~ spl44_300 ),
    inference(resolution,[],[f2432,f499])).

fof(f2432,plain,
    ( v1_zfmisc_1(sK3(sK31))
    | ~ spl44_300 ),
    inference(avatar_component_clause,[],[f2431])).

fof(f5213,plain,
    ( spl44_290
    | spl44_710
    | ~ spl44_300 ),
    inference(avatar_split_clause,[],[f5157,f2431,f5211,f2370])).

fof(f5157,plain,
    ( v1_zfmisc_1(sK1(sK3(sK31)))
    | v1_xboole_0(sK3(sK31))
    | ~ spl44_300 ),
    inference(resolution,[],[f5071,f436])).

fof(f436,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f338])).

fof(f338,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f161,f337])).

fof(f337,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f161,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f97])).

fof(f97,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',rc1_subset_1)).

fof(f5205,plain,
    ( spl44_274
    | spl44_708
    | ~ spl44_284 ),
    inference(avatar_split_clause,[],[f5140,f2349,f5203,f2288])).

fof(f2288,plain,
    ( spl44_274
  <=> v1_xboole_0(sK2(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_274])])).

fof(f2349,plain,
    ( spl44_284
  <=> v1_zfmisc_1(sK2(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_284])])).

fof(f5140,plain,
    ( v1_zfmisc_1(sK4(sK2(sK31)))
    | v1_xboole_0(sK2(sK31))
    | ~ spl44_284 ),
    inference(resolution,[],[f5069,f444])).

fof(f5069,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2(sK31)))
        | v1_zfmisc_1(X0) )
    | ~ spl44_284 ),
    inference(resolution,[],[f2350,f499])).

fof(f2350,plain,
    ( v1_zfmisc_1(sK2(sK31))
    | ~ spl44_284 ),
    inference(avatar_component_clause,[],[f2349])).

fof(f5197,plain,
    ( spl44_274
    | spl44_706
    | ~ spl44_284 ),
    inference(avatar_split_clause,[],[f5137,f2349,f5195,f2288])).

fof(f5137,plain,
    ( v1_zfmisc_1(sK1(sK2(sK31)))
    | v1_xboole_0(sK2(sK31))
    | ~ spl44_284 ),
    inference(resolution,[],[f5069,f436])).

fof(f5189,plain,
    ( spl44_248
    | spl44_704
    | ~ spl44_184 ),
    inference(avatar_split_clause,[],[f3595,f1536,f5187,f2142])).

fof(f2142,plain,
    ( spl44_248
  <=> v1_xboole_0(sK25(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_248])])).

fof(f1536,plain,
    ( spl44_184
  <=> v1_zfmisc_1(sK25(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_184])])).

fof(f3595,plain,
    ( v1_zfmisc_1(sK4(sK25(sK31)))
    | v1_xboole_0(sK25(sK31))
    | ~ spl44_184 ),
    inference(resolution,[],[f2785,f444])).

fof(f2785,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK25(sK31)))
        | v1_zfmisc_1(X0) )
    | ~ spl44_184 ),
    inference(resolution,[],[f1537,f499])).

fof(f1537,plain,
    ( v1_zfmisc_1(sK25(sK31))
    | ~ spl44_184 ),
    inference(avatar_component_clause,[],[f1536])).

fof(f5181,plain,
    ( spl44_248
    | spl44_702
    | ~ spl44_184 ),
    inference(avatar_split_clause,[],[f3592,f1536,f5179,f2142])).

fof(f3592,plain,
    ( v1_zfmisc_1(sK1(sK25(sK31)))
    | v1_xboole_0(sK25(sK31))
    | ~ spl44_184 ),
    inference(resolution,[],[f2785,f436])).

fof(f5173,plain,
    ( spl44_700
    | ~ spl44_300 ),
    inference(avatar_split_clause,[],[f5163,f2431,f5171])).

fof(f5171,plain,
    ( spl44_700
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_700])])).

fof(f5163,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK3(sK31))))
    | ~ spl44_300 ),
    inference(resolution,[],[f5071,f605])).

fof(f5153,plain,
    ( spl44_698
    | ~ spl44_284 ),
    inference(avatar_split_clause,[],[f5143,f2349,f5151])).

fof(f5151,plain,
    ( spl44_698
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_698])])).

fof(f5143,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK2(sK31))))
    | ~ spl44_284 ),
    inference(resolution,[],[f5069,f605])).

fof(f5134,plain,
    ( spl44_696
    | ~ spl44_262 ),
    inference(avatar_split_clause,[],[f5127,f2221,f5132])).

fof(f5132,plain,
    ( spl44_696
  <=> v1_relat_1(sK23(sK4(sK25(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_696])])).

fof(f5127,plain,
    ( v1_relat_1(sK23(sK4(sK25(sK31))))
    | ~ spl44_262 ),
    inference(resolution,[],[f4957,f605])).

fof(f4957,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK4(sK25(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_262 ),
    inference(resolution,[],[f2222,f446])).

fof(f5117,plain,
    ( spl44_694
    | ~ spl44_262 ),
    inference(avatar_split_clause,[],[f5110,f2221,f5115])).

fof(f5115,plain,
    ( spl44_694
  <=> v1_funct_1(sK23(sK4(sK25(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_694])])).

fof(f5110,plain,
    ( v1_funct_1(sK23(sK4(sK25(sK31))))
    | ~ spl44_262 ),
    inference(resolution,[],[f4956,f605])).

fof(f4956,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK4(sK25(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_262 ),
    inference(resolution,[],[f2222,f447])).

fof(f5109,plain,
    ( spl44_692
    | ~ spl44_260 ),
    inference(avatar_split_clause,[],[f5102,f2214,f5107])).

fof(f5107,plain,
    ( spl44_692
  <=> v1_relat_1(sK23(sK3(sK25(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_692])])).

fof(f5102,plain,
    ( v1_relat_1(sK23(sK3(sK25(sK31))))
    | ~ spl44_260 ),
    inference(resolution,[],[f4954,f605])).

fof(f4954,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK3(sK25(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_260 ),
    inference(resolution,[],[f2215,f446])).

fof(f5101,plain,
    ( spl44_690
    | ~ spl44_260 ),
    inference(avatar_split_clause,[],[f5094,f2214,f5099])).

fof(f5099,plain,
    ( spl44_690
  <=> v1_funct_1(sK23(sK3(sK25(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_690])])).

fof(f5094,plain,
    ( v1_funct_1(sK23(sK3(sK25(sK31))))
    | ~ spl44_260 ),
    inference(resolution,[],[f4953,f605])).

fof(f4953,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK3(sK25(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_260 ),
    inference(resolution,[],[f2215,f447])).

fof(f5093,plain,
    ( spl44_688
    | ~ spl44_254 ),
    inference(avatar_split_clause,[],[f5086,f2176,f5091])).

fof(f5091,plain,
    ( spl44_688
  <=> v1_relat_1(sK23(sK2(sK25(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_688])])).

fof(f5086,plain,
    ( v1_relat_1(sK23(sK2(sK25(sK31))))
    | ~ spl44_254 ),
    inference(resolution,[],[f4951,f605])).

fof(f4951,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK2(sK25(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_254 ),
    inference(resolution,[],[f2177,f446])).

fof(f5085,plain,
    ( spl44_686
    | ~ spl44_254 ),
    inference(avatar_split_clause,[],[f5078,f2176,f5083])).

fof(f5083,plain,
    ( spl44_686
  <=> v1_funct_1(sK23(sK2(sK25(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_686])])).

fof(f5078,plain,
    ( v1_funct_1(sK23(sK2(sK25(sK31))))
    | ~ spl44_254 ),
    inference(resolution,[],[f4950,f605])).

fof(f4950,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK2(sK25(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_254 ),
    inference(resolution,[],[f2177,f447])).

fof(f5070,plain,
    ( spl44_300
    | ~ spl44_444 ),
    inference(avatar_split_clause,[],[f5051,f3295,f2431])).

fof(f5051,plain,
    ( v1_zfmisc_1(sK3(sK31))
    | ~ spl44_444 ),
    inference(resolution,[],[f5045,f3296])).

fof(f5045,plain,(
    ! [X22] :
      ( ~ v1_zfmisc_1(sK25(X22))
      | v1_zfmisc_1(X22) ) ),
    inference(subsumption_resolution,[],[f5032,f609])).

fof(f609,plain,(
    ! [X0] : ~ v1_subset_1(sK25(X0),X0) ),
    inference(cnf_transformation,[],[f386])).

fof(f5032,plain,(
    ! [X22] :
      ( ~ v1_zfmisc_1(sK25(X22))
      | v1_subset_1(sK25(X22),X22)
      | v1_zfmisc_1(X22) ) ),
    inference(resolution,[],[f674,f608])).

fof(f674,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X1)
      | v1_subset_1(X1,X0)
      | v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f673,f433])).

fof(f433,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f156])).

fof(f156,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_zfmisc_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
     => ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',cc1_realset1)).

fof(f673,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f555,f434])).

fof(f434,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f158])).

fof(f158,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f157])).

fof(f157,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( v1_xboole_0(X1)
           => v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',cc3_subset_1)).

fof(f555,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f268])).

fof(f268,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,X0)
            & ~ v1_xboole_0(X1) )
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f267])).

fof(f267,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,X0)
            & ~ v1_xboole_0(X1) )
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,X0)
              & ~ v1_xboole_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',cc4_tex_2)).

fof(f5068,plain,
    ( spl44_284
    | ~ spl44_426 ),
    inference(avatar_split_clause,[],[f5049,f3200,f2349])).

fof(f5049,plain,
    ( v1_zfmisc_1(sK2(sK31))
    | ~ spl44_426 ),
    inference(resolution,[],[f5045,f3201])).

fof(f5004,plain,
    ( spl44_684
    | ~ spl44_326 ),
    inference(avatar_split_clause,[],[f4919,f2585,f5002])).

fof(f5002,plain,
    ( spl44_684
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK4(sK25(sK34))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_684])])).

fof(f2585,plain,
    ( spl44_326
  <=> v1_zfmisc_1(sK4(sK25(sK34))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_326])])).

fof(f4919,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK4(sK25(sK34)))))
    | ~ spl44_326 ),
    inference(resolution,[],[f2612,f605])).

fof(f2612,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK25(sK34))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_326 ),
    inference(resolution,[],[f2586,f499])).

fof(f2586,plain,
    ( v1_zfmisc_1(sK4(sK25(sK34)))
    | ~ spl44_326 ),
    inference(avatar_component_clause,[],[f2585])).

fof(f4997,plain,
    ( spl44_682
    | ~ spl44_212 ),
    inference(avatar_split_clause,[],[f4195,f1820,f4995])).

fof(f4995,plain,
    ( spl44_682
  <=> v1_relat_1(sK23(sK23(k1_zfmisc_1(sK25(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_682])])).

fof(f1820,plain,
    ( spl44_212
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK25(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_212])])).

fof(f4195,plain,
    ( v1_relat_1(sK23(sK23(k1_zfmisc_1(sK25(sK31)))))
    | ~ spl44_212 ),
    inference(resolution,[],[f1825,f605])).

fof(f1825,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK23(k1_zfmisc_1(sK25(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_212 ),
    inference(resolution,[],[f1821,f446])).

fof(f1821,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK25(sK31))))
    | ~ spl44_212 ),
    inference(avatar_component_clause,[],[f1820])).

fof(f4990,plain,
    ( spl44_680
    | ~ spl44_212 ),
    inference(avatar_split_clause,[],[f4191,f1820,f4988])).

fof(f4988,plain,
    ( spl44_680
  <=> v1_funct_1(sK23(sK23(k1_zfmisc_1(sK25(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_680])])).

fof(f4191,plain,
    ( v1_funct_1(sK23(sK23(k1_zfmisc_1(sK25(sK31)))))
    | ~ spl44_212 ),
    inference(resolution,[],[f1824,f605])).

fof(f1824,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK23(k1_zfmisc_1(sK25(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_212 ),
    inference(resolution,[],[f1821,f447])).

fof(f4983,plain,
    ( spl44_678
    | ~ spl44_210 ),
    inference(avatar_split_clause,[],[f4165,f1810,f4981])).

fof(f4981,plain,
    ( spl44_678
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK25(sK25(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_678])])).

fof(f1810,plain,
    ( spl44_210
  <=> v4_funct_1(sK25(sK25(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_210])])).

fof(f4165,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK25(sK25(sK31)))))
    | ~ spl44_210 ),
    inference(resolution,[],[f1813,f605])).

fof(f1813,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK25(sK25(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_210 ),
    inference(resolution,[],[f1811,f448])).

fof(f1811,plain,
    ( v4_funct_1(sK25(sK25(sK31)))
    | ~ spl44_210 ),
    inference(avatar_component_clause,[],[f1810])).

fof(f4971,plain,
    ( spl44_676
    | ~ spl44_210 ),
    inference(avatar_split_clause,[],[f4167,f1810,f4969])).

fof(f4167,plain,
    ( v4_funct_1(sK25(sK25(sK25(sK31))))
    | ~ spl44_210 ),
    inference(resolution,[],[f1813,f608])).

fof(f4964,plain,
    ( spl44_674
    | ~ spl44_184 ),
    inference(avatar_split_clause,[],[f3598,f1536,f4962])).

fof(f4962,plain,
    ( spl44_674
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK25(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_674])])).

fof(f3598,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK25(sK31))))
    | ~ spl44_184 ),
    inference(resolution,[],[f2785,f605])).

fof(f4945,plain,
    ( ~ spl44_8
    | spl44_23
    | spl44_257 ),
    inference(avatar_contradiction_clause,[],[f4944])).

fof(f4944,plain,
    ( $false
    | ~ spl44_8
    | ~ spl44_23
    | ~ spl44_257 ),
    inference(subsumption_resolution,[],[f4943,f768])).

fof(f768,plain,
    ( ~ v1_xboole_0(sK31)
    | ~ spl44_23 ),
    inference(avatar_component_clause,[],[f767])).

fof(f767,plain,
    ( spl44_23
  <=> ~ v1_xboole_0(sK31) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_23])])).

fof(f4943,plain,
    ( v1_xboole_0(sK31)
    | ~ spl44_8
    | ~ spl44_257 ),
    inference(resolution,[],[f4936,f2199])).

fof(f2199,plain,
    ( ~ v1_subset_1(k1_xboole_0,sK31)
    | ~ spl44_257 ),
    inference(avatar_component_clause,[],[f2198])).

fof(f2198,plain,
    ( spl44_257
  <=> ~ v1_subset_1(k1_xboole_0,sK31) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_257])])).

fof(f4936,plain,
    ( ! [X2] :
        ( v1_subset_1(k1_xboole_0,X2)
        | v1_xboole_0(X2) )
    | ~ spl44_8 ),
    inference(subsumption_resolution,[],[f4931,f1036])).

fof(f4931,plain,
    ( ! [X2] :
        ( v1_subset_1(k1_xboole_0,X2)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
        | v1_xboole_0(X2) )
    | ~ spl44_8 ),
    inference(resolution,[],[f434,f719])).

fof(f4929,plain,
    ( spl44_672
    | ~ spl44_326 ),
    inference(avatar_split_clause,[],[f4921,f2585,f4927])).

fof(f4927,plain,
    ( spl44_672
  <=> v1_zfmisc_1(sK25(sK4(sK25(sK34)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_672])])).

fof(f4921,plain,
    ( v1_zfmisc_1(sK25(sK4(sK25(sK34))))
    | ~ spl44_326 ),
    inference(resolution,[],[f2612,f608])).

fof(f4909,plain,
    ( spl44_670
    | ~ spl44_322 ),
    inference(avatar_split_clause,[],[f4891,f2559,f4907])).

fof(f4907,plain,
    ( spl44_670
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK1(sK25(sK34))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_670])])).

fof(f2559,plain,
    ( spl44_322
  <=> v1_zfmisc_1(sK1(sK25(sK34))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_322])])).

fof(f4891,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK1(sK25(sK34)))))
    | ~ spl44_322 ),
    inference(resolution,[],[f2580,f605])).

fof(f2580,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK25(sK34))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_322 ),
    inference(resolution,[],[f2560,f499])).

fof(f2560,plain,
    ( v1_zfmisc_1(sK1(sK25(sK34)))
    | ~ spl44_322 ),
    inference(avatar_component_clause,[],[f2559])).

fof(f4901,plain,
    ( spl44_668
    | ~ spl44_322 ),
    inference(avatar_split_clause,[],[f4893,f2559,f4899])).

fof(f4899,plain,
    ( spl44_668
  <=> v1_zfmisc_1(sK25(sK1(sK25(sK34)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_668])])).

fof(f4893,plain,
    ( v1_zfmisc_1(sK25(sK1(sK25(sK34))))
    | ~ spl44_322 ),
    inference(resolution,[],[f2580,f608])).

fof(f4879,plain,
    ( spl44_666
    | ~ spl44_298 ),
    inference(avatar_split_clause,[],[f4860,f2421,f4877])).

fof(f4877,plain,
    ( spl44_666
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK4(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_666])])).

fof(f2421,plain,
    ( spl44_298
  <=> v4_funct_1(sK4(sK3(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_298])])).

fof(f4860,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK4(sK3(sK31)))))
    | ~ spl44_298 ),
    inference(resolution,[],[f2424,f605])).

fof(f2424,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK3(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_298 ),
    inference(resolution,[],[f2422,f448])).

fof(f2422,plain,
    ( v4_funct_1(sK4(sK3(sK31)))
    | ~ spl44_298 ),
    inference(avatar_component_clause,[],[f2421])).

fof(f4869,plain,
    ( spl44_664
    | ~ spl44_298 ),
    inference(avatar_split_clause,[],[f4862,f2421,f4867])).

fof(f4862,plain,
    ( v4_funct_1(sK25(sK4(sK3(sK31))))
    | ~ spl44_298 ),
    inference(resolution,[],[f2424,f608])).

fof(f4848,plain,
    ( spl44_662
    | ~ spl44_296 ),
    inference(avatar_split_clause,[],[f4829,f2411,f4846])).

fof(f4846,plain,
    ( spl44_662
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK3(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_662])])).

fof(f2411,plain,
    ( spl44_296
  <=> v4_funct_1(sK3(sK3(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_296])])).

fof(f4829,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK3(sK3(sK31)))))
    | ~ spl44_296 ),
    inference(resolution,[],[f2414,f605])).

fof(f2414,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3(sK3(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_296 ),
    inference(resolution,[],[f2412,f448])).

fof(f2412,plain,
    ( v4_funct_1(sK3(sK3(sK31)))
    | ~ spl44_296 ),
    inference(avatar_component_clause,[],[f2411])).

fof(f4838,plain,
    ( spl44_660
    | ~ spl44_296 ),
    inference(avatar_split_clause,[],[f4831,f2411,f4836])).

fof(f4831,plain,
    ( v4_funct_1(sK25(sK3(sK3(sK31))))
    | ~ spl44_296 ),
    inference(resolution,[],[f2414,f608])).

fof(f4817,plain,
    ( spl44_658
    | ~ spl44_294 ),
    inference(avatar_split_clause,[],[f4796,f2401,f4815])).

fof(f4815,plain,
    ( spl44_658
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK2(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_658])])).

fof(f2401,plain,
    ( spl44_294
  <=> v4_funct_1(sK2(sK3(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_294])])).

fof(f4796,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK2(sK3(sK31)))))
    | ~ spl44_294 ),
    inference(resolution,[],[f2404,f605])).

fof(f2404,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2(sK3(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_294 ),
    inference(resolution,[],[f2402,f448])).

fof(f2402,plain,
    ( v4_funct_1(sK2(sK3(sK31)))
    | ~ spl44_294 ),
    inference(avatar_component_clause,[],[f2401])).

fof(f4805,plain,
    ( spl44_656
    | ~ spl44_294 ),
    inference(avatar_split_clause,[],[f4798,f2401,f4803])).

fof(f4798,plain,
    ( v4_funct_1(sK25(sK2(sK3(sK31))))
    | ~ spl44_294 ),
    inference(resolution,[],[f2404,f608])).

fof(f4784,plain,
    ( spl44_654
    | ~ spl44_292 ),
    inference(avatar_split_clause,[],[f4765,f2376,f4782])).

fof(f4782,plain,
    ( spl44_654
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK1(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_654])])).

fof(f2376,plain,
    ( spl44_292
  <=> v4_funct_1(sK1(sK3(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_292])])).

fof(f4765,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK1(sK3(sK31)))))
    | ~ spl44_292 ),
    inference(resolution,[],[f2394,f605])).

fof(f2394,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK3(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_292 ),
    inference(resolution,[],[f2377,f448])).

fof(f2377,plain,
    ( v4_funct_1(sK1(sK3(sK31)))
    | ~ spl44_292 ),
    inference(avatar_component_clause,[],[f2376])).

fof(f4774,plain,
    ( spl44_652
    | ~ spl44_292 ),
    inference(avatar_split_clause,[],[f4767,f2376,f4772])).

fof(f4767,plain,
    ( v4_funct_1(sK25(sK1(sK3(sK31))))
    | ~ spl44_292 ),
    inference(resolution,[],[f2394,f608])).

fof(f4753,plain,
    ( spl44_650
    | ~ spl44_282 ),
    inference(avatar_split_clause,[],[f4734,f2339,f4751])).

fof(f4751,plain,
    ( spl44_650
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK4(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_650])])).

fof(f2339,plain,
    ( spl44_282
  <=> v4_funct_1(sK4(sK2(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_282])])).

fof(f4734,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK4(sK2(sK31)))))
    | ~ spl44_282 ),
    inference(resolution,[],[f2342,f605])).

fof(f2342,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK2(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_282 ),
    inference(resolution,[],[f2340,f448])).

fof(f2340,plain,
    ( v4_funct_1(sK4(sK2(sK31)))
    | ~ spl44_282 ),
    inference(avatar_component_clause,[],[f2339])).

fof(f4743,plain,
    ( spl44_648
    | ~ spl44_282 ),
    inference(avatar_split_clause,[],[f4736,f2339,f4741])).

fof(f4736,plain,
    ( v4_funct_1(sK25(sK4(sK2(sK31))))
    | ~ spl44_282 ),
    inference(resolution,[],[f2342,f608])).

fof(f4722,plain,
    ( spl44_646
    | ~ spl44_280 ),
    inference(avatar_split_clause,[],[f4703,f2329,f4720])).

fof(f4720,plain,
    ( spl44_646
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK3(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_646])])).

fof(f2329,plain,
    ( spl44_280
  <=> v4_funct_1(sK3(sK2(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_280])])).

fof(f4703,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK3(sK2(sK31)))))
    | ~ spl44_280 ),
    inference(resolution,[],[f2332,f605])).

fof(f2332,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3(sK2(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_280 ),
    inference(resolution,[],[f2330,f448])).

fof(f2330,plain,
    ( v4_funct_1(sK3(sK2(sK31)))
    | ~ spl44_280 ),
    inference(avatar_component_clause,[],[f2329])).

fof(f4712,plain,
    ( spl44_644
    | ~ spl44_280 ),
    inference(avatar_split_clause,[],[f4705,f2329,f4710])).

fof(f4705,plain,
    ( v4_funct_1(sK25(sK3(sK2(sK31))))
    | ~ spl44_280 ),
    inference(resolution,[],[f2332,f608])).

fof(f4691,plain,
    ( spl44_642
    | ~ spl44_278 ),
    inference(avatar_split_clause,[],[f4670,f2319,f4689])).

fof(f4689,plain,
    ( spl44_642
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK2(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_642])])).

fof(f2319,plain,
    ( spl44_278
  <=> v4_funct_1(sK2(sK2(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_278])])).

fof(f4670,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK2(sK2(sK31)))))
    | ~ spl44_278 ),
    inference(resolution,[],[f2322,f605])).

fof(f2322,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2(sK2(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_278 ),
    inference(resolution,[],[f2320,f448])).

fof(f2320,plain,
    ( v4_funct_1(sK2(sK2(sK31)))
    | ~ spl44_278 ),
    inference(avatar_component_clause,[],[f2319])).

fof(f4679,plain,
    ( spl44_640
    | ~ spl44_278 ),
    inference(avatar_split_clause,[],[f4672,f2319,f4677])).

fof(f4672,plain,
    ( v4_funct_1(sK25(sK2(sK2(sK31))))
    | ~ spl44_278 ),
    inference(resolution,[],[f2322,f608])).

fof(f4658,plain,
    ( spl44_638
    | ~ spl44_276 ),
    inference(avatar_split_clause,[],[f4639,f2294,f4656])).

fof(f4656,plain,
    ( spl44_638
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK1(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_638])])).

fof(f2294,plain,
    ( spl44_276
  <=> v4_funct_1(sK1(sK2(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_276])])).

fof(f4639,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK1(sK2(sK31)))))
    | ~ spl44_276 ),
    inference(resolution,[],[f2312,f605])).

fof(f2312,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK2(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_276 ),
    inference(resolution,[],[f2295,f448])).

fof(f2295,plain,
    ( v4_funct_1(sK1(sK2(sK31)))
    | ~ spl44_276 ),
    inference(avatar_component_clause,[],[f2294])).

fof(f4648,plain,
    ( spl44_636
    | ~ spl44_276 ),
    inference(avatar_split_clause,[],[f4641,f2294,f4646])).

fof(f4641,plain,
    ( v4_funct_1(sK25(sK1(sK2(sK31))))
    | ~ spl44_276 ),
    inference(resolution,[],[f2312,f608])).

fof(f4627,plain,
    ( spl44_634
    | ~ spl44_272 ),
    inference(avatar_split_clause,[],[f4608,f2278,f4625])).

fof(f4625,plain,
    ( spl44_634
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK4(sK1(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_634])])).

fof(f2278,plain,
    ( spl44_272
  <=> v4_funct_1(sK4(sK1(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_272])])).

fof(f4608,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK4(sK1(sK31)))))
    | ~ spl44_272 ),
    inference(resolution,[],[f2281,f605])).

fof(f2281,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK1(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_272 ),
    inference(resolution,[],[f2279,f448])).

fof(f2279,plain,
    ( v4_funct_1(sK4(sK1(sK31)))
    | ~ spl44_272 ),
    inference(avatar_component_clause,[],[f2278])).

fof(f4617,plain,
    ( spl44_632
    | ~ spl44_272 ),
    inference(avatar_split_clause,[],[f4610,f2278,f4615])).

fof(f4610,plain,
    ( v4_funct_1(sK25(sK4(sK1(sK31))))
    | ~ spl44_272 ),
    inference(resolution,[],[f2281,f608])).

fof(f4596,plain,
    ( spl44_630
    | ~ spl44_270 ),
    inference(avatar_split_clause,[],[f4577,f2268,f4594])).

fof(f4594,plain,
    ( spl44_630
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK3(sK1(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_630])])).

fof(f2268,plain,
    ( spl44_270
  <=> v4_funct_1(sK3(sK1(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_270])])).

fof(f4577,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK3(sK1(sK31)))))
    | ~ spl44_270 ),
    inference(resolution,[],[f2271,f605])).

fof(f2271,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3(sK1(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_270 ),
    inference(resolution,[],[f2269,f448])).

fof(f2269,plain,
    ( v4_funct_1(sK3(sK1(sK31)))
    | ~ spl44_270 ),
    inference(avatar_component_clause,[],[f2268])).

fof(f4586,plain,
    ( spl44_628
    | ~ spl44_270 ),
    inference(avatar_split_clause,[],[f4579,f2268,f4584])).

fof(f4579,plain,
    ( v4_funct_1(sK25(sK3(sK1(sK31))))
    | ~ spl44_270 ),
    inference(resolution,[],[f2271,f608])).

fof(f4565,plain,
    ( spl44_626
    | ~ spl44_268 ),
    inference(avatar_split_clause,[],[f4544,f2258,f4563])).

fof(f4563,plain,
    ( spl44_626
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK2(sK1(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_626])])).

fof(f2258,plain,
    ( spl44_268
  <=> v4_funct_1(sK2(sK1(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_268])])).

fof(f4544,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK2(sK1(sK31)))))
    | ~ spl44_268 ),
    inference(resolution,[],[f2261,f605])).

fof(f2261,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2(sK1(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_268 ),
    inference(resolution,[],[f2259,f448])).

fof(f2259,plain,
    ( v4_funct_1(sK2(sK1(sK31)))
    | ~ spl44_268 ),
    inference(avatar_component_clause,[],[f2258])).

fof(f4553,plain,
    ( spl44_624
    | ~ spl44_268 ),
    inference(avatar_split_clause,[],[f4546,f2258,f4551])).

fof(f4546,plain,
    ( v4_funct_1(sK25(sK2(sK1(sK31))))
    | ~ spl44_268 ),
    inference(resolution,[],[f2261,f608])).

fof(f4532,plain,
    ( spl44_622
    | ~ spl44_266 ),
    inference(avatar_split_clause,[],[f4513,f2234,f4530])).

fof(f4530,plain,
    ( spl44_622
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK1(sK1(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_622])])).

fof(f2234,plain,
    ( spl44_266
  <=> v4_funct_1(sK1(sK1(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_266])])).

fof(f4513,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK1(sK1(sK31)))))
    | ~ spl44_266 ),
    inference(resolution,[],[f2251,f605])).

fof(f2251,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK1(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_266 ),
    inference(resolution,[],[f2235,f448])).

fof(f2235,plain,
    ( v4_funct_1(sK1(sK1(sK31)))
    | ~ spl44_266 ),
    inference(avatar_component_clause,[],[f2234])).

fof(f4522,plain,
    ( spl44_620
    | ~ spl44_266 ),
    inference(avatar_split_clause,[],[f4515,f2234,f4520])).

fof(f4515,plain,
    ( v4_funct_1(sK25(sK1(sK1(sK31))))
    | ~ spl44_266 ),
    inference(resolution,[],[f2251,f608])).

fof(f4503,plain,
    ( spl44_618
    | ~ spl44_242 ),
    inference(avatar_split_clause,[],[f4485,f2038,f4501])).

fof(f4501,plain,
    ( spl44_618
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK25(sK4(sK34))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_618])])).

fof(f2038,plain,
    ( spl44_242
  <=> v1_zfmisc_1(sK25(sK4(sK34))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_242])])).

fof(f4485,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK25(sK4(sK34)))))
    | ~ spl44_242 ),
    inference(resolution,[],[f2041,f605])).

fof(f2041,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK25(sK4(sK34))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_242 ),
    inference(resolution,[],[f2039,f499])).

fof(f2039,plain,
    ( v1_zfmisc_1(sK25(sK4(sK34)))
    | ~ spl44_242 ),
    inference(avatar_component_clause,[],[f2038])).

fof(f4495,plain,
    ( spl44_616
    | ~ spl44_242 ),
    inference(avatar_split_clause,[],[f4487,f2038,f4493])).

fof(f4493,plain,
    ( spl44_616
  <=> v1_zfmisc_1(sK25(sK25(sK4(sK34)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_616])])).

fof(f4487,plain,
    ( v1_zfmisc_1(sK25(sK25(sK4(sK34))))
    | ~ spl44_242 ),
    inference(resolution,[],[f2041,f608])).

fof(f4475,plain,
    ( spl44_614
    | ~ spl44_238 ),
    inference(avatar_split_clause,[],[f4457,f2010,f4473])).

fof(f4473,plain,
    ( spl44_614
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK25(sK1(sK34))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_614])])).

fof(f2010,plain,
    ( spl44_238
  <=> v1_zfmisc_1(sK25(sK1(sK34))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_238])])).

fof(f4457,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK25(sK1(sK34)))))
    | ~ spl44_238 ),
    inference(resolution,[],[f2013,f605])).

fof(f2013,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK25(sK1(sK34))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_238 ),
    inference(resolution,[],[f2011,f499])).

fof(f2011,plain,
    ( v1_zfmisc_1(sK25(sK1(sK34)))
    | ~ spl44_238 ),
    inference(avatar_component_clause,[],[f2010])).

fof(f4467,plain,
    ( spl44_612
    | ~ spl44_238 ),
    inference(avatar_split_clause,[],[f4459,f2010,f4465])).

fof(f4465,plain,
    ( spl44_612
  <=> v1_zfmisc_1(sK25(sK25(sK1(sK34)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_612])])).

fof(f4459,plain,
    ( v1_zfmisc_1(sK25(sK25(sK1(sK34))))
    | ~ spl44_238 ),
    inference(resolution,[],[f2013,f608])).

fof(f4447,plain,
    ( spl44_610
    | ~ spl44_234 ),
    inference(avatar_split_clause,[],[f4429,f1982,f4445])).

fof(f4445,plain,
    ( spl44_610
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK25(sK25(sK34))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_610])])).

fof(f1982,plain,
    ( spl44_234
  <=> v1_zfmisc_1(sK25(sK25(sK34))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_234])])).

fof(f4429,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK25(sK25(sK34)))))
    | ~ spl44_234 ),
    inference(resolution,[],[f1985,f605])).

fof(f1985,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK25(sK25(sK34))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_234 ),
    inference(resolution,[],[f1983,f499])).

fof(f1983,plain,
    ( v1_zfmisc_1(sK25(sK25(sK34)))
    | ~ spl44_234 ),
    inference(avatar_component_clause,[],[f1982])).

fof(f4439,plain,
    ( spl44_608
    | ~ spl44_234 ),
    inference(avatar_split_clause,[],[f4431,f1982,f4437])).

fof(f4437,plain,
    ( spl44_608
  <=> v1_zfmisc_1(sK25(sK25(sK25(sK34)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_608])])).

fof(f4431,plain,
    ( v1_zfmisc_1(sK25(sK25(sK25(sK34))))
    | ~ spl44_234 ),
    inference(resolution,[],[f1985,f608])).

fof(f4420,plain,
    ( spl44_606
    | ~ spl44_228 ),
    inference(avatar_split_clause,[],[f4413,f1944,f4418])).

fof(f4418,plain,
    ( spl44_606
  <=> v1_relat_1(sK23(sK23(k1_zfmisc_1(sK4(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_606])])).

fof(f1944,plain,
    ( spl44_228
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK4(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_228])])).

fof(f4413,plain,
    ( v1_relat_1(sK23(sK23(k1_zfmisc_1(sK4(sK31)))))
    | ~ spl44_228 ),
    inference(resolution,[],[f1949,f605])).

fof(f1949,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK23(k1_zfmisc_1(sK4(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_228 ),
    inference(resolution,[],[f1945,f446])).

fof(f1945,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK4(sK31))))
    | ~ spl44_228 ),
    inference(avatar_component_clause,[],[f1944])).

fof(f4412,plain,
    ( spl44_604
    | ~ spl44_228 ),
    inference(avatar_split_clause,[],[f4405,f1944,f4410])).

fof(f4410,plain,
    ( spl44_604
  <=> v1_funct_1(sK23(sK23(k1_zfmisc_1(sK4(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_604])])).

fof(f4405,plain,
    ( v1_funct_1(sK23(sK23(k1_zfmisc_1(sK4(sK31)))))
    | ~ spl44_228 ),
    inference(resolution,[],[f1948,f605])).

fof(f1948,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK23(k1_zfmisc_1(sK4(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_228 ),
    inference(resolution,[],[f1945,f447])).

fof(f4401,plain,
    ( spl44_602
    | ~ spl44_226 ),
    inference(avatar_split_clause,[],[f4382,f1934,f4399])).

fof(f4399,plain,
    ( spl44_602
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK25(sK4(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_602])])).

fof(f1934,plain,
    ( spl44_226
  <=> v4_funct_1(sK25(sK4(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_226])])).

fof(f4382,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK25(sK4(sK31)))))
    | ~ spl44_226 ),
    inference(resolution,[],[f1937,f605])).

fof(f1937,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK25(sK4(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_226 ),
    inference(resolution,[],[f1935,f448])).

fof(f1935,plain,
    ( v4_funct_1(sK25(sK4(sK31)))
    | ~ spl44_226 ),
    inference(avatar_component_clause,[],[f1934])).

fof(f4391,plain,
    ( spl44_600
    | ~ spl44_226 ),
    inference(avatar_split_clause,[],[f4384,f1934,f4389])).

fof(f4384,plain,
    ( v4_funct_1(sK25(sK25(sK4(sK31))))
    | ~ spl44_226 ),
    inference(resolution,[],[f1937,f608])).

fof(f4373,plain,
    ( spl44_598
    | ~ spl44_224 ),
    inference(avatar_split_clause,[],[f4366,f1913,f4371])).

fof(f4371,plain,
    ( spl44_598
  <=> v1_relat_1(sK23(sK23(k1_zfmisc_1(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_598])])).

fof(f1913,plain,
    ( spl44_224
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_224])])).

fof(f4366,plain,
    ( v1_relat_1(sK23(sK23(k1_zfmisc_1(sK3(sK31)))))
    | ~ spl44_224 ),
    inference(resolution,[],[f1918,f605])).

fof(f1918,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK23(k1_zfmisc_1(sK3(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_224 ),
    inference(resolution,[],[f1914,f446])).

fof(f1914,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK3(sK31))))
    | ~ spl44_224 ),
    inference(avatar_component_clause,[],[f1913])).

fof(f4365,plain,
    ( spl44_596
    | ~ spl44_224 ),
    inference(avatar_split_clause,[],[f4358,f1913,f4363])).

fof(f4363,plain,
    ( spl44_596
  <=> v1_funct_1(sK23(sK23(k1_zfmisc_1(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_596])])).

fof(f4358,plain,
    ( v1_funct_1(sK23(sK23(k1_zfmisc_1(sK3(sK31)))))
    | ~ spl44_224 ),
    inference(resolution,[],[f1917,f605])).

fof(f1917,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK23(k1_zfmisc_1(sK3(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_224 ),
    inference(resolution,[],[f1914,f447])).

fof(f4354,plain,
    ( spl44_594
    | ~ spl44_222 ),
    inference(avatar_split_clause,[],[f4334,f1903,f4352])).

fof(f4352,plain,
    ( spl44_594
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK25(sK3(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_594])])).

fof(f1903,plain,
    ( spl44_222
  <=> v4_funct_1(sK25(sK3(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_222])])).

fof(f4334,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK25(sK3(sK31)))))
    | ~ spl44_222 ),
    inference(resolution,[],[f1906,f605])).

fof(f1906,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK25(sK3(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_222 ),
    inference(resolution,[],[f1904,f448])).

fof(f1904,plain,
    ( v4_funct_1(sK25(sK3(sK31)))
    | ~ spl44_222 ),
    inference(avatar_component_clause,[],[f1903])).

fof(f4343,plain,
    ( spl44_592
    | ~ spl44_222 ),
    inference(avatar_split_clause,[],[f4336,f1903,f4341])).

fof(f4336,plain,
    ( v4_funct_1(sK25(sK25(sK3(sK31))))
    | ~ spl44_222 ),
    inference(resolution,[],[f1906,f608])).

fof(f4325,plain,
    ( spl44_590
    | ~ spl44_220 ),
    inference(avatar_split_clause,[],[f4318,f1882,f4323])).

fof(f4323,plain,
    ( spl44_590
  <=> v1_relat_1(sK23(sK23(k1_zfmisc_1(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_590])])).

fof(f1882,plain,
    ( spl44_220
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_220])])).

fof(f4318,plain,
    ( v1_relat_1(sK23(sK23(k1_zfmisc_1(sK2(sK31)))))
    | ~ spl44_220 ),
    inference(resolution,[],[f1887,f605])).

fof(f1887,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK23(k1_zfmisc_1(sK2(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_220 ),
    inference(resolution,[],[f1883,f446])).

fof(f1883,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK2(sK31))))
    | ~ spl44_220 ),
    inference(avatar_component_clause,[],[f1882])).

fof(f4317,plain,
    ( spl44_588
    | ~ spl44_220 ),
    inference(avatar_split_clause,[],[f4310,f1882,f4315])).

fof(f4315,plain,
    ( spl44_588
  <=> v1_funct_1(sK23(sK23(k1_zfmisc_1(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_588])])).

fof(f4310,plain,
    ( v1_funct_1(sK23(sK23(k1_zfmisc_1(sK2(sK31)))))
    | ~ spl44_220 ),
    inference(resolution,[],[f1886,f605])).

fof(f1886,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK23(k1_zfmisc_1(sK2(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_220 ),
    inference(resolution,[],[f1883,f447])).

fof(f4305,plain,
    ( spl44_586
    | ~ spl44_218 ),
    inference(avatar_split_clause,[],[f4254,f1872,f4303])).

fof(f4303,plain,
    ( spl44_586
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK25(sK2(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_586])])).

fof(f1872,plain,
    ( spl44_218
  <=> v4_funct_1(sK25(sK2(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_218])])).

fof(f4254,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK25(sK2(sK31)))))
    | ~ spl44_218 ),
    inference(resolution,[],[f1875,f605])).

fof(f1875,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK25(sK2(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_218 ),
    inference(resolution,[],[f1873,f448])).

fof(f1873,plain,
    ( v4_funct_1(sK25(sK2(sK31)))
    | ~ spl44_218 ),
    inference(avatar_component_clause,[],[f1872])).

fof(f4293,plain,
    ( spl44_584
    | ~ spl44_218 ),
    inference(avatar_split_clause,[],[f4256,f1872,f4291])).

fof(f4256,plain,
    ( v4_funct_1(sK25(sK25(sK2(sK31))))
    | ~ spl44_218 ),
    inference(resolution,[],[f1875,f608])).

fof(f4286,plain,
    ( spl44_580
    | spl44_582 ),
    inference(avatar_split_clause,[],[f4258,f4284,f4278])).

fof(f4278,plain,
    ( spl44_580
  <=> ! [X2] :
        ( ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_580])])).

fof(f4284,plain,
    ( spl44_582
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_582])])).

fof(f4258,plain,(
    ! [X2] :
      ( v1_funct_1(k1_xboole_0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f593,f1036])).

fof(f593,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_funct_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f312])).

fof(f312,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f311])).

fof(f311,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',cc3_funct_1)).

fof(f4245,plain,
    ( spl44_578
    | ~ spl44_216 ),
    inference(avatar_split_clause,[],[f4238,f1851,f4243])).

fof(f4243,plain,
    ( spl44_578
  <=> v1_relat_1(sK23(sK23(k1_zfmisc_1(sK1(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_578])])).

fof(f1851,plain,
    ( spl44_216
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK1(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_216])])).

fof(f4238,plain,
    ( v1_relat_1(sK23(sK23(k1_zfmisc_1(sK1(sK31)))))
    | ~ spl44_216 ),
    inference(resolution,[],[f1856,f605])).

fof(f1856,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK23(k1_zfmisc_1(sK1(sK31))))
        | v1_relat_1(X2) )
    | ~ spl44_216 ),
    inference(resolution,[],[f1852,f446])).

fof(f1852,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK1(sK31))))
    | ~ spl44_216 ),
    inference(avatar_component_clause,[],[f1851])).

fof(f4237,plain,
    ( spl44_576
    | ~ spl44_216 ),
    inference(avatar_split_clause,[],[f4230,f1851,f4235])).

fof(f4235,plain,
    ( spl44_576
  <=> v1_funct_1(sK23(sK23(k1_zfmisc_1(sK1(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_576])])).

fof(f4230,plain,
    ( v1_funct_1(sK23(sK23(k1_zfmisc_1(sK1(sK31)))))
    | ~ spl44_216 ),
    inference(resolution,[],[f1855,f605])).

fof(f1855,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK23(k1_zfmisc_1(sK1(sK31))))
        | v1_funct_1(X1) )
    | ~ spl44_216 ),
    inference(resolution,[],[f1852,f447])).

fof(f4226,plain,
    ( spl44_574
    | ~ spl44_214 ),
    inference(avatar_split_clause,[],[f4207,f1841,f4224])).

fof(f4224,plain,
    ( spl44_574
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK25(sK1(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_574])])).

fof(f1841,plain,
    ( spl44_214
  <=> v4_funct_1(sK25(sK1(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_214])])).

fof(f4207,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK25(sK1(sK31)))))
    | ~ spl44_214 ),
    inference(resolution,[],[f1844,f605])).

fof(f1844,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK25(sK1(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_214 ),
    inference(resolution,[],[f1842,f448])).

fof(f1842,plain,
    ( v4_funct_1(sK25(sK1(sK31)))
    | ~ spl44_214 ),
    inference(avatar_component_clause,[],[f1841])).

fof(f4216,plain,
    ( spl44_572
    | ~ spl44_214 ),
    inference(avatar_split_clause,[],[f4209,f1841,f4214])).

fof(f4209,plain,
    ( v4_funct_1(sK25(sK25(sK1(sK31))))
    | ~ spl44_214 ),
    inference(resolution,[],[f1844,f608])).

fof(f4155,plain,
    ( spl44_570
    | ~ spl44_200 ),
    inference(avatar_split_clause,[],[f4137,f1656,f4153])).

fof(f4153,plain,
    ( spl44_570
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK23(k1_zfmisc_1(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_570])])).

fof(f1656,plain,
    ( spl44_200
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_200])])).

fof(f4137,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK23(k1_zfmisc_1(sK31)))))
    | ~ spl44_200 ),
    inference(resolution,[],[f1681,f605])).

fof(f1681,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK23(k1_zfmisc_1(sK31))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_200 ),
    inference(resolution,[],[f1657,f499])).

fof(f1657,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK31)))
    | ~ spl44_200 ),
    inference(avatar_component_clause,[],[f1656])).

fof(f4147,plain,
    ( spl44_568
    | ~ spl44_200 ),
    inference(avatar_split_clause,[],[f4139,f1656,f4145])).

fof(f4145,plain,
    ( spl44_568
  <=> v1_zfmisc_1(sK25(sK23(k1_zfmisc_1(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_568])])).

fof(f4139,plain,
    ( v1_zfmisc_1(sK25(sK23(k1_zfmisc_1(sK31))))
    | ~ spl44_200 ),
    inference(resolution,[],[f1681,f608])).

fof(f4072,plain,
    ( spl44_566
    | ~ spl44_178 ),
    inference(avatar_split_clause,[],[f4054,f1498,f4070])).

fof(f4070,plain,
    ( spl44_566
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK23(k1_zfmisc_1(sK34))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_566])])).

fof(f1498,plain,
    ( spl44_178
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK34))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_178])])).

fof(f4054,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK23(k1_zfmisc_1(sK34)))))
    | ~ spl44_178 ),
    inference(resolution,[],[f1517,f605])).

fof(f1517,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK23(k1_zfmisc_1(sK34))))
        | v1_zfmisc_1(X0) )
    | ~ spl44_178 ),
    inference(resolution,[],[f1499,f499])).

fof(f1499,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK34)))
    | ~ spl44_178 ),
    inference(avatar_component_clause,[],[f1498])).

fof(f4064,plain,
    ( spl44_564
    | ~ spl44_178 ),
    inference(avatar_split_clause,[],[f4056,f1498,f4062])).

fof(f4062,plain,
    ( spl44_564
  <=> v1_zfmisc_1(sK25(sK23(k1_zfmisc_1(sK34)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_564])])).

fof(f4056,plain,
    ( v1_zfmisc_1(sK25(sK23(k1_zfmisc_1(sK34))))
    | ~ spl44_178 ),
    inference(resolution,[],[f1517,f608])).

fof(f4042,plain,
    ( spl44_562
    | ~ spl44_120 ),
    inference(avatar_split_clause,[],[f4023,f1207,f4040])).

fof(f4040,plain,
    ( spl44_562
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK23(k1_zfmisc_1(sK31))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_562])])).

fof(f1207,plain,
    ( spl44_120
  <=> v4_funct_1(sK23(k1_zfmisc_1(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_120])])).

fof(f4023,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK23(k1_zfmisc_1(sK31)))))
    | ~ spl44_120 ),
    inference(resolution,[],[f1257,f605])).

fof(f1257,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK23(k1_zfmisc_1(sK31))))
        | v4_funct_1(X0) )
    | ~ spl44_120 ),
    inference(resolution,[],[f1208,f448])).

fof(f1208,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK31)))
    | ~ spl44_120 ),
    inference(avatar_component_clause,[],[f1207])).

fof(f4032,plain,
    ( spl44_560
    | ~ spl44_120 ),
    inference(avatar_split_clause,[],[f4025,f1207,f4030])).

fof(f4025,plain,
    ( v4_funct_1(sK25(sK23(k1_zfmisc_1(sK31))))
    | ~ spl44_120 ),
    inference(resolution,[],[f1257,f608])).

fof(f3928,plain,
    ( spl44_558
    | ~ spl44_482 ),
    inference(avatar_split_clause,[],[f3921,f3568,f3926])).

fof(f3926,plain,
    ( spl44_558
  <=> v1_relat_1(sK23(sK17(sK17(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_558])])).

fof(f3921,plain,
    ( v1_relat_1(sK23(sK17(sK17(sK31))))
    | ~ spl44_482 ),
    inference(resolution,[],[f3573,f605])).

fof(f3573,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK17(sK17(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_482 ),
    inference(resolution,[],[f3569,f446])).

fof(f3920,plain,
    ( spl44_556
    | ~ spl44_482 ),
    inference(avatar_split_clause,[],[f3913,f3568,f3918])).

fof(f3918,plain,
    ( spl44_556
  <=> v1_funct_1(sK23(sK17(sK17(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_556])])).

fof(f3913,plain,
    ( v1_funct_1(sK23(sK17(sK17(sK31))))
    | ~ spl44_482 ),
    inference(resolution,[],[f3572,f605])).

fof(f3572,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK17(sK17(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_482 ),
    inference(resolution,[],[f3569,f447])).

fof(f3912,plain,
    ( spl44_554
    | ~ spl44_480 ),
    inference(avatar_split_clause,[],[f3905,f3558,f3910])).

fof(f3910,plain,
    ( spl44_554
  <=> v1_relat_1(sK23(sK16(sK17(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_554])])).

fof(f3905,plain,
    ( v1_relat_1(sK23(sK16(sK17(sK31))))
    | ~ spl44_480 ),
    inference(resolution,[],[f3563,f605])).

fof(f3563,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK16(sK17(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_480 ),
    inference(resolution,[],[f3559,f446])).

fof(f3904,plain,
    ( spl44_552
    | ~ spl44_480 ),
    inference(avatar_split_clause,[],[f3897,f3558,f3902])).

fof(f3902,plain,
    ( spl44_552
  <=> v1_funct_1(sK23(sK16(sK17(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_552])])).

fof(f3897,plain,
    ( v1_funct_1(sK23(sK16(sK17(sK31))))
    | ~ spl44_480 ),
    inference(resolution,[],[f3562,f605])).

fof(f3562,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK16(sK17(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_480 ),
    inference(resolution,[],[f3559,f447])).

fof(f3895,plain,
    ( spl44_550
    | ~ spl44_476 ),
    inference(avatar_split_clause,[],[f3888,f3542,f3893])).

fof(f3893,plain,
    ( spl44_550
  <=> v1_relat_1(sK23(sK4(sK17(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_550])])).

fof(f3888,plain,
    ( v1_relat_1(sK23(sK4(sK17(sK31))))
    | ~ spl44_476 ),
    inference(resolution,[],[f3547,f605])).

fof(f3547,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK4(sK17(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_476 ),
    inference(resolution,[],[f3543,f446])).

fof(f3887,plain,
    ( spl44_548
    | ~ spl44_476 ),
    inference(avatar_split_clause,[],[f3880,f3542,f3885])).

fof(f3885,plain,
    ( spl44_548
  <=> v1_funct_1(sK23(sK4(sK17(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_548])])).

fof(f3880,plain,
    ( v1_funct_1(sK23(sK4(sK17(sK31))))
    | ~ spl44_476 ),
    inference(resolution,[],[f3546,f605])).

fof(f3546,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK4(sK17(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_476 ),
    inference(resolution,[],[f3543,f447])).

fof(f3879,plain,
    ( spl44_546
    | ~ spl44_474 ),
    inference(avatar_split_clause,[],[f3872,f3532,f3877])).

fof(f3877,plain,
    ( spl44_546
  <=> v1_relat_1(sK23(sK3(sK17(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_546])])).

fof(f3872,plain,
    ( v1_relat_1(sK23(sK3(sK17(sK31))))
    | ~ spl44_474 ),
    inference(resolution,[],[f3537,f605])).

fof(f3537,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK3(sK17(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_474 ),
    inference(resolution,[],[f3533,f446])).

fof(f3871,plain,
    ( spl44_544
    | ~ spl44_474 ),
    inference(avatar_split_clause,[],[f3864,f3532,f3869])).

fof(f3869,plain,
    ( spl44_544
  <=> v1_funct_1(sK23(sK3(sK17(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_544])])).

fof(f3864,plain,
    ( v1_funct_1(sK23(sK3(sK17(sK31))))
    | ~ spl44_474 ),
    inference(resolution,[],[f3536,f605])).

fof(f3536,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK3(sK17(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_474 ),
    inference(resolution,[],[f3533,f447])).

fof(f3863,plain,
    ( spl44_542
    | ~ spl44_472 ),
    inference(avatar_split_clause,[],[f3856,f3522,f3861])).

fof(f3861,plain,
    ( spl44_542
  <=> v1_relat_1(sK23(sK2(sK17(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_542])])).

fof(f3856,plain,
    ( v1_relat_1(sK23(sK2(sK17(sK31))))
    | ~ spl44_472 ),
    inference(resolution,[],[f3527,f605])).

fof(f3527,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK2(sK17(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_472 ),
    inference(resolution,[],[f3523,f446])).

fof(f3855,plain,
    ( spl44_540
    | ~ spl44_472 ),
    inference(avatar_split_clause,[],[f3848,f3522,f3853])).

fof(f3853,plain,
    ( spl44_540
  <=> v1_funct_1(sK23(sK2(sK17(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_540])])).

fof(f3848,plain,
    ( v1_funct_1(sK23(sK2(sK17(sK31))))
    | ~ spl44_472 ),
    inference(resolution,[],[f3526,f605])).

fof(f3526,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK2(sK17(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_472 ),
    inference(resolution,[],[f3523,f447])).

fof(f3847,plain,
    ( spl44_538
    | ~ spl44_470 ),
    inference(avatar_split_clause,[],[f3840,f3512,f3845])).

fof(f3845,plain,
    ( spl44_538
  <=> v1_relat_1(sK23(sK1(sK17(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_538])])).

fof(f3840,plain,
    ( v1_relat_1(sK23(sK1(sK17(sK31))))
    | ~ spl44_470 ),
    inference(resolution,[],[f3517,f605])).

fof(f3517,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK1(sK17(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_470 ),
    inference(resolution,[],[f3513,f446])).

fof(f3839,plain,
    ( spl44_536
    | ~ spl44_470 ),
    inference(avatar_split_clause,[],[f3832,f3512,f3837])).

fof(f3837,plain,
    ( spl44_536
  <=> v1_funct_1(sK23(sK1(sK17(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_536])])).

fof(f3832,plain,
    ( v1_funct_1(sK23(sK1(sK17(sK31))))
    | ~ spl44_470 ),
    inference(resolution,[],[f3516,f605])).

fof(f3516,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK1(sK17(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_470 ),
    inference(resolution,[],[f3513,f447])).

fof(f3828,plain,
    ( spl44_534
    | ~ spl44_204
    | spl44_307 ),
    inference(avatar_split_clause,[],[f3805,f2449,f1671,f3826])).

fof(f1671,plain,
    ( spl44_204
  <=> v1_zfmisc_1(sK4(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_204])])).

fof(f2449,plain,
    ( spl44_307
  <=> ~ v1_xboole_0(sK4(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_307])])).

fof(f3805,plain,
    ( v1_zfmisc_1(sK4(sK4(sK31)))
    | ~ spl44_204
    | ~ spl44_307 ),
    inference(subsumption_resolution,[],[f3798,f2450])).

fof(f2450,plain,
    ( ~ v1_xboole_0(sK4(sK31))
    | ~ spl44_307 ),
    inference(avatar_component_clause,[],[f2449])).

fof(f3798,plain,
    ( v1_zfmisc_1(sK4(sK4(sK31)))
    | v1_xboole_0(sK4(sK31))
    | ~ spl44_204 ),
    inference(resolution,[],[f3458,f444])).

fof(f3458,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK31)))
        | v1_zfmisc_1(X0) )
    | ~ spl44_204 ),
    inference(resolution,[],[f1672,f499])).

fof(f1672,plain,
    ( v1_zfmisc_1(sK4(sK31))
    | ~ spl44_204 ),
    inference(avatar_component_clause,[],[f1671])).

fof(f3820,plain,
    ( spl44_532
    | ~ spl44_204
    | spl44_307 ),
    inference(avatar_split_clause,[],[f3804,f2449,f1671,f3818])).

fof(f3804,plain,
    ( v1_zfmisc_1(sK1(sK4(sK31)))
    | ~ spl44_204
    | ~ spl44_307 ),
    inference(subsumption_resolution,[],[f3795,f2450])).

fof(f3795,plain,
    ( v1_zfmisc_1(sK1(sK4(sK31)))
    | v1_xboole_0(sK4(sK31))
    | ~ spl44_204 ),
    inference(resolution,[],[f3458,f436])).

fof(f3813,plain,
    ( spl44_530
    | ~ spl44_204 ),
    inference(avatar_split_clause,[],[f3801,f1671,f3811])).

fof(f3811,plain,
    ( spl44_530
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK4(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_530])])).

fof(f3801,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK4(sK31))))
    | ~ spl44_204 ),
    inference(resolution,[],[f3458,f605])).

fof(f3792,plain,
    ( spl44_528
    | ~ spl44_318 ),
    inference(avatar_split_clause,[],[f3785,f2546,f3790])).

fof(f3790,plain,
    ( spl44_528
  <=> v1_relat_1(sK23(sK4(sK4(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_528])])).

fof(f3785,plain,
    ( v1_relat_1(sK23(sK4(sK4(sK31))))
    | ~ spl44_318 ),
    inference(resolution,[],[f3338,f605])).

fof(f3338,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK4(sK4(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_318 ),
    inference(resolution,[],[f2547,f446])).

fof(f3784,plain,
    ( spl44_526
    | ~ spl44_318 ),
    inference(avatar_split_clause,[],[f3777,f2546,f3782])).

fof(f3782,plain,
    ( spl44_526
  <=> v1_funct_1(sK23(sK4(sK4(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_526])])).

fof(f3777,plain,
    ( v1_funct_1(sK23(sK4(sK4(sK31))))
    | ~ spl44_318 ),
    inference(resolution,[],[f3337,f605])).

fof(f3337,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK4(sK4(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_318 ),
    inference(resolution,[],[f2547,f447])).

fof(f3776,plain,
    ( spl44_524
    | ~ spl44_316 ),
    inference(avatar_split_clause,[],[f3769,f2539,f3774])).

fof(f3774,plain,
    ( spl44_524
  <=> v1_relat_1(sK23(sK3(sK4(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_524])])).

fof(f3769,plain,
    ( v1_relat_1(sK23(sK3(sK4(sK31))))
    | ~ spl44_316 ),
    inference(resolution,[],[f3335,f605])).

fof(f3335,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK3(sK4(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_316 ),
    inference(resolution,[],[f2540,f446])).

fof(f3768,plain,
    ( spl44_522
    | ~ spl44_316 ),
    inference(avatar_split_clause,[],[f3761,f2539,f3766])).

fof(f3766,plain,
    ( spl44_522
  <=> v1_funct_1(sK23(sK3(sK4(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_522])])).

fof(f3761,plain,
    ( v1_funct_1(sK23(sK3(sK4(sK31))))
    | ~ spl44_316 ),
    inference(resolution,[],[f3334,f605])).

fof(f3334,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK3(sK4(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_316 ),
    inference(resolution,[],[f2540,f447])).

fof(f3760,plain,
    ( spl44_520
    | ~ spl44_312 ),
    inference(avatar_split_clause,[],[f3753,f2487,f3758])).

fof(f3758,plain,
    ( spl44_520
  <=> v1_relat_1(sK23(sK2(sK4(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_520])])).

fof(f3753,plain,
    ( v1_relat_1(sK23(sK2(sK4(sK31))))
    | ~ spl44_312 ),
    inference(resolution,[],[f3332,f605])).

fof(f3332,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK2(sK4(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_312 ),
    inference(resolution,[],[f2488,f446])).

fof(f3751,plain,
    ( spl44_518
    | ~ spl44_312 ),
    inference(avatar_split_clause,[],[f3744,f2487,f3749])).

fof(f3749,plain,
    ( spl44_518
  <=> v1_funct_1(sK23(sK2(sK4(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_518])])).

fof(f3744,plain,
    ( v1_funct_1(sK23(sK2(sK4(sK31))))
    | ~ spl44_312 ),
    inference(resolution,[],[f3331,f605])).

fof(f3331,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK2(sK4(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_312 ),
    inference(resolution,[],[f2488,f447])).

fof(f3743,plain,
    ( spl44_516
    | ~ spl44_308 ),
    inference(avatar_split_clause,[],[f3736,f2458,f3741])).

fof(f3741,plain,
    ( spl44_516
  <=> v1_relat_1(sK23(sK1(sK4(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_516])])).

fof(f3736,plain,
    ( v1_relat_1(sK23(sK1(sK4(sK31))))
    | ~ spl44_308 ),
    inference(resolution,[],[f3329,f605])).

fof(f3329,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK1(sK4(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_308 ),
    inference(resolution,[],[f2459,f446])).

fof(f3735,plain,
    ( spl44_514
    | ~ spl44_308 ),
    inference(avatar_split_clause,[],[f3728,f2458,f3733])).

fof(f3733,plain,
    ( spl44_514
  <=> v1_funct_1(sK23(sK1(sK4(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_514])])).

fof(f3728,plain,
    ( v1_funct_1(sK23(sK1(sK4(sK31))))
    | ~ spl44_308 ),
    inference(resolution,[],[f3328,f605])).

fof(f3328,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK1(sK4(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_308 ),
    inference(resolution,[],[f2459,f447])).

fof(f3727,plain,
    ( spl44_512
    | ~ spl44_304 ),
    inference(avatar_split_clause,[],[f3720,f2445,f3725])).

fof(f3725,plain,
    ( spl44_512
  <=> v1_relat_1(sK23(sK17(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_512])])).

fof(f3720,plain,
    ( v1_relat_1(sK23(sK17(sK3(sK31))))
    | ~ spl44_304 ),
    inference(resolution,[],[f3307,f605])).

fof(f3307,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK17(sK3(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_304 ),
    inference(resolution,[],[f2446,f446])).

fof(f3719,plain,
    ( spl44_510
    | ~ spl44_304 ),
    inference(avatar_split_clause,[],[f3712,f2445,f3717])).

fof(f3717,plain,
    ( spl44_510
  <=> v1_funct_1(sK23(sK17(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_510])])).

fof(f3712,plain,
    ( v1_funct_1(sK23(sK17(sK3(sK31))))
    | ~ spl44_304 ),
    inference(resolution,[],[f3306,f605])).

fof(f3306,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK17(sK3(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_304 ),
    inference(resolution,[],[f2446,f447])).

fof(f3711,plain,
    ( spl44_508
    | ~ spl44_302 ),
    inference(avatar_split_clause,[],[f3704,f2437,f3709])).

fof(f3709,plain,
    ( spl44_508
  <=> v1_relat_1(sK23(sK16(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_508])])).

fof(f3704,plain,
    ( v1_relat_1(sK23(sK16(sK3(sK31))))
    | ~ spl44_302 ),
    inference(resolution,[],[f3304,f605])).

fof(f3304,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK16(sK3(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_302 ),
    inference(resolution,[],[f2438,f446])).

fof(f3703,plain,
    ( spl44_506
    | ~ spl44_302 ),
    inference(avatar_split_clause,[],[f3696,f2437,f3701])).

fof(f3701,plain,
    ( spl44_506
  <=> v1_funct_1(sK23(sK16(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_506])])).

fof(f3696,plain,
    ( v1_funct_1(sK23(sK16(sK3(sK31))))
    | ~ spl44_302 ),
    inference(resolution,[],[f3303,f605])).

fof(f3303,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK16(sK3(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_302 ),
    inference(resolution,[],[f2438,f447])).

fof(f3695,plain,
    ( spl44_504
    | ~ spl44_288 ),
    inference(avatar_split_clause,[],[f3688,f2363,f3693])).

fof(f3693,plain,
    ( spl44_504
  <=> v1_relat_1(sK23(sK17(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_504])])).

fof(f3688,plain,
    ( v1_relat_1(sK23(sK17(sK2(sK31))))
    | ~ spl44_288 ),
    inference(resolution,[],[f3212,f605])).

fof(f3212,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK17(sK2(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_288 ),
    inference(resolution,[],[f2364,f446])).

fof(f3687,plain,
    ( spl44_502
    | ~ spl44_288 ),
    inference(avatar_split_clause,[],[f3680,f2363,f3685])).

fof(f3685,plain,
    ( spl44_502
  <=> v1_funct_1(sK23(sK17(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_502])])).

fof(f3680,plain,
    ( v1_funct_1(sK23(sK17(sK2(sK31))))
    | ~ spl44_288 ),
    inference(resolution,[],[f3211,f605])).

fof(f3211,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK17(sK2(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_288 ),
    inference(resolution,[],[f2364,f447])).

fof(f3679,plain,
    ( spl44_500
    | ~ spl44_286 ),
    inference(avatar_split_clause,[],[f3672,f2355,f3677])).

fof(f3677,plain,
    ( spl44_500
  <=> v1_relat_1(sK23(sK16(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_500])])).

fof(f3672,plain,
    ( v1_relat_1(sK23(sK16(sK2(sK31))))
    | ~ spl44_286 ),
    inference(resolution,[],[f3209,f605])).

fof(f3209,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK16(sK2(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_286 ),
    inference(resolution,[],[f2356,f446])).

fof(f3671,plain,
    ( spl44_498
    | ~ spl44_286 ),
    inference(avatar_split_clause,[],[f3664,f2355,f3669])).

fof(f3669,plain,
    ( spl44_498
  <=> v1_funct_1(sK23(sK16(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_498])])).

fof(f3664,plain,
    ( v1_funct_1(sK23(sK16(sK2(sK31))))
    | ~ spl44_286 ),
    inference(resolution,[],[f3208,f605])).

fof(f3208,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK16(sK2(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_286 ),
    inference(resolution,[],[f2356,f447])).

fof(f3661,plain,
    ( spl44_496
    | ~ spl44_202
    | spl44_265 ),
    inference(avatar_split_clause,[],[f3638,f2225,f1663,f3659])).

fof(f1663,plain,
    ( spl44_202
  <=> v1_zfmisc_1(sK1(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_202])])).

fof(f2225,plain,
    ( spl44_265
  <=> ~ v1_xboole_0(sK1(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_265])])).

fof(f3638,plain,
    ( v1_zfmisc_1(sK4(sK1(sK31)))
    | ~ spl44_202
    | ~ spl44_265 ),
    inference(subsumption_resolution,[],[f3631,f2226])).

fof(f2226,plain,
    ( ~ v1_xboole_0(sK1(sK31))
    | ~ spl44_265 ),
    inference(avatar_component_clause,[],[f2225])).

fof(f3631,plain,
    ( v1_zfmisc_1(sK4(sK1(sK31)))
    | v1_xboole_0(sK1(sK31))
    | ~ spl44_202 ),
    inference(resolution,[],[f2902,f444])).

fof(f2902,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK31)))
        | v1_zfmisc_1(X0) )
    | ~ spl44_202 ),
    inference(resolution,[],[f1664,f499])).

fof(f1664,plain,
    ( v1_zfmisc_1(sK1(sK31))
    | ~ spl44_202 ),
    inference(avatar_component_clause,[],[f1663])).

fof(f3653,plain,
    ( spl44_494
    | ~ spl44_202
    | spl44_265 ),
    inference(avatar_split_clause,[],[f3637,f2225,f1663,f3651])).

fof(f3637,plain,
    ( v1_zfmisc_1(sK1(sK1(sK31)))
    | ~ spl44_202
    | ~ spl44_265 ),
    inference(subsumption_resolution,[],[f3628,f2226])).

fof(f3628,plain,
    ( v1_zfmisc_1(sK1(sK1(sK31)))
    | v1_xboole_0(sK1(sK31))
    | ~ spl44_202 ),
    inference(resolution,[],[f2902,f436])).

fof(f3646,plain,
    ( spl44_492
    | ~ spl44_202 ),
    inference(avatar_split_clause,[],[f3634,f1663,f3644])).

fof(f3644,plain,
    ( spl44_492
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK1(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_492])])).

fof(f3634,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK1(sK31))))
    | ~ spl44_202 ),
    inference(resolution,[],[f2902,f605])).

fof(f3625,plain,
    ( spl44_490
    | ~ spl44_354 ),
    inference(avatar_split_clause,[],[f3618,f2815,f3623])).

fof(f3623,plain,
    ( spl44_490
  <=> v1_relat_1(sK23(sK25(sK17(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_490])])).

fof(f3618,plain,
    ( v1_relat_1(sK23(sK25(sK17(sK31))))
    | ~ spl44_354 ),
    inference(resolution,[],[f2862,f605])).

fof(f2862,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK17(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_354 ),
    inference(resolution,[],[f2816,f446])).

fof(f3617,plain,
    ( spl44_488
    | ~ spl44_354 ),
    inference(avatar_split_clause,[],[f3610,f2815,f3615])).

fof(f3615,plain,
    ( spl44_488
  <=> v1_funct_1(sK23(sK25(sK17(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_488])])).

fof(f3610,plain,
    ( v1_funct_1(sK23(sK25(sK17(sK31))))
    | ~ spl44_354 ),
    inference(resolution,[],[f2861,f605])).

fof(f2861,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK17(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_354 ),
    inference(resolution,[],[f2816,f447])).

fof(f3589,plain,
    ( spl44_486
    | ~ spl44_246 ),
    inference(avatar_split_clause,[],[f3582,f2094,f3587])).

fof(f3587,plain,
    ( spl44_486
  <=> v1_relat_1(sK23(sK25(sK16(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_486])])).

fof(f3582,plain,
    ( v1_relat_1(sK23(sK25(sK16(sK31))))
    | ~ spl44_246 ),
    inference(resolution,[],[f2761,f605])).

fof(f2761,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK16(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_246 ),
    inference(resolution,[],[f2095,f446])).

fof(f3581,plain,
    ( spl44_484
    | ~ spl44_246 ),
    inference(avatar_split_clause,[],[f3574,f2094,f3579])).

fof(f3579,plain,
    ( spl44_484
  <=> v1_funct_1(sK23(sK25(sK16(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_484])])).

fof(f3574,plain,
    ( v1_funct_1(sK23(sK25(sK16(sK31))))
    | ~ spl44_246 ),
    inference(resolution,[],[f2760,f605])).

fof(f2760,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK16(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_246 ),
    inference(resolution,[],[f2095,f447])).

fof(f3570,plain,
    ( spl44_478
    | spl44_482
    | ~ spl44_134 ),
    inference(avatar_split_clause,[],[f3447,f1280,f3568,f3552])).

fof(f3552,plain,
    ( spl44_478
  <=> v1_zfmisc_1(sK17(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_478])])).

fof(f1280,plain,
    ( spl44_134
  <=> v4_funct_1(sK17(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_134])])).

fof(f3447,plain,
    ( v4_funct_1(sK17(sK17(sK31)))
    | v1_zfmisc_1(sK17(sK31))
    | ~ spl44_134 ),
    inference(resolution,[],[f3373,f682])).

fof(f682,plain,(
    ! [X0] :
      ( m1_subset_1(sK17(X0),k1_zfmisc_1(X0))
      | v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f562,f433])).

fof(f562,plain,(
    ! [X0] :
      ( m1_subset_1(sK17(X0),k1_zfmisc_1(X0))
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f370])).

fof(f370,plain,(
    ! [X0] :
      ( ( v1_subset_1(sK17(X0),X0)
        & v1_zfmisc_1(sK17(X0))
        & ~ v1_xboole_0(sK17(X0))
        & m1_subset_1(sK17(X0),k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f274,f369])).

fof(f369,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,X0)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_subset_1(sK17(X0),X0)
        & v1_zfmisc_1(sK17(X0))
        & ~ v1_xboole_0(sK17(X0))
        & m1_subset_1(sK17(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f274,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,X0)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f273])).

fof(f273,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,X0)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f106])).

fof(f106,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ? [X1] :
          ( v1_subset_1(X1,X0)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',rc2_tex_2)).

fof(f3373,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK17(sK31)))
        | v4_funct_1(X0) )
    | ~ spl44_134 ),
    inference(resolution,[],[f1281,f448])).

fof(f1281,plain,
    ( v4_funct_1(sK17(sK31))
    | ~ spl44_134 ),
    inference(avatar_component_clause,[],[f1280])).

fof(f3560,plain,
    ( spl44_478
    | spl44_480
    | ~ spl44_134 ),
    inference(avatar_split_clause,[],[f3446,f1280,f3558,f3552])).

fof(f3446,plain,
    ( v4_funct_1(sK16(sK17(sK31)))
    | v1_zfmisc_1(sK17(sK31))
    | ~ spl44_134 ),
    inference(resolution,[],[f3373,f678])).

fof(f678,plain,(
    ! [X0] :
      ( m1_subset_1(sK16(X0),k1_zfmisc_1(X0))
      | v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f558,f433])).

fof(f558,plain,(
    ! [X0] :
      ( m1_subset_1(sK16(X0),k1_zfmisc_1(X0))
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f368])).

fof(f368,plain,(
    ! [X0] :
      ( ( ~ v1_subset_1(sK16(X0),X0)
        & ~ v1_zfmisc_1(sK16(X0))
        & ~ v1_xboole_0(sK16(X0))
        & m1_subset_1(sK16(X0),k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f272,f367])).

fof(f367,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK16(X0),X0)
        & ~ v1_zfmisc_1(sK16(X0))
        & ~ v1_xboole_0(sK16(X0))
        & m1_subset_1(sK16(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f272,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f271])).

fof(f271,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f113])).

fof(f113,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',rc3_tex_2)).

fof(f3544,plain,
    ( spl44_468
    | spl44_476
    | ~ spl44_134 ),
    inference(avatar_split_clause,[],[f3445,f1280,f3542,f3506])).

fof(f3506,plain,
    ( spl44_468
  <=> v1_xboole_0(sK17(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_468])])).

fof(f3445,plain,
    ( v4_funct_1(sK4(sK17(sK31)))
    | v1_xboole_0(sK17(sK31))
    | ~ spl44_134 ),
    inference(resolution,[],[f3373,f444])).

fof(f3534,plain,
    ( spl44_468
    | spl44_474
    | ~ spl44_134 ),
    inference(avatar_split_clause,[],[f3444,f1280,f3532,f3506])).

fof(f3444,plain,
    ( v4_funct_1(sK3(sK17(sK31)))
    | v1_xboole_0(sK17(sK31))
    | ~ spl44_134 ),
    inference(resolution,[],[f3373,f441])).

fof(f441,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f342])).

fof(f342,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(sK3(X0))
        & ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f163,f341])).

fof(f341,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_zfmisc_1(sK3(X0))
        & ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f163,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f111])).

fof(f111,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',rc3_realset1)).

fof(f3524,plain,
    ( spl44_468
    | spl44_472
    | ~ spl44_134 ),
    inference(avatar_split_clause,[],[f3443,f1280,f3522,f3506])).

fof(f3443,plain,
    ( v4_funct_1(sK2(sK17(sK31)))
    | v1_xboole_0(sK17(sK31))
    | ~ spl44_134 ),
    inference(resolution,[],[f3373,f438])).

fof(f438,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f340])).

fof(f340,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(sK2(X0))
        & ~ v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f162,f339])).

fof(f339,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_zfmisc_1(sK2(X0))
        & ~ v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f162,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f98])).

fof(f98,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',rc1_tex_2)).

fof(f3514,plain,
    ( spl44_468
    | spl44_470
    | ~ spl44_134 ),
    inference(avatar_split_clause,[],[f3442,f1280,f3512,f3506])).

fof(f3442,plain,
    ( v4_funct_1(sK1(sK17(sK31)))
    | v1_xboole_0(sK17(sK31))
    | ~ spl44_134 ),
    inference(resolution,[],[f3373,f436])).

fof(f3483,plain,
    ( spl44_131
    | ~ spl44_374 ),
    inference(avatar_contradiction_clause,[],[f3482])).

fof(f3482,plain,
    ( $false
    | ~ spl44_131
    | ~ spl44_374 ),
    inference(subsumption_resolution,[],[f3474,f1262])).

fof(f1262,plain,
    ( ~ v1_zfmisc_1(sK31)
    | ~ spl44_131 ),
    inference(avatar_component_clause,[],[f1261])).

fof(f1261,plain,
    ( spl44_131
  <=> ~ v1_zfmisc_1(sK31) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_131])])).

fof(f3474,plain,
    ( v1_zfmisc_1(sK31)
    | ~ spl44_374 ),
    inference(resolution,[],[f2954,f677])).

fof(f677,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK16(X0))
      | v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f559,f433])).

fof(f559,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK16(X0))
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f368])).

fof(f2954,plain,
    ( v1_xboole_0(sK16(sK31))
    | ~ spl44_374 ),
    inference(avatar_component_clause,[],[f2953])).

fof(f2953,plain,
    ( spl44_374
  <=> v1_xboole_0(sK16(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_374])])).

fof(f3473,plain,
    ( spl44_374
    | spl44_466
    | ~ spl44_132 ),
    inference(avatar_split_clause,[],[f3432,f1270,f3471,f2953])).

fof(f3471,plain,
    ( spl44_466
  <=> v4_funct_1(sK2(sK16(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_466])])).

fof(f1270,plain,
    ( spl44_132
  <=> v4_funct_1(sK16(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_132])])).

fof(f3432,plain,
    ( v4_funct_1(sK2(sK16(sK31)))
    | v1_xboole_0(sK16(sK31))
    | ~ spl44_132 ),
    inference(resolution,[],[f3370,f438])).

fof(f3370,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK16(sK31)))
        | v4_funct_1(X0) )
    | ~ spl44_132 ),
    inference(resolution,[],[f1271,f448])).

fof(f1271,plain,
    ( v4_funct_1(sK16(sK31))
    | ~ spl44_132 ),
    inference(avatar_component_clause,[],[f1270])).

fof(f3466,plain,
    ( spl44_204
    | spl44_464
    | ~ spl44_128 ),
    inference(avatar_split_clause,[],[f1926,f1251,f3464,f1671])).

fof(f3464,plain,
    ( spl44_464
  <=> v4_funct_1(sK17(sK4(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_464])])).

fof(f1251,plain,
    ( spl44_128
  <=> v4_funct_1(sK4(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_128])])).

fof(f1926,plain,
    ( v4_funct_1(sK17(sK4(sK31)))
    | v1_zfmisc_1(sK4(sK31))
    | ~ spl44_128 ),
    inference(resolution,[],[f1254,f682])).

fof(f1254,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK31)))
        | v4_funct_1(X0) )
    | ~ spl44_128 ),
    inference(resolution,[],[f1252,f448])).

fof(f1252,plain,
    ( v4_funct_1(sK4(sK31))
    | ~ spl44_128 ),
    inference(avatar_component_clause,[],[f1251])).

fof(f3457,plain,
    ( spl44_204
    | spl44_462
    | ~ spl44_128 ),
    inference(avatar_split_clause,[],[f1925,f1251,f3455,f1671])).

fof(f3455,plain,
    ( spl44_462
  <=> v4_funct_1(sK16(sK4(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_462])])).

fof(f1925,plain,
    ( v4_funct_1(sK16(sK4(sK31)))
    | v1_zfmisc_1(sK4(sK31))
    | ~ spl44_128 ),
    inference(resolution,[],[f1254,f678])).

fof(f3424,plain,
    ( spl44_314
    | ~ spl44_252
    | ~ spl44_446 ),
    inference(avatar_split_clause,[],[f3357,f3314,f2166,f2532])).

fof(f2532,plain,
    ( spl44_314
  <=> v1_funct_1(sK23(sK1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_314])])).

fof(f2166,plain,
    ( spl44_252
  <=> k1_xboole_0 = sK25(sK31) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_252])])).

fof(f3314,plain,
    ( spl44_446
  <=> v1_funct_1(sK23(sK1(sK25(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_446])])).

fof(f3357,plain,
    ( v1_funct_1(sK23(sK1(k1_xboole_0)))
    | ~ spl44_252
    | ~ spl44_446 ),
    inference(superposition,[],[f3315,f2167])).

fof(f2167,plain,
    ( k1_xboole_0 = sK25(sK31)
    | ~ spl44_252 ),
    inference(avatar_component_clause,[],[f2166])).

fof(f3315,plain,
    ( v1_funct_1(sK23(sK1(sK25(sK31))))
    | ~ spl44_446 ),
    inference(avatar_component_clause,[],[f3314])).

fof(f3423,plain,
    ( spl44_460
    | ~ spl44_226 ),
    inference(avatar_split_clause,[],[f3052,f1934,f3421])).

fof(f3421,plain,
    ( spl44_460
  <=> v1_relat_1(sK23(sK25(sK4(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_460])])).

fof(f3052,plain,
    ( v1_relat_1(sK23(sK25(sK4(sK31))))
    | ~ spl44_226 ),
    inference(resolution,[],[f1939,f605])).

fof(f1939,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK4(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_226 ),
    inference(resolution,[],[f1935,f446])).

fof(f3416,plain,
    ( spl44_458
    | ~ spl44_226 ),
    inference(avatar_split_clause,[],[f3049,f1934,f3414])).

fof(f3414,plain,
    ( spl44_458
  <=> v1_funct_1(sK23(sK25(sK4(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_458])])).

fof(f3049,plain,
    ( v1_funct_1(sK23(sK25(sK4(sK31))))
    | ~ spl44_226 ),
    inference(resolution,[],[f1938,f605])).

fof(f1938,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK4(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_226 ),
    inference(resolution,[],[f1935,f447])).

fof(f3406,plain,
    ( ~ spl44_457
    | ~ spl44_252
    | spl44_263 ),
    inference(avatar_split_clause,[],[f3405,f2218,f2166,f3399])).

fof(f3399,plain,
    ( spl44_457
  <=> ~ v4_funct_1(sK4(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_457])])).

fof(f2218,plain,
    ( spl44_263
  <=> ~ v4_funct_1(sK4(sK25(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_263])])).

fof(f3405,plain,
    ( ~ v4_funct_1(sK4(k1_xboole_0))
    | ~ spl44_252
    | ~ spl44_263 ),
    inference(forward_demodulation,[],[f2219,f2167])).

fof(f2219,plain,
    ( ~ v4_funct_1(sK4(sK25(sK31)))
    | ~ spl44_263 ),
    inference(avatar_component_clause,[],[f2218])).

fof(f3404,plain,
    ( spl44_456
    | ~ spl44_252
    | ~ spl44_262 ),
    inference(avatar_split_clause,[],[f3353,f2221,f2166,f3402])).

fof(f3402,plain,
    ( spl44_456
  <=> v4_funct_1(sK4(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_456])])).

fof(f3353,plain,
    ( v4_funct_1(sK4(k1_xboole_0))
    | ~ spl44_252
    | ~ spl44_262 ),
    inference(superposition,[],[f2222,f2167])).

fof(f3397,plain,
    ( ~ spl44_455
    | ~ spl44_252
    | spl44_261 ),
    inference(avatar_split_clause,[],[f3396,f2211,f2166,f3390])).

fof(f3390,plain,
    ( spl44_455
  <=> ~ v4_funct_1(sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_455])])).

fof(f2211,plain,
    ( spl44_261
  <=> ~ v4_funct_1(sK3(sK25(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_261])])).

fof(f3396,plain,
    ( ~ v4_funct_1(sK3(k1_xboole_0))
    | ~ spl44_252
    | ~ spl44_261 ),
    inference(forward_demodulation,[],[f2212,f2167])).

fof(f2212,plain,
    ( ~ v4_funct_1(sK3(sK25(sK31)))
    | ~ spl44_261 ),
    inference(avatar_component_clause,[],[f2211])).

fof(f3395,plain,
    ( spl44_454
    | ~ spl44_252
    | ~ spl44_260 ),
    inference(avatar_split_clause,[],[f3352,f2214,f2166,f3393])).

fof(f3393,plain,
    ( spl44_454
  <=> v4_funct_1(sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_454])])).

fof(f3352,plain,
    ( v4_funct_1(sK3(k1_xboole_0))
    | ~ spl44_252
    | ~ spl44_260 ),
    inference(superposition,[],[f2215,f2167])).

fof(f3388,plain,
    ( ~ spl44_453
    | ~ spl44_252
    | spl44_255 ),
    inference(avatar_split_clause,[],[f3387,f2173,f2166,f3381])).

fof(f3381,plain,
    ( spl44_453
  <=> ~ v4_funct_1(sK2(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_453])])).

fof(f2173,plain,
    ( spl44_255
  <=> ~ v4_funct_1(sK2(sK25(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_255])])).

fof(f3387,plain,
    ( ~ v4_funct_1(sK2(k1_xboole_0))
    | ~ spl44_252
    | ~ spl44_255 ),
    inference(forward_demodulation,[],[f2174,f2167])).

fof(f2174,plain,
    ( ~ v4_funct_1(sK2(sK25(sK31)))
    | ~ spl44_255 ),
    inference(avatar_component_clause,[],[f2173])).

fof(f3386,plain,
    ( spl44_452
    | ~ spl44_252
    | ~ spl44_254 ),
    inference(avatar_split_clause,[],[f3351,f2176,f2166,f3384])).

fof(f3384,plain,
    ( spl44_452
  <=> v4_funct_1(sK2(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_452])])).

fof(f3351,plain,
    ( v4_funct_1(sK2(k1_xboole_0))
    | ~ spl44_252
    | ~ spl44_254 ),
    inference(superposition,[],[f2177,f2167])).

fof(f3368,plain,
    ( spl44_450
    | ~ spl44_204 ),
    inference(avatar_split_clause,[],[f2972,f1671,f3366])).

fof(f2972,plain,
    ( v1_zfmisc_1(sK25(sK4(sK31)))
    | ~ spl44_204 ),
    inference(resolution,[],[f1704,f608])).

fof(f1704,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK31)))
        | v1_zfmisc_1(X0) )
    | ~ spl44_204 ),
    inference(resolution,[],[f1672,f499])).

fof(f3324,plain,
    ( spl44_448
    | ~ spl44_250 ),
    inference(avatar_split_clause,[],[f3317,f2148,f3322])).

fof(f3322,plain,
    ( spl44_448
  <=> v1_relat_1(sK23(sK1(sK25(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_448])])).

fof(f3317,plain,
    ( v1_relat_1(sK23(sK1(sK25(sK31))))
    | ~ spl44_250 ),
    inference(resolution,[],[f2515,f605])).

fof(f2515,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK1(sK25(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_250 ),
    inference(resolution,[],[f2149,f446])).

fof(f3316,plain,
    ( spl44_446
    | ~ spl44_250 ),
    inference(avatar_split_clause,[],[f3309,f2148,f3314])).

fof(f3309,plain,
    ( v1_funct_1(sK23(sK1(sK25(sK31))))
    | ~ spl44_250 ),
    inference(resolution,[],[f2514,f605])).

fof(f2514,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK1(sK25(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_250 ),
    inference(resolution,[],[f2149,f447])).

fof(f3301,plain,
    ( spl44_23
    | spl44_301 ),
    inference(avatar_contradiction_clause,[],[f3300])).

fof(f3300,plain,
    ( $false
    | ~ spl44_23
    | ~ spl44_301 ),
    inference(subsumption_resolution,[],[f3298,f768])).

fof(f3298,plain,
    ( v1_xboole_0(sK31)
    | ~ spl44_301 ),
    inference(resolution,[],[f2429,f443])).

fof(f443,plain,(
    ! [X0] :
      ( v1_zfmisc_1(sK3(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f342])).

fof(f2429,plain,
    ( ~ v1_zfmisc_1(sK3(sK31))
    | ~ spl44_301 ),
    inference(avatar_component_clause,[],[f2428])).

fof(f2428,plain,
    ( spl44_301
  <=> ~ v1_zfmisc_1(sK3(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_301])])).

fof(f3297,plain,
    ( spl44_444
    | ~ spl44_300 ),
    inference(avatar_split_clause,[],[f3289,f2431,f3295])).

fof(f3289,plain,
    ( v1_zfmisc_1(sK25(sK3(sK31)))
    | ~ spl44_300 ),
    inference(resolution,[],[f2440,f608])).

fof(f2440,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3(sK31)))
        | v1_zfmisc_1(X0) )
    | ~ spl44_300 ),
    inference(resolution,[],[f2432,f499])).

fof(f3278,plain,
    ( spl44_442
    | ~ spl44_298 ),
    inference(avatar_split_clause,[],[f3271,f2421,f3276])).

fof(f3276,plain,
    ( spl44_442
  <=> v1_relat_1(sK23(sK4(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_442])])).

fof(f3271,plain,
    ( v1_relat_1(sK23(sK4(sK3(sK31))))
    | ~ spl44_298 ),
    inference(resolution,[],[f2426,f605])).

fof(f2426,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK4(sK3(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_298 ),
    inference(resolution,[],[f2422,f446])).

fof(f3270,plain,
    ( spl44_440
    | ~ spl44_298 ),
    inference(avatar_split_clause,[],[f3263,f2421,f3268])).

fof(f3268,plain,
    ( spl44_440
  <=> v1_funct_1(sK23(sK4(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_440])])).

fof(f3263,plain,
    ( v1_funct_1(sK23(sK4(sK3(sK31))))
    | ~ spl44_298 ),
    inference(resolution,[],[f2425,f605])).

fof(f2425,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK4(sK3(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_298 ),
    inference(resolution,[],[f2422,f447])).

fof(f3262,plain,
    ( spl44_438
    | ~ spl44_296 ),
    inference(avatar_split_clause,[],[f3255,f2411,f3260])).

fof(f3260,plain,
    ( spl44_438
  <=> v1_relat_1(sK23(sK3(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_438])])).

fof(f3255,plain,
    ( v1_relat_1(sK23(sK3(sK3(sK31))))
    | ~ spl44_296 ),
    inference(resolution,[],[f2416,f605])).

fof(f2416,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK3(sK3(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_296 ),
    inference(resolution,[],[f2412,f446])).

fof(f3254,plain,
    ( spl44_436
    | ~ spl44_296 ),
    inference(avatar_split_clause,[],[f3247,f2411,f3252])).

fof(f3252,plain,
    ( spl44_436
  <=> v1_funct_1(sK23(sK3(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_436])])).

fof(f3247,plain,
    ( v1_funct_1(sK23(sK3(sK3(sK31))))
    | ~ spl44_296 ),
    inference(resolution,[],[f2415,f605])).

fof(f2415,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK3(sK3(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_296 ),
    inference(resolution,[],[f2412,f447])).

fof(f3246,plain,
    ( spl44_434
    | ~ spl44_294 ),
    inference(avatar_split_clause,[],[f3239,f2401,f3244])).

fof(f3244,plain,
    ( spl44_434
  <=> v1_relat_1(sK23(sK2(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_434])])).

fof(f3239,plain,
    ( v1_relat_1(sK23(sK2(sK3(sK31))))
    | ~ spl44_294 ),
    inference(resolution,[],[f2406,f605])).

fof(f2406,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK2(sK3(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_294 ),
    inference(resolution,[],[f2402,f446])).

fof(f3238,plain,
    ( spl44_432
    | ~ spl44_294 ),
    inference(avatar_split_clause,[],[f3231,f2401,f3236])).

fof(f3236,plain,
    ( spl44_432
  <=> v1_funct_1(sK23(sK2(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_432])])).

fof(f3231,plain,
    ( v1_funct_1(sK23(sK2(sK3(sK31))))
    | ~ spl44_294 ),
    inference(resolution,[],[f2405,f605])).

fof(f2405,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK2(sK3(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_294 ),
    inference(resolution,[],[f2402,f447])).

fof(f3230,plain,
    ( spl44_430
    | ~ spl44_292 ),
    inference(avatar_split_clause,[],[f3222,f2376,f3228])).

fof(f3228,plain,
    ( spl44_430
  <=> v1_relat_1(sK23(sK1(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_430])])).

fof(f3222,plain,
    ( v1_relat_1(sK23(sK1(sK3(sK31))))
    | ~ spl44_292 ),
    inference(resolution,[],[f2396,f605])).

fof(f2396,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK1(sK3(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_292 ),
    inference(resolution,[],[f2377,f446])).

fof(f3221,plain,
    ( spl44_428
    | ~ spl44_292 ),
    inference(avatar_split_clause,[],[f3214,f2376,f3219])).

fof(f3219,plain,
    ( spl44_428
  <=> v1_funct_1(sK23(sK1(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_428])])).

fof(f3214,plain,
    ( v1_funct_1(sK23(sK1(sK3(sK31))))
    | ~ spl44_292 ),
    inference(resolution,[],[f2395,f605])).

fof(f2395,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK1(sK3(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_292 ),
    inference(resolution,[],[f2377,f447])).

fof(f3206,plain,
    ( spl44_23
    | spl44_285 ),
    inference(avatar_contradiction_clause,[],[f3205])).

fof(f3205,plain,
    ( $false
    | ~ spl44_23
    | ~ spl44_285 ),
    inference(subsumption_resolution,[],[f3203,f768])).

fof(f3203,plain,
    ( v1_xboole_0(sK31)
    | ~ spl44_285 ),
    inference(resolution,[],[f2347,f440])).

fof(f440,plain,(
    ! [X0] :
      ( v1_zfmisc_1(sK2(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f340])).

fof(f2347,plain,
    ( ~ v1_zfmisc_1(sK2(sK31))
    | ~ spl44_285 ),
    inference(avatar_component_clause,[],[f2346])).

fof(f2346,plain,
    ( spl44_285
  <=> ~ v1_zfmisc_1(sK2(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_285])])).

fof(f3202,plain,
    ( spl44_426
    | ~ spl44_284 ),
    inference(avatar_split_clause,[],[f3194,f2349,f3200])).

fof(f3194,plain,
    ( v1_zfmisc_1(sK25(sK2(sK31)))
    | ~ spl44_284 ),
    inference(resolution,[],[f2358,f608])).

fof(f2358,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2(sK31)))
        | v1_zfmisc_1(X0) )
    | ~ spl44_284 ),
    inference(resolution,[],[f2350,f499])).

fof(f3183,plain,
    ( spl44_424
    | ~ spl44_282 ),
    inference(avatar_split_clause,[],[f3176,f2339,f3181])).

fof(f3181,plain,
    ( spl44_424
  <=> v1_relat_1(sK23(sK4(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_424])])).

fof(f3176,plain,
    ( v1_relat_1(sK23(sK4(sK2(sK31))))
    | ~ spl44_282 ),
    inference(resolution,[],[f2344,f605])).

fof(f2344,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK4(sK2(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_282 ),
    inference(resolution,[],[f2340,f446])).

fof(f3175,plain,
    ( spl44_422
    | ~ spl44_282 ),
    inference(avatar_split_clause,[],[f3168,f2339,f3173])).

fof(f3173,plain,
    ( spl44_422
  <=> v1_funct_1(sK23(sK4(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_422])])).

fof(f3168,plain,
    ( v1_funct_1(sK23(sK4(sK2(sK31))))
    | ~ spl44_282 ),
    inference(resolution,[],[f2343,f605])).

fof(f2343,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK4(sK2(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_282 ),
    inference(resolution,[],[f2340,f447])).

fof(f3167,plain,
    ( spl44_420
    | ~ spl44_280 ),
    inference(avatar_split_clause,[],[f3160,f2329,f3165])).

fof(f3165,plain,
    ( spl44_420
  <=> v1_relat_1(sK23(sK3(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_420])])).

fof(f3160,plain,
    ( v1_relat_1(sK23(sK3(sK2(sK31))))
    | ~ spl44_280 ),
    inference(resolution,[],[f2334,f605])).

fof(f2334,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK3(sK2(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_280 ),
    inference(resolution,[],[f2330,f446])).

fof(f3159,plain,
    ( spl44_418
    | ~ spl44_280 ),
    inference(avatar_split_clause,[],[f3152,f2329,f3157])).

fof(f3157,plain,
    ( spl44_418
  <=> v1_funct_1(sK23(sK3(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_418])])).

fof(f3152,plain,
    ( v1_funct_1(sK23(sK3(sK2(sK31))))
    | ~ spl44_280 ),
    inference(resolution,[],[f2333,f605])).

fof(f2333,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK3(sK2(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_280 ),
    inference(resolution,[],[f2330,f447])).

fof(f3151,plain,
    ( spl44_416
    | ~ spl44_278 ),
    inference(avatar_split_clause,[],[f3143,f2319,f3149])).

fof(f3149,plain,
    ( spl44_416
  <=> v1_relat_1(sK23(sK2(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_416])])).

fof(f3143,plain,
    ( v1_relat_1(sK23(sK2(sK2(sK31))))
    | ~ spl44_278 ),
    inference(resolution,[],[f2324,f605])).

fof(f2324,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK2(sK2(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_278 ),
    inference(resolution,[],[f2320,f446])).

fof(f3142,plain,
    ( spl44_414
    | ~ spl44_278 ),
    inference(avatar_split_clause,[],[f3135,f2319,f3140])).

fof(f3140,plain,
    ( spl44_414
  <=> v1_funct_1(sK23(sK2(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_414])])).

fof(f3135,plain,
    ( v1_funct_1(sK23(sK2(sK2(sK31))))
    | ~ spl44_278 ),
    inference(resolution,[],[f2323,f605])).

fof(f2323,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK2(sK2(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_278 ),
    inference(resolution,[],[f2320,f447])).

fof(f3134,plain,
    ( spl44_412
    | ~ spl44_276 ),
    inference(avatar_split_clause,[],[f3127,f2294,f3132])).

fof(f3132,plain,
    ( spl44_412
  <=> v1_relat_1(sK23(sK1(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_412])])).

fof(f3127,plain,
    ( v1_relat_1(sK23(sK1(sK2(sK31))))
    | ~ spl44_276 ),
    inference(resolution,[],[f2314,f605])).

fof(f2314,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK1(sK2(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_276 ),
    inference(resolution,[],[f2295,f446])).

fof(f3126,plain,
    ( spl44_410
    | ~ spl44_276 ),
    inference(avatar_split_clause,[],[f3119,f2294,f3124])).

fof(f3124,plain,
    ( spl44_410
  <=> v1_funct_1(sK23(sK1(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_410])])).

fof(f3119,plain,
    ( v1_funct_1(sK23(sK1(sK2(sK31))))
    | ~ spl44_276 ),
    inference(resolution,[],[f2313,f605])).

fof(f2313,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK1(sK2(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_276 ),
    inference(resolution,[],[f2295,f447])).

fof(f3118,plain,
    ( spl44_408
    | ~ spl44_272 ),
    inference(avatar_split_clause,[],[f3111,f2278,f3116])).

fof(f3116,plain,
    ( spl44_408
  <=> v1_relat_1(sK23(sK4(sK1(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_408])])).

fof(f3111,plain,
    ( v1_relat_1(sK23(sK4(sK1(sK31))))
    | ~ spl44_272 ),
    inference(resolution,[],[f2283,f605])).

fof(f2283,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK4(sK1(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_272 ),
    inference(resolution,[],[f2279,f446])).

fof(f3110,plain,
    ( spl44_406
    | ~ spl44_272 ),
    inference(avatar_split_clause,[],[f3103,f2278,f3108])).

fof(f3108,plain,
    ( spl44_406
  <=> v1_funct_1(sK23(sK4(sK1(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_406])])).

fof(f3103,plain,
    ( v1_funct_1(sK23(sK4(sK1(sK31))))
    | ~ spl44_272 ),
    inference(resolution,[],[f2282,f605])).

fof(f2282,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK4(sK1(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_272 ),
    inference(resolution,[],[f2279,f447])).

fof(f3102,plain,
    ( spl44_404
    | ~ spl44_270 ),
    inference(avatar_split_clause,[],[f3095,f2268,f3100])).

fof(f3100,plain,
    ( spl44_404
  <=> v1_relat_1(sK23(sK3(sK1(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_404])])).

fof(f3095,plain,
    ( v1_relat_1(sK23(sK3(sK1(sK31))))
    | ~ spl44_270 ),
    inference(resolution,[],[f2273,f605])).

fof(f2273,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK3(sK1(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_270 ),
    inference(resolution,[],[f2269,f446])).

fof(f3094,plain,
    ( spl44_402
    | ~ spl44_270 ),
    inference(avatar_split_clause,[],[f3087,f2268,f3092])).

fof(f3092,plain,
    ( spl44_402
  <=> v1_funct_1(sK23(sK3(sK1(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_402])])).

fof(f3087,plain,
    ( v1_funct_1(sK23(sK3(sK1(sK31))))
    | ~ spl44_270 ),
    inference(resolution,[],[f2272,f605])).

fof(f2272,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK3(sK1(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_270 ),
    inference(resolution,[],[f2269,f447])).

fof(f3086,plain,
    ( spl44_400
    | ~ spl44_268 ),
    inference(avatar_split_clause,[],[f3079,f2258,f3084])).

fof(f3084,plain,
    ( spl44_400
  <=> v1_relat_1(sK23(sK2(sK1(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_400])])).

fof(f3079,plain,
    ( v1_relat_1(sK23(sK2(sK1(sK31))))
    | ~ spl44_268 ),
    inference(resolution,[],[f2263,f605])).

fof(f2263,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK2(sK1(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_268 ),
    inference(resolution,[],[f2259,f446])).

fof(f3078,plain,
    ( spl44_398
    | ~ spl44_268 ),
    inference(avatar_split_clause,[],[f3071,f2258,f3076])).

fof(f3076,plain,
    ( spl44_398
  <=> v1_funct_1(sK23(sK2(sK1(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_398])])).

fof(f3071,plain,
    ( v1_funct_1(sK23(sK2(sK1(sK31))))
    | ~ spl44_268 ),
    inference(resolution,[],[f2262,f605])).

fof(f2262,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK2(sK1(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_268 ),
    inference(resolution,[],[f2259,f447])).

fof(f3070,plain,
    ( spl44_396
    | ~ spl44_266 ),
    inference(avatar_split_clause,[],[f3063,f2234,f3068])).

fof(f3068,plain,
    ( spl44_396
  <=> v1_relat_1(sK23(sK1(sK1(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_396])])).

fof(f3063,plain,
    ( v1_relat_1(sK23(sK1(sK1(sK31))))
    | ~ spl44_266 ),
    inference(resolution,[],[f2253,f605])).

fof(f2253,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK1(sK1(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_266 ),
    inference(resolution,[],[f2235,f446])).

fof(f3062,plain,
    ( spl44_394
    | ~ spl44_266 ),
    inference(avatar_split_clause,[],[f3055,f2234,f3060])).

fof(f3060,plain,
    ( spl44_394
  <=> v1_funct_1(sK23(sK1(sK1(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_394])])).

fof(f3055,plain,
    ( v1_funct_1(sK23(sK1(sK1(sK31))))
    | ~ spl44_266 ),
    inference(resolution,[],[f2252,f605])).

fof(f2252,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK1(sK1(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_266 ),
    inference(resolution,[],[f2235,f447])).

fof(f3048,plain,
    ( spl44_392
    | ~ spl44_222 ),
    inference(avatar_split_clause,[],[f3041,f1903,f3046])).

fof(f3046,plain,
    ( spl44_392
  <=> v1_relat_1(sK23(sK25(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_392])])).

fof(f3041,plain,
    ( v1_relat_1(sK23(sK25(sK3(sK31))))
    | ~ spl44_222 ),
    inference(resolution,[],[f1908,f605])).

fof(f1908,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK3(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_222 ),
    inference(resolution,[],[f1904,f446])).

fof(f3040,plain,
    ( spl44_390
    | ~ spl44_222 ),
    inference(avatar_split_clause,[],[f3033,f1903,f3038])).

fof(f3038,plain,
    ( spl44_390
  <=> v1_funct_1(sK23(sK25(sK3(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_390])])).

fof(f3033,plain,
    ( v1_funct_1(sK23(sK25(sK3(sK31))))
    | ~ spl44_222 ),
    inference(resolution,[],[f1907,f605])).

fof(f1907,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK3(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_222 ),
    inference(resolution,[],[f1904,f447])).

fof(f3032,plain,
    ( spl44_388
    | ~ spl44_218 ),
    inference(avatar_split_clause,[],[f3025,f1872,f3030])).

fof(f3030,plain,
    ( spl44_388
  <=> v1_relat_1(sK23(sK25(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_388])])).

fof(f3025,plain,
    ( v1_relat_1(sK23(sK25(sK2(sK31))))
    | ~ spl44_218 ),
    inference(resolution,[],[f1877,f605])).

fof(f1877,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK2(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_218 ),
    inference(resolution,[],[f1873,f446])).

fof(f3024,plain,
    ( spl44_386
    | ~ spl44_218 ),
    inference(avatar_split_clause,[],[f3017,f1872,f3022])).

fof(f3022,plain,
    ( spl44_386
  <=> v1_funct_1(sK23(sK25(sK2(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_386])])).

fof(f3017,plain,
    ( v1_funct_1(sK23(sK25(sK2(sK31))))
    | ~ spl44_218 ),
    inference(resolution,[],[f1876,f605])).

fof(f1876,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK2(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_218 ),
    inference(resolution,[],[f1873,f447])).

fof(f3015,plain,
    ( spl44_384
    | ~ spl44_214 ),
    inference(avatar_split_clause,[],[f3008,f1841,f3013])).

fof(f3013,plain,
    ( spl44_384
  <=> v1_relat_1(sK23(sK25(sK1(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_384])])).

fof(f3008,plain,
    ( v1_relat_1(sK23(sK25(sK1(sK31))))
    | ~ spl44_214 ),
    inference(resolution,[],[f1846,f605])).

fof(f1846,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK1(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_214 ),
    inference(resolution,[],[f1842,f446])).

fof(f3007,plain,
    ( spl44_382
    | ~ spl44_214 ),
    inference(avatar_split_clause,[],[f3000,f1841,f3005])).

fof(f3005,plain,
    ( spl44_382
  <=> v1_funct_1(sK23(sK25(sK1(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_382])])).

fof(f3000,plain,
    ( v1_funct_1(sK23(sK25(sK1(sK31))))
    | ~ spl44_214 ),
    inference(resolution,[],[f1845,f605])).

fof(f1845,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK1(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_214 ),
    inference(resolution,[],[f1842,f447])).

fof(f2999,plain,
    ( spl44_380
    | ~ spl44_210 ),
    inference(avatar_split_clause,[],[f2992,f1810,f2997])).

fof(f2997,plain,
    ( spl44_380
  <=> v1_relat_1(sK23(sK25(sK25(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_380])])).

fof(f2992,plain,
    ( v1_relat_1(sK23(sK25(sK25(sK31))))
    | ~ spl44_210 ),
    inference(resolution,[],[f1815,f605])).

fof(f1815,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK25(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_210 ),
    inference(resolution,[],[f1811,f446])).

fof(f2991,plain,
    ( spl44_378
    | ~ spl44_210 ),
    inference(avatar_split_clause,[],[f2984,f1810,f2989])).

fof(f2989,plain,
    ( spl44_378
  <=> v1_funct_1(sK23(sK25(sK25(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_378])])).

fof(f2984,plain,
    ( v1_funct_1(sK23(sK25(sK25(sK31))))
    | ~ spl44_210 ),
    inference(resolution,[],[f1814,f605])).

fof(f1814,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK25(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_210 ),
    inference(resolution,[],[f1811,f447])).

fof(f2961,plain,
    ( spl44_374
    | spl44_376
    | ~ spl44_132 ),
    inference(avatar_split_clause,[],[f2872,f1270,f2959,f2953])).

fof(f2959,plain,
    ( spl44_376
  <=> v4_funct_1(sK1(sK16(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_376])])).

fof(f2872,plain,
    ( v4_funct_1(sK1(sK16(sK31)))
    | v1_xboole_0(sK16(sK31))
    | ~ spl44_132 ),
    inference(resolution,[],[f2852,f436])).

fof(f2852,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK16(sK31)))
        | v4_funct_1(X0) )
    | ~ spl44_132 ),
    inference(resolution,[],[f1271,f448])).

fof(f2948,plain,
    ( spl44_202
    | spl44_372
    | ~ spl44_122 ),
    inference(avatar_split_clause,[],[f1833,f1221,f2946,f1663])).

fof(f2946,plain,
    ( spl44_372
  <=> v4_funct_1(sK17(sK1(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_372])])).

fof(f1221,plain,
    ( spl44_122
  <=> v4_funct_1(sK1(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_122])])).

fof(f1833,plain,
    ( v4_funct_1(sK17(sK1(sK31)))
    | v1_zfmisc_1(sK1(sK31))
    | ~ spl44_122 ),
    inference(resolution,[],[f1224,f682])).

fof(f1224,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK31)))
        | v4_funct_1(X0) )
    | ~ spl44_122 ),
    inference(resolution,[],[f1222,f448])).

fof(f1222,plain,
    ( v4_funct_1(sK1(sK31))
    | ~ spl44_122 ),
    inference(avatar_component_clause,[],[f1221])).

fof(f2941,plain,
    ( spl44_202
    | spl44_370
    | ~ spl44_122 ),
    inference(avatar_split_clause,[],[f1832,f1221,f2939,f1663])).

fof(f2939,plain,
    ( spl44_370
  <=> v4_funct_1(sK16(sK1(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_370])])).

fof(f1832,plain,
    ( v4_funct_1(sK16(sK1(sK31)))
    | v1_zfmisc_1(sK1(sK31))
    | ~ spl44_122 ),
    inference(resolution,[],[f1224,f678])).

fof(f2934,plain,
    ( ~ spl44_365
    | spl44_366
    | ~ spl44_369
    | spl44_49
    | ~ spl44_50 ),
    inference(avatar_split_clause,[],[f2901,f865,f858,f2932,f2926,f2920])).

fof(f2920,plain,
    ( spl44_365
  <=> ~ l1_pre_topc(sK36) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_365])])).

fof(f2926,plain,
    ( spl44_366
  <=> v1_tdlat_3(sK36) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_366])])).

fof(f2932,plain,
    ( spl44_369
  <=> ~ v2_pre_topc(sK36) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_369])])).

fof(f858,plain,
    ( spl44_49
  <=> ~ v2_struct_0(sK36) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_49])])).

fof(f865,plain,
    ( spl44_50
  <=> v7_struct_0(sK36) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_50])])).

fof(f2901,plain,
    ( ~ v2_pre_topc(sK36)
    | v1_tdlat_3(sK36)
    | ~ l1_pre_topc(sK36)
    | ~ spl44_49
    | ~ spl44_50 ),
    inference(subsumption_resolution,[],[f2900,f859])).

fof(f859,plain,
    ( ~ v2_struct_0(sK36)
    | ~ spl44_49 ),
    inference(avatar_component_clause,[],[f858])).

fof(f2900,plain,
    ( ~ v2_pre_topc(sK36)
    | v1_tdlat_3(sK36)
    | v2_struct_0(sK36)
    | ~ l1_pre_topc(sK36)
    | ~ spl44_50 ),
    inference(resolution,[],[f468,f866])).

fof(f866,plain,
    ( v7_struct_0(sK36)
    | ~ spl44_50 ),
    inference(avatar_component_clause,[],[f865])).

fof(f468,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | v1_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f194])).

fof(f194,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f193])).

fof(f193,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',cc1_tex_1)).

fof(f2898,plain,
    ( spl44_362
    | ~ spl44_134 ),
    inference(avatar_split_clause,[],[f2889,f1280,f2896])).

fof(f2889,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK17(sK31))))
    | ~ spl44_134 ),
    inference(resolution,[],[f2855,f605])).

fof(f2855,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK17(sK31)))
        | v4_funct_1(X0) )
    | ~ spl44_134 ),
    inference(resolution,[],[f1281,f448])).

fof(f2859,plain,
    ( ~ spl44_265
    | spl44_203 ),
    inference(avatar_split_clause,[],[f2858,f1660,f2225])).

fof(f1660,plain,
    ( spl44_203
  <=> ~ v1_zfmisc_1(sK1(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_203])])).

fof(f2858,plain,
    ( ~ v1_xboole_0(sK1(sK31))
    | ~ spl44_203 ),
    inference(resolution,[],[f1661,f433])).

fof(f1661,plain,
    ( ~ v1_zfmisc_1(sK1(sK31))
    | ~ spl44_203 ),
    inference(avatar_component_clause,[],[f1660])).

fof(f2850,plain,
    ( spl44_360
    | ~ spl44_202 ),
    inference(avatar_split_clause,[],[f2842,f1663,f2848])).

fof(f2842,plain,
    ( v1_zfmisc_1(sK25(sK1(sK31)))
    | ~ spl44_202 ),
    inference(resolution,[],[f1666,f608])).

fof(f1666,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK31)))
        | v1_zfmisc_1(X0) )
    | ~ spl44_202 ),
    inference(resolution,[],[f1664,f499])).

fof(f2831,plain,
    ( spl44_184
    | spl44_358
    | ~ spl44_118 ),
    inference(avatar_split_clause,[],[f1802,f1197,f2829,f1536])).

fof(f2829,plain,
    ( spl44_358
  <=> v4_funct_1(sK17(sK25(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_358])])).

fof(f1197,plain,
    ( spl44_118
  <=> v4_funct_1(sK25(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_118])])).

fof(f1802,plain,
    ( v4_funct_1(sK17(sK25(sK31)))
    | v1_zfmisc_1(sK25(sK31))
    | ~ spl44_118 ),
    inference(resolution,[],[f1200,f682])).

fof(f1200,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK25(sK31)))
        | v4_funct_1(X0) )
    | ~ spl44_118 ),
    inference(resolution,[],[f1198,f448])).

fof(f1198,plain,
    ( v4_funct_1(sK25(sK31))
    | ~ spl44_118 ),
    inference(avatar_component_clause,[],[f1197])).

fof(f2824,plain,
    ( spl44_184
    | spl44_356
    | ~ spl44_118 ),
    inference(avatar_split_clause,[],[f1801,f1197,f2822,f1536])).

fof(f2822,plain,
    ( spl44_356
  <=> v4_funct_1(sK16(sK25(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_356])])).

fof(f1801,plain,
    ( v4_funct_1(sK16(sK25(sK31)))
    | v1_zfmisc_1(sK25(sK31))
    | ~ spl44_118 ),
    inference(resolution,[],[f1200,f678])).

fof(f2817,plain,
    ( spl44_354
    | ~ spl44_134 ),
    inference(avatar_split_clause,[],[f2810,f1280,f2815])).

fof(f2810,plain,
    ( v4_funct_1(sK25(sK17(sK31)))
    | ~ spl44_134 ),
    inference(resolution,[],[f2755,f608])).

fof(f2755,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK17(sK31)))
        | v4_funct_1(X0) )
    | ~ spl44_134 ),
    inference(resolution,[],[f1281,f448])).

fof(f2783,plain,
    ( spl44_352
    | ~ spl44_132 ),
    inference(avatar_split_clause,[],[f2774,f1270,f2781])).

fof(f2774,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK16(sK31))))
    | ~ spl44_132 ),
    inference(resolution,[],[f2752,f605])).

fof(f2752,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK16(sK31)))
        | v4_funct_1(X0) )
    | ~ spl44_132 ),
    inference(resolution,[],[f1271,f448])).

fof(f2750,plain,
    ( spl44_350
    | ~ spl44_184 ),
    inference(avatar_split_clause,[],[f2740,f1536,f2748])).

fof(f2740,plain,
    ( v1_zfmisc_1(sK25(sK25(sK31)))
    | ~ spl44_184 ),
    inference(resolution,[],[f1556,f608])).

fof(f1556,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK25(sK31)))
        | v1_zfmisc_1(X0) )
    | ~ spl44_184 ),
    inference(resolution,[],[f1537,f499])).

fof(f2729,plain,
    ( spl44_348
    | ~ spl44_342 ),
    inference(avatar_split_clause,[],[f2722,f2685,f2727])).

fof(f2727,plain,
    ( spl44_348
  <=> v1_funct_1(sK23(sK4(sK34))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_348])])).

fof(f2685,plain,
    ( spl44_342
  <=> v4_funct_1(sK4(sK34)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_342])])).

fof(f2722,plain,
    ( v1_funct_1(sK23(sK4(sK34)))
    | ~ spl44_342 ),
    inference(resolution,[],[f2708,f605])).

fof(f2708,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK4(sK34))
        | v1_funct_1(X1) )
    | ~ spl44_342 ),
    inference(resolution,[],[f2686,f447])).

fof(f2686,plain,
    ( v4_funct_1(sK4(sK34))
    | ~ spl44_342 ),
    inference(avatar_component_clause,[],[f2685])).

fof(f2719,plain,
    ( spl44_346
    | ~ spl44_338 ),
    inference(avatar_split_clause,[],[f2697,f2661,f2717])).

fof(f2717,plain,
    ( spl44_346
  <=> k1_xboole_0 = sK4(sK34) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_346])])).

fof(f2661,plain,
    ( spl44_338
  <=> v1_xboole_0(sK4(sK34)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_338])])).

fof(f2697,plain,
    ( k1_xboole_0 = sK4(sK34)
    | ~ spl44_338 ),
    inference(resolution,[],[f2662,f505])).

fof(f2662,plain,
    ( v1_xboole_0(sK4(sK34))
    | ~ spl44_338 ),
    inference(avatar_component_clause,[],[f2661])).

fof(f2695,plain,
    ( spl44_338
    | spl44_344
    | ~ spl44_182 ),
    inference(avatar_split_clause,[],[f2027,f1513,f2693,f2661])).

fof(f1513,plain,
    ( spl44_182
  <=> v1_zfmisc_1(sK4(sK34)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_182])])).

fof(f2027,plain,
    ( v1_zfmisc_1(sK4(sK4(sK34)))
    | v1_xboole_0(sK4(sK34))
    | ~ spl44_182 ),
    inference(resolution,[],[f1516,f444])).

fof(f1516,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK34)))
        | v1_zfmisc_1(X0) )
    | ~ spl44_182 ),
    inference(resolution,[],[f1514,f499])).

fof(f1514,plain,
    ( v1_zfmisc_1(sK4(sK34))
    | ~ spl44_182 ),
    inference(avatar_component_clause,[],[f1513])).

fof(f2687,plain,
    ( spl44_342
    | ~ spl44_338 ),
    inference(avatar_split_clause,[],[f2670,f2661,f2685])).

fof(f2670,plain,
    ( v4_funct_1(sK4(sK34))
    | ~ spl44_338 ),
    inference(resolution,[],[f2662,f500])).

fof(f500,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v4_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f221])).

fof(f221,plain,(
    ! [X0] :
      ( v4_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f63])).

fof(f63,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v4_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',cc8_funct_1)).

fof(f2669,plain,
    ( spl44_338
    | spl44_340
    | ~ spl44_182 ),
    inference(avatar_split_clause,[],[f2024,f1513,f2667,f2661])).

fof(f2024,plain,
    ( v1_zfmisc_1(sK1(sK4(sK34)))
    | v1_xboole_0(sK4(sK34))
    | ~ spl44_182 ),
    inference(resolution,[],[f1516,f436])).

fof(f2655,plain,
    ( spl44_332
    | spl44_336
    | ~ spl44_180 ),
    inference(avatar_split_clause,[],[f1999,f1505,f2653,f2625])).

fof(f2625,plain,
    ( spl44_332
  <=> v1_xboole_0(sK1(sK34)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_332])])).

fof(f1505,plain,
    ( spl44_180
  <=> v1_zfmisc_1(sK1(sK34)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_180])])).

fof(f1999,plain,
    ( v1_zfmisc_1(sK4(sK1(sK34)))
    | v1_xboole_0(sK1(sK34))
    | ~ spl44_180 ),
    inference(resolution,[],[f1508,f444])).

fof(f1508,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK34)))
        | v1_zfmisc_1(X0) )
    | ~ spl44_180 ),
    inference(resolution,[],[f1506,f499])).

fof(f1506,plain,
    ( v1_zfmisc_1(sK1(sK34))
    | ~ spl44_180 ),
    inference(avatar_component_clause,[],[f1505])).

fof(f2643,plain,
    ( spl44_37
    | ~ spl44_332 ),
    inference(avatar_contradiction_clause,[],[f2642])).

fof(f2642,plain,
    ( $false
    | ~ spl44_37
    | ~ spl44_332 ),
    inference(subsumption_resolution,[],[f2634,f817])).

fof(f817,plain,
    ( ~ v1_xboole_0(sK34)
    | ~ spl44_37 ),
    inference(avatar_component_clause,[],[f816])).

fof(f816,plain,
    ( spl44_37
  <=> ~ v1_xboole_0(sK34) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_37])])).

fof(f2634,plain,
    ( v1_xboole_0(sK34)
    | ~ spl44_332 ),
    inference(resolution,[],[f2626,f437])).

fof(f437,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f338])).

fof(f2626,plain,
    ( v1_xboole_0(sK1(sK34))
    | ~ spl44_332 ),
    inference(avatar_component_clause,[],[f2625])).

fof(f2633,plain,
    ( spl44_332
    | spl44_334
    | ~ spl44_180 ),
    inference(avatar_split_clause,[],[f1996,f1505,f2631,f2625])).

fof(f1996,plain,
    ( v1_zfmisc_1(sK1(sK1(sK34)))
    | v1_xboole_0(sK1(sK34))
    | ~ spl44_180 ),
    inference(resolution,[],[f1508,f436])).

fof(f2620,plain,
    ( spl44_330
    | ~ spl44_324 ),
    inference(avatar_split_clause,[],[f2613,f2577,f2618])).

fof(f2618,plain,
    ( spl44_330
  <=> v1_funct_1(sK23(sK25(sK34))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_330])])).

fof(f2577,plain,
    ( spl44_324
  <=> v4_funct_1(sK25(sK34)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_324])])).

fof(f2613,plain,
    ( v1_funct_1(sK23(sK25(sK34)))
    | ~ spl44_324 ),
    inference(resolution,[],[f2600,f605])).

fof(f2600,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK34))
        | v1_funct_1(X1) )
    | ~ spl44_324 ),
    inference(resolution,[],[f2578,f447])).

fof(f2578,plain,
    ( v4_funct_1(sK25(sK34))
    | ~ spl44_324 ),
    inference(avatar_component_clause,[],[f2577])).

fof(f2611,plain,
    ( spl44_328
    | ~ spl44_320 ),
    inference(avatar_split_clause,[],[f2589,f2553,f2609])).

fof(f2609,plain,
    ( spl44_328
  <=> k1_xboole_0 = sK25(sK34) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_328])])).

fof(f2553,plain,
    ( spl44_320
  <=> v1_xboole_0(sK25(sK34)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_320])])).

fof(f2589,plain,
    ( k1_xboole_0 = sK25(sK34)
    | ~ spl44_320 ),
    inference(resolution,[],[f2554,f505])).

fof(f2554,plain,
    ( v1_xboole_0(sK25(sK34))
    | ~ spl44_320 ),
    inference(avatar_component_clause,[],[f2553])).

fof(f2587,plain,
    ( spl44_320
    | spl44_326
    | ~ spl44_176 ),
    inference(avatar_split_clause,[],[f1971,f1490,f2585,f2553])).

fof(f1490,plain,
    ( spl44_176
  <=> v1_zfmisc_1(sK25(sK34)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_176])])).

fof(f1971,plain,
    ( v1_zfmisc_1(sK4(sK25(sK34)))
    | v1_xboole_0(sK25(sK34))
    | ~ spl44_176 ),
    inference(resolution,[],[f1493,f444])).

fof(f1493,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK25(sK34)))
        | v1_zfmisc_1(X0) )
    | ~ spl44_176 ),
    inference(resolution,[],[f1491,f499])).

fof(f1491,plain,
    ( v1_zfmisc_1(sK25(sK34))
    | ~ spl44_176 ),
    inference(avatar_component_clause,[],[f1490])).

fof(f2579,plain,
    ( spl44_324
    | ~ spl44_320 ),
    inference(avatar_split_clause,[],[f2562,f2553,f2577])).

fof(f2562,plain,
    ( v4_funct_1(sK25(sK34))
    | ~ spl44_320 ),
    inference(resolution,[],[f2554,f500])).

fof(f2561,plain,
    ( spl44_320
    | spl44_322
    | ~ spl44_176 ),
    inference(avatar_split_clause,[],[f1968,f1490,f2559,f2553])).

fof(f1968,plain,
    ( v1_zfmisc_1(sK1(sK25(sK34)))
    | v1_xboole_0(sK25(sK34))
    | ~ spl44_176 ),
    inference(resolution,[],[f1493,f436])).

fof(f2548,plain,
    ( spl44_306
    | spl44_318
    | ~ spl44_128 ),
    inference(avatar_split_clause,[],[f1924,f1251,f2546,f2452])).

fof(f2452,plain,
    ( spl44_306
  <=> v1_xboole_0(sK4(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_306])])).

fof(f1924,plain,
    ( v4_funct_1(sK4(sK4(sK31)))
    | v1_xboole_0(sK4(sK31))
    | ~ spl44_128 ),
    inference(resolution,[],[f1254,f444])).

fof(f2541,plain,
    ( spl44_306
    | spl44_316
    | ~ spl44_128 ),
    inference(avatar_split_clause,[],[f1923,f1251,f2539,f2452])).

fof(f1923,plain,
    ( v4_funct_1(sK3(sK4(sK31)))
    | v1_xboole_0(sK4(sK31))
    | ~ spl44_128 ),
    inference(resolution,[],[f1254,f441])).

fof(f2534,plain,
    ( spl44_314
    | ~ spl44_258 ),
    inference(avatar_split_clause,[],[f2527,f2205,f2532])).

fof(f2205,plain,
    ( spl44_258
  <=> v4_funct_1(sK1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_258])])).

fof(f2527,plain,
    ( v1_funct_1(sK23(sK1(k1_xboole_0)))
    | ~ spl44_258 ),
    inference(resolution,[],[f2493,f605])).

fof(f2493,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK1(k1_xboole_0))
        | v1_funct_1(X1) )
    | ~ spl44_258 ),
    inference(resolution,[],[f2206,f447])).

fof(f2206,plain,
    ( v4_funct_1(sK1(k1_xboole_0))
    | ~ spl44_258 ),
    inference(avatar_component_clause,[],[f2205])).

fof(f2525,plain,
    ( spl44_256
    | spl44_23
    | ~ spl44_310 ),
    inference(avatar_split_clause,[],[f2512,f2477,f767,f2195])).

fof(f2195,plain,
    ( spl44_256
  <=> v1_subset_1(k1_xboole_0,sK31) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_256])])).

fof(f2477,plain,
    ( spl44_310
  <=> k1_xboole_0 = sK4(sK31) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_310])])).

fof(f2512,plain,
    ( v1_subset_1(k1_xboole_0,sK31)
    | ~ spl44_23
    | ~ spl44_310 ),
    inference(subsumption_resolution,[],[f2508,f768])).

fof(f2508,plain,
    ( v1_subset_1(k1_xboole_0,sK31)
    | v1_xboole_0(sK31)
    | ~ spl44_310 ),
    inference(superposition,[],[f445,f2478])).

fof(f2478,plain,
    ( k1_xboole_0 = sK4(sK31)
    | ~ spl44_310 ),
    inference(avatar_component_clause,[],[f2477])).

fof(f445,plain,(
    ! [X0] :
      ( v1_subset_1(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f344])).

fof(f2511,plain,
    ( spl44_23
    | spl44_257
    | ~ spl44_310 ),
    inference(avatar_contradiction_clause,[],[f2510])).

fof(f2510,plain,
    ( $false
    | ~ spl44_23
    | ~ spl44_257
    | ~ spl44_310 ),
    inference(subsumption_resolution,[],[f2509,f768])).

fof(f2509,plain,
    ( v1_xboole_0(sK31)
    | ~ spl44_257
    | ~ spl44_310 ),
    inference(subsumption_resolution,[],[f2508,f2199])).

fof(f2489,plain,
    ( spl44_306
    | spl44_312
    | ~ spl44_128 ),
    inference(avatar_split_clause,[],[f1922,f1251,f2487,f2452])).

fof(f1922,plain,
    ( v4_funct_1(sK2(sK4(sK31)))
    | v1_xboole_0(sK4(sK31))
    | ~ spl44_128 ),
    inference(resolution,[],[f1254,f438])).

fof(f2479,plain,
    ( spl44_310
    | ~ spl44_306 ),
    inference(avatar_split_clause,[],[f2462,f2452,f2477])).

fof(f2462,plain,
    ( k1_xboole_0 = sK4(sK31)
    | ~ spl44_306 ),
    inference(resolution,[],[f2453,f505])).

fof(f2453,plain,
    ( v1_xboole_0(sK4(sK31))
    | ~ spl44_306 ),
    inference(avatar_component_clause,[],[f2452])).

fof(f2460,plain,
    ( spl44_306
    | spl44_308
    | ~ spl44_128 ),
    inference(avatar_split_clause,[],[f1921,f1251,f2458,f2452])).

fof(f1921,plain,
    ( v4_funct_1(sK1(sK4(sK31)))
    | v1_xboole_0(sK4(sK31))
    | ~ spl44_128 ),
    inference(resolution,[],[f1254,f436])).

fof(f2447,plain,
    ( spl44_300
    | spl44_304
    | ~ spl44_126 ),
    inference(avatar_split_clause,[],[f1895,f1241,f2445,f2431])).

fof(f1241,plain,
    ( spl44_126
  <=> v4_funct_1(sK3(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_126])])).

fof(f1895,plain,
    ( v4_funct_1(sK17(sK3(sK31)))
    | v1_zfmisc_1(sK3(sK31))
    | ~ spl44_126 ),
    inference(resolution,[],[f1244,f682])).

fof(f1244,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3(sK31)))
        | v4_funct_1(X0) )
    | ~ spl44_126 ),
    inference(resolution,[],[f1242,f448])).

fof(f1242,plain,
    ( v4_funct_1(sK3(sK31))
    | ~ spl44_126 ),
    inference(avatar_component_clause,[],[f1241])).

fof(f2439,plain,
    ( spl44_300
    | spl44_302
    | ~ spl44_126 ),
    inference(avatar_split_clause,[],[f1894,f1241,f2437,f2431])).

fof(f1894,plain,
    ( v4_funct_1(sK16(sK3(sK31)))
    | v1_zfmisc_1(sK3(sK31))
    | ~ spl44_126 ),
    inference(resolution,[],[f1244,f678])).

fof(f2423,plain,
    ( spl44_290
    | spl44_298
    | ~ spl44_126 ),
    inference(avatar_split_clause,[],[f1893,f1241,f2421,f2370])).

fof(f1893,plain,
    ( v4_funct_1(sK4(sK3(sK31)))
    | v1_xboole_0(sK3(sK31))
    | ~ spl44_126 ),
    inference(resolution,[],[f1244,f444])).

fof(f2413,plain,
    ( spl44_290
    | spl44_296
    | ~ spl44_126 ),
    inference(avatar_split_clause,[],[f1892,f1241,f2411,f2370])).

fof(f1892,plain,
    ( v4_funct_1(sK3(sK3(sK31)))
    | v1_xboole_0(sK3(sK31))
    | ~ spl44_126 ),
    inference(resolution,[],[f1244,f441])).

fof(f2403,plain,
    ( spl44_290
    | spl44_294
    | ~ spl44_126 ),
    inference(avatar_split_clause,[],[f1891,f1241,f2401,f2370])).

fof(f1891,plain,
    ( v4_funct_1(sK2(sK3(sK31)))
    | v1_xboole_0(sK3(sK31))
    | ~ spl44_126 ),
    inference(resolution,[],[f1244,f438])).

fof(f2388,plain,
    ( spl44_23
    | ~ spl44_290 ),
    inference(avatar_contradiction_clause,[],[f2387])).

fof(f2387,plain,
    ( $false
    | ~ spl44_23
    | ~ spl44_290 ),
    inference(subsumption_resolution,[],[f2379,f768])).

fof(f2379,plain,
    ( v1_xboole_0(sK31)
    | ~ spl44_290 ),
    inference(resolution,[],[f2371,f442])).

fof(f442,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f342])).

fof(f2371,plain,
    ( v1_xboole_0(sK3(sK31))
    | ~ spl44_290 ),
    inference(avatar_component_clause,[],[f2370])).

fof(f2378,plain,
    ( spl44_290
    | spl44_292
    | ~ spl44_126 ),
    inference(avatar_split_clause,[],[f1890,f1241,f2376,f2370])).

fof(f1890,plain,
    ( v4_funct_1(sK1(sK3(sK31)))
    | v1_xboole_0(sK3(sK31))
    | ~ spl44_126 ),
    inference(resolution,[],[f1244,f436])).

fof(f2365,plain,
    ( spl44_284
    | spl44_288
    | ~ spl44_124 ),
    inference(avatar_split_clause,[],[f1864,f1231,f2363,f2349])).

fof(f1231,plain,
    ( spl44_124
  <=> v4_funct_1(sK2(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_124])])).

fof(f1864,plain,
    ( v4_funct_1(sK17(sK2(sK31)))
    | v1_zfmisc_1(sK2(sK31))
    | ~ spl44_124 ),
    inference(resolution,[],[f1234,f682])).

fof(f1234,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2(sK31)))
        | v4_funct_1(X0) )
    | ~ spl44_124 ),
    inference(resolution,[],[f1232,f448])).

fof(f1232,plain,
    ( v4_funct_1(sK2(sK31))
    | ~ spl44_124 ),
    inference(avatar_component_clause,[],[f1231])).

fof(f2357,plain,
    ( spl44_284
    | spl44_286
    | ~ spl44_124 ),
    inference(avatar_split_clause,[],[f1863,f1231,f2355,f2349])).

fof(f1863,plain,
    ( v4_funct_1(sK16(sK2(sK31)))
    | v1_zfmisc_1(sK2(sK31))
    | ~ spl44_124 ),
    inference(resolution,[],[f1234,f678])).

fof(f2341,plain,
    ( spl44_274
    | spl44_282
    | ~ spl44_124 ),
    inference(avatar_split_clause,[],[f1862,f1231,f2339,f2288])).

fof(f1862,plain,
    ( v4_funct_1(sK4(sK2(sK31)))
    | v1_xboole_0(sK2(sK31))
    | ~ spl44_124 ),
    inference(resolution,[],[f1234,f444])).

fof(f2331,plain,
    ( spl44_274
    | spl44_280
    | ~ spl44_124 ),
    inference(avatar_split_clause,[],[f1861,f1231,f2329,f2288])).

fof(f1861,plain,
    ( v4_funct_1(sK3(sK2(sK31)))
    | v1_xboole_0(sK2(sK31))
    | ~ spl44_124 ),
    inference(resolution,[],[f1234,f441])).

fof(f2321,plain,
    ( spl44_274
    | spl44_278
    | ~ spl44_124 ),
    inference(avatar_split_clause,[],[f1860,f1231,f2319,f2288])).

fof(f1860,plain,
    ( v4_funct_1(sK2(sK2(sK31)))
    | v1_xboole_0(sK2(sK31))
    | ~ spl44_124 ),
    inference(resolution,[],[f1234,f438])).

fof(f2306,plain,
    ( spl44_23
    | ~ spl44_274 ),
    inference(avatar_contradiction_clause,[],[f2305])).

fof(f2305,plain,
    ( $false
    | ~ spl44_23
    | ~ spl44_274 ),
    inference(subsumption_resolution,[],[f2297,f768])).

fof(f2297,plain,
    ( v1_xboole_0(sK31)
    | ~ spl44_274 ),
    inference(resolution,[],[f2289,f439])).

fof(f439,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK2(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f340])).

fof(f2289,plain,
    ( v1_xboole_0(sK2(sK31))
    | ~ spl44_274 ),
    inference(avatar_component_clause,[],[f2288])).

fof(f2296,plain,
    ( spl44_274
    | spl44_276
    | ~ spl44_124 ),
    inference(avatar_split_clause,[],[f1859,f1231,f2294,f2288])).

fof(f1859,plain,
    ( v4_funct_1(sK1(sK2(sK31)))
    | v1_xboole_0(sK2(sK31))
    | ~ spl44_124 ),
    inference(resolution,[],[f1234,f436])).

fof(f2280,plain,
    ( spl44_264
    | spl44_272
    | ~ spl44_122 ),
    inference(avatar_split_clause,[],[f1831,f1221,f2278,f2228])).

fof(f2228,plain,
    ( spl44_264
  <=> v1_xboole_0(sK1(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_264])])).

fof(f1831,plain,
    ( v4_funct_1(sK4(sK1(sK31)))
    | v1_xboole_0(sK1(sK31))
    | ~ spl44_122 ),
    inference(resolution,[],[f1224,f444])).

fof(f2270,plain,
    ( spl44_264
    | spl44_270
    | ~ spl44_122 ),
    inference(avatar_split_clause,[],[f1830,f1221,f2268,f2228])).

fof(f1830,plain,
    ( v4_funct_1(sK3(sK1(sK31)))
    | v1_xboole_0(sK1(sK31))
    | ~ spl44_122 ),
    inference(resolution,[],[f1224,f441])).

fof(f2260,plain,
    ( spl44_264
    | spl44_268
    | ~ spl44_122 ),
    inference(avatar_split_clause,[],[f1829,f1221,f2258,f2228])).

fof(f1829,plain,
    ( v4_funct_1(sK2(sK1(sK31)))
    | v1_xboole_0(sK1(sK31))
    | ~ spl44_122 ),
    inference(resolution,[],[f1224,f438])).

fof(f2246,plain,
    ( spl44_23
    | ~ spl44_264 ),
    inference(avatar_contradiction_clause,[],[f2245])).

fof(f2245,plain,
    ( $false
    | ~ spl44_23
    | ~ spl44_264 ),
    inference(subsumption_resolution,[],[f2237,f768])).

fof(f2237,plain,
    ( v1_xboole_0(sK31)
    | ~ spl44_264 ),
    inference(resolution,[],[f2229,f437])).

fof(f2229,plain,
    ( v1_xboole_0(sK1(sK31))
    | ~ spl44_264 ),
    inference(avatar_component_clause,[],[f2228])).

fof(f2236,plain,
    ( spl44_264
    | spl44_266
    | ~ spl44_122 ),
    inference(avatar_split_clause,[],[f1828,f1221,f2234,f2228])).

fof(f1828,plain,
    ( v4_funct_1(sK1(sK1(sK31)))
    | v1_xboole_0(sK1(sK31))
    | ~ spl44_122 ),
    inference(resolution,[],[f1224,f436])).

fof(f2223,plain,
    ( spl44_248
    | spl44_262
    | ~ spl44_118 ),
    inference(avatar_split_clause,[],[f1800,f1197,f2221,f2142])).

fof(f1800,plain,
    ( v4_funct_1(sK4(sK25(sK31)))
    | v1_xboole_0(sK25(sK31))
    | ~ spl44_118 ),
    inference(resolution,[],[f1200,f444])).

fof(f2216,plain,
    ( spl44_248
    | spl44_260
    | ~ spl44_118 ),
    inference(avatar_split_clause,[],[f1799,f1197,f2214,f2142])).

fof(f1799,plain,
    ( v4_funct_1(sK3(sK25(sK31)))
    | v1_xboole_0(sK25(sK31))
    | ~ spl44_118 ),
    inference(resolution,[],[f1200,f441])).

fof(f2209,plain,
    ( ~ spl44_259
    | spl44_251
    | ~ spl44_252 ),
    inference(avatar_split_clause,[],[f2208,f2166,f2145,f2202])).

fof(f2202,plain,
    ( spl44_259
  <=> ~ v4_funct_1(sK1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_259])])).

fof(f2145,plain,
    ( spl44_251
  <=> ~ v4_funct_1(sK1(sK25(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_251])])).

fof(f2208,plain,
    ( ~ v4_funct_1(sK1(k1_xboole_0))
    | ~ spl44_251
    | ~ spl44_252 ),
    inference(forward_demodulation,[],[f2146,f2167])).

fof(f2146,plain,
    ( ~ v4_funct_1(sK1(sK25(sK31)))
    | ~ spl44_251 ),
    inference(avatar_component_clause,[],[f2145])).

fof(f2207,plain,
    ( spl44_258
    | ~ spl44_250
    | ~ spl44_252 ),
    inference(avatar_split_clause,[],[f2190,f2166,f2148,f2205])).

fof(f2190,plain,
    ( v4_funct_1(sK1(k1_xboole_0))
    | ~ spl44_250
    | ~ spl44_252 ),
    inference(superposition,[],[f2149,f2167])).

fof(f2200,plain,
    ( ~ spl44_257
    | ~ spl44_252 ),
    inference(avatar_split_clause,[],[f2193,f2166,f2198])).

fof(f2193,plain,
    ( ~ v1_subset_1(k1_xboole_0,sK31)
    | ~ spl44_252 ),
    inference(superposition,[],[f609,f2167])).

fof(f2178,plain,
    ( spl44_248
    | spl44_254
    | ~ spl44_118 ),
    inference(avatar_split_clause,[],[f1798,f1197,f2176,f2142])).

fof(f1798,plain,
    ( v4_funct_1(sK2(sK25(sK31)))
    | v1_xboole_0(sK25(sK31))
    | ~ spl44_118 ),
    inference(resolution,[],[f1200,f438])).

fof(f2168,plain,
    ( spl44_252
    | ~ spl44_248 ),
    inference(avatar_split_clause,[],[f2152,f2142,f2166])).

fof(f2152,plain,
    ( k1_xboole_0 = sK25(sK31)
    | ~ spl44_248 ),
    inference(resolution,[],[f2143,f505])).

fof(f2143,plain,
    ( v1_xboole_0(sK25(sK31))
    | ~ spl44_248 ),
    inference(avatar_component_clause,[],[f2142])).

fof(f2150,plain,
    ( spl44_248
    | spl44_250
    | ~ spl44_118 ),
    inference(avatar_split_clause,[],[f1797,f1197,f2148,f2142])).

fof(f1797,plain,
    ( v4_funct_1(sK1(sK25(sK31)))
    | v1_xboole_0(sK25(sK31))
    | ~ spl44_118 ),
    inference(resolution,[],[f1200,f436])).

fof(f2096,plain,
    ( spl44_246
    | ~ spl44_132 ),
    inference(avatar_split_clause,[],[f2089,f1270,f2094])).

fof(f2089,plain,
    ( v4_funct_1(sK25(sK16(sK31)))
    | ~ spl44_132 ),
    inference(resolution,[],[f1675,f608])).

fof(f1675,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK16(sK31)))
        | v4_funct_1(X0) )
    | ~ spl44_132 ),
    inference(resolution,[],[f1271,f448])).

fof(f2048,plain,
    ( spl44_244
    | ~ spl44_182 ),
    inference(avatar_split_clause,[],[f2030,f1513,f2046])).

fof(f2046,plain,
    ( spl44_244
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK4(sK34)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_244])])).

fof(f2030,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK4(sK34))))
    | ~ spl44_182 ),
    inference(resolution,[],[f1516,f605])).

fof(f2040,plain,
    ( spl44_242
    | ~ spl44_182 ),
    inference(avatar_split_clause,[],[f2032,f1513,f2038])).

fof(f2032,plain,
    ( v1_zfmisc_1(sK25(sK4(sK34)))
    | ~ spl44_182 ),
    inference(resolution,[],[f1516,f608])).

fof(f2020,plain,
    ( spl44_240
    | ~ spl44_180 ),
    inference(avatar_split_clause,[],[f2002,f1505,f2018])).

fof(f2018,plain,
    ( spl44_240
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK1(sK34)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_240])])).

fof(f2002,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK1(sK34))))
    | ~ spl44_180 ),
    inference(resolution,[],[f1508,f605])).

fof(f2012,plain,
    ( spl44_238
    | ~ spl44_180 ),
    inference(avatar_split_clause,[],[f2004,f1505,f2010])).

fof(f2004,plain,
    ( v1_zfmisc_1(sK25(sK1(sK34)))
    | ~ spl44_180 ),
    inference(resolution,[],[f1508,f608])).

fof(f1992,plain,
    ( spl44_236
    | ~ spl44_176 ),
    inference(avatar_split_clause,[],[f1974,f1490,f1990])).

fof(f1990,plain,
    ( spl44_236
  <=> v1_zfmisc_1(sK23(k1_zfmisc_1(sK25(sK34)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_236])])).

fof(f1974,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK25(sK34))))
    | ~ spl44_176 ),
    inference(resolution,[],[f1493,f605])).

fof(f1984,plain,
    ( spl44_234
    | ~ spl44_176 ),
    inference(avatar_split_clause,[],[f1976,f1490,f1982])).

fof(f1976,plain,
    ( v1_zfmisc_1(sK25(sK25(sK34)))
    | ~ spl44_176 ),
    inference(resolution,[],[f1493,f608])).

fof(f1965,plain,
    ( spl44_232
    | ~ spl44_120 ),
    inference(avatar_split_clause,[],[f1958,f1207,f1963])).

fof(f1963,plain,
    ( spl44_232
  <=> v1_relat_1(sK23(sK23(k1_zfmisc_1(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_232])])).

fof(f1958,plain,
    ( v1_relat_1(sK23(sK23(k1_zfmisc_1(sK31))))
    | ~ spl44_120 ),
    inference(resolution,[],[f1259,f605])).

fof(f1259,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK23(k1_zfmisc_1(sK31)))
        | v1_relat_1(X2) )
    | ~ spl44_120 ),
    inference(resolution,[],[f1208,f446])).

fof(f1957,plain,
    ( spl44_230
    | ~ spl44_120 ),
    inference(avatar_split_clause,[],[f1950,f1207,f1955])).

fof(f1955,plain,
    ( spl44_230
  <=> v1_funct_1(sK23(sK23(k1_zfmisc_1(sK31)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_230])])).

fof(f1950,plain,
    ( v1_funct_1(sK23(sK23(k1_zfmisc_1(sK31))))
    | ~ spl44_120 ),
    inference(resolution,[],[f1258,f605])).

fof(f1258,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK23(k1_zfmisc_1(sK31)))
        | v1_funct_1(X1) )
    | ~ spl44_120 ),
    inference(resolution,[],[f1208,f447])).

fof(f1946,plain,
    ( spl44_228
    | ~ spl44_128 ),
    inference(avatar_split_clause,[],[f1927,f1251,f1944])).

fof(f1927,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK4(sK31))))
    | ~ spl44_128 ),
    inference(resolution,[],[f1254,f605])).

fof(f1936,plain,
    ( spl44_226
    | ~ spl44_128 ),
    inference(avatar_split_clause,[],[f1929,f1251,f1934])).

fof(f1929,plain,
    ( v4_funct_1(sK25(sK4(sK31)))
    | ~ spl44_128 ),
    inference(resolution,[],[f1254,f608])).

fof(f1915,plain,
    ( spl44_224
    | ~ spl44_126 ),
    inference(avatar_split_clause,[],[f1896,f1241,f1913])).

fof(f1896,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK3(sK31))))
    | ~ spl44_126 ),
    inference(resolution,[],[f1244,f605])).

fof(f1905,plain,
    ( spl44_222
    | ~ spl44_126 ),
    inference(avatar_split_clause,[],[f1898,f1241,f1903])).

fof(f1898,plain,
    ( v4_funct_1(sK25(sK3(sK31)))
    | ~ spl44_126 ),
    inference(resolution,[],[f1244,f608])).

fof(f1884,plain,
    ( spl44_220
    | ~ spl44_124 ),
    inference(avatar_split_clause,[],[f1865,f1231,f1882])).

fof(f1865,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK2(sK31))))
    | ~ spl44_124 ),
    inference(resolution,[],[f1234,f605])).

fof(f1874,plain,
    ( spl44_218
    | ~ spl44_124 ),
    inference(avatar_split_clause,[],[f1867,f1231,f1872])).

fof(f1867,plain,
    ( v4_funct_1(sK25(sK2(sK31)))
    | ~ spl44_124 ),
    inference(resolution,[],[f1234,f608])).

fof(f1853,plain,
    ( spl44_216
    | ~ spl44_122 ),
    inference(avatar_split_clause,[],[f1834,f1221,f1851])).

fof(f1834,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK1(sK31))))
    | ~ spl44_122 ),
    inference(resolution,[],[f1224,f605])).

fof(f1843,plain,
    ( spl44_214
    | ~ spl44_122 ),
    inference(avatar_split_clause,[],[f1836,f1221,f1841])).

fof(f1836,plain,
    ( v4_funct_1(sK25(sK1(sK31)))
    | ~ spl44_122 ),
    inference(resolution,[],[f1224,f608])).

fof(f1822,plain,
    ( spl44_212
    | ~ spl44_118 ),
    inference(avatar_split_clause,[],[f1803,f1197,f1820])).

fof(f1803,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK25(sK31))))
    | ~ spl44_118 ),
    inference(resolution,[],[f1200,f605])).

fof(f1812,plain,
    ( spl44_210
    | ~ spl44_118 ),
    inference(avatar_split_clause,[],[f1805,f1197,f1810])).

fof(f1805,plain,
    ( v4_funct_1(sK25(sK25(sK31)))
    | ~ spl44_118 ),
    inference(resolution,[],[f1200,f608])).

fof(f1740,plain,
    ( ~ spl44_209
    | ~ spl44_76
    | ~ spl44_78
    | spl44_81 ),
    inference(avatar_split_clause,[],[f1733,f970,f963,f956,f1738])).

fof(f1738,plain,
    ( spl44_209
  <=> ~ v1_zfmisc_1(sK42) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_209])])).

fof(f956,plain,
    ( spl44_76
  <=> v1_relat_1(sK42) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_76])])).

fof(f963,plain,
    ( spl44_78
  <=> v1_funct_1(sK42) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_78])])).

fof(f970,plain,
    ( spl44_81
  <=> ~ v3_funct_1(sK42) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_81])])).

fof(f1733,plain,
    ( ~ v1_zfmisc_1(sK42)
    | ~ spl44_76
    | ~ spl44_78
    | ~ spl44_81 ),
    inference(subsumption_resolution,[],[f1732,f957])).

fof(f957,plain,
    ( v1_relat_1(sK42)
    | ~ spl44_76 ),
    inference(avatar_component_clause,[],[f956])).

fof(f1732,plain,
    ( ~ v1_zfmisc_1(sK42)
    | ~ v1_relat_1(sK42)
    | ~ spl44_78
    | ~ spl44_81 ),
    inference(subsumption_resolution,[],[f1731,f964])).

fof(f964,plain,
    ( v1_funct_1(sK42)
    | ~ spl44_78 ),
    inference(avatar_component_clause,[],[f963])).

fof(f1731,plain,
    ( ~ v1_zfmisc_1(sK42)
    | ~ v1_funct_1(sK42)
    | ~ v1_relat_1(sK42)
    | ~ spl44_81 ),
    inference(resolution,[],[f590,f971])).

fof(f971,plain,
    ( ~ v3_funct_1(sK42)
    | ~ spl44_81 ),
    inference(avatar_component_clause,[],[f970])).

fof(f590,plain,(
    ! [X0] :
      ( v3_funct_1(X0)
      | ~ v1_zfmisc_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f310])).

fof(f310,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & ~ v1_zfmisc_1(X0) )
      | v3_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f309])).

fof(f309,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & ~ v1_zfmisc_1(X0) )
      | v3_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f54])).

fof(f54,axiom,(
    ! [X0] :
      ( ( ~ v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & ~ v1_zfmisc_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',cc6_funct_1)).

fof(f1702,plain,
    ( spl44_206
    | ~ spl44_134 ),
    inference(avatar_split_clause,[],[f1695,f1280,f1700])).

fof(f1700,plain,
    ( spl44_206
  <=> v1_relat_1(sK23(sK17(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_206])])).

fof(f1695,plain,
    ( v1_relat_1(sK23(sK17(sK31)))
    | ~ spl44_134 ),
    inference(resolution,[],[f1680,f605])).

fof(f1680,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK17(sK31))
        | v1_relat_1(X2) )
    | ~ spl44_134 ),
    inference(resolution,[],[f1281,f446])).

fof(f1673,plain,
    ( spl44_204
    | spl44_23
    | ~ spl44_130 ),
    inference(avatar_split_clause,[],[f1650,f1264,f767,f1671])).

fof(f1264,plain,
    ( spl44_130
  <=> v1_zfmisc_1(sK31) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_130])])).

fof(f1650,plain,
    ( v1_zfmisc_1(sK4(sK31))
    | ~ spl44_23
    | ~ spl44_130 ),
    inference(subsumption_resolution,[],[f1643,f768])).

fof(f1643,plain,
    ( v1_zfmisc_1(sK4(sK31))
    | v1_xboole_0(sK31)
    | ~ spl44_130 ),
    inference(resolution,[],[f1555,f444])).

fof(f1555,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK31))
        | v1_zfmisc_1(X0) )
    | ~ spl44_130 ),
    inference(resolution,[],[f1265,f499])).

fof(f1265,plain,
    ( v1_zfmisc_1(sK31)
    | ~ spl44_130 ),
    inference(avatar_component_clause,[],[f1264])).

fof(f1665,plain,
    ( spl44_202
    | spl44_23
    | ~ spl44_130 ),
    inference(avatar_split_clause,[],[f1649,f1264,f767,f1663])).

fof(f1649,plain,
    ( v1_zfmisc_1(sK1(sK31))
    | ~ spl44_23
    | ~ spl44_130 ),
    inference(subsumption_resolution,[],[f1640,f768])).

fof(f1640,plain,
    ( v1_zfmisc_1(sK1(sK31))
    | v1_xboole_0(sK31)
    | ~ spl44_130 ),
    inference(resolution,[],[f1555,f436])).

fof(f1658,plain,
    ( spl44_200
    | ~ spl44_130 ),
    inference(avatar_split_clause,[],[f1646,f1264,f1656])).

fof(f1646,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK31)))
    | ~ spl44_130 ),
    inference(resolution,[],[f1555,f605])).

fof(f1633,plain,
    ( spl44_198
    | ~ spl44_192 ),
    inference(avatar_split_clause,[],[f1602,f1597,f1631])).

fof(f1631,plain,
    ( spl44_198
  <=> k1_xboole_0 = sK23(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_198])])).

fof(f1597,plain,
    ( spl44_192
  <=> v1_xboole_0(sK23(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_192])])).

fof(f1602,plain,
    ( k1_xboole_0 = sK23(k1_zfmisc_1(k1_xboole_0))
    | ~ spl44_192 ),
    inference(resolution,[],[f1598,f505])).

fof(f1598,plain,
    ( v1_xboole_0(sK23(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl44_192 ),
    inference(avatar_component_clause,[],[f1597])).

fof(f1626,plain,
    ( ~ spl44_197
    | ~ spl44_194 ),
    inference(avatar_split_clause,[],[f1619,f1608,f1624])).

fof(f1624,plain,
    ( spl44_197
  <=> ~ v1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_197])])).

fof(f1608,plain,
    ( spl44_194
  <=> k1_xboole_0 = sK25(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_194])])).

fof(f1619,plain,
    ( ~ v1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl44_194 ),
    inference(superposition,[],[f609,f1609])).

fof(f1609,plain,
    ( k1_xboole_0 = sK25(k1_xboole_0)
    | ~ spl44_194 ),
    inference(avatar_component_clause,[],[f1608])).

fof(f1610,plain,
    ( spl44_194
    | ~ spl44_190 ),
    inference(avatar_split_clause,[],[f1591,f1586,f1608])).

fof(f1586,plain,
    ( spl44_190
  <=> v1_xboole_0(sK25(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_190])])).

fof(f1591,plain,
    ( k1_xboole_0 = sK25(k1_xboole_0)
    | ~ spl44_190 ),
    inference(resolution,[],[f1587,f505])).

fof(f1587,plain,
    ( v1_xboole_0(sK25(k1_xboole_0))
    | ~ spl44_190 ),
    inference(avatar_component_clause,[],[f1586])).

fof(f1599,plain,
    ( spl44_192
    | ~ spl44_8 ),
    inference(avatar_split_clause,[],[f1579,f718,f1597])).

fof(f1579,plain,
    ( v1_xboole_0(sK23(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl44_8 ),
    inference(resolution,[],[f1559,f605])).

fof(f1559,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X2) )
    | ~ spl44_8 ),
    inference(resolution,[],[f506,f719])).

fof(f506,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f227])).

fof(f227,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',cc1_subset_1)).

fof(f1588,plain,
    ( spl44_190
    | ~ spl44_8 ),
    inference(avatar_split_clause,[],[f1581,f718,f1586])).

fof(f1581,plain,
    ( v1_xboole_0(sK25(k1_xboole_0))
    | ~ spl44_8 ),
    inference(resolution,[],[f1559,f608])).

fof(f1570,plain,
    ( spl44_188
    | ~ spl44_134 ),
    inference(avatar_split_clause,[],[f1557,f1280,f1568])).

fof(f1568,plain,
    ( spl44_188
  <=> v1_funct_1(sK23(sK17(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_188])])).

fof(f1557,plain,
    ( v1_funct_1(sK23(sK17(sK31)))
    | ~ spl44_134 ),
    inference(resolution,[],[f1544,f605])).

fof(f1544,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK17(sK31))
        | v1_funct_1(X1) )
    | ~ spl44_134 ),
    inference(resolution,[],[f1281,f447])).

fof(f1554,plain,
    ( spl44_186
    | ~ spl44_132 ),
    inference(avatar_split_clause,[],[f1547,f1270,f1552])).

fof(f1552,plain,
    ( spl44_186
  <=> v1_relat_1(sK23(sK16(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_186])])).

fof(f1547,plain,
    ( v1_relat_1(sK23(sK16(sK31)))
    | ~ spl44_132 ),
    inference(resolution,[],[f1542,f605])).

fof(f1542,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK16(sK31))
        | v1_relat_1(X2) )
    | ~ spl44_132 ),
    inference(resolution,[],[f1271,f446])).

fof(f1538,plain,
    ( spl44_184
    | ~ spl44_130 ),
    inference(avatar_split_clause,[],[f1528,f1264,f1536])).

fof(f1528,plain,
    ( v1_zfmisc_1(sK25(sK31))
    | ~ spl44_130 ),
    inference(resolution,[],[f1470,f608])).

fof(f1470,plain,
    ( ! [X17] :
        ( ~ m1_subset_1(X17,k1_zfmisc_1(sK31))
        | v1_zfmisc_1(X17) )
    | ~ spl44_130 ),
    inference(resolution,[],[f499,f1265])).

fof(f1515,plain,
    ( spl44_182
    | spl44_37
    | ~ spl44_38 ),
    inference(avatar_split_clause,[],[f1484,f823,f816,f1513])).

fof(f823,plain,
    ( spl44_38
  <=> v1_zfmisc_1(sK34) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_38])])).

fof(f1484,plain,
    ( v1_zfmisc_1(sK4(sK34))
    | ~ spl44_37
    | ~ spl44_38 ),
    inference(subsumption_resolution,[],[f1477,f817])).

fof(f1477,plain,
    ( v1_zfmisc_1(sK4(sK34))
    | v1_xboole_0(sK34)
    | ~ spl44_38 ),
    inference(resolution,[],[f1471,f444])).

fof(f1471,plain,
    ( ! [X18] :
        ( ~ m1_subset_1(X18,k1_zfmisc_1(sK34))
        | v1_zfmisc_1(X18) )
    | ~ spl44_38 ),
    inference(resolution,[],[f499,f824])).

fof(f824,plain,
    ( v1_zfmisc_1(sK34)
    | ~ spl44_38 ),
    inference(avatar_component_clause,[],[f823])).

fof(f1507,plain,
    ( spl44_180
    | spl44_37
    | ~ spl44_38 ),
    inference(avatar_split_clause,[],[f1483,f823,f816,f1505])).

fof(f1483,plain,
    ( v1_zfmisc_1(sK1(sK34))
    | ~ spl44_37
    | ~ spl44_38 ),
    inference(subsumption_resolution,[],[f1474,f817])).

fof(f1474,plain,
    ( v1_zfmisc_1(sK1(sK34))
    | v1_xboole_0(sK34)
    | ~ spl44_38 ),
    inference(resolution,[],[f1471,f436])).

fof(f1500,plain,
    ( spl44_178
    | ~ spl44_38 ),
    inference(avatar_split_clause,[],[f1480,f823,f1498])).

fof(f1480,plain,
    ( v1_zfmisc_1(sK23(k1_zfmisc_1(sK34)))
    | ~ spl44_38 ),
    inference(resolution,[],[f1471,f605])).

fof(f1492,plain,
    ( spl44_176
    | ~ spl44_38 ),
    inference(avatar_split_clause,[],[f1482,f823,f1490])).

fof(f1482,plain,
    ( v1_zfmisc_1(sK25(sK34))
    | ~ spl44_38 ),
    inference(resolution,[],[f1471,f608])).

fof(f1460,plain,
    ( spl44_174
    | ~ spl44_136 ),
    inference(avatar_split_clause,[],[f1453,f1298,f1458])).

fof(f1458,plain,
    ( spl44_174
  <=> v1_relat_1(sK23(sK25(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_174])])).

fof(f1298,plain,
    ( spl44_136
  <=> v4_funct_1(sK25(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_136])])).

fof(f1453,plain,
    ( v1_relat_1(sK23(sK25(k1_xboole_0)))
    | ~ spl44_136 ),
    inference(resolution,[],[f1303,f605])).

fof(f1303,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(k1_xboole_0))
        | v1_relat_1(X2) )
    | ~ spl44_136 ),
    inference(resolution,[],[f1299,f446])).

fof(f1299,plain,
    ( v4_funct_1(sK25(k1_xboole_0))
    | ~ spl44_136 ),
    inference(avatar_component_clause,[],[f1298])).

fof(f1452,plain,
    ( spl44_172
    | ~ spl44_136 ),
    inference(avatar_split_clause,[],[f1445,f1298,f1450])).

fof(f1450,plain,
    ( spl44_172
  <=> v1_funct_1(sK23(sK25(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_172])])).

fof(f1445,plain,
    ( v1_funct_1(sK23(sK25(k1_xboole_0)))
    | ~ spl44_136 ),
    inference(resolution,[],[f1302,f605])).

fof(f1302,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(k1_xboole_0))
        | v1_funct_1(X1) )
    | ~ spl44_136 ),
    inference(resolution,[],[f1299,f447])).

fof(f1444,plain,
    ( spl44_170
    | ~ spl44_132 ),
    inference(avatar_split_clause,[],[f1437,f1270,f1442])).

fof(f1442,plain,
    ( spl44_170
  <=> v1_funct_1(sK23(sK16(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_170])])).

fof(f1437,plain,
    ( v1_funct_1(sK23(sK16(sK31)))
    | ~ spl44_132 ),
    inference(resolution,[],[f1274,f605])).

fof(f1274,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK16(sK31))
        | v1_funct_1(X1) )
    | ~ spl44_132 ),
    inference(resolution,[],[f1271,f447])).

fof(f1436,plain,
    ( spl44_168
    | ~ spl44_128 ),
    inference(avatar_split_clause,[],[f1429,f1251,f1434])).

fof(f1434,plain,
    ( spl44_168
  <=> v1_relat_1(sK23(sK4(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_168])])).

fof(f1429,plain,
    ( v1_relat_1(sK23(sK4(sK31)))
    | ~ spl44_128 ),
    inference(resolution,[],[f1256,f605])).

fof(f1256,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK4(sK31))
        | v1_relat_1(X2) )
    | ~ spl44_128 ),
    inference(resolution,[],[f1252,f446])).

fof(f1428,plain,
    ( spl44_166
    | ~ spl44_128 ),
    inference(avatar_split_clause,[],[f1398,f1251,f1426])).

fof(f1426,plain,
    ( spl44_166
  <=> v1_funct_1(sK23(sK4(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_166])])).

fof(f1398,plain,
    ( v1_funct_1(sK23(sK4(sK31)))
    | ~ spl44_128 ),
    inference(resolution,[],[f1255,f605])).

fof(f1255,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK4(sK31))
        | v1_funct_1(X1) )
    | ~ spl44_128 ),
    inference(resolution,[],[f1252,f447])).

fof(f1421,plain,
    ( spl44_162
    | spl44_164 ),
    inference(avatar_split_clause,[],[f1400,f1419,f1413])).

fof(f1413,plain,
    ( spl44_162
  <=> ! [X2] : ~ v1_relat_1(X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_162])])).

fof(f1419,plain,
    ( spl44_164
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_164])])).

fof(f1400,plain,(
    ! [X2] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f497,f1036])).

fof(f497,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f218])).

fof(f218,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',cc2_relat_1)).

fof(f1397,plain,
    ( spl44_160
    | ~ spl44_126 ),
    inference(avatar_split_clause,[],[f1390,f1241,f1395])).

fof(f1395,plain,
    ( spl44_160
  <=> v1_relat_1(sK23(sK3(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_160])])).

fof(f1390,plain,
    ( v1_relat_1(sK23(sK3(sK31)))
    | ~ spl44_126 ),
    inference(resolution,[],[f1246,f605])).

fof(f1246,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK3(sK31))
        | v1_relat_1(X2) )
    | ~ spl44_126 ),
    inference(resolution,[],[f1242,f446])).

fof(f1389,plain,
    ( spl44_158
    | ~ spl44_126 ),
    inference(avatar_split_clause,[],[f1382,f1241,f1387])).

fof(f1387,plain,
    ( spl44_158
  <=> v1_funct_1(sK23(sK3(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_158])])).

fof(f1382,plain,
    ( v1_funct_1(sK23(sK3(sK31)))
    | ~ spl44_126 ),
    inference(resolution,[],[f1245,f605])).

fof(f1245,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK3(sK31))
        | v1_funct_1(X1) )
    | ~ spl44_126 ),
    inference(resolution,[],[f1242,f447])).

fof(f1381,plain,
    ( spl44_156
    | ~ spl44_124 ),
    inference(avatar_split_clause,[],[f1374,f1231,f1379])).

fof(f1379,plain,
    ( spl44_156
  <=> v1_relat_1(sK23(sK2(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_156])])).

fof(f1374,plain,
    ( v1_relat_1(sK23(sK2(sK31)))
    | ~ spl44_124 ),
    inference(resolution,[],[f1236,f605])).

fof(f1236,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK2(sK31))
        | v1_relat_1(X2) )
    | ~ spl44_124 ),
    inference(resolution,[],[f1232,f446])).

fof(f1373,plain,
    ( spl44_154
    | ~ spl44_124 ),
    inference(avatar_split_clause,[],[f1366,f1231,f1371])).

fof(f1371,plain,
    ( spl44_154
  <=> v1_funct_1(sK23(sK2(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_154])])).

fof(f1366,plain,
    ( v1_funct_1(sK23(sK2(sK31)))
    | ~ spl44_124 ),
    inference(resolution,[],[f1235,f605])).

fof(f1235,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK2(sK31))
        | v1_funct_1(X1) )
    | ~ spl44_124 ),
    inference(resolution,[],[f1232,f447])).

fof(f1365,plain,
    ( spl44_152
    | ~ spl44_122 ),
    inference(avatar_split_clause,[],[f1358,f1221,f1363])).

fof(f1363,plain,
    ( spl44_152
  <=> v1_relat_1(sK23(sK1(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_152])])).

fof(f1358,plain,
    ( v1_relat_1(sK23(sK1(sK31)))
    | ~ spl44_122 ),
    inference(resolution,[],[f1226,f605])).

fof(f1226,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK1(sK31))
        | v1_relat_1(X2) )
    | ~ spl44_122 ),
    inference(resolution,[],[f1222,f446])).

fof(f1357,plain,
    ( spl44_150
    | ~ spl44_122 ),
    inference(avatar_split_clause,[],[f1350,f1221,f1355])).

fof(f1355,plain,
    ( spl44_150
  <=> v1_funct_1(sK23(sK1(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_150])])).

fof(f1350,plain,
    ( v1_funct_1(sK23(sK1(sK31)))
    | ~ spl44_122 ),
    inference(resolution,[],[f1225,f605])).

fof(f1225,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK1(sK31))
        | v1_funct_1(X1) )
    | ~ spl44_122 ),
    inference(resolution,[],[f1222,f447])).

fof(f1349,plain,
    ( spl44_148
    | ~ spl44_118 ),
    inference(avatar_split_clause,[],[f1342,f1197,f1347])).

fof(f1347,plain,
    ( spl44_148
  <=> v1_relat_1(sK23(sK25(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_148])])).

fof(f1342,plain,
    ( v1_relat_1(sK23(sK25(sK31)))
    | ~ spl44_118 ),
    inference(resolution,[],[f1202,f605])).

fof(f1202,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK25(sK31))
        | v1_relat_1(X2) )
    | ~ spl44_118 ),
    inference(resolution,[],[f1198,f446])).

fof(f1341,plain,
    ( spl44_146
    | ~ spl44_118 ),
    inference(avatar_split_clause,[],[f1334,f1197,f1339])).

fof(f1339,plain,
    ( spl44_146
  <=> v1_funct_1(sK23(sK25(sK31))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_146])])).

fof(f1334,plain,
    ( v1_funct_1(sK23(sK25(sK31)))
    | ~ spl44_118 ),
    inference(resolution,[],[f1201,f605])).

fof(f1201,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK25(sK31))
        | v1_funct_1(X1) )
    | ~ spl44_118 ),
    inference(resolution,[],[f1198,f447])).

fof(f1333,plain,
    ( spl44_140
    | spl44_144
    | ~ spl44_88 ),
    inference(avatar_split_clause,[],[f1290,f1002,f1331,f1318])).

fof(f1318,plain,
    ( spl44_140
  <=> v1_zfmisc_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_140])])).

fof(f1331,plain,
    ( spl44_144
  <=> v4_funct_1(sK17(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_144])])).

fof(f1002,plain,
    ( spl44_88
  <=> v4_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_88])])).

fof(f1290,plain,
    ( v4_funct_1(sK17(k1_xboole_0))
    | v1_zfmisc_1(k1_xboole_0)
    | ~ spl44_88 ),
    inference(resolution,[],[f1172,f682])).

fof(f1172,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | v4_funct_1(X2) )
    | ~ spl44_88 ),
    inference(resolution,[],[f448,f1003])).

fof(f1003,plain,
    ( v4_funct_1(k1_xboole_0)
    | ~ spl44_88 ),
    inference(avatar_component_clause,[],[f1002])).

fof(f1326,plain,
    ( spl44_140
    | spl44_142
    | ~ spl44_88 ),
    inference(avatar_split_clause,[],[f1289,f1002,f1324,f1318])).

fof(f1324,plain,
    ( spl44_142
  <=> v4_funct_1(sK16(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_142])])).

fof(f1289,plain,
    ( v4_funct_1(sK16(k1_xboole_0))
    | v1_zfmisc_1(k1_xboole_0)
    | ~ spl44_88 ),
    inference(resolution,[],[f1172,f678])).

fof(f1310,plain,
    ( spl44_138
    | ~ spl44_88 ),
    inference(avatar_split_clause,[],[f1291,f1002,f1308])).

fof(f1308,plain,
    ( spl44_138
  <=> v4_funct_1(sK23(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_138])])).

fof(f1291,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl44_88 ),
    inference(resolution,[],[f1172,f605])).

fof(f1300,plain,
    ( spl44_136
    | ~ spl44_88 ),
    inference(avatar_split_clause,[],[f1293,f1002,f1298])).

fof(f1293,plain,
    ( v4_funct_1(sK25(k1_xboole_0))
    | ~ spl44_88 ),
    inference(resolution,[],[f1172,f608])).

fof(f1282,plain,
    ( spl44_130
    | spl44_134
    | ~ spl44_24 ),
    inference(avatar_split_clause,[],[f1185,f774,f1280,f1264])).

fof(f774,plain,
    ( spl44_24
  <=> v4_funct_1(sK31) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_24])])).

fof(f1185,plain,
    ( v4_funct_1(sK17(sK31))
    | v1_zfmisc_1(sK31)
    | ~ spl44_24 ),
    inference(resolution,[],[f1175,f682])).

fof(f1175,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(sK31))
        | v4_funct_1(X6) )
    | ~ spl44_24 ),
    inference(resolution,[],[f448,f775])).

fof(f775,plain,
    ( v4_funct_1(sK31)
    | ~ spl44_24 ),
    inference(avatar_component_clause,[],[f774])).

fof(f1272,plain,
    ( spl44_130
    | spl44_132
    | ~ spl44_24 ),
    inference(avatar_split_clause,[],[f1184,f774,f1270,f1264])).

fof(f1184,plain,
    ( v4_funct_1(sK16(sK31))
    | v1_zfmisc_1(sK31)
    | ~ spl44_24 ),
    inference(resolution,[],[f1175,f678])).

fof(f1253,plain,
    ( spl44_128
    | spl44_23
    | ~ spl44_24 ),
    inference(avatar_split_clause,[],[f1192,f774,f767,f1251])).

fof(f1192,plain,
    ( v4_funct_1(sK4(sK31))
    | ~ spl44_23
    | ~ spl44_24 ),
    inference(subsumption_resolution,[],[f1183,f768])).

fof(f1183,plain,
    ( v4_funct_1(sK4(sK31))
    | v1_xboole_0(sK31)
    | ~ spl44_24 ),
    inference(resolution,[],[f1175,f444])).

fof(f1243,plain,
    ( spl44_126
    | spl44_23
    | ~ spl44_24 ),
    inference(avatar_split_clause,[],[f1191,f774,f767,f1241])).

fof(f1191,plain,
    ( v4_funct_1(sK3(sK31))
    | ~ spl44_23
    | ~ spl44_24 ),
    inference(subsumption_resolution,[],[f1182,f768])).

fof(f1182,plain,
    ( v4_funct_1(sK3(sK31))
    | v1_xboole_0(sK31)
    | ~ spl44_24 ),
    inference(resolution,[],[f1175,f441])).

fof(f1233,plain,
    ( spl44_124
    | spl44_23
    | ~ spl44_24 ),
    inference(avatar_split_clause,[],[f1190,f774,f767,f1231])).

fof(f1190,plain,
    ( v4_funct_1(sK2(sK31))
    | ~ spl44_23
    | ~ spl44_24 ),
    inference(subsumption_resolution,[],[f1181,f768])).

fof(f1181,plain,
    ( v4_funct_1(sK2(sK31))
    | v1_xboole_0(sK31)
    | ~ spl44_24 ),
    inference(resolution,[],[f1175,f438])).

fof(f1223,plain,
    ( spl44_122
    | spl44_23
    | ~ spl44_24 ),
    inference(avatar_split_clause,[],[f1189,f774,f767,f1221])).

fof(f1189,plain,
    ( v4_funct_1(sK1(sK31))
    | ~ spl44_23
    | ~ spl44_24 ),
    inference(subsumption_resolution,[],[f1180,f768])).

fof(f1180,plain,
    ( v4_funct_1(sK1(sK31))
    | v1_xboole_0(sK31)
    | ~ spl44_24 ),
    inference(resolution,[],[f1175,f436])).

fof(f1209,plain,
    ( spl44_120
    | ~ spl44_24 ),
    inference(avatar_split_clause,[],[f1186,f774,f1207])).

fof(f1186,plain,
    ( v4_funct_1(sK23(k1_zfmisc_1(sK31)))
    | ~ spl44_24 ),
    inference(resolution,[],[f1175,f605])).

fof(f1199,plain,
    ( spl44_118
    | ~ spl44_24 ),
    inference(avatar_split_clause,[],[f1188,f774,f1197])).

fof(f1188,plain,
    ( v4_funct_1(sK25(sK31))
    | ~ spl44_24 ),
    inference(resolution,[],[f1175,f608])).

fof(f1154,plain,
    ( spl44_116
    | ~ spl44_88 ),
    inference(avatar_split_clause,[],[f1147,f1002,f1152])).

fof(f1152,plain,
    ( spl44_116
  <=> v1_funct_1(sK23(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_116])])).

fof(f1147,plain,
    ( v1_funct_1(sK23(k1_xboole_0))
    | ~ spl44_88 ),
    inference(resolution,[],[f1133,f605])).

fof(f1133,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_xboole_0)
        | v1_funct_1(X2) )
    | ~ spl44_88 ),
    inference(resolution,[],[f447,f1003])).

fof(f1146,plain,
    ( spl44_114
    | ~ spl44_24 ),
    inference(avatar_split_clause,[],[f1139,f774,f1144])).

fof(f1144,plain,
    ( spl44_114
  <=> v1_funct_1(sK23(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_114])])).

fof(f1139,plain,
    ( v1_funct_1(sK23(sK31))
    | ~ spl44_24 ),
    inference(resolution,[],[f1136,f605])).

fof(f1136,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,sK31)
        | v1_funct_1(X6) )
    | ~ spl44_24 ),
    inference(resolution,[],[f447,f775])).

fof(f1131,plain,
    ( spl44_112
    | ~ spl44_88 ),
    inference(avatar_split_clause,[],[f1124,f1002,f1129])).

fof(f1129,plain,
    ( spl44_112
  <=> v1_relat_1(sK23(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_112])])).

fof(f1124,plain,
    ( v1_relat_1(sK23(k1_xboole_0))
    | ~ spl44_88 ),
    inference(resolution,[],[f1110,f605])).

fof(f1110,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_xboole_0)
        | v1_relat_1(X2) )
    | ~ spl44_88 ),
    inference(resolution,[],[f446,f1003])).

fof(f1123,plain,
    ( spl44_110
    | ~ spl44_24 ),
    inference(avatar_split_clause,[],[f1116,f774,f1121])).

fof(f1121,plain,
    ( spl44_110
  <=> v1_relat_1(sK23(sK31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_110])])).

fof(f1116,plain,
    ( v1_relat_1(sK23(sK31))
    | ~ spl44_24 ),
    inference(resolution,[],[f1113,f605])).

fof(f1113,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,sK31)
        | v1_relat_1(X6) )
    | ~ spl44_24 ),
    inference(resolution,[],[f446,f775])).

fof(f1102,plain,
    ( spl44_108
    | ~ spl44_58 ),
    inference(avatar_split_clause,[],[f1072,f893,f1100])).

fof(f1100,plain,
    ( spl44_108
  <=> k1_struct_0(sK38) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_108])])).

fof(f893,plain,
    ( spl44_58
  <=> l1_pre_topc(sK38) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_58])])).

fof(f1072,plain,
    ( k1_struct_0(sK38) = k1_xboole_0
    | ~ spl44_58 ),
    inference(resolution,[],[f1038,f894])).

fof(f894,plain,
    ( l1_pre_topc(sK38)
    | ~ spl44_58 ),
    inference(avatar_component_clause,[],[f893])).

fof(f1038,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k1_struct_0(X0) = k1_xboole_0 ) ),
    inference(resolution,[],[f450,f460])).

fof(f460,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f182])).

fof(f182,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f74])).

fof(f74,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',dt_l1_pre_topc)).

fof(f450,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_struct_0(X0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f168])).

fof(f168,plain,(
    ! [X0] :
      ( k1_struct_0(X0) = k1_xboole_0
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f69])).

fof(f69,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_struct_0(X0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',d2_struct_0)).

fof(f1095,plain,
    ( spl44_106
    | ~ spl44_52 ),
    inference(avatar_split_clause,[],[f1071,f872,f1093])).

fof(f1093,plain,
    ( spl44_106
  <=> k1_struct_0(sK37) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_106])])).

fof(f872,plain,
    ( spl44_52
  <=> l1_pre_topc(sK37) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_52])])).

fof(f1071,plain,
    ( k1_struct_0(sK37) = k1_xboole_0
    | ~ spl44_52 ),
    inference(resolution,[],[f1038,f873])).

fof(f873,plain,
    ( l1_pre_topc(sK37)
    | ~ spl44_52 ),
    inference(avatar_component_clause,[],[f872])).

fof(f1088,plain,
    ( spl44_104
    | ~ spl44_14 ),
    inference(avatar_split_clause,[],[f1070,f739,f1086])).

fof(f1086,plain,
    ( spl44_104
  <=> k1_struct_0(sK28) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_104])])).

fof(f739,plain,
    ( spl44_14
  <=> l1_pre_topc(sK28) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_14])])).

fof(f1070,plain,
    ( k1_struct_0(sK28) = k1_xboole_0
    | ~ spl44_14 ),
    inference(resolution,[],[f1038,f740])).

fof(f740,plain,
    ( l1_pre_topc(sK28)
    | ~ spl44_14 ),
    inference(avatar_component_clause,[],[f739])).

fof(f1079,plain,
    ( spl44_102
    | ~ spl44_6 ),
    inference(avatar_split_clause,[],[f1069,f711,f1077])).

fof(f1077,plain,
    ( spl44_102
  <=> k1_struct_0(sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_102])])).

fof(f1069,plain,
    ( k1_struct_0(sK0) = k1_xboole_0
    | ~ spl44_6 ),
    inference(resolution,[],[f1038,f712])).

fof(f1062,plain,
    ( spl44_100
    | ~ spl44_46 ),
    inference(avatar_split_clause,[],[f1041,f851,f1060])).

fof(f1060,plain,
    ( spl44_100
  <=> k1_struct_0(sK36) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_100])])).

fof(f851,plain,
    ( spl44_46
  <=> l1_struct_0(sK36) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_46])])).

fof(f1041,plain,
    ( k1_struct_0(sK36) = k1_xboole_0
    | ~ spl44_46 ),
    inference(resolution,[],[f450,f852])).

fof(f852,plain,
    ( l1_struct_0(sK36)
    | ~ spl44_46 ),
    inference(avatar_component_clause,[],[f851])).

fof(f1055,plain,
    ( spl44_98
    | ~ spl44_40 ),
    inference(avatar_split_clause,[],[f1040,f830,f1053])).

fof(f1053,plain,
    ( spl44_98
  <=> k1_struct_0(sK35) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_98])])).

fof(f830,plain,
    ( spl44_40
  <=> l1_struct_0(sK35) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_40])])).

fof(f1040,plain,
    ( k1_struct_0(sK35) = k1_xboole_0
    | ~ spl44_40 ),
    inference(resolution,[],[f450,f831])).

fof(f831,plain,
    ( l1_struct_0(sK35)
    | ~ spl44_40 ),
    inference(avatar_component_clause,[],[f830])).

fof(f1048,plain,
    ( spl44_96
    | ~ spl44_12 ),
    inference(avatar_split_clause,[],[f1039,f732,f1046])).

fof(f1046,plain,
    ( spl44_96
  <=> k1_struct_0(sK27) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_96])])).

fof(f732,plain,
    ( spl44_12
  <=> l1_struct_0(sK27) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_12])])).

fof(f1039,plain,
    ( k1_struct_0(sK27) = k1_xboole_0
    | ~ spl44_12 ),
    inference(resolution,[],[f450,f733])).

fof(f733,plain,
    ( l1_struct_0(sK27)
    | ~ spl44_12 ),
    inference(avatar_component_clause,[],[f732])).

fof(f1033,plain,
    ( spl44_94
    | ~ spl44_16 ),
    inference(avatar_split_clause,[],[f1024,f746,f1031])).

fof(f1031,plain,
    ( spl44_94
  <=> k1_xboole_0 = sK29 ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_94])])).

fof(f746,plain,
    ( spl44_16
  <=> v1_xboole_0(sK29) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_16])])).

fof(f1024,plain,
    ( k1_xboole_0 = sK29
    | ~ spl44_16 ),
    inference(resolution,[],[f505,f747])).

fof(f747,plain,
    ( v1_xboole_0(sK29)
    | ~ spl44_16 ),
    inference(avatar_component_clause,[],[f746])).

fof(f1019,plain,
    ( ~ spl44_93
    | spl44_81 ),
    inference(avatar_split_clause,[],[f1012,f970,f1017])).

fof(f1017,plain,
    ( spl44_93
  <=> ~ v1_xboole_0(sK42) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_93])])).

fof(f1012,plain,
    ( ~ v1_xboole_0(sK42)
    | ~ spl44_81 ),
    inference(resolution,[],[f685,f971])).

fof(f685,plain,(
    ! [X0] :
      ( v3_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f684,f502])).

fof(f502,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f223])).

fof(f223,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',cc1_relat_1)).

fof(f684,plain,(
    ! [X0] :
      ( v3_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f602,f501])).

fof(f501,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f222])).

fof(f222,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',cc1_funct_1)).

fof(f602,plain,(
    ! [X0] :
      ( v3_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f320])).

fof(f320,plain,(
    ! [X0] :
      ( ( v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f319])).

fof(f319,plain,(
    ! [X0] :
      ( ( v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',cc4_funct_1)).

fof(f1011,plain,
    ( spl44_90
    | ~ spl44_16 ),
    inference(avatar_split_clause,[],[f997,f746,f1009])).

fof(f1009,plain,
    ( spl44_90
  <=> v4_funct_1(sK29) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_90])])).

fof(f997,plain,
    ( v4_funct_1(sK29)
    | ~ spl44_16 ),
    inference(resolution,[],[f500,f747])).

fof(f1004,plain,
    ( spl44_88
    | ~ spl44_8 ),
    inference(avatar_split_clause,[],[f996,f718,f1002])).

fof(f996,plain,
    ( v4_funct_1(k1_xboole_0)
    | ~ spl44_8 ),
    inference(resolution,[],[f500,f719])).

fof(f993,plain,(
    spl44_86 ),
    inference(avatar_split_clause,[],[f430,f991])).

fof(f991,plain,
    ( spl44_86
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_86])])).

fof(f430,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

fof(f70,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',d2_xboole_0)).

fof(f986,plain,(
    spl44_84 ),
    inference(avatar_split_clause,[],[f655,f984])).

fof(f984,plain,
    ( spl44_84
  <=> v1_funct_1(sK43) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_84])])).

fof(f655,plain,(
    v1_funct_1(sK43) ),
    inference(cnf_transformation,[],[f422])).

fof(f422,plain,
    ( v1_funct_1(sK43)
    & v1_relat_1(sK43) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK43])],[f151,f421])).

fof(f421,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( v1_funct_1(sK43)
      & v1_relat_1(sK43) ) ),
    introduced(choice_axiom,[])).

fof(f151,plain,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(pure_predicate_removal,[],[f102])).

fof(f102,axiom,(
    ? [X0] :
      ( v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',rc2_funct_1)).

fof(f979,plain,(
    spl44_82 ),
    inference(avatar_split_clause,[],[f654,f977])).

fof(f977,plain,
    ( spl44_82
  <=> v1_relat_1(sK43) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_82])])).

fof(f654,plain,(
    v1_relat_1(sK43) ),
    inference(cnf_transformation,[],[f422])).

fof(f972,plain,(
    ~ spl44_81 ),
    inference(avatar_split_clause,[],[f653,f970])).

fof(f653,plain,(
    ~ v3_funct_1(sK42) ),
    inference(cnf_transformation,[],[f420])).

fof(f420,plain,
    ( ~ v3_funct_1(sK42)
    & v1_funct_1(sK42)
    & v1_relat_1(sK42) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK42])],[f119,f419])).

fof(f419,plain,
    ( ? [X0] :
        ( ~ v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v3_funct_1(sK42)
      & v1_funct_1(sK42)
      & v1_relat_1(sK42) ) ),
    introduced(choice_axiom,[])).

fof(f119,axiom,(
    ? [X0] :
      ( ~ v3_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',rc5_funct_1)).

fof(f965,plain,(
    spl44_78 ),
    inference(avatar_split_clause,[],[f652,f963])).

fof(f652,plain,(
    v1_funct_1(sK42) ),
    inference(cnf_transformation,[],[f420])).

fof(f958,plain,(
    spl44_76 ),
    inference(avatar_split_clause,[],[f651,f956])).

fof(f651,plain,(
    v1_relat_1(sK42) ),
    inference(cnf_transformation,[],[f420])).

fof(f951,plain,(
    spl44_74 ),
    inference(avatar_split_clause,[],[f650,f949])).

fof(f949,plain,
    ( spl44_74
  <=> v1_funct_1(sK41) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_74])])).

fof(f650,plain,(
    v1_funct_1(sK41) ),
    inference(cnf_transformation,[],[f418])).

fof(f418,plain,
    ( v1_funct_1(sK41)
    & v1_relat_1(sK41) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK41])],[f94,f417])).

fof(f417,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( v1_funct_1(sK41)
      & v1_relat_1(sK41) ) ),
    introduced(choice_axiom,[])).

fof(f94,axiom,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',rc1_funct_1)).

fof(f944,plain,(
    spl44_72 ),
    inference(avatar_split_clause,[],[f649,f942])).

fof(f942,plain,
    ( spl44_72
  <=> v1_relat_1(sK41) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_72])])).

fof(f649,plain,(
    v1_relat_1(sK41) ),
    inference(cnf_transformation,[],[f418])).

fof(f937,plain,(
    spl44_70 ),
    inference(avatar_split_clause,[],[f648,f935])).

fof(f935,plain,
    ( spl44_70
  <=> v1_funct_1(sK40) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_70])])).

fof(f648,plain,(
    v1_funct_1(sK40) ),
    inference(cnf_transformation,[],[f416])).

fof(f416,plain,
    ( v1_funct_1(sK40)
    & v1_relat_1(sK40) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK40])],[f145,f415])).

fof(f415,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( v1_funct_1(sK40)
      & v1_relat_1(sK40) ) ),
    introduced(choice_axiom,[])).

fof(f145,plain,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(pure_predicate_removal,[],[f110])).

fof(f110,axiom,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v2_relat_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',rc3_funct_1)).

fof(f930,plain,(
    spl44_68 ),
    inference(avatar_split_clause,[],[f647,f928])).

fof(f928,plain,
    ( spl44_68
  <=> v1_relat_1(sK40) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_68])])).

fof(f647,plain,(
    v1_relat_1(sK40) ),
    inference(cnf_transformation,[],[f416])).

fof(f923,plain,(
    spl44_66 ),
    inference(avatar_split_clause,[],[f646,f921])).

fof(f921,plain,
    ( spl44_66
  <=> v1_relat_1(sK39) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_66])])).

fof(f646,plain,(
    v1_relat_1(sK39) ),
    inference(cnf_transformation,[],[f414])).

fof(f414,plain,(
    v1_relat_1(sK39) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK39])],[f146,f413])).

fof(f413,plain,
    ( ? [X0] : v1_relat_1(X0)
   => v1_relat_1(sK39) ),
    introduced(choice_axiom,[])).

fof(f146,plain,(
    ? [X0] : v1_relat_1(X0) ),
    inference(pure_predicate_removal,[],[f104])).

fof(f104,axiom,(
    ? [X0] :
      ( v2_relat_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',rc2_relat_1)).

fof(f916,plain,(
    spl44_64 ),
    inference(avatar_split_clause,[],[f645,f914])).

fof(f914,plain,
    ( spl44_64
  <=> v8_pre_topc(sK38) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_64])])).

fof(f645,plain,(
    v8_pre_topc(sK38) ),
    inference(cnf_transformation,[],[f412])).

fof(f412,plain,
    ( v8_pre_topc(sK38)
    & v2_pre_topc(sK38)
    & ~ v2_struct_0(sK38)
    & l1_pre_topc(sK38) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK38])],[f93,f411])).

fof(f411,plain,
    ( ? [X0] :
        ( v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0)
        & l1_pre_topc(X0) )
   => ( v8_pre_topc(sK38)
      & v2_pre_topc(sK38)
      & ~ v2_struct_0(sK38)
      & l1_pre_topc(sK38) ) ),
    introduced(choice_axiom,[])).

fof(f93,axiom,(
    ? [X0] :
      ( v8_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',rc1_compts_1)).

fof(f909,plain,(
    spl44_62 ),
    inference(avatar_split_clause,[],[f644,f907])).

fof(f907,plain,
    ( spl44_62
  <=> v2_pre_topc(sK38) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_62])])).

fof(f644,plain,(
    v2_pre_topc(sK38) ),
    inference(cnf_transformation,[],[f412])).

fof(f902,plain,(
    ~ spl44_61 ),
    inference(avatar_split_clause,[],[f643,f900])).

fof(f900,plain,
    ( spl44_61
  <=> ~ v2_struct_0(sK38) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_61])])).

fof(f643,plain,(
    ~ v2_struct_0(sK38) ),
    inference(cnf_transformation,[],[f412])).

fof(f895,plain,(
    spl44_58 ),
    inference(avatar_split_clause,[],[f642,f893])).

fof(f642,plain,(
    l1_pre_topc(sK38) ),
    inference(cnf_transformation,[],[f412])).

fof(f888,plain,(
    spl44_56 ),
    inference(avatar_split_clause,[],[f641,f886])).

fof(f886,plain,
    ( spl44_56
  <=> v2_pre_topc(sK37) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_56])])).

fof(f641,plain,(
    v2_pre_topc(sK37) ),
    inference(cnf_transformation,[],[f410])).

fof(f410,plain,
    ( v2_pre_topc(sK37)
    & ~ v2_struct_0(sK37)
    & l1_pre_topc(sK37) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK37])],[f143,f409])).

fof(f409,plain,
    ( ? [X0] :
        ( v2_pre_topc(X0)
        & ~ v2_struct_0(X0)
        & l1_pre_topc(X0) )
   => ( v2_pre_topc(sK37)
      & ~ v2_struct_0(sK37)
      & l1_pre_topc(sK37) ) ),
    introduced(choice_axiom,[])).

fof(f143,plain,(
    ? [X0] :
      ( v2_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    inference(pure_predicate_removal,[],[f128])).

fof(f128,axiom,(
    ? [X0] :
      ( v7_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',rc9_pre_topc)).

fof(f881,plain,(
    ~ spl44_55 ),
    inference(avatar_split_clause,[],[f640,f879])).

fof(f879,plain,
    ( spl44_55
  <=> ~ v2_struct_0(sK37) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_55])])).

fof(f640,plain,(
    ~ v2_struct_0(sK37) ),
    inference(cnf_transformation,[],[f410])).

fof(f874,plain,(
    spl44_52 ),
    inference(avatar_split_clause,[],[f639,f872])).

fof(f639,plain,(
    l1_pre_topc(sK37) ),
    inference(cnf_transformation,[],[f410])).

fof(f867,plain,(
    spl44_50 ),
    inference(avatar_split_clause,[],[f638,f865])).

fof(f638,plain,(
    v7_struct_0(sK36) ),
    inference(cnf_transformation,[],[f408])).

fof(f408,plain,
    ( v7_struct_0(sK36)
    & ~ v2_struct_0(sK36)
    & l1_struct_0(sK36) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK36])],[f129,f407])).

fof(f407,plain,
    ( ? [X0] :
        ( v7_struct_0(X0)
        & ~ v2_struct_0(X0)
        & l1_struct_0(X0) )
   => ( v7_struct_0(sK36)
      & ~ v2_struct_0(sK36)
      & l1_struct_0(sK36) ) ),
    introduced(choice_axiom,[])).

fof(f129,axiom,(
    ? [X0] :
      ( v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',rc9_struct_0)).

fof(f860,plain,(
    ~ spl44_49 ),
    inference(avatar_split_clause,[],[f637,f858])).

fof(f637,plain,(
    ~ v2_struct_0(sK36) ),
    inference(cnf_transformation,[],[f408])).

fof(f853,plain,(
    spl44_46 ),
    inference(avatar_split_clause,[],[f636,f851])).

fof(f636,plain,(
    l1_struct_0(sK36) ),
    inference(cnf_transformation,[],[f408])).

fof(f846,plain,(
    ~ spl44_45 ),
    inference(avatar_split_clause,[],[f635,f844])).

fof(f844,plain,
    ( spl44_45
  <=> ~ v7_struct_0(sK35) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_45])])).

fof(f635,plain,(
    ~ v7_struct_0(sK35) ),
    inference(cnf_transformation,[],[f406])).

fof(f406,plain,
    ( ~ v7_struct_0(sK35)
    & ~ v2_struct_0(sK35)
    & l1_struct_0(sK35) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35])],[f92,f405])).

fof(f405,plain,
    ( ? [X0] :
        ( ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0)
        & l1_struct_0(X0) )
   => ( ~ v7_struct_0(sK35)
      & ~ v2_struct_0(sK35)
      & l1_struct_0(sK35) ) ),
    introduced(choice_axiom,[])).

fof(f92,axiom,(
    ? [X0] :
      ( ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',rc10_struct_0)).

fof(f839,plain,(
    ~ spl44_43 ),
    inference(avatar_split_clause,[],[f634,f837])).

fof(f837,plain,
    ( spl44_43
  <=> ~ v2_struct_0(sK35) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_43])])).

fof(f634,plain,(
    ~ v2_struct_0(sK35) ),
    inference(cnf_transformation,[],[f406])).

fof(f832,plain,(
    spl44_40 ),
    inference(avatar_split_clause,[],[f633,f830])).

fof(f633,plain,(
    l1_struct_0(sK35) ),
    inference(cnf_transformation,[],[f406])).

fof(f825,plain,(
    spl44_38 ),
    inference(avatar_split_clause,[],[f632,f823])).

fof(f632,plain,(
    v1_zfmisc_1(sK34) ),
    inference(cnf_transformation,[],[f404])).

fof(f404,plain,
    ( v1_zfmisc_1(sK34)
    & ~ v1_xboole_0(sK34) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK34])],[f95,f403])).

fof(f403,plain,
    ( ? [X0] :
        ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v1_zfmisc_1(sK34)
      & ~ v1_xboole_0(sK34) ) ),
    introduced(choice_axiom,[])).

fof(f95,axiom,(
    ? [X0] :
      ( v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',rc1_realset1)).

fof(f818,plain,(
    ~ spl44_37 ),
    inference(avatar_split_clause,[],[f631,f816])).

fof(f631,plain,(
    ~ v1_xboole_0(sK34) ),
    inference(cnf_transformation,[],[f404])).

fof(f811,plain,(
    spl44_34 ),
    inference(avatar_split_clause,[],[f630,f809])).

fof(f809,plain,
    ( spl44_34
  <=> v1_funct_1(sK33) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_34])])).

fof(f630,plain,(
    v1_funct_1(sK33) ),
    inference(cnf_transformation,[],[f402])).

fof(f402,plain,
    ( v1_funct_1(sK33)
    & v1_relat_1(sK33)
    & ~ v1_xboole_0(sK33) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK33])],[f147,f401])).

fof(f401,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v1_funct_1(sK33)
      & v1_relat_1(sK33)
      & ~ v1_xboole_0(sK33) ) ),
    introduced(choice_axiom,[])).

fof(f147,plain,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(pure_predicate_removal,[],[f115])).

fof(f115,axiom,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v2_relat_1(X0)
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',rc4_funct_1)).

fof(f804,plain,(
    spl44_32 ),
    inference(avatar_split_clause,[],[f629,f802])).

fof(f802,plain,
    ( spl44_32
  <=> v1_relat_1(sK33) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_32])])).

fof(f629,plain,(
    v1_relat_1(sK33) ),
    inference(cnf_transformation,[],[f402])).

fof(f797,plain,(
    ~ spl44_31 ),
    inference(avatar_split_clause,[],[f628,f795])).

fof(f795,plain,
    ( spl44_31
  <=> ~ v1_xboole_0(sK33) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_31])])).

fof(f628,plain,(
    ~ v1_xboole_0(sK33) ),
    inference(cnf_transformation,[],[f402])).

fof(f790,plain,(
    spl44_28 ),
    inference(avatar_split_clause,[],[f627,f788])).

fof(f788,plain,
    ( spl44_28
  <=> v1_relat_1(sK32) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_28])])).

fof(f627,plain,(
    v1_relat_1(sK32) ),
    inference(cnf_transformation,[],[f400])).

fof(f400,plain,
    ( v1_relat_1(sK32)
    & ~ v1_xboole_0(sK32) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK32])],[f96,f399])).

fof(f399,plain,
    ( ? [X0] :
        ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v1_relat_1(sK32)
      & ~ v1_xboole_0(sK32) ) ),
    introduced(choice_axiom,[])).

fof(f96,axiom,(
    ? [X0] :
      ( v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',rc1_relat_1)).

fof(f783,plain,(
    ~ spl44_27 ),
    inference(avatar_split_clause,[],[f626,f781])).

fof(f781,plain,
    ( spl44_27
  <=> ~ v1_xboole_0(sK32) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_27])])).

fof(f626,plain,(
    ~ v1_xboole_0(sK32) ),
    inference(cnf_transformation,[],[f400])).

fof(f776,plain,(
    spl44_24 ),
    inference(avatar_split_clause,[],[f625,f774])).

fof(f625,plain,(
    v4_funct_1(sK31) ),
    inference(cnf_transformation,[],[f398])).

fof(f398,plain,
    ( v4_funct_1(sK31)
    & ~ v1_xboole_0(sK31) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK31])],[f125,f397])).

fof(f397,plain,
    ( ? [X0] :
        ( v4_funct_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v4_funct_1(sK31)
      & ~ v1_xboole_0(sK31) ) ),
    introduced(choice_axiom,[])).

fof(f125,axiom,(
    ? [X0] :
      ( v4_funct_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',rc7_funct_1)).

fof(f769,plain,(
    ~ spl44_23 ),
    inference(avatar_split_clause,[],[f624,f767])).

fof(f624,plain,(
    ~ v1_xboole_0(sK31) ),
    inference(cnf_transformation,[],[f398])).

fof(f762,plain,(
    ~ spl44_21 ),
    inference(avatar_split_clause,[],[f623,f760])).

fof(f760,plain,
    ( spl44_21
  <=> ~ v1_zfmisc_1(sK30) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_21])])).

fof(f623,plain,(
    ~ v1_zfmisc_1(sK30) ),
    inference(cnf_transformation,[],[f396])).

fof(f396,plain,
    ( ~ v1_zfmisc_1(sK30)
    & ~ v1_xboole_0(sK30) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK30])],[f103,f395])).

fof(f395,plain,
    ( ? [X0] :
        ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ~ v1_zfmisc_1(sK30)
      & ~ v1_xboole_0(sK30) ) ),
    introduced(choice_axiom,[])).

fof(f103,axiom,(
    ? [X0] :
      ( ~ v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',rc2_realset1)).

fof(f755,plain,(
    ~ spl44_19 ),
    inference(avatar_split_clause,[],[f622,f753])).

fof(f753,plain,
    ( spl44_19
  <=> ~ v1_xboole_0(sK30) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_19])])).

fof(f622,plain,(
    ~ v1_xboole_0(sK30) ),
    inference(cnf_transformation,[],[f396])).

fof(f748,plain,(
    spl44_16 ),
    inference(avatar_split_clause,[],[f621,f746])).

fof(f621,plain,(
    v1_xboole_0(sK29) ),
    inference(cnf_transformation,[],[f394])).

fof(f394,plain,(
    v1_xboole_0(sK29) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK29])],[f100,f393])).

fof(f393,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK29) ),
    introduced(choice_axiom,[])).

fof(f100,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',rc1_xboole_0)).

fof(f741,plain,(
    spl44_14 ),
    inference(avatar_split_clause,[],[f620,f739])).

fof(f620,plain,(
    l1_pre_topc(sK28) ),
    inference(cnf_transformation,[],[f392])).

fof(f392,plain,(
    l1_pre_topc(sK28) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK28])],[f79,f391])).

fof(f391,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK28) ),
    introduced(choice_axiom,[])).

fof(f79,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',existence_l1_pre_topc)).

fof(f734,plain,(
    spl44_12 ),
    inference(avatar_split_clause,[],[f619,f732])).

fof(f619,plain,(
    l1_struct_0(sK27) ),
    inference(cnf_transformation,[],[f390])).

fof(f390,plain,(
    l1_struct_0(sK27) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK27])],[f80,f389])).

fof(f389,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK27) ),
    introduced(choice_axiom,[])).

fof(f80,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',existence_l1_struct_0)).

fof(f727,plain,(
    ~ spl44_11 ),
    inference(avatar_split_clause,[],[f618,f725])).

fof(f725,plain,
    ( spl44_11
  <=> ~ v1_xboole_0(sK26) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_11])])).

fof(f618,plain,(
    ~ v1_xboole_0(sK26) ),
    inference(cnf_transformation,[],[f388])).

fof(f388,plain,(
    ~ v1_xboole_0(sK26) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK26])],[f108,f387])).

fof(f387,plain,
    ( ? [X0] : ~ v1_xboole_0(X0)
   => ~ v1_xboole_0(sK26) ),
    introduced(choice_axiom,[])).

fof(f108,axiom,(
    ? [X0] : ~ v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',rc2_xboole_0)).

fof(f720,plain,(
    spl44_8 ),
    inference(avatar_split_clause,[],[f428,f718])).

fof(f428,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t66_tex_2.p',fc1_xboole_0)).

fof(f713,plain,(
    spl44_6 ),
    inference(avatar_split_clause,[],[f426,f711])).

fof(f426,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f336])).

fof(f706,plain,(
    spl44_4 ),
    inference(avatar_split_clause,[],[f425,f704])).

fof(f425,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f336])).

fof(f699,plain,(
    spl44_2 ),
    inference(avatar_split_clause,[],[f424,f697])).

fof(f424,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f336])).

fof(f692,plain,(
    ~ spl44_1 ),
    inference(avatar_split_clause,[],[f423,f690])).

fof(f423,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f336])).
%------------------------------------------------------------------------------
